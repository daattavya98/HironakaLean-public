/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact
public import Mathlib.RingTheory.TotallySplit
public import Architect
public import Hironaka.Compat.Graded
public import Hironaka.Ch2.Flatness
public import Hironaka.Ch0.NormalFlatness
public import Hironaka.Compat.RegularGraded
public import Hironaka.Ch2.GradedIdeal
public import Hironaka.Ch2.Lemma8Diagram
public import Hironaka.Compat.SubschemeStalk
public import Hironaka.Compat.RegularLocalization
public import Hironaka.Compat.AdicCompletionRegular
public import Hironaka.Compat.GradedLocalization
public import Hironaka.Statements

/-!
# Ch. II §3: Normal flatness along an ascending chain of subschemes (pp. 197–203)

> Let A be a noetherian ring and M an A-module. We say that M is faithfully flat over A (or, a
> faithfully flat A-module) if one (hence all) of the following conditions (equivalent to each
> other) is satisfied:
> (i) M is flat over A and, for any A-module N, M ⊗_A N = 0 implies N = 0.
> (ii) M is flat over A and M ⊗_A A/m ≠ 0 for every maximal ideal m of A.
> (iii) For any sequence of homomorphisms of A-modules: N' → N → N'', it is exact if and only
> if N' ⊗_A M → N ⊗_A M → N'' ⊗_A M is exact. (See Proposition 2.2 of the Seminar note No. IV
> by A. Grothendieck at l'Institut des Hautes Études Scientifiques.) … (pp. 197–198)

Contents, in the paper's order: faithful flatness (pp. 197–198), Lemma 9 and its Corollary
(p. 198), the initial form in `gr_Q(gr_P(R))` (p. 199), Lemma 10 (p. 199), Lemma 11 (p. 200), Theorem 3
(pp. 200–203) and its Corollary (p. 203).

Conventions.  "M is faithfully flat over A" is Mathlib's `Module.FaithfullyFlat A M`, which is
the paper's condition (ii) (see `IsFaithfullyFlat`).  "gr_P(O) is flat over O/P" for a
noetherian local ring `O` is `IsNormallyFlatAlongIdeal P` (Definition 1 of Ch. 0, p. 136, and
Lemma 1 of §1), as in `Hironaka/Ch2/Flatness.lean`; for an `A`-module `M`, "gr_I(M) is flat
over A/I" is `∀ n, Module.Flat (A ⧸ I) (GrModPiece I M n)` (a direct sum is flat iff each
summand is).
The completion of a local ring `O` is `AdicCompletion (maximalIdeal O) O` and `O_Q` is
`Localization.AtPrime Q`.

## Lemma 10 (p. 199)

The paragraph preceding Lemma 10 fixes `R` regular local, `J ⊆ P ⊆ Q` with `P, Q` prime and
`R/P`, `R/Q` regular, and constructs an isomorphism of simply graded `R/Q`-algebras
`λ : gr_Q(gr_P(R)) → gr_Q(R)` as the composite of the canonical isomorphism
`gr⁰_{Q'}(gr_P(R)) ⊗_{R/Q} gr_{Q/P}(R/P) → gr_Q(gr_P(R))` (`Q' = Q·gr_P(R)`) with an
isomorphism `gr⁰_{Q'}(gr_P(R)) ⊗_{R/Q} gr_{Q/P}(R/P) → gr_Q(R)` which "is determined" by a
choice of elements `y₁, …, y_s` of `R` whose residue classes in `R/P` form a minimal base of
`Q/P`.  Lemma 10 says: with `O = R/J`, `P̄ = P/J`, `Q̄ = Q/J` and such a `λ` fixed, if
`gr_{P̄O_Q̄}(O_Q̄)` is flat over `O_Q̄/P̄O_Q̄`, then for every `g ∈ J` the `λ`-image of the initial
form of `g` in `gr_Q(gr_P(R))` is contained in `gr_Q(J, R)_Q`.  `λ` is constructed degreewise, in
each double degree `(ν, n)`, as `lambdaPiece` (the canonical isomorphism `Λ = grModMap` followed by
`λ'`, `lamTensor`), and in each total degree as the isomorphism `lambdaEquiv` (`phiTotal`,
`lambdaTotal`); the paper-form Lemma 10 is `exists_mul_mem_grIdeal_lambdaPiece` (blueprint
`lem:II.3-10`), proved by the printed diagram (`betaDouble`, `alphaDouble`,
`grPieceMapQuot_lambdaPiece`, `lambdaPiece_mem_grIdeal_of_diagram`).  The elementwise form of
Lemma 10 (`λ` encoded by `IsLambdaImage`; blueprint `lem:II.3-10-elementwise`) is kept and follows
from it (`exists_mul_mem_grIdeal_of_isLambdaImage_of_span_eq_map`); Theorem 3 uses the paper-form
Lemma 10 directly (`exists_mul_mem_grIdeal_lambdaPiece_of_isQuasiRegular`).
The notion Lemma 10 concerns, the initial form of an element of `gr_P(R)` in `gr_Q(gr_P(R))`, is
`doubleInitialForm` below (and `doubleInitialFormPiece` in a double degree).
-/

@[expose] public section

open TensorProduct AlgebraicGeometry

namespace Hironaka

universe u

/-! ### Faithful flatness (pp. 197–198) -/

section FaithfullyFlat

/-- p. 197: "Let A be a noetherian ring and M an A-module. We say that M is faithfully flat over
A (or, a faithfully flat A-module) if one (hence all) of the following conditions (equivalent to
each other) is satisfied: (i) M is flat over A and, for any A-module N, M ⊗_A N = 0 implies
N = 0. (ii) M is flat over A and M ⊗_A A/m ≠ 0 for every maximal ideal m of A. (iii) For any
sequence of homomorphisms of A-modules N' → N → N'', it is exact if and only if
N' ⊗_A M → N ⊗_A M → N'' ⊗_A M is exact."

We take Mathlib's `Module.FaithfullyFlat A M`: "`M` is flat and `m • M ≠ M` for every maximal
ideal `m` of `A`" (Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean), which is the paper's
condition (ii), since `M ⊗_A A/m ≅ M/mM`.  This abbreviation only carries the blueprint node;
every statement below uses `Module.FaithfullyFlat` directly.  The equivalence with (i) and
(iii) is `faithfullyFlat_tfae`. -/
@[blueprint "def:II.3-faithfully-flat"
  (statement := /-- Let $A$ be a noetherian ring and $M$ an $A$-module. We say that $M$ is
    \emph{faithfully flat over $A$} (or, a faithfully flat $A$-module) if one (hence all) of
    the following conditions (equivalent to each other) is satisfied: (i) $M$ is flat over $A$
    and, for any $A$-module $N$, $M\otimes_AN=0$ implies $N=0$; (ii) $M$ is flat over $A$ and
    $M\otimes_AA/\mathfrak m\ne0$ for every maximal ideal $\mathfrak m$ of $A$; (iii) for any
    sequence of homomorphisms of $A$-modules $N'\to N\to N''$, it is exact if and only if
    $N'\otimes_AM\to N\otimes_AM\to N''\otimes_AM$ is exact. (p.~197.) (Formalization note:
    the definition adopted is Mathlib's \texttt{Module.FaithfullyFlat}, i.e.\ condition (ii)
    in the form ``$M$ is flat and $\mathfrak mM\ne M$ for every maximal ideal $\mathfrak m$'';
    the equivalence with (i) and (iii) is \cref{lem:II.3-faithfully-flat-tfae}.) -/)
  (latexEnv := "definition")]
abbrev IsFaithfullyFlat (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M]
    [Module A M] : Prop :=
  Module.FaithfullyFlat A M

/-- The paper's conditions (i), (ii), (iii) of p. 197 are equivalent to each other and to
Mathlib's `Module.FaithfullyFlat A M`.  Order of the list: Mathlib's definition, (i), (ii),
(iii).  ("`M ⊗_A N = 0`" is `Subsingleton (M ⊗[A] N)`, "`≠ 0`" is `Nontrivial`.) -/
@[blueprint "lem:II.3-faithfully-flat-tfae"
  (statement := /-- Let $A$ be a noetherian ring and $M$ an $A$-module. The conditions (i),
    (ii) and (iii) of \cref{def:II.3-faithfully-flat} are equivalent to each other (and to
    \texttt{Module.FaithfullyFlat}). (p.~197.) -/)
  (proof := /-- Cited by the paper: ``Proposition 2.2 of the Seminar note No.~IV by A.~Grothendieck at l'Institut des Hautes \'Etudes Scientifiques'' (pp.~197--198). In Mathlib:
    \texttt{Module.FaithfullyFlat.iff\_flat\_and\_lTensor\_reflects\_triviality} for (i),
    $M\otimes_AA/\mathfrak m\cong M/\mathfrak mM$ for (ii), and
    \texttt{Module.FaithfullyFlat.iff\_exact\_iff\_rTensor\_exact} for (iii). -/)
  (latexEnv := "lemma")]
theorem faithfullyFlat_tfae (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] :
    [Module.FaithfullyFlat A M,
      Module.Flat A M ∧ ∀ (N : Type u) [AddCommGroup N] [Module A N],
        Subsingleton (M ⊗[A] N) → Subsingleton N,
      Module.Flat A M ∧ ∀ m : Ideal A, m.IsMaximal → Nontrivial (M ⊗[A] (A ⧸ m)),
      ∀ (N₁ : Type u) [AddCommGroup N₁] [Module A N₁] (N₂ : Type u) [AddCommGroup N₂]
        [Module A N₂] (N₃ : Type u) [AddCommGroup N₃] [Module A N₃]
        (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N₃),
        Function.Exact f g ↔ Function.Exact (f.rTensor M) (g.rTensor M)].TFAE := by
  tfae_have 1 ↔ 2 := Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality A M
  tfae_have 1 ↔ 3 := by
    rw [Module.faithfullyFlat_iff]
    refine and_congr_right fun _ => forall_congr' fun m => imp_congr_right fun _ => ?_
    rw [(TensorProduct.tensorQuotEquivQuotSMul M m).toEquiv.nontrivial_congr,
      Submodule.Quotient.nontrivial_iff]
  tfae_have 1 ↔ 4 := Module.FaithfullyFlat.iff_exact_iff_rTensor_exact A M
  tfae_finish

/-- p. 198: "It follows immediately that: Let A → B be a local homomorphism of local rings and
M a B-module of finite type. Then M is faithfully flat over A if and only if it is flat over A
and different from zero."  (Local rings are noetherian throughout the paper, p. 181; the proof
does not use it.) -/
@[blueprint "lem:II.3-faithfully-flat-local"
  (statement := /-- Let $A\to B$ be a local homomorphism of local rings and $M$ a $B$-module
    of finite type. Then $M$ is faithfully flat over $A$ if and only if it is flat over $A$
    and different from zero. (p.~198.) -/)
  (proof := /-- ``It follows immediately'' from condition (ii) of
    \cref{def:II.3-faithfully-flat}: the only maximal ideal of $A$ is $\mathfrak m_A$, and
    $\mathfrak m_AM\subseteq\mathfrak m_BM\ne M$ by Nakayama's lemma when $M\ne0$; conversely
    $\mathfrak m_AM\ne M$ forces $M\ne0$. -/)
  (latexEnv := "lemma")]
theorem faithfullyFlat_iff_flat_and_nontrivial (A B : Type u) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] (M : Type u) [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] [Module.Finite B M] :
    Module.FaithfullyFlat A M ↔ Module.Flat A M ∧ Nontrivial M := by
  constructor
  · intro h
    refine ⟨inferInstance, ?_⟩
    by_contra hM
    rw [not_nontrivial_iff_subsingleton] at hM
    have : Subsingleton (Submodule A M) := (Submodule.subsingleton_iff A).mpr hM
    exact h.submodule_ne_top (IsLocalRing.maximalIdeal.isMaximal A) (Subsingleton.elim _ _)
  · rintro ⟨hflat, hM⟩
    refine ⟨fun m hm hmM => ?_⟩
    rw [IsLocalRing.eq_maximalIdeal hm] at hmM
    -- `m_A M ⊆ m_B M` since `A → B` is local, and `m_B M ≠ M` by Nakayama's lemma over `B`.
    have hle : (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M) ≤
        ((IsLocalRing.maximalIdeal B) • (⊤ : Submodule B M)).restrictScalars A := by
      refine Submodule.smul_le.mpr fun a ha x _ => ?_
      rw [Submodule.restrictScalars_mem, ← algebraMap_smul B a x]
      exact Submodule.smul_mem_smul (map_nonunit (algebraMap A B) a ha) Submodule.mem_top
    rw [hmM, top_le_iff, Submodule.restrictScalars_eq_top_iff] at hle
    have hann : Module.annihilator B M ≠ ⊤ := fun h =>
      not_subsingleton M (Module.annihilator_eq_top_iff.mp h)
    exact Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.jacobson_eq_maximalIdeal _ hann).ge hle.symm

end FaithfullyFlat

/-! ### Lemma 9 and its Corollary (p. 198) -/

section Lemma9

open GrModPiece

/-- `λ_n : (IⁿM) ⊗_A A' → Iⁿ(M ⊗_A A')` of the proof of Lemma 9 (p. 198), before tensoring: the
restriction `IⁿM → I'ⁿM'` of `f : M → M'`, `I' = IA'`; `Iⁿ(M ⊗_A A') = I'ⁿ(M ⊗_A A')` since
`I'ⁿ = IⁿA'`. -/
private def smulTopRestrictPow {A : Type u} (A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {M : Type u} [AddCommGroup M] [Module A M] {M' : Type u} [AddCommGroup M'] [Module A' M']
    [Module A M'] [IsScalarTower A A' M'] (f : M →ₗ[A] M') (I : Ideal A) (n : ℕ) :
    ↥(I ^ n • (⊤ : Submodule A M)) →ₗ[A] ↥(I.map (algebraMap A A') ^ n • (⊤ : Submodule A' M')) :=
  smulTopRestrict f (I ^ n) (I.map (algebraMap A A') ^ n) (Ideal.map_pow _ _ _).le

/-- `IsBaseChange` says that the `A'`-linear extension `A' ⊗_A N → N'` of `l : N → N'` is
bijective. -/
private theorem isBaseChange_iff_bijective_liftBaseChange {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] {N N' : Type u} [AddCommGroup N] [Module R N] [AddCommGroup N']
    [Module S N'] [Module R N'] [IsScalarTower R S N'] (l : N →ₗ[R] N') :
    IsBaseChange S l ↔ Function.Bijective (l.liftBaseChange S) := by
  constructor
  · intro h
    have : (l.liftBaseChange S : S ⊗[R] N → N') = h.equiv := by
      funext x
      induction x using TensorProduct.inductionOn with
      | tmul s m => simp [IsBaseChange.equiv_tmul]
      | add x y hx hy => rw [map_add, hx, hy, map_add]
    rw [this]
    exact h.equiv.bijective
  · intro h
    exact IsBaseChange.of_equiv (LinearEquiv.ofBijective (l.liftBaseChange S) h) fun x => by
      simp

/-- Proof of Lemma 9, "It is clear that `λₙ` is surjective for all `n`" (p. 198): `I'ⁿ(M ⊗_A A')`
is generated, as an `A'`-module, by the elements `a · f(m)` with `a ∈ Iⁿ`, `m ∈ M`, and
`a · f(m) = f(a m) = λₙ(a m)`. -/
private theorem surjective_liftBaseChange_smulTopRestrict {A A' : Type u} [CommRing A]
    [CommRing A'] [Algebra A A'] {M : Type u} [AddCommGroup M] [Module A M] {M' : Type u}
    [AddCommGroup M'] [Module A' M'] [Module A M'] [IsScalarTower A A' M'] {f : M →ₗ[A] M'}
    (hf : IsBaseChange A' f) (J : Ideal A) (J' : Ideal A')
    (hJ : J.map (algebraMap A A') = J') :
    Function.Surjective ((smulTopRestrict f J J' hJ.le).liftBaseChange A') := by
  rintro ⟨y, hy⟩
  -- `r • n` is in the image for `r ∈ J'` and `n ∈ M'`, `J' = JA'` being generated by `J`
  have hr_all : ∀ r ∈ J', ∀ n : M',
      ∃ x, (((smulTopRestrict f J J' hJ.le).liftBaseChange A' x :
        ↥(J' • (⊤ : Submodule A' M'))) : M') = r • n := by
    intro r hr
    rw [← hJ] at hr
    have hr' : r ∈ Submodule.span A' (algebraMap A A' '' J) := hr
    clear hr
    induction hr' using Submodule.span_induction with
    | mem r hmem =>
      intro n
      obtain ⟨a, ha, rfl⟩ := hmem
      induction n using hf.inductionOn with
      | tmul m =>
        refine ⟨1 ⊗ₜ ⟨a • m, Submodule.smul_mem_smul ha Submodule.mem_top⟩, ?_⟩
        simp [smulTopRestrict, algebraMap_smul]
      | smul s n hn =>
        obtain ⟨x, hx⟩ := hn
        refine ⟨s • x, ?_⟩
        rw [map_smul, Submodule.coe_smul, hx, smul_comm]
      | add x y hx hy =>
        obtain ⟨u, hu⟩ := hx
        obtain ⟨v, hv⟩ := hy
        exact ⟨u + v, by rw [map_add, Submodule.coe_add, hu, hv, smul_add]⟩
    | zero => exact fun n => ⟨0, by simp⟩
    | add r s _ _ hr hs =>
      intro n
      obtain ⟨u, hu⟩ := hr n
      obtain ⟨v, hv⟩ := hs n
      exact ⟨u + v, by rw [map_add, Submodule.coe_add, hu, hv, add_smul]⟩
    | smul c r _ hr =>
      intro n
      obtain ⟨u, hu⟩ := hr n
      exact ⟨c • u, by rw [map_smul, Submodule.coe_smul, hu, smul_eq_mul, mul_smul]⟩
  have key : ∀ y ∈ J' • (⊤ : Submodule A' M'),
      ∃ x, (((smulTopRestrict f J J' hJ.le).liftBaseChange A' x : ↥(J' • (⊤ : Submodule A' M')))
        : M') = y := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun r hr n _ => hr_all r hr n) (fun x y hx hy => ?_)
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add, Submodule.coe_add, hu, hv]⟩
  obtain ⟨x, hx⟩ := key y hy
  exact ⟨x, Subtype.ext hx⟩

/-- Proof of Lemma 9, "Since `λ₀` is bijective" (p. 198): `I⁰M = M` and `I'⁰M' = M'`, so `λ₀` is
the map `f : M → M'` itself. -/
private theorem isBaseChange_smulTopRestrictPow_zero {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] {M : Type u} [AddCommGroup M] [Module A M] {M' : Type u} [AddCommGroup M']
    [Module A' M'] [Module A M'] [IsScalarTower A A' M'] {f : M →ₗ[A] M'}
    (hf : IsBaseChange A' f) (I : Ideal A) : IsBaseChange A' (smulTopRestrictPow A' f I 0) := by
  have h₀ : I ^ 0 • (⊤ : Submodule A M) = ⊤ := by
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  have h₀' : I.map (algebraMap A A') ^ 0 • (⊤ : Submodule A' M') = ⊤ := by
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  exact (IsBaseChange.iff_of_equiv_comm (LinearEquiv.ofTop _ h₀).symm
    (LinearEquiv.ofTop _ h₀').symm (LinearMap.ext fun m => Subtype.ext rfl)).mp hf

/-- The map `ε_n : grⁿ_I(M) → grⁿ_{I'}(M')` of the proof of Lemma 9 (p. 198), induced by `λₙ`
(`M' = M ⊗_A A'`, `I' = IA'`), before tensoring with `A'`. -/
private def grModPieceMap {A : Type u} (A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {M : Type u} [AddCommGroup M] [Module A M] {M' : Type u} [AddCommGroup M'] [Module A' M']
    [Module A M'] [IsScalarTower A A' M'] (f : M →ₗ[A] M') (I : Ideal A) (n : ℕ) :
    GrModPiece I M n →ₗ[A] GrModPiece (I.map (algebraMap A A')) M' n :=
  (Submodule.comap (I ^ n • ⊤ : Submodule A M).subtype (I ^ (n + 1) • ⊤)).liftQ
    ((Submodule.comap (I.map (algebraMap A A') ^ n • ⊤ : Submodule A' M').subtype
      (I.map (algebraMap A A') ^ (n + 1) • ⊤)).mkQ.restrictScalars A ∘ₗ smulTopRestrictPow A' f I n)
    (by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact map_mem_smul_top_of_map_le f (Ideal.map_pow _ _ _).le hx)

/-- Proof of Lemma 9, the induction step (p. 198): "Since `A'` is flat over `A`, the first
horizontal sequence is exact. The second sequence is clearly exact. (Note that
`Iⁿ(M ⊗_A A') = I'ⁿ(M ⊗_A A')` for all `n`.) It is clear that `λₙ` is surjective for all `n`,
hence, so is `εₙ`. Therefore the above diagram shows that, if `λₙ` is bijective, then `λₙ₊₁` and
`εₙ` are bijective."  Here "bijective" is `IsBaseChange A'`, i.e. bijectivity of the `A'`-linear
extension to `A' ⊗_A (-)`. -/
private theorem isBaseChange_smulTopRestrictPow_succ_and_grModPieceMap {A A' : Type u}
    [CommRing A] [CommRing A'] [Algebra A A'] [Module.Flat A A'] {M : Type u} [AddCommGroup M]
    [Module A M] {M' : Type u} [AddCommGroup M'] [Module A' M'] [Module A M']
    [IsScalarTower A A' M'] {f : M →ₗ[A] M'} (hf : IsBaseChange A' f) (I : Ideal A) (n : ℕ)
    (hn : IsBaseChange A' (smulTopRestrictPow A' f I n)) :
    IsBaseChange A' (smulTopRestrictPow A' f I (n + 1)) ∧ IsBaseChange A' (grModPieceMap A' f I n) := by
  have hle : I ^ (n + 1) • (⊤ : Submodule A M) ≤ I ^ n • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right n.le_succ)
  have hle' : I.map (algebraMap A A') ^ (n + 1) • (⊤ : Submodule A' M') ≤
      I.map (algebraMap A A') ^ n • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right n.le_succ)
  -- "Since `A'` is flat over `A`, the first horizontal sequence is exact": its left map
  -- `(Iⁿ⁺¹M) ⊗_A A' → (IⁿM) ⊗_A A'` is injective.
  have hinj : Function.Injective ((Submodule.inclusion hle).baseChange A') := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.inclusion_injective hle)
  -- The left square commutes.
  have hcomm : ∀ z, (smulTopRestrictPow A' f I n).liftBaseChange A'
      ((Submodule.inclusion hle).baseChange A' z) =
      Submodule.inclusion hle' ((smulTopRestrictPow A' f I (n + 1)).liftBaseChange A' z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x => exact Subtype.ext rfl
    | add y z hy hz => rw [map_add, map_add, map_add, map_add, hy, hz]
  -- `λₙ₊₁` is bijective: it is surjective ("It is clear that `λₙ` is surjective for all `n`")
  -- and injective, since `λₙ` is injective and the first row is exact on the left.
  have h₁ : IsBaseChange A' (smulTopRestrictPow A' f I (n + 1)) := by
    rw [isBaseChange_iff_bijective_liftBaseChange] at hn ⊢
    refine ⟨fun x y hxy => hinj (hn.1 ?_), surjective_liftBaseChange_smulTopRestrict hf _ _
      (Ideal.map_pow _ _ _)⟩
    rw [hcomm, hcomm, hxy]
  refine ⟨h₁, ?_⟩
  -- `εₙ` is bijective: the diagram, whose rows are exact, has bijective `λₙ₊₁`, `λₙ`.
  refine IsBaseChange.of_right_exact A' (smulTopRestrictPow A' f I (n + 1))
    (smulTopRestrictPow A' f I n) (grModPieceMap A' f I n) (f := Submodule.inclusion hle)
    (g := (Submodule.comap (I ^ n • ⊤ : Submodule A M).subtype (I ^ (n + 1) • ⊤)).mkQ)
    (f' := Submodule.inclusion hle')
    (g' := (Submodule.comap (I.map (algebraMap A A') ^ n • ⊤ : Submodule A' M').subtype
      (I.map (algebraMap A A') ^ (n + 1) • ⊤)).mkQ) ?_ ?_ h₁ hn ?_ (Submodule.mkQ_surjective _)
    ?_ (Submodule.mkQ_surjective _)
  · ext x; rfl
  · ext x; rfl
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_inclusion]
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_inclusion]

/-- Proof of Lemma 9, the induction on `n` (p. 198): "Since `λ₀` is bijective, `λₙ` and `εₙ` can
be proved bijective by induction on `n`."  This is the first half: every `λₙ` is bijective. -/
private theorem isBaseChange_smulTopRestrictPow {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] [Module.Flat A A'] {M : Type u} [AddCommGroup M] [Module A M] {M' : Type u}
    [AddCommGroup M'] [Module A' M'] [Module A M'] [IsScalarTower A A' M'] {f : M →ₗ[A] M'}
    (hf : IsBaseChange A' f) (I : Ideal A) (n : ℕ) :
    IsBaseChange A' (smulTopRestrictPow A' f I n) := by
  induction n with
  | zero => exact isBaseChange_smulTopRestrictPow_zero hf I
  | succ n ih => exact (isBaseChange_smulTopRestrictPow_succ_and_grModPieceMap hf I n ih).1

/-- Proof of Lemma 9, the induction on `n` (p. 198), second half: every `εₙ` is bijective. -/
private theorem isBaseChange_grModPieceMap {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] [Module.Flat A A'] {M : Type u} [AddCommGroup M] [Module A M] {M' : Type u}
    [AddCommGroup M'] [Module A' M'] [Module A M'] [IsScalarTower A A' M'] {f : M →ₗ[A] M'}
    (hf : IsBaseChange A' f) (I : Ideal A) (n : ℕ) : IsBaseChange A' (grModPieceMap A' f I n) :=
  (isBaseChange_smulTopRestrictPow_succ_and_grModPieceMap hf I n
    (isBaseChange_smulTopRestrictPow hf I n)).2

/-- Proof of Lemma 9, second step: if `A'` is flat over `A` and `M'` is the base change of `M`
(e.g. `M' = M ⊗_A A'`), then `ε_n : grⁿ_I(M) ⊗_A A' → grⁿ_{I'}(M')` is bijective, which gives
an `A'/I'`-linear isomorphism `grⁿ_I(M) ⊗_{A/I} A'/I' ≅ grⁿ_{I'}(M')` (`I' = IA'`). -/
private theorem nonempty_grModPiece_baseChange_equiv {A A' : Type u} [CommRing A]
    [CommRing A'] [Algebra A A'] [Module.Flat A A'] {M : Type u} [AddCommGroup M] [Module A M]
    {M' : Type u} [AddCommGroup M'] [Module A' M'] [Module A M'] [IsScalarTower A A' M']
    {f : M →ₗ[A] M'} (hf : IsBaseChange A' f) (I : Ideal A) (n : ℕ) :
    Nonempty ((A' ⧸ I.map (algebraMap A A')) ⊗[A ⧸ I] GrModPiece I M n ≃ₗ[A' ⧸ I.map
      (algebraMap A A')] GrModPiece (I.map (algebraMap A A')) M' n) := by
  -- `grⁿ_{I'}(M') ≅ grⁿ_I(M) ⊗_A A' = grⁿ_I(M) ⊗_A A'/I' = grⁿ_I(M) ⊗_{A/I} A'/I'`.
  have hT := (isBaseChange_grModPieceMap hf I n).comp (isBaseChange_quotient_id
    (I.map (algebraMap A A')) (GrModPiece (I.map (algebraMap A A')) M' n))
  exact ⟨LinearEquiv.baseChange (A ⧸ I) (A' ⧸ I.map (algebraMap A A')) _ _
      (isBaseChange_quotient_id I (GrModPiece I M n)).equiv.symm ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A' ⧸ I.map (algebraMap A A'))
      (A' ⧸ I.map (algebraMap A A')) (GrModPiece I M n) ≪≫ₗ hT.equiv⟩

/-- Lemma 9 for one degree `n` and any base change `M'` of `M` along the faithfully flat
`A → A'`: `grⁿ_I(M)` is flat over `A/I` iff `grⁿ_{I'}(M')` is flat over `A'/I'`. -/
private theorem grModPiece_flat_iff_of_isBaseChange {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] [Module.FaithfullyFlat A A'] {M : Type u} [AddCommGroup M] [Module A M]
    {M' : Type u} [AddCommGroup M'] [Module A' M'] [Module A M'] [IsScalarTower A A' M']
    {f : M →ₗ[A] M'} (hf : IsBaseChange A' f) (I : Ideal A) (n : ℕ) :
    Module.Flat (A ⧸ I) (GrModPiece I M n) ↔
      Module.Flat (A' ⧸ I.map (algebraMap A A')) (GrModPiece (I.map (algebraMap A A')) M' n) := by
  obtain ⟨e⟩ := nonempty_grModPiece_baseChange_equiv hf I n
  -- `A'/I' = A/I ⊗_A A'` is faithfully flat over `A/I`.
  have : Module.FaithfullyFlat (A ⧸ I) (A' ⧸ I.map (algebraMap A A')) :=
    Module.FaithfullyFlat.of_linearEquiv _ _
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A' I).toLinearEquiv
  exact (Module.Flat.iff_flat_tensorProduct (R := A ⧸ I) (M := GrModPiece I M n)
    (A' ⧸ I.map (algebraMap A A'))).symm.trans (Module.Flat.equiv_iff e)

/-- Lemma 9, p. 198: "Let A → A' be a homomorphism of noetherian rings. Let I be an ideal in A
and I' = IA'. Suppose A' be faithfully flat over A. Then, for an A-module M of finite type,
gr_I(M) is flat over A/I if and only if gr_{I'}(M ⊗_A A') is flat over A'/I'."

Encoding: the homomorphism `A → A'` is `[Algebra A A']`; "gr_I(M) is flat over A/I" is
"`grⁿ_I(M) = IⁿM/Iⁿ⁺¹M` is flat over `A/I` for every `n`" (`GrModPiece`, cf. the conventions
in the module docstring); `M ⊗_A A'` is `A' ⊗[A] M`, on which Mathlib puts the `A'`-module
structure.

The proof is the paper's (p. 198), step by step.  The diagram has the exact rows `0 → (Iⁿ⁺¹M) ⊗_A A'
→ (IⁿM) ⊗_A A' → grⁿ_I(M) ⊗_A A' → 0` and `0 → Iⁿ⁺¹(M ⊗_A A') → Iⁿ(M ⊗_A A') → grⁿ_{I'}(M ⊗_A A')
→ 0` with vertical arrows `λₙ₊₁`, `λₙ`, `εₙ` (`smulTopRestrictPow`, `grModPieceMap`; `Iⁿ(M ⊗_A A') =
I'ⁿ(M ⊗_A A')` is built in, `I'ⁿ = IⁿA'` being `Ideal.map_pow`).  "Since `A'` is flat over `A`,
the first horizontal sequence is exact" is the injectivity of its left map; "It is clear that
`λₙ` is surjective for all `n`" is `surjective_liftBaseChange_smulTopRestrict`; "if `λₙ` is
bijective, then `λₙ₊₁` and `εₙ` are bijective" is
`isBaseChange_smulTopRestrictPow_succ_and_grModPieceMap`; "Since `λ₀` is bijective, `λₙ` and
`εₙ` can be proved bijective by induction on `n`" is the induction in
`isBaseChange_smulTopRestrictPow` and `isBaseChange_grModPieceMap`; the descent step
("`A'/I'` is faithfully flat over `A/I`" and `grⁿ_I(M) ⊗_{A/I} A'/I' = grⁿ_I(M) ⊗_A A'`) is in
`nonempty_grModPiece_baseChange_equiv` and `grModPiece_flat_iff_of_isBaseChange`.  Gaps filled:
"the second sequence is clearly exact", "it is clear that `λₙ` is surjective", "since `λ₀` is
bijective" (`λ₀ = f`) and "`A'/I'` is faithfully flat over `A/I`" are proved. -/
@[blueprint "lem:II.3-9"
  (statement := /-- Let $A\to A'$ be a homomorphism of noetherian rings. Let $I$ be an ideal
    in $A$ and $I'=IA'$. Suppose $A'$ be faithfully flat over $A$. Then, for an $A$-module $M$
    of finite type, $\operatorname{gr}_I(M)$ is flat over $A/I$ if and only if
    $\operatorname{gr}_{I'}(M\otimes_AA')$ is flat over $A'/I'$. (p.~198.) (Formalization
    note: ``$\operatorname{gr}_I(M)$ is flat over $A/I$'' is transcribed as
    ``$\operatorname{gr}^n_I(M)$ is flat over $A/I$ for every $n$''
    (\cref{def:II.1-graded-module}), and $M\otimes_AA'$ is written $A'\otimes_AM$.) -/)
  (proof := /-- Consider the commutative diagram with rows
    $0\to(I^{n+1}M)\otimes_AA'\to(I^nM)\otimes_AA'\to\operatorname{gr}^n_I(M)\otimes_AA'\to0$
    and $0\to I^{n+1}(M\otimes_AA')\to I^n(M\otimes_AA')\to
    \operatorname{gr}^n_{I'}(M\otimes_AA')\to0$, with vertical arrows $\lambda_{n+1}$,
    $\lambda_n$, $\varepsilon_n$. Since $A'$ is flat over $A$, the first horizontal sequence
    is exact. The second sequence is clearly exact. (Note that
    $I^n(M\otimes_AA')=I'^n(M\otimes_AA')$ for all $n$.) It is clear that $\lambda_n$ is
    surjective for all $n$, hence, so is $\varepsilon_n$. Therefore the above diagram shows
    that, if $\lambda_n$ is bijective, then $\lambda_{n+1}$ and $\varepsilon_n$ are
    bijective. Since $\lambda_0$ is bijective, $\lambda_n$ and $\varepsilon_n$ can be proved
    bijective by induction on $n$. Thus we have an isomorphism of $A'$-modules
    $\varepsilon_n\colon\operatorname{gr}^n_I(M)\otimes_AA'\cong
    \operatorname{gr}^n_{I'}(M\otimes_AA')$ for every non-negative integer $n$. Now, since
    $A'$ is faithfully flat over $A$, so is $A'/I'$ over $A/I$. Hence
    $\operatorname{gr}^n_I(M)$ is flat over $A/I$ if and only if
    $\operatorname{gr}^n_I(M)\otimes_{A/I}A'/I'$ $(=\operatorname{gr}^n_I(M)\otimes_AA')$ is
    flat over $A'/I'$. In view of the isomorphism $\varepsilon_n$, $\operatorname{gr}_I(M)$ is
    flat over $A/I$ if and only if $\operatorname{gr}_{I'}(M\otimes_AA')$ is flat over
    $A'/I'$.

    \textbf{Lean.} The proof follows the printed one, step by step. The maps $\lambda_n$ and
    $\varepsilon_n$ are the vertical arrows of the diagram (with $I^n(M\otimes_AA')$ replaced by
    $I'^n(M\otimes_AA')$, as the paper's note allows; $I'^n=I^nA'$). ``Since $A'$ is flat over
    $A$, the first horizontal sequence is exact'': its left map is injective. The exactness of
    the second sequence, the surjectivity of $\lambda_n$ (``it is clear''), the bijectivity of
    $\lambda_0$ (it is the map $M\to M\otimes_AA'$ itself) and the faithful flatness of $A'/I'$
    over $A/I$ are not argued in the paper and are proved in Lean. The step ``if $\lambda_n$ is
    bijective then $\lambda_{n+1}$ and $\varepsilon_n$ are bijective'' is the diagram chase of
    the paper; the induction on $n$ is carried out as printed. -/)
  (latexEnv := "lemma")]
theorem grModPiece_flat_iff_flat_baseChange (A A' : Type u) [CommRing A] [CommRing A']
    [IsNoetherianRing A] [IsNoetherianRing A'] [Algebra A A']
    (hA' : Module.FaithfullyFlat A A') (I : Ideal A) (M : Type u) [AddCommGroup M]
    [Module A M] [Module.Finite A M] :
    (∀ n : ℕ, Module.Flat (A ⧸ I) (GrModPiece I M n)) ↔
      ∀ n : ℕ, Module.Flat (A' ⧸ I.map (algebraMap A A'))
        (GrModPiece (I.map (algebraMap A A')) (A' ⊗[A] M) n) :=
  forall_congr' fun n =>
    grModPiece_flat_iff_of_isBaseChange (TensorProduct.isBaseChange A M A') I n

variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]

/-- The completion `Ô` of the local ring `O` (with respect to its maximal ideal). -/
local notation "Ô" => AdicCompletion (IsLocalRing.maximalIdeal O) O

/-- Lemma 9 for the ring itself (`M = A`) along a faithfully flat `A → A'` with `A` noetherian
local: `A` is normally flat along `I` iff `A'` is normally flat along `IA'`. -/
private theorem isNormallyFlatAlongIdeal_iff_of_faithfullyFlat {A A' : Type u} [CommRing A]
    [CommRing A'] [IsLocalRing A] [IsNoetherianRing A] [Algebra A A']
    [Module.FaithfullyFlat A A'] (I : Ideal A) :
    IsNormallyFlatAlongIdeal I ↔ IsNormallyFlatAlongIdeal (I.map (algebraMap A A')) := by
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · obtain ⟨e₁⟩ := GrPiece.nonempty_equiv_grModPiece I n
    obtain ⟨e₂⟩ := GrPiece.nonempty_equiv_grModPiece (I.map (algebraMap A A')) n
    obtain ⟨e⟩ := nonempty_grModPiece_baseChange_equiv (IsBaseChange.linearMap A A') I n
    have := h n
    have : Module.Free (A ⧸ I) (GrModPiece I A n) := Module.Free.of_equiv e₁
    exact Module.Free.of_equiv (e ≪≫ₗ e₂.symm)
  · rw [isNormallyFlatAlongIdeal_iff_flat]
    intro n
    obtain ⟨e₁⟩ := GrPiece.nonempty_equiv_grModPiece I n
    obtain ⟨e₂⟩ := GrPiece.nonempty_equiv_grModPiece (I.map (algebraMap A A')) n
    have := h n
    have : Module.Flat (A' ⧸ I.map (algebraMap A A'))
        (GrModPiece (I.map (algebraMap A A')) A' n) := Module.Flat.of_linearEquiv e₂.symm
    have := (grModPiece_flat_iff_of_isBaseChange (IsBaseChange.linearMap A A') I n).mpr this
    exact Module.Flat.of_linearEquiv e₁

/-- The second assertion of the Corollary to Lemma 9, once `Q̂ = QÔ` is known to be prime. -/
private theorem isNormallyFlatAlongIdeal_localization_iff_completion_of_isPrime (P Q : Ideal O)
    [Q.IsPrime] [(Q.map (algebraMap O Ô)).IsPrime] :
    IsNormallyFlatAlongIdeal (P.map (algebraMap O (Localization.AtPrime Q))) ↔
      IsNormallyFlatAlongIdeal ((P.map (algebraMap O Ô)).map
        (algebraMap Ô (Localization.AtPrime (Q.map (algebraMap O Ô))))) := by
  -- `Ô` is faithfully flat over `O`, so `Q̂ ∩ O = Q`.
  have : Module.FaithfullyFlat O Ô := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hQ : Q = (Q.map (algebraMap O Ô)).comap (algebraMap O Ô) :=
    (Ideal.comap_map_eq_self_of_faithfullyFlat Q).symm
  -- The local homomorphism `O_Q → Ô_Q̂`; it is flat, hence faithfully flat.
  let f := Localization.localRingHom Q (Q.map (algebraMap O Ô)) (algebraMap O Ô) hQ
  let : Algebra (Localization.AtPrime Q) (Localization.AtPrime (Q.map (algebraMap O Ô))) :=
    f.toAlgebra
  have : Module.Flat (Localization.AtPrime Q) (Localization.AtPrime (Q.map (algebraMap O Ô))) :=
    RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) _ _ hQ
  have : IsLocalHom (algebraMap (Localization.AtPrime Q)
      (Localization.AtPrime (Q.map (algebraMap O Ô)))) :=
    Localization.isLocalHom_localRingHom _ _ _ hQ
  have : Module.FaithfullyFlat (Localization.AtPrime Q)
      (Localization.AtPrime (Q.map (algebraMap O Ô))) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hmap : (P.map (algebraMap O (Localization.AtPrime Q))).map (algebraMap
      (Localization.AtPrime Q) (Localization.AtPrime (Q.map (algebraMap O Ô)))) =
      (P.map (algebraMap O Ô)).map
        (algebraMap Ô (Localization.AtPrime (Q.map (algebraMap O Ô)))) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext x
    exact Localization.localRingHom_to_map _ _ _ hQ x
  rw [← hmap]
  exact isNormallyFlatAlongIdeal_iff_of_faithfullyFlat _

/-- `QÔ` is the kernel of `Ô → (O/Q)^`, where `(O/Q)^` is the completion of the `O`-module `O/Q`
(`Ô/QÔ = Ô ⊗_O O/Q ≅ (O/Q)^`, `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`). -/
private theorem mem_map_of_adicCompletionMap_mkQ_eq_zero (Q : Ideal O) {a : Ô}
    (ha : AdicCompletion.map (IsLocalRing.maximalIdeal O) Q.mkQ a = 0) :
    a ∈ Q.map (algebraMap O Ô) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Ô Q).injective
  apply (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (IsLocalRing.maximalIdeal O)
    (O ⧸ Q)).injective
  rw [map_zero, map_zero]
  erw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  rw [AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
    AdicCompletion.ofTensorProduct_tmul, ← ha]
  have h1 : (a : Ô) = a • AdicCompletion.of (IsLocalRing.maximalIdeal O) O 1 := by
    rw [smul_eq_mul]
    exact (mul_one a).symm
  conv_rhs => rw [h1]
  rw [map_smul, AdicCompletion.map_of]
  rfl

/-- The ring map `ψ : Ô → (O/Q)^` from the completion of `O` to the completion of `O/Q` (along
the maximal ideals) is surjective and has kernel `Q̂ = QÔ`, i.e. `Ô/Q̂ ≅ (O/Q)^` (the isomorphism
that the paper uses in the proof of the Corollary to Lemma 9, p. 198, without proof).  The kernel
is `QÔ` because `Ô/QÔ = Ô ⊗_O O/Q ≅ (O/Q)^` (`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`);
surjectivity is proved by choosing, for an element of `(O/Q)^`, a Cauchy sequence of lifts to `O`
(a lift modulo `Q + mⁿ⁺¹` is corrected by an element of `Q` to be congruent to the previous one
modulo `mⁿ`). -/
private theorem exists_ringHom_adicCompletion_quotient (Q : Ideal O) [Q.IsPrime]
    [IsRegularLocalRing (O ⧸ Q)] :
    ∃ ψ : Ô →+* AdicCompletion (IsLocalRing.maximalIdeal (O ⧸ Q)) (O ⧸ Q),
      RingHom.ker ψ = Q.map (algebraMap O Ô) ∧ Function.Surjective ψ := by
  set m := IsLocalRing.maximalIdeal O
  set mS := IsLocalRing.maximalIdeal (O ⧸ Q)
  have hmS : m.map (Ideal.Quotient.mk Q) = mS :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hle : ∀ n, m ^ n ≤ (mS ^ n).comap (Ideal.Quotient.mk Q) := fun n => by
    rw [← hmS, ← Ideal.map_pow]
    exact Ideal.le_comap_map
  -- `gₙ : O/mⁿ → S/m_Sⁿ` (`S = O/Q`).
  let g : ∀ n, O ⧸ m ^ n →+* (O ⧸ Q) ⧸ mS ^ n := fun n =>
    Ideal.quotientMap _ (Ideal.Quotient.mk Q) (hle n)
  have hg : ∀ n (r : O), g n (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk Q r) := fun n r => Ideal.quotientMap_mk
  -- `evalₐ` on `Ô` of a Cauchy sequence.
  have hev : ∀ {k n : ℕ} (hkn : k ≤ n) (a : Ô), Ideal.Quotient.factorPow m hkn
      (AdicCompletion.evalₐ m n a) = AdicCompletion.evalₐ m k a := by
    intro k n hkn a
    obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective m O a
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
    have := AdicCompletion.AdicCauchySequence.mk_eq_mk hkn c
    rw [Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top] at this
    exact this
  let ψ : Ô →+* AdicCompletion mS (O ⧸ Q) :=
    AdicCompletion.liftRingHom mS (fun n => (g n).comp (AdicCompletion.evalₐ m n).toRingHom)
      (fun {k n} hkn => by
        ext a
        obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ m n a)
        have hk := hev hkn a
        rw [← hr, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk] at hk
        simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe]
        rw [← hr, ← hk, hg, hg, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk])
  have hψ : ∀ n (a : Ô), AdicCompletion.evalₐ mS n (ψ a) =
      g n (AdicCompletion.evalₐ m n a) := fun n a => AdicCompletion.evalₐ_liftRingHom _ _ _ _ _
  have hker : RingHom.ker ψ = Q.map (algebraMap O Ô) := by
    apply le_antisymm
    · intro a ha
      rw [RingHom.mem_ker] at ha
      apply mem_map_of_adicCompletionMap_mkQ_eq_zero
      obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective m O a
      ext n
      have h := hψ n (AdicCompletion.mk m O c)
      rw [ha, map_zero, AdicCompletion.evalₐ_mk, hg, eq_comm, Ideal.Quotient.eq_zero_iff_mem,
        ← hmS, ← Ideal.map_pow] at h
      rw [AdicCompletion.map_val_apply, AdicCompletion.mk_apply_coe, Submodule.mkQ_apply,
        LinearMap.reduceModIdeal_apply, AdicCompletion.val_zero_apply,
        Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
        Ideal.Quotient.algebraMap_eq]
      exact h
    · rw [Ideal.map_le_iff_le_comap]
      intro q hq
      rw [Ideal.mem_comap, RingHom.mem_ker]
      refine AdicCompletion.ext_evalₐ fun n => ?_
      rw [hψ, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        AdicCompletion.evalₐ_of, hg, map_zero, Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]
  -- `ψ` is surjective
  have hsurj : Function.Surjective ψ := by
    intro y
    -- `y` is compatible: its components in `S/mSⁿ` map onto each other
    have hevS : ∀ {k n : ℕ} (hkn : k ≤ n) (a : AdicCompletion mS (O ⧸ Q)),
        Ideal.Quotient.factorPow mS hkn (AdicCompletion.evalₐ mS n a) =
          AdicCompletion.evalₐ mS k a := by
      intro k n hkn a
      obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective mS (O ⧸ Q) a
      rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
        Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
      have := AdicCompletion.AdicCauchySequence.mk_eq_mk hkn c
      rw [Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top] at this
      exact this
    -- the step: a lift of the `n`-th component can be corrected by an element of `Q` to a lift
    -- of the `(n+1)`-st component that is congruent to it modulo `mⁿ`
    have hstep : ∀ (n : ℕ) (r : O),
        Ideal.Quotient.mk (mS ^ n) (Ideal.Quotient.mk Q r) = AdicCompletion.evalₐ mS n y →
        ∃ r' : O, Ideal.Quotient.mk (mS ^ (n + 1)) (Ideal.Quotient.mk Q r') =
            AdicCompletion.evalₐ mS (n + 1) y ∧ r' - r ∈ m ^ n := by
      intro n r hr
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ mS (n + 1) y)
      obtain ⟨r₀, rfl⟩ := Ideal.Quotient.mk_surjective s
      have h1 : Ideal.Quotient.mk (mS ^ n) (Ideal.Quotient.mk Q r₀) =
          Ideal.Quotient.mk (mS ^ n) (Ideal.Quotient.mk Q r) := by
        rw [hr, ← hevS (Nat.le_succ n) y, ← hs, Ideal.Quotient.factorPow,
          Ideal.Quotient.factor_mk]
      rw [Ideal.Quotient.eq, ← map_sub, ← hmS, ← Ideal.map_pow] at h1
      obtain ⟨a, ha, hae⟩ := (Ideal.mem_map_iff_of_surjective _
        Ideal.Quotient.mk_surjective).mp h1
      refine ⟨r + a, ?_, by rwa [add_sub_cancel_left]⟩
      rw [← hs]
      congr 1
      rw [map_add, hae, map_sub]
      ring
    choose! next hnext using hstep
    let r : ℕ → O := fun n => Nat.rec 0 (fun k rk => next k rk) n
    have hr_succ : ∀ n, r (n + 1) = next n (r n) := fun n => rfl
    have hP : ∀ n, Ideal.Quotient.mk (mS ^ n) (Ideal.Quotient.mk Q (r n)) =
        AdicCompletion.evalₐ mS n y := by
      intro n
      induction n with
      | zero =>
        have : Subsingleton ((O ⧸ Q) ⧸ mS ^ 0) := by
          rw [pow_zero, Ideal.one_eq_top]
          exact Ideal.Quotient.subsingleton_iff.mpr rfl
        exact Subsingleton.elim _ _
      | succ n ih =>
        rw [hr_succ]
        exact (hnext n (r n) ih).1
    have hdiff : ∀ n, r (n + 1) - r n ∈ m ^ n := fun n => by
      rw [hr_succ]
      exact (hnext n (r n) (hP n)).2
    have hcauchy : ∀ {k n : ℕ}, k ≤ n → r n - r k ∈ m ^ k := by
      intro k n hkn
      induction n, hkn using Nat.le_induction with
      | base => simp
      | succ n hkn ih =>
        have h1 : r (n + 1) - r k = (r (n + 1) - r n) + (r n - r k) := by ring
        rw [h1]
        exact Ideal.add_mem _ (Ideal.pow_le_pow_right hkn (hdiff n)) ih
    let c : AdicCompletion.AdicCauchySequence m O := ⟨r, fun {k n} hkn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]
      exact Ideal.neg_mem_iff _ |>.mpr (hcauchy hkn)⟩
    refine ⟨AdicCompletion.mk m O c, ?_⟩
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [hψ, AdicCompletion.evalₐ_mk, hg]
    exact hP n
  exact ⟨ψ, hker, hsurj⟩

/-- The first assertion of the Corollary to Lemma 9, as in the paper (p. 198): "Since `Ô/Q̂` is
isomorphic to the completion of `O/Q` which is regular, `Ô/Q̂` is regular.  In particular, `Q̂` is a
prime ideal in `Ô`."  The isomorphism `Ô/Q̂ ≅ (O/Q)^` is `exists_ringHom_adicCompletion_quotient`;
the completion of the regular local ring `O/Q` is regular
(`isRegularLocalRing_adicCompletion_of_isRegularLocalRing`), and a regular local ring is a domain. -/
private theorem isPrime_map_adicCompletion (Q : Ideal O) [Q.IsPrime]
    [IsRegularLocalRing (O ⧸ Q)] : (Q.map (algebraMap O Ô)).IsPrime := by
  obtain ⟨ψ, hker, hsurj⟩ := exists_ringHom_adicCompletion_quotient O Q
  -- `Ô/Q̂ ≅ (O/Q)^`
  let e : (Ô ⧸ Q.map (algebraMap O Ô)) ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal (O ⧸ Q)) (O ⧸ Q) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  -- the completion of the regular local ring `O/Q` is regular, hence so is `Ô/Q̂`
  have : IsRegularLocalRing (AdicCompletion (IsLocalRing.maximalIdeal (O ⧸ Q)) (O ⧸ Q)) :=
    isRegularLocalRing_adicCompletion_of_isRegularLocalRing (O ⧸ Q)
  have : IsRegularLocalRing (Ô ⧸ Q.map (algebraMap O Ô)) :=
    IsRegularLocalRing.of_ringEquiv e.symm
  -- in particular `Ô/Q̂` is a domain, i.e. `Q̂` is a prime ideal
  exact (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)

/-- Corollary to Lemma 9, p. 198: "Let O be a local ring. Let P be an ideal in O and Q a prime
ideal in O such that Q ⊇ P and O/Q is regular. Let Ô be the completion of O, P̂ = PÔ and
Q̂ = QÔ. Then Q̂ is a prime ideal in Ô, and gr_{PO_Q}(O_Q) is flat over O_Q/PO_Q if and only
if gr_{P̂Ô_Q̂}(Ô_Q̂) is flat over Ô_Q̂/P̂Ô_Q̂."

Encoding: `Ô = AdicCompletion (maximalIdeal O) O`, `P̂ = P.map (algebraMap O Ô)`,
`Q̂ = Q.map (algebraMap O Ô)`; the localizations `O_Q`, `Ô_Q̂` are `Localization.AtPrime`,
the second one requiring the primality of `Q̂` asserted first (hence the `∃ h, …` form).
"gr_{PO_Q}(O_Q) is flat over O_Q/PO_Q" is `IsNormallyFlatAlongIdeal (PO_Q)` (the local ring
`O_Q` is noetherian; likewise `Ô_Q̂`, the completion of a noetherian local ring being noetherian
and local, so Definition 1 of Ch. 0 applies on both sides).

The proof is the paper's: `Ô/Q̂` is isomorphic to the completion `(O/Q)^` of `O/Q`
(`exists_ringHom_adicCompletion_quotient`), which is regular
(`isRegularLocalRing_adicCompletion_of_isRegularLocalRing`), so `Ô/Q̂` is regular and in particular
a domain, i.e. `Q̂` is a prime ideal (`isPrime_map_adicCompletion`); `Ô` is flat over `O`, hence
`Ô_Q̂` is flat over `O_Q`, and `O_Q → Ô_Q̂` is a local homomorphism, so `Ô_Q̂` is faithfully flat
over `O_Q` (Mathlib's `Module.FaithfullyFlat.of_flat_of_isLocalHom`, the same fact as
`lem:II.3-faithfully-flat-local`); then the assertion is Lemma 9
(`isNormallyFlatAlongIdeal_localization_iff_completion_of_isPrime`).

Deviation from the paper (gap filled): "`Ô/Q̂` is isomorphic to the completion of `O/Q`" (p. 198)
is stated without proof.  It is proved here: the kernel of `Ô → (O/Q)^` is `QÔ` (since
`Ô/QÔ = Ô ⊗_O O/Q ≅ (O/Q)^`), and the map is surjective (a Cauchy sequence of lifts to `O` is
built step by step). -/
@[blueprint "cor:II.3-lem9"
  (statement := /-- Let $O$ be a local ring. Let $P$ be an ideal in $O$ and $Q$ a prime ideal
    in $O$ such that $Q\supseteq P$ and $O/Q$ is regular. Let $\hat O$ be the completion of
    $O$, $\hat P=P\hat O$ and $\hat Q=Q\hat O$. Then $\hat Q$ is a prime ideal in $\hat O$,
    and $\operatorname{gr}_{PO_Q}(O_Q)$ is flat over $O_Q/PO_Q$ if and only if
    $\operatorname{gr}_{\hat P\hat O_{\hat Q}}(\hat O_{\hat Q})$ is flat over
    $\hat O_{\hat Q}/\hat P\hat O_{\hat Q}$. (p.~198.) -/)
  (proof := /-- Since $\hat O/\hat Q$ is isomorphic to the completion of $O/Q$ which is
    regular, $\hat O/\hat Q$ is regular. In particular, $\hat Q$ is a prime ideal in $\hat O$.
    We know that $\hat O$ is flat over $O$, hence, $\hat O_{\hat Q}$ is flat over $O_Q$. But
    $O_Q\to\hat O_{\hat Q}$ is a local homomorphism and therefore $\hat O_{\hat Q}$ is
    faithfully flat over $O_Q$ (\cref{lem:II.3-faithfully-flat-local}). Now the assertion is
    clear by \cref{lem:II.3-9}.

    \textbf{Deviation from the paper (gap filled).} ``Since $\hat O/\hat Q$ is isomorphic to the
    completion of $O/Q$'' (p.~198) is stated without proof. In Lean it is proved: the kernel of
    $\hat O\to(O/Q)^\wedge$ is $Q\hat O$ (because $\hat O/Q\hat O=\hat O\otimes_OO/Q\cong
    (O/Q)^\wedge$) and the map is surjective (a Cauchy sequence of lifts to $O$ is built step by
    step). -/)
  (latexEnv := "corollary")]
theorem isNormallyFlatAlongIdeal_localization_iff_completion (P Q : Ideal O) [Q.IsPrime]
    (hPQ : P ≤ Q) [IsRegularLocalRing (O ⧸ Q)] :
    ∃ h : (Q.map (algebraMap O Ô)).IsPrime,
      haveI := h
      (IsNormallyFlatAlongIdeal (P.map (algebraMap O (Localization.AtPrime Q))) ↔
        IsNormallyFlatAlongIdeal ((P.map (algebraMap O Ô)).map
          (algebraMap Ô (Localization.AtPrime (Q.map (algebraMap O Ô)))))) := by
  -- (The argument does not need `P ⊆ Q`.)
  have _ := hPQ
  -- `Ô/Q̂` is the completion of the regular local ring `O/Q`, a domain: `Q̂` is prime.
  have h := isPrime_map_adicCompletion O Q
  -- `Ô_Q̂` is faithfully flat over `O_Q`; conclude by Lemma 9.
  exact ⟨h, isNormallyFlatAlongIdeal_localization_iff_completion_of_isPrime O P Q⟩

end Lemma9

/-! ### The initial form in `gr_Q(gr_P(R))` (p. 199) -/

section DoubleInitialForm

variable {R : Type u} [CommRing R]

/-- p. 199: "Let Φ be a form in gr_P(R), say deg Φ = ν. Then by ν_{Q/P}(Φ) we shall denote the
maximal integer n such that Φ ∈ Qⁿ gr_P(R) = (Q/P)ⁿ gr_P(R)."  This is `ν_{Q·gr_P(R)}(Φ)` in
the sense of `Ideal.ordElem` (Def. of p. 189), with value `∞` if `Φ ∈ Qⁿ gr_P(R)` for all
`n`; it is defined for every element `Φ` of `gr_P(R)`. -/
noncomputable def doubleOrd (P Q : Ideal R) (Φ : AssocGraded P) : ℕ∞ :=
  Ideal.ordElem (Q.map (algebraMap R (AssocGraded P))) Φ

/-- p. 199: "Let n = ν_{Q/P}(Φ). Then the class Φ_* of Φ in
grⁿ_Q(gr_P(R)) = Qⁿ gr_P(R)/Qⁿ⁺¹ gr_P(R) is a form of double grade (ν, n). We shall call Φ_*
the initial form of Φ in gr_Q(gr_P(R)). If g is an element of R, and if Φ is the initial form
of g in gr_P(R), then Φ_* will be called the initial form of g in gr_Q(gr_P(R))."

`gr_Q(gr_P(R))` is by definition the associated graded algebra of `gr_P(R)` with respect to
the ideal `Q·gr_P(R)`, i.e. `AssocGraded (Q.map (algebraMap R (AssocGraded P)))`, and `Φ_*` is
the initial form of `Φ` for that ideal (`initialForm`, p. 189).  The initial form of `g ∈ R`
in `gr_Q(gr_P(R))` is `doubleInitialForm P Q (initialForm P g)`.  (Formalization note
(encoding): defined for every `Φ`, not only for forms; the double grading `(ν, n)` is not
recorded.) -/
@[blueprint "def:II.3-double-initial-form"
  (statement := /-- Let $R$ be a regular local ring and $P\subseteq Q$ prime ideals of $R$
    with $R/P$ and $R/Q$ regular. Let $\Phi$ be a form in $\operatorname{gr}_P(R)$, say
    $\deg\Phi=\nu$. Then by $\nu_{Q/P}(\Phi)$ we shall denote the maximal integer $n$ such
    that $\Phi\in Q^n\operatorname{gr}_P(R)=(Q/P)^n\operatorname{gr}_P(R)$. Let
    $n=\nu_{Q/P}(\Phi)$. Then the class $\Phi_*$ of $\Phi$ in
    $\operatorname{gr}^n_Q(\operatorname{gr}_P(R))=Q^n\operatorname{gr}_P(R)/
    Q^{n+1}\operatorname{gr}_P(R)$ is a form of double grade $(\nu,n)$. We shall call $\Phi_*$
    the \emph{initial form of $\Phi$ in $\operatorname{gr}_Q(\operatorname{gr}_P(R))$}. If
    $g$ is an element of $R$, and if $\Phi$ is the initial form of $g$ in
    $\operatorname{gr}_P(R)$, then $\Phi_*$ will be called the initial form of $g$ in
    $\operatorname{gr}_Q(\operatorname{gr}_P(R))$. (p.~199.) (Formalization note (encoding):
    $\operatorname{gr}_Q(\operatorname{gr}_P(R))$ is the associated graded algebra
    (\cref{def:II.1-associated-graded-algebra}) of $\operatorname{gr}_P(R)$ with respect to
    the ideal $Q\operatorname{gr}_P(R)$; $\nu_{Q/P}$ is \cref{def:II.2-order-element} and
    $\Phi_*$ is \cref{def:II.2-initial-form} for that ideal. They are defined for every
    element $\Phi$ of $\operatorname{gr}_P(R)$, not only for forms, and the double grading is
    not recorded.) -/)
  (latexEnv := "definition")]
noncomputable def doubleInitialForm (P Q : Ideal R) (Φ : AssocGraded P) :
    AssocGraded (Q.map (algebraMap R (AssocGraded P))) :=
  initialForm (Q.map (algebraMap R (AssocGraded P))) Φ

end DoubleInitialForm

/-! ### Lemma 11 (p. 200) -/

section Lemma11

/-- `O = R/J` is a local ring as soon as `J` is contained in a prime `Q` of the local ring `R`
(so that `J ≠ R`), as in Lemmas 10, 11 and Theorem 3. -/
theorem isLocalRing_quotient_of_le_prime {R : Type u} [CommRing R] [IsLocalRing R]
    {J Q : Ideal R} [hQ : Q.IsPrime] (hJQ : J ≤ Q) : IsLocalRing (R ⧸ J) :=
  haveI : Nontrivial (R ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top hQ.ne_top hJQ)
  IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

/-- Lemma 11, p. 200: "Let R, J, Q, O and Q̄ be the same as in Lemma 10. If gr_Q̄(O) is flat
over O/Q̄, then we have gr_Q(J, R)_Q ∩ gr_Q(R) = gr_Q(J, R)."

Here (from the paragraph preceding Lemma 10) `R` is a regular local ring, `J` an ideal in `R`,
`Q` a prime ideal containing `J` with `R/Q` regular, `O = R/J` and `Q̄ = Q/J`; `_Q` is the
localization with respect to `R − Q`.  (Lemma 10 also carries a prime `P` with
`J ⊆ P ⊆ Q` and `R/P` regular, which plays no role in this statement and is omitted.)

Encoding: `O = R ⧸ J` (a noetherian local ring, `isLocalRing_quotient_of_le_prime`),
`Q̄ = Q.map (Ideal.Quotient.mk J)`, and "gr_Q̄(O) is flat over O/Q̄" is
`IsNormallyFlatAlongIdeal Q̄`.  The conclusion `gr_Q(J, R)_Q ∩ gr_Q(R) = gr_Q(J, R)` (the
intersection taken in `gr_Q(R)_Q`, where `gr_Q(R) → gr_Q(R)_Q` is injective by the lemma's
proof) says exactly that `gr_Q(J, R)` is saturated with respect to `R − Q`: an element `φ` of
`gr_Q(R)` with `sφ ∈ gr_Q(J, R)` for some `s ∈ R − Q` lies in `gr_Q(J, R)`; this is the form
in which it is stated.

Deviation from the paper (statement modified): the prime `P` is dropped (a stronger
statement), and the equality is stated in the equivalent saturation form above (equivalent
because `gr_Q(R)` is torsion-free over the domain `R/Q`).  The proof is the paper's, with
"the last vertical arrow is injective" read as "a flat module over the domain `O/Q̄` is
torsion-free". -/
@[blueprint "lem:II.3-11"
  (statement := /-- Let $R$ be a regular local ring, $J$ an ideal in $R$, $Q$ a prime ideal in
    $R$ containing $J$ such that $R/Q$ is regular, $O=R/J$ and $\bar Q=Q/J$ (the notation of
    Lemma 10). If $\operatorname{gr}_{\bar Q}(O)$ is flat over $O/\bar Q$, then we have
    $\operatorname{gr}_Q(J,R)_Q\cap\operatorname{gr}_Q(R)=\operatorname{gr}_Q(J,R)$, where
    $(\ )_Q$ denotes the localization with respect to $R-Q$. (p.~200.)

    \textbf{Deviation from the paper (statement modified).} The prime $P$ with
    $J\subseteq P\subseteq Q$ and $R/P$ regular carried by the notation of Lemma 10 plays no
    role here and is omitted; the conclusion is transcribed as the (equivalent, since
    $\operatorname{gr}_Q(R)$ is torsion-free over $R/Q$) saturation property: for $s\in R-Q$
    and $\varphi\in\operatorname{gr}_Q(R)$, $s\varphi\in\operatorname{gr}_Q(J,R)$ implies
    $\varphi\in\operatorname{gr}_Q(J,R)$. -/)
  (proof := /-- Let us consider the commutative diagram with rows
    $0\to\operatorname{gr}_Q(J,R)\to\operatorname{gr}_Q(R)\to\operatorname{gr}_{\bar Q}(O)\to0$
    (\cref{lem:II.2-5}) and $0\to\operatorname{gr}_Q(J,R)_Q\to\operatorname{gr}_Q(R)_Q\to
    \operatorname{gr}_{\bar Q}(O)_Q\to0$, where the horizontal sequences are exact and the
    first two vertical arrows are injections. Since $\operatorname{gr}_{\bar Q}(O)$ is flat
    over $O/\bar Q$, the last vertical arrow is also injective. The assertion in the lemma
    follows. -/)
  (latexEnv := "lemma")]
theorem grIdeal_saturated_of_isNormallyFlatAlongIdeal (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (J Q : Ideal R) [Q.IsPrime] (hJQ : J ≤ Q)
    [IsRegularLocalRing (R ⧸ Q)]
    (h : IsNormallyFlatAlongIdeal (Q.map (Ideal.Quotient.mk J))) :
    ∀ s ∉ Q, ∀ φ : AssocGraded Q,
      algebraMap R (AssocGraded Q) s * φ ∈ grIdeal Q J → φ ∈ grIdeal Q J := by
  intro s hs φ hφ
  -- `Q̄ = Q/J` is prime (`J ⊆ Q`), so `O/Q̄ (≅ R/Q)` is a domain.
  have : (Q.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJQ)
  -- `gr_{Q̄}(O)` is flat over `O/Q̄` (each graded piece is free), hence torsion-free over the
  -- domain `O/Q̄`.
  have : Module.Flat ((R ⧸ J) ⧸ Q.map (Ideal.Quotient.mk J))
      (AssocGraded (Q.map (Ideal.Quotient.mk J))) :=
    (isGrFlat_iff_forall_flat_piece _).mpr fun n => by have := h n; infer_instance
  -- The class `s̄` of `s` in `O/Q̄` is non-zero, since `s ∉ Q`.
  have hs' : Ideal.Quotient.mk (Q.map (Ideal.Quotient.mk J)) (Ideal.Quotient.mk J s) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_quotient_iff_mem hJQ]
    exact hs
  -- The exact sequence `0 → gr_Q(J, R) → gr_Q(R) → gr_{Q̄}(O) → 0` (Lemma 5): `s̄` kills the
  -- image of `φ` in `gr_{Q̄}(O)`, so this image vanishes, i.e. `φ ∈ gr_Q(J, R)`.
  rw [← ker_grMapQuot, RingHom.mem_ker] at hφ ⊢
  rw [map_mul, AlgHom.commutes,
    IsScalarTower.algebraMap_apply R (R ⧸ J) (AssocGraded (Q.map (Ideal.Quotient.mk J))) s,
    IsScalarTower.algebraMap_apply (R ⧸ J) ((R ⧸ J) ⧸ Q.map (Ideal.Quotient.mk J))
      (AssocGraded (Q.map (Ideal.Quotient.mk J))) _,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_eq, ← Algebra.smul_def] at hφ
  exact (smul_eq_zero_iff_right hs').mp hφ

/-- Lemma 11, p. 200, in the paper's form, with the prime `P`: "Let `R`, `J`, `Q`, `O` and `Q̄` be
the same as in Lemma 10. If `gr_Q̄(O)` is flat over `O/Q̄`, then we have
`gr_Q(J, R)_Q ∩ gr_Q(R) = gr_Q(J, R)`", where `R` is a regular local ring, `P` and `Q` are prime
ideals with `J ⊆ P ⊆ Q` and `R/P`, `R/Q` regular, `O = R/J`, `Q̄ = Q/J`, and `_Q` is the
localization with respect to `R − Q`.

Encoding: the localization of `gr_Q(R)` with respect to `R − Q` is
`Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl)`, `gr_Q(J, R)_Q` is the
extension of `grIdeal Q J` to it, and "`gr_Q(J, R)_Q ∩ gr_Q(R) = gr_Q(J, R)`" (the intersection
taken in `gr_Q(R)_Q`) is that the inverse image of `gr_Q(J, R)_Q` in `gr_Q(R)` is `gr_Q(J, R)`.

Deviation from the paper (statement modified): the injectivity of `gr_Q(R) → gr_Q(R)_Q`, used by
the paper to regard `gr_Q(R)` as a subset of `gr_Q(R)_Q`, is not part of this statement (the equality
is stated for the inverse image, which is what the intersection means when the map is injective);
the statement with the intersection taken literally, together with that injectivity, is
`grIdeal_localization_inf_range_eq` (blueprint `lem:II.3-11-intersection`).  The prime `P` is
carried but not used (it plays no role in the proof); the statement is deduced from the saturation
form `grIdeal_saturated_of_isNormallyFlatAlongIdeal`.  Theorem 3 does not use this node: it uses
Lemma 11 in its printed intersection form, `grIdeal_localization_inf_range_eq` (via
`mem_grIdeal_of_algebraMap_mem_map`). -/
@[blueprint "lem:II.3-11-localization"
  (statement := /-- Let $R$ be a regular local ring, $J$ an ideal in $R$, $P$ and $Q$ prime ideals
    in $R$ such that $Q\supseteq P\supseteq J$ and that $R/P$ and $R/Q$ are both regular, $O=R/J$
    and $\bar Q=Q/J$ (the notation of Lemma 10). If $\operatorname{gr}_{\bar Q}(O)$ is flat over
    $O/\bar Q$, then we have $\operatorname{gr}_Q(J,R)_Q\cap\operatorname{gr}_Q(R)=
    \operatorname{gr}_Q(J,R)$, where $(\ )_Q$ denotes the localization with respect to $R-Q$.
    (Lemma 11, p.~200, in the paper's form.)

    \textbf{Formalization note (encoding).} The intersection is taken in
    $\operatorname{gr}_Q(R)_Q$: the statement is that the inverse image of
    $\operatorname{gr}_Q(J,R)_Q$ under $\operatorname{gr}_Q(R)\to\operatorname{gr}_Q(R)_Q$ is
    $\operatorname{gr}_Q(J,R)$.

    \textbf{Deviation from the paper (statement modified).} Injectivity of
    $\operatorname{gr}_Q(R)\to\operatorname{gr}_Q(R)_Q$ is not part of the statement; the
    literal form is \cref{lem:II.3-11-intersection}. -/)
  (proof := /-- If $\varphi\in\operatorname{gr}_Q(R)$ has image in $\operatorname{gr}_Q(J,R)_Q$,
    then $t\varphi\in\operatorname{gr}_Q(J,R)$ for some $t\in R-Q$, so $\varphi\in
    \operatorname{gr}_Q(J,R)$ by \cref{lem:II.3-11}; the other inclusion is clear. -/)
  (latexEnv := "lemma")]
theorem comap_map_grIdeal_eq_of_isNormallyFlatAlongIdeal (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (J P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (_hJP : J ≤ P)
    (hPQ : P ≤ Q) [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)]
    (h : IsNormallyFlatAlongIdeal (Q.map (Ideal.Quotient.mk J))) :
    ((grIdeal Q J).map (algebraMap (AssocGraded Q)
      (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl)))).comap
      (algebraMap (AssocGraded Q)
        (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))) =
      grIdeal Q J := by
  refine le_antisymm (fun φ hφ => ?_) (fun φ hφ => Ideal.mem_map_of_mem _ hφ)
  obtain ⟨⟨a, t⟩, hat⟩ := (IsLocalization.mem_map_algebraMap_iff
    (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl)
    (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))).mp
    (Ideal.mem_comap.mp hφ)
  rw [← map_mul] at hat
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
    (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl)
    (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))).mp hat
  obtain ⟨t₁, ht₁, ht₁'⟩ := Submonoid.mem_map.mp t.2
  obtain ⟨c₁, hc₁, hc₁'⟩ := Submonoid.mem_map.mp c.2
  have hmem : algebraMap R (AssocGraded Q) (c₁ * t₁) * φ ∈ grIdeal Q J := by
    have h1 : algebraMap R (AssocGraded Q) (c₁ * t₁) * φ = (c : AssocGraded Q) * a := by
      calc algebraMap R (AssocGraded Q) (c₁ * t₁) * φ
          = (c : AssocGraded Q) * (φ * (t : AssocGraded Q)) := by
            rw [map_mul]
            rw [hc₁', ht₁']
            ring
        _ = (c : AssocGraded Q) * a := hc
    rw [h1]
    exact Ideal.mul_mem_left _ _ a.2
  exact grIdeal_saturated_of_isNormallyFlatAlongIdeal R J Q (_hJP.trans hPQ) h _
    (Q.primeCompl.mul_mem hc₁ ht₁) φ hmem

/-- A localization of a flat algebra `B` over a domain `K` with respect to the image of a
multiplicative set `M` of elements acting through `K` by non-zero scalars: `B → B_M` is injective
(the elements of `M` are non-zero-divisors on the torsion-free module `B`). -/
theorem injective_algebraMap_localization_of_flat {A B K : Type*} [CommRing A] [CommRing B]
    [CommRing K] [IsDomain K] [Algebra A B] [Algebra A K] [Algebra K B] [IsScalarTower A K B]
    [Module.Flat K B] (M : Submonoid A) (hM : ∀ s ∈ M, algebraMap A K s ≠ 0)
    (L : Type*) [CommRing L] [Algebra B L] [IsLocalization (Algebra.algebraMapSubmonoid B M) L] :
    Function.Injective (algebraMap B L) := by
  refine IsLocalization.injective L (M := Algebra.algebraMapSubmonoid B M) ?_
  rintro _ ⟨s, hs, rfl⟩
  have h1 : algebraMap A B s = algebraMap K B (algebraMap A K s) :=
    IsScalarTower.algebraMap_apply A K B s
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [h1, ← Algebra.smul_def] at hx
    exact (smul_eq_zero_iff_right (hM s hs)).mp hx
  · rw [h1, mul_comm, ← Algebra.smul_def] at hx
    exact (smul_eq_zero_iff_right (hM s hs)).mp hx

/-- The elements of `R - Q` are non-zero-divisors on `gr_Q(R)`: `gr_Q(R) → gr_Q(R)_Q` is injective
(`gr_Q(R)` is a polynomial ring over the domain `R/Q`, hence torsion-free over `R/Q`).  This is
the first two vertical arrows of the diagram of Lemma 11 being "injections" (p. 200), for the
second one; it is the case `J = 0` of Lemma 11. -/
theorem injective_algebraMap_localization_assocGraded (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (Q : Ideal R) [Q.IsPrime] [IsRegularLocalRing (R ⧸ Q)] :
    Function.Injective (algebraMap (AssocGraded Q)
      (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))) := by
  have hflat : Module.Flat (R ⧸ Q) (AssocGraded Q) :=
    (isGrFlat_iff_forall_flat_piece _).mpr fun n => by
      have := isNormallyFlatAlongIdeal_of_isRegularLocalRing_quotient Q n
      infer_instance
  refine injective_algebraMap_localization_of_flat (K := R ⧸ Q) Q.primeCompl (fun s hs => ?_) _
  show Ideal.Quotient.mk Q s ≠ 0
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact hs

/-- The last vertical arrow of the diagram of Lemma 11 is injective "since `gr_Q̄(O)` is flat over
`O/Q̄`": `gr_Q̄(O) → gr_Q̄(O)_Q` is injective (a flat module over the domain `O/Q̄` is
torsion-free). -/
theorem injective_algebraMap_localization_assocGraded_quotient (R : Type u) [CommRing R]
    (J Q : Ideal R) [Q.IsPrime] (hJQ : J ≤ Q)
    (h : IsNormallyFlatAlongIdeal (Q.map (Ideal.Quotient.mk J))) :
    Function.Injective (algebraMap (AssocGraded (Q.map (Ideal.Quotient.mk J)))
      (Localization (Algebra.algebraMapSubmonoid (AssocGraded (Q.map (Ideal.Quotient.mk J)))
        Q.primeCompl))) := by
  have : (Q.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJQ)
  have hflat : Module.Flat ((R ⧸ J) ⧸ Q.map (Ideal.Quotient.mk J))
      (AssocGraded (Q.map (Ideal.Quotient.mk J))) :=
    (isGrFlat_iff_forall_flat_piece _).mpr fun n => by have := h n; infer_instance
  have : IsScalarTower R ((R ⧸ J) ⧸ Q.map (Ideal.Quotient.mk J))
      (AssocGraded (Q.map (Ideal.Quotient.mk J))) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := (R ⧸ J) ⧸ Q.map (Ideal.Quotient.mk J))
      (A := AssocGraded (Q.map (Ideal.Quotient.mk J))) fun r => by
      rw [IsScalarTower.algebraMap_apply R (R ⧸ J) (AssocGraded (Q.map (Ideal.Quotient.mk J))) r,
        IsScalarTower.algebraMap_apply (R ⧸ J) ((R ⧸ J) ⧸ Q.map (Ideal.Quotient.mk J))
          (AssocGraded (Q.map (Ideal.Quotient.mk J)))]
      rfl
  refine injective_algebraMap_localization_of_flat
    (K := (R ⧸ J) ⧸ Q.map (Ideal.Quotient.mk J)) Q.primeCompl (fun s hs => ?_) _
  show Ideal.Quotient.mk (Q.map (Ideal.Quotient.mk J)) (Ideal.Quotient.mk J s) ≠ 0
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_quotient_iff_mem hJQ]
  exact hs

/-- Lemma 11, p. 200, with the intersection taken literally: "Let R, J, Q, O and Q̄ be the same as in
Lemma 10. If gr_Q̄(O) is flat over O/Q̄, then we have gr_Q(J, R)_Q ∩ gr_Q(R) = gr_Q(J, R)", where
`R` is a regular local ring, `P` and `Q` are prime ideals with `J ⊆ P ⊆ Q` and `R/P`, `R/Q`
regular, `O = R/J`, `Q̄ = Q/J`, and `_Q` is the localization with respect to `R − Q`.

Encoding: the localization of `gr_Q(R)` with respect to `R − Q` is
`Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl)`; the first conjunct says
that `gr_Q(R) → gr_Q(R)_Q` is injective, so that `gr_Q(R)` is a subset of `gr_Q(R)_Q` as the paper
regards it; `gr_Q(J, R)_Q` is the extension of the ideal `grIdeal Q J`, and the second conjunct is
`gr_Q(J, R)_Q ∩ gr_Q(R) = gr_Q(J, R)` as an equality of subsets of `gr_Q(R)_Q` (`gr_Q(R)` being
its image, `gr_Q(J, R)` the image of `grIdeal Q J`).

The proof is the printed one: the localized row `0 → gr_Q(J, R)_Q → gr_Q(R)_Q → gr_Q̄(O)_Q` is exact
(the map induced by `gr_Q(R) → gr_Q̄(O)`, `IsLocalization.map`), the first two vertical arrows are
injections (`injective_algebraMap_localization_assocGraded`: `gr_Q(R)` is a polynomial ring over
the domain `R/Q`), the last is injective since `gr_Q̄(O)` is flat over `O/Q̄`
(`injective_algebraMap_localization_assocGraded_quotient`), and then an element of `gr_Q(R)` whose
image in `gr_Q(R)_Q` lies in `gr_Q(J, R)_Q` maps to zero in `gr_Q̄(O)_Q`, hence in `gr_Q̄(O)`,
hence lies in `gr_Q(J, R)` (Lemma 5).  The prime `P` is carried but not used.  This is the form of
Lemma 11 used in the proof of Theorem 3 (`mem_grIdeal_of_algebraMap_mem_map`); the saturation form
`grIdeal_saturated_of_isNormallyFlatAlongIdeal` (a flat module over a domain is torsion-free) and
`comap_map_grIdeal_eq_of_isNormallyFlatAlongIdeal` (the inverse image form) are equivalent
statements proved earlier and are not used by it. -/
@[blueprint "lem:II.3-11-intersection"
  (statement := /-- Let $R$ be a regular local ring, $J$ an ideal in $R$, $P$ and $Q$ prime ideals
    in $R$ such that $Q\supseteq P\supseteq J$ and that $R/P$ and $R/Q$ are both regular, $O=R/J$
    and $\bar Q=Q/J$ (the notation of Lemma 10). If $\operatorname{gr}_{\bar Q}(O)$ is flat over
    $O/\bar Q$, then we have $\operatorname{gr}_Q(J,R)_Q\cap\operatorname{gr}_Q(R)=
    \operatorname{gr}_Q(J,R)$, where $(\ )_Q$ denotes the localization with respect to $R-Q$ and
    $\operatorname{gr}_Q(R)$ is regarded as a subset of $\operatorname{gr}_Q(R)_Q$ (the map
    $\operatorname{gr}_Q(R)\to\operatorname{gr}_Q(R)_Q$ is injective). (Lemma 11, p.~200.)

    \textbf{Formalization note (encoding).} The intersection is taken in
    $\operatorname{gr}_Q(R)_Q$, with $\operatorname{gr}_Q(R)$ and $\operatorname{gr}_Q(J,R)$
    replaced by their images under the (injective) localization map. -/)
  (proof := /-- Let us consider the following commutative diagram: the rows
    $0\to\operatorname{gr}_Q(J,R)\to\operatorname{gr}_Q(R)\to\operatorname{gr}_{\bar Q}(O)\to0$
    (\cref{lem:II.2-5}) and $0\to\operatorname{gr}_Q(J,R)_Q\to\operatorname{gr}_Q(R)_Q\to
    \operatorname{gr}_{\bar Q}(O)_Q\to0$, where the horizontal sequences are exact and the
    first two vertical arrows are injections ($\operatorname{gr}_Q(R)$ is a polynomial ring over
    the domain $R/Q$, so the elements of $R-Q$ are non-zero-divisors on it). Since
    $\operatorname{gr}_{\bar Q}(O)$ is flat over $O/\bar Q$, the last vertical arrow is also
    injective (a flat module over a domain is torsion-free). The assertion in the lemma follows:
    an element of $\operatorname{gr}_Q(R)$ whose image lies in $\operatorname{gr}_Q(J,R)_Q$ maps to
    zero in $\operatorname{gr}_{\bar Q}(O)_Q$, hence in $\operatorname{gr}_{\bar Q}(O)$, hence lies
    in $\operatorname{gr}_Q(J,R)$. -/)
  (latexEnv := "lemma")]
theorem grIdeal_localization_inf_range_eq (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (J P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (_hJP : J ≤ P)
    (hPQ : P ≤ Q) [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)]
    (h : IsNormallyFlatAlongIdeal (Q.map (Ideal.Quotient.mk J))) :
    Function.Injective (algebraMap (AssocGraded Q)
      (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))) ∧
    ((((grIdeal Q J).map (algebraMap (AssocGraded Q)
        (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))) :
        Ideal (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))) :
        Set (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))) ∩
      Set.range (algebraMap (AssocGraded Q)
        (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))) =
      algebraMap (AssocGraded Q)
        (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl)) ''
        (grIdeal Q J : Set (AssocGraded Q))) := by
  have hJQ : J ≤ Q := _hJP.trans hPQ
  refine ⟨injective_algebraMap_localization_assocGraded R Q, ?_⟩
  set LA := Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl) with hLA
  set LB := Localization (Algebra.algebraMapSubmonoid (AssocGraded (Q.map (Ideal.Quotient.mk J)))
    Q.primeCompl) with hLB
  set f : AssocGraded Q →+* AssocGraded (Q.map (Ideal.Quotient.mk J)) := (grMapQuot Q J).toRingHom
    with hf
  have hy : Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl ≤
      (Algebra.algebraMapSubmonoid (AssocGraded (Q.map (Ideal.Quotient.mk J))) Q.primeCompl).comap
        f := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨s, hs, ((grMapQuot Q J).commutes s).symm⟩
  let fL : LA →+* LB := IsLocalization.map LB f hy
  have hcomm : ∀ a, fL (algebraMap _ LA a) = algebraMap _ LB (f a) := fun a =>
    IsLocalization.map_eq hy a
  -- the second row is exact
  have hker : RingHom.ker fL = (grIdeal Q J).map (algebraMap (AssocGraded Q) LA) := by
    refine le_antisymm (fun x hx => ?_) ?_
    · obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective
        (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl) x
      have h0 : fL (IsLocalization.mk' LA a t) = 0 := hx
      rw [IsLocalization.map_mk'] at h0
      obtain ⟨⟨_, u, hu, rfl⟩, hu'⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp h0
      rw [IsLocalization.mk'_mem_map_algebraMap_iff
        (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl)]
      refine ⟨algebraMap R (AssocGraded Q) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← ker_grMapQuot, RingHom.mem_ker]
      have : f (algebraMap R (AssocGraded Q) u * a) = 0 := by
        rw [map_mul]
        have h1 : f (algebraMap R (AssocGraded Q) u) =
            algebraMap R (AssocGraded (Q.map (Ideal.Quotient.mk J))) u :=
          (grMapQuot Q J).commutes u
        rw [h1]
        exact hu'
      exact this
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, hcomm]
      rw [← ker_grMapQuot, RingHom.mem_ker] at ha
      rw [show f a = 0 from ha, map_zero]
  -- the chase
  ext x
  constructor
  · rintro ⟨hx, φ, rfl⟩
    refine ⟨φ, ?_, rfl⟩
    have h1 : fL (algebraMap _ LA φ) = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact hx
    rw [hcomm] at h1
    have h2 : f φ = 0 := by
      refine injective_algebraMap_localization_assocGraded_quotient R J Q hJQ h ?_
      rw [h1, map_zero]
    rw [SetLike.mem_coe, ← ker_grMapQuot, RingHom.mem_ker]
    exact h2
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨Ideal.mem_map_of_mem _ hφ, φ, rfl⟩

/-- Lemma 11 (p. 200) as it is used in Theorem 3 (pp. 201--202): "by Lemma 11,
`gr_Q(J,R)_Q ∩ gr_Q(R) = gr_Q(J,R)`": an element of `gr_Q(R)` whose image lies in `gr_Q(J,R)_Q`
(the extension of the ideal `grIdeal Q J` to `gr_Q(R)_Q`) lies in `gr_Q(J,R)`. -/
theorem mem_grIdeal_of_algebraMap_mem_map (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (J P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hJP : J ≤ P) (hPQ : P ≤ Q)
    [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)]
    (h : IsNormallyFlatAlongIdeal (Q.map (Ideal.Quotient.mk J))) {φ : AssocGraded Q}
    (hφ : algebraMap (AssocGraded Q)
      (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl)) φ ∈
      (grIdeal Q J).map (algebraMap (AssocGraded Q)
        (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl)))) :
    φ ∈ grIdeal Q J := by
  obtain ⟨hinj, hint⟩ := grIdeal_localization_inf_range_eq R J P Q hJP hPQ h
  have hmem : algebraMap (AssocGraded Q)
      (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl)) φ ∈
      (((grIdeal Q J).map (algebraMap (AssocGraded Q)
        (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))) :
        Ideal (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))) :
        Set (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))) ∩
      Set.range (algebraMap (AssocGraded Q)
        (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))) := ⟨hφ, φ, rfl⟩
  rw [hint] at hmem
  obtain ⟨w, hw, hwφ⟩ := hmem
  exact hinj hwφ ▸ hw

/-- "`ψ ∈ gr_Q(J,R)_Q`" for `ψ ∈ gr_Q(R)`, in the form `t ψ ∈ gr_Q(J,R)` for some `t ∈ R − Q`. -/
theorem algebraMap_mem_map_grIdeal_of_mul_mem (R : Type u) [CommRing R] (J Q : Ideal R)
    [Q.IsPrime] {t : R} (ht : t ∉ Q) {φ : AssocGraded Q}
    (h : algebraMap R (AssocGraded Q) t * φ ∈ grIdeal Q J) :
    algebraMap (AssocGraded Q)
      (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl)) φ ∈
      (grIdeal Q J).map (algebraMap (AssocGraded Q)
        (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))) :=
  (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl)
    (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))
    (grIdeal Q J) φ).mpr ⟨_, ⟨t, ht, rfl⟩, h⟩

end Lemma11

/-! ### Theorem 3 (pp. 200–203) -/

section Bridge

variable {R : Type u} [CommRing R] (P Q : Ideal R) (ν n : ℕ)

/-- `[g] ∈ Qⁿ grᵛ_P(R)` means `g ∈ Qⁿ Pᵛ + Pᵛ⁺¹`. -/
theorem mem_mul_sup_of_mem_pow_smul_top {g : R} (hgP : g ∈ P ^ ν)
    (hΦ : (Submodule.Quotient.mk ⟨g, hgP⟩ : GrPiece P ν) ∈
      (Q.map (Ideal.Quotient.mk P)) ^ n • (⊤ : Submodule (R ⧸ P) (GrPiece P ν))) :
    g ∈ Q ^ n * P ^ ν ⊔ P ^ (ν + 1) := by
  have h1 : (Submodule.Quotient.mk ⟨g, hgP⟩ : GrPiece P ν) ∈
      (Q ^ n • (⊤ : Submodule R (GrPiece P ν))) := by
    rw [← smul_top_map_eq P Q (GrPiece P ν) n]
    exact hΦ
  obtain ⟨a, ha, haP, hmk⟩ := exists_mem_mul_of_mem_smul_top P (Q ^ n) ν h1
  have h2 : g - a ∈ P ^ (ν + 1) := by
    have := (Submodule.Quotient.eq _).mp hmk.symm
    simpa using this
  have : g = a + (g - a) := by ring
  rw [this]
  exact add_mem (Ideal.mem_sup_left ha) (Ideal.mem_sup_right h2)

/-- A degree-`ν` projection of an element of `Qⁿ gr_P(R)` lies in `Qⁿ grᵛ_P(R)`. -/
theorem grProj_mem_pow_smul_top {x : AssocGraded P}
    (hx : x ∈ (Q.map (algebraMap R (AssocGraded P))) ^ n) :
    grProj P ν x ∈ (Q.map (Ideal.Quotient.mk P)) ^ n •
      (⊤ : Submodule (R ⧸ P) (GrPiece P ν)) := by
  set W : Submodule (R ⧸ P) (AssocGraded P) :=
    (Q.map (Ideal.Quotient.mk P)) ^ n • (⊤ : Submodule (R ⧸ P) (AssocGraded P)) with hW
  have hWmul : ∀ (r : AssocGraded P) (x : AssocGraded P), x ∈ W → r * x ∈ W := by
    intro r x hx
    refine Submodule.smul_induction_on hx (fun b hb m _ => ?_) (fun a b ha hb => ?_)
    · have : r * (b • m) = b • (r * m) := by rw [mul_smul_comm]
      rw [this]
      exact Submodule.smul_mem_smul hb trivial
    · rw [mul_add]
      exact add_mem ha hb
  have hmem : x ∈ W := by
    rw [← Ideal.map_pow] at hx
    refine Submodule.span_induction (p := fun x _ => x ∈ W) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨c, hc, rfl⟩
      have h1 : algebraMap R (AssocGraded P) c =
          (Ideal.Quotient.mk P c) • (1 : AssocGraded P) := by
        rw [Algebra.smul_def, mul_one]
        rfl
      rw [h1]
      refine Submodule.smul_mem_smul ?_ trivial
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hc
    · exact zero_mem _
    · intro a b _ _ ha hb
      exact add_mem ha hb
    · intro r a _ ha
      exact hWmul r a ha
  have := Submodule.mem_map_of_mem (f := grProj P ν) hmem
  rw [hW, Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

end Bridge

section GrClassBase

variable {R : Type u} [CommRing R] (P Q Y : Ideal R)

/-- "`Ψ ∈ Q^μ gr^d_P(R)`" (Theorem 3, pp. 201-203), for the initial form `Ψ = [g]` of an element
`g ∈ P^d` in `gr_P(R)`: the class of `g` lies in the `μ`-th power of the ideal `Q gr_P(R)` of
`gr_P(R)` (it then lies in `Q^μ gr^d_P(R)`, `Q` acting through `Q̄ = Q/P`). -/
def GrClassMemPow (d μ : ℕ) (g : R) : Prop :=
  ∃ hg : g ∈ P ^ d, AssocGraded.mk P d g hg ∈ (Q.map (algebraMap R (AssocGraded P))) ^ μ

variable {P Q Y}

/-- `[g] ∈ Q^μ gr^d_P(R)` means `g ∈ Q^μ P^d + P^{d+1}`. -/
theorem GrClassMemPow.mem_mul_sup {d μ : ℕ} {g : R} (h : GrClassMemPow P Q d μ g) :
    g ∈ P ^ d ∧ g ∈ Q ^ μ * P ^ d ⊔ P ^ (d + 1) := by
  obtain ⟨hg, h⟩ := h
  refine ⟨hg, ?_⟩
  have h1 := grProj_mem_pow_smul_top P Q d μ h
  rw [grProj_mk_same] at h1
  exact mem_mul_sup_of_mem_pow_smul_top P Q d μ hg h1

/-- The converse of `GrClassMemPow.mem_mul_sup`. -/
theorem grClassMemPow_of_mem_mul_sup {d μ : ℕ} {g : R} (hg : g ∈ P ^ d)
    (h : g ∈ Q ^ μ * P ^ d ⊔ P ^ (d + 1)) : GrClassMemPow P Q d μ g := by
  refine ⟨hg, ?_⟩
  have key : ∀ x ∈ Q ^ μ * P ^ d, ∃ hx : x ∈ P ^ d,
      AssocGraded.mk P d x hx ∈ (Q.map (algebraMap R (AssocGraded P))) ^ μ := by
    intro x hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    · refine ⟨Ideal.mul_mem_left _ _ hb, ?_⟩
      have h0 : algebraMap R (AssocGraded P) a = AssocGraded.mk P 0 a (by simp) := rfl
      have h1 : AssocGraded.mk P d (a * b) (Ideal.mul_mem_left _ _ hb) =
          algebraMap R (AssocGraded P) a * AssocGraded.mk P d b hb := by
        rw [h0, AssocGraded.mk_mul_mk P]
        exact mk_congr_of_eq P (zero_add d).symm rfl _ _
      rw [h1]
      refine Ideal.mul_mem_right _ _ ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha
    · obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      refine ⟨add_mem hx1 hy1, ?_⟩
      rw [AssocGraded.mk_add P d x y hx1 hy1]
      exact add_mem hx2 hy2
  obtain ⟨q, hq, p, hp, rfl⟩ := Submodule.mem_sup.mp h
  obtain ⟨hqP, hqI⟩ := key q hq
  have : AssocGraded.mk P d (q + p) hg = AssocGraded.mk P d q hqP :=
    mk_eq_mk_of_sub_mem_pow_succ P hg hqP (by simpa using hp)
  rw [this]
  exact hqI

theorem GrClassMemPow.mono {d μ μ' : ℕ} {g : R} (hμ : μ ≤ μ') (h : GrClassMemPow P Q d μ' g) :
    GrClassMemPow P Q d μ g := by
  obtain ⟨hg, h⟩ := h
  exact ⟨hg, Ideal.pow_le_pow_right hμ h⟩

theorem grClassMemPow_zero {d : ℕ} {g : R} (hg : g ∈ P ^ d) : GrClassMemPow P Q d 0 g :=
  ⟨hg, by simp⟩

end GrClassBase

section Theorem3


/-- Cohen's structure theorem, as invoked in the proof of Theorem 3 (p. 200): "By Cohen's
structure theorem of a complete local ring, O is a quotient ring R/J of a complete regular local
ring R by an ideal J."  Cited in the paper, not proved there: I. S. Cohen, *On the structure and
ideal theory of complete local rings*, Trans. Amer. Math. Soc. 59 (1946), 54–106; see also
Matsumura, *Commutative Ring Theory*, Theorem 29.4, and Nagata, *Local Rings*, (31.12).

Encoding: `O` is a noetherian local ring complete for its maximal ideal
(`IsAdicComplete (maximalIdeal O) O`); "`O` is a quotient ring `R/J`" is a surjective ring
homomorphism `R →+* O` (with `J` its kernel). -/
@[blueprint "thm:cohen-structure"
  (statement := /-- (Cohen's structure theorem.) Let $O$ be a complete (noetherian) local
    ring. Then $O$ is a quotient ring $R/J$ of a complete regular local ring $R$ by an ideal
    $J$. (Cited in the proof of \cref{thm:II.3-3}, p.~200.) -/)
  (proof := /-- Cited: I.~S.~Cohen, On the structure and ideal theory of complete local rings,
    Trans.\ Amer.\ Math.\ Soc.\ 59 (1946); Matsumura, \emph{Commutative Ring Theory},
    Theorem~29.4; Nagata, \emph{Local Rings}, (31.12). -/)
  (latexEnv := "theorem")]
theorem exists_surjective_of_isRegularLocalRing_of_isAdicComplete [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] :
    ∀ (O : Type u) [CommRing O]
    [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O],
    ∃ (R : Type u) (_ : CommRing R) (_ : IsRegularLocalRing R)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (f : R →+* O),
      Function.Surjective f :=
  @Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.exists_surjective_of_isRegularLocalRing_of_isAdicComplete _

/-! The reduction of Theorem 3 to the case of a complete `O` ("By cor:II.3-lem9 we may assume
that O is complete") uses that the completion `Ô` of a noetherian local ring is noetherian and
that `Ô/QÔ`, the completion of `O/Q`, is regular when `O/Q` is. -/

/-- A polynomial all of whose monomials have total degree `≥ k`, evaluated at elements of an
ideal `m`, lies in `mᵏ`. -/
private theorem eval_mem_pow_of_degree_le {S : Type u} [CommRing S] {n : ℕ} (m : Ideal S)
    (x : Fin n → S) (hx : ∀ i, x i ∈ m)
    (k : ℕ) (H : MvPolynomial (Fin n) S)
    (hH : ∀ α ∈ H.support, k ≤ α.degree) : MvPolynomial.eval x H ∈ m ^ k := by
  classical
  rw [MvPolynomial.eval_eq]
  refine Ideal.sum_mem _ fun α hα => ?_
  refine Ideal.mul_mem_left _ _ ?_
  refine Ideal.pow_le_pow_right (hH α hα) ?_
  have : ∏ i ∈ α.support, x i ^ α i ∈ ∏ i ∈ α.support, m ^ α i :=
    Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hx i) _
  rwa [Finset.prod_pow_eq_pow_sum] at this

/-- Every element of `mᵏ` is the value at the generators `x` of a homogeneous polynomial of
degree `k`. -/
private theorem exists_isHomogeneous_eval_eq {S : Type u} [CommRing S] {n : ℕ} (m : Ideal S)
    (x : Fin n → S)
    (hx : Ideal.span (Set.range x) = m) (k : ℕ) (d : S) (hd : d ∈ m ^ k) :
    ∃ P : MvPolynomial (Fin n) S, P.IsHomogeneous k ∧ MvPolynomial.eval x P = d := by
  induction k generalizing d with
  | zero => exact ⟨MvPolynomial.C d, MvPolynomial.isHomogeneous_C _ _, by simp⟩
  | succ k ih =>
    rw [pow_succ] at hd
    refine Submodule.mul_induction_on hd (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · obtain ⟨Pa, hPa, rfl⟩ := ih a ha
      rw [← hx] at hb
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hb
      refine ⟨Pa * ∑ i, MvPolynomial.C (c i) * MvPolynomial.X i, hPa.mul ?_, ?_⟩
      · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
        simpa using (MvPolynomial.isHomogeneous_C _ (c i)).mul (MvPolynomial.isHomogeneous_X _ i)
      · simp [smul_eq_mul]
    · obtain ⟨Pa, hPa, rfl⟩ := ha
      obtain ⟨Pb, hPb, rfl⟩ := hb
      exact ⟨Pa + Pb, hPa.add hPb, by simp⟩

open MvPowerSeries in
/-- The adic completion of a noetherian ring along an ideal is noetherian: it is a quotient of a
power series ring `S⟦X₁, …, Xₙ⟧` (`Xᵢ ↦ xᵢ`, the `xᵢ` generating the ideal). -/
private theorem isNoetherianRing_adicCompletion {S : Type u} [CommRing S] [IsNoetherianRing S]
    (m : Ideal S) :
    IsNoetherianRing (AdicCompletion m S) := by
  classical
  obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian m)
  have hxm : ∀ i, x i ∈ m := fun i => hx ▸ Ideal.subset_span ⟨i, rfl⟩
  have htop : ∀ a b : S ⧸ m ^ 0, a = b := fun a b => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.eq, pow_zero, Ideal.one_eq_top]
    trivial
  -- two truncations agreeing in degrees `< k` have the same value modulo `mᵏ`
  have hdiff : ∀ (k : ℕ) (H₁ H₂ : MvPolynomial (Fin n) S),
      (∀ α : Fin n →₀ ℕ, α.degree < k → H₁.coeff α = H₂.coeff α) →
      Ideal.Quotient.mk (m ^ k) (MvPolynomial.eval x H₁) =
        Ideal.Quotient.mk (m ^ k) (MvPolynomial.eval x H₂) := by
    intro k H₁ H₂ h
    rw [Ideal.Quotient.eq, ← map_sub]
    refine eval_mem_pow_of_degree_le m x hxm k _ fun α hα => ?_
    by_contra hlt
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, h α (not_le.mp hlt),
      sub_self] at hα
    exact hα rfl
  let f : ∀ k, MvPowerSeries (Fin n) S →+* S ⧸ m ^ k := fun k =>
    { toFun := fun F => Ideal.Quotient.mk (m ^ k) (MvPolynomial.eval x (truncTotal k F))
      map_one' := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · exact htop _ _
        · rw [truncTotal_one hk.ne', map_one, map_one]
      map_mul' := fun F G => by
        rw [← map_mul, ← map_mul]
        exact hdiff k _ _ fun α hα => by
          rw [coeff_truncTotal _ hα, coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hα]
      map_zero' := by simp
      map_add' := fun F G => by simp }
  have hf : ∀ k F, f k F = Ideal.Quotient.mk (m ^ k) (MvPolynomial.eval x (truncTotal k F)) :=
    fun _ _ => rfl
  have hcompat : ∀ {k l : ℕ} (hkl : k ≤ l),
      (Ideal.Quotient.factorPow m hkl).comp (f l) = f k := by
    intro k l hkl
    ext F
    rw [RingHom.comp_apply, hf, hf, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    exact hdiff k _ _ fun α hα => by
      rw [coeff_truncTotal _ hα, coeff_truncTotal _ (lt_of_lt_of_le hα hkl)]
  let Φ := AdicCompletion.liftRingHom m f hcompat
  have hΦ : Function.Surjective Φ := by
    intro a
    obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective m S a
    have hd : ∀ k, c.val (k + 1) - c.val k ∈ m ^ k := by
      intro k
      have := AdicCompletion.AdicCauchySequence.mk_eq_mk (Nat.le_succ k) c
      rw [Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top] at this
      exact this
    choose P hP hPe using fun k => exists_isHomogeneous_eval_eq m x hx k _ (hd k)
    let F : MvPowerSeries (Fin n) S := fun α =>
      (P α.degree).coeff α + if α = 0 then c.val 0 else 0
    have hF : ∀ α, MvPowerSeries.coeff α F = (P α.degree).coeff α + if α = 0 then c.val 0 else 0 :=
      fun _ => rfl
    have htrunc : ∀ k, 0 < k → truncTotal k F =
        MvPolynomial.C (c.val 0) + ∑ j ∈ Finset.range k, P j := by
      intro k hk
      ext α
      rw [coeff_truncTotal_eq_ite, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        MvPolynomial.coeff_C, MvPolynomial.coeff_sum]
      by_cases hα : α.degree < k
      · have hsum : ∑ j ∈ Finset.range k, (P j).coeff α = (P α.degree).coeff α := by
          refine Finset.sum_eq_single α.degree (fun j _ hj => ?_) (fun h => ?_)
          · exact (hP j).coeff_eq_zero (fun h => hj h.symm)
          · exact absurd (Finset.mem_range.mpr hα) h
        simp only [hα, ↓reduceIte, hsum, hF]
        by_cases h0 : α = 0
        · simp only [h0, ↓reduceIte]
          ring
        · have h0' : ¬ (0 = α) := fun h => h0 h.symm
          simp only [h0, h0', ↓reduceIte]
          ring
      · have hsum : ∑ j ∈ Finset.range k, (P j).coeff α = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          refine (hP j).coeff_eq_zero fun h => hα ?_
          rw [h]
          exact Finset.mem_range.mp hj
        have h0 : ¬ (0 = α) := fun h => hα (by rw [← h]; simpa using hk)
        simp only [hα, h0, ↓reduceIte, hsum, add_zero]
    refine ⟨F, AdicCompletion.ext_evalₐ fun k => ?_⟩
    rw [AdicCompletion.evalₐ_liftRingHom, AdicCompletion.evalₐ_mk, hf]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact htop _ _
    · rw [htrunc k hk, map_add, map_sum, MvPolynomial.eval_C]
      simp only [hPe]
      rw [Finset.sum_range_sub (fun j => c.val j), add_sub_cancel]
  exact isNoetherianRing_of_surjective _ _ Φ hΦ

/-- The completion of a regular local ring is a regular local ring: the images of a regular
system of parameters form a regular sequence in `Ŝ` (faithfully flat over `S`) generating its
maximal ideal. -/
private theorem isRegularLocalRing_adicCompletion (S : Type u) [CommRing S] [IsRegularLocalRing S] :
    IsRegularLocalRing (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
  classical
  set m := IsLocalRing.maximalIdeal S
  have := isNoetherianRing_adicCompletion m
  obtain ⟨S₀, hScard, hSspan⟩ := (IsNoetherian.noetherian m).exists_span_finset_card_eq_spanFinrank
  have hS : Ideal.span (S₀ : Set S) = m := hSspan
  let z : Fin S₀.card → S := fun i => (S₀.equivFin.symm i : S)
  have hinj : Function.Injective z := Subtype.val_injective.comp S₀.equivFin.symm.injective
  have hreg := isRegular_ofFn_of_minimal hS hScard hinj (fun i => (S₀.equivFin.symm i).2)
  have : Module.FaithfullyFlat S (AdicCompletion m S) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hreg' := hreg.of_faithfullyFlat (S := AdicCompletion m S)
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hreg'
  have hz : Ideal.ofList (List.ofFn z) = m := by
    rw [← hS]
    show Ideal.span {r | r ∈ List.ofFn z} = Ideal.span (S₀ : Set S)
    congr 1
    ext y
    show y ∈ List.ofFn z ↔ y ∈ (S₀ : Set S)
    rw [List.mem_ofFn, Finset.mem_coe]
    constructor
    · rintro ⟨i, rfl⟩
      exact (S₀.equivFin.symm i).2
    · intro hy
      exact ⟨S₀.equivFin ⟨y, hy⟩, by simp [z]⟩
  have hof : Ideal.ofList ((List.ofFn z).map (algebraMap S (AdicCompletion m S))) =
      IsLocalRing.maximalIdeal (AdicCompletion m S) := by
    rw [← Ideal.map_ofList, hz, AdicCompletion.maximalIdeal_eq_map]
  rw [hof, List.length_map, List.length_ofFn] at hdim
  have h0 : ringKrullDim (AdicCompletion m S ⧸ IsLocalRing.maximalIdeal (AdicCompletion m S)) =
      0 := by
    let _ := Ideal.Quotient.field (IsLocalRing.maximalIdeal (AdicCompletion m S))
    exact ringKrullDim_eq_zero_of_field _
  rw [h0, zero_add] at hdim
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  rw [AdicCompletion.spanFinrank_maximalIdeal_eq, ← hScard, hdim]

/-- For an ideal `Q` of a noetherian local ring `O` with `O/Q` local, `Ô/QÔ` is the completion
of `O/Q`. -/
private theorem nonempty_adicCompletion_quotient_ringEquiv (O : Type u) [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] (Q : Ideal O) [IsLocalRing (O ⧸ Q)] :
    Nonempty (((AdicCompletion (IsLocalRing.maximalIdeal O) O) ⧸
        Q.map (algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O))) ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal (O ⧸ Q)) (O ⧸ Q)) := by
  classical
  set m := IsLocalRing.maximalIdeal O
  set mS := IsLocalRing.maximalIdeal (O ⧸ Q)
  have hmS : m.map (Ideal.Quotient.mk Q) = mS :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hle : ∀ n, m ^ n ≤ (mS ^ n).comap (Ideal.Quotient.mk Q) := fun n => by
    rw [← hmS, ← Ideal.map_pow]
    exact Ideal.le_comap_map
  -- `gₙ : O/mⁿ → S/m_Sⁿ` (`S = O/Q`).
  let g : ∀ n, O ⧸ m ^ n →+* (O ⧸ Q) ⧸ mS ^ n := fun n =>
    Ideal.quotientMap _ (Ideal.Quotient.mk Q) (hle n)
  have hg : ∀ n (r : O), g n (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk Q r) := fun n r => Ideal.quotientMap_mk
  -- `evalₐ` on `(AdicCompletion (IsLocalRing.maximalIdeal O) O)` of a Cauchy sequence.
  have hev : ∀ {k n : ℕ} (hkn : k ≤ n) (a : (AdicCompletion (IsLocalRing.maximalIdeal O) O)),
      Ideal.Quotient.factorPow m hkn
      (AdicCompletion.evalₐ m n a) = AdicCompletion.evalₐ m k a := by
    intro k n hkn a
    obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective m O a
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
    have := AdicCompletion.AdicCauchySequence.mk_eq_mk hkn c
    rw [Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top] at this
    exact this
  let ψ : (AdicCompletion (IsLocalRing.maximalIdeal O) O) →+* AdicCompletion mS (O ⧸ Q) :=
    AdicCompletion.liftRingHom mS (fun n => (g n).comp (AdicCompletion.evalₐ m n).toRingHom)
      (fun {k n} hkn => by
        ext a
        obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ m n a)
        have hk := hev hkn a
        rw [← hr, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk] at hk
        simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe]
        rw [← hr, ← hk, hg, hg, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk])
  have hψ : ∀ n (a : (AdicCompletion (IsLocalRing.maximalIdeal O) O)),
      AdicCompletion.evalₐ mS n (ψ a) =
      g n (AdicCompletion.evalₐ m n a) := fun n a => AdicCompletion.evalₐ_liftRingHom _ _ _ _ _
  have hker : RingHom.ker ψ =
      Q.map (algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O)) := by
    apply le_antisymm
    · intro a ha
      rw [RingHom.mem_ker] at ha
      apply mem_map_of_adicCompletionMap_mkQ_eq_zero O
      obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective m O a
      ext n
      have h := hψ n (AdicCompletion.mk m O c)
      rw [ha, map_zero, AdicCompletion.evalₐ_mk, hg, eq_comm, Ideal.Quotient.eq_zero_iff_mem,
        ← hmS, ← Ideal.map_pow] at h
      rw [AdicCompletion.map_val_apply, AdicCompletion.mk_apply_coe, Submodule.mkQ_apply,
        LinearMap.reduceModIdeal_apply, AdicCompletion.val_zero_apply,
        Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
        Ideal.Quotient.algebraMap_eq]
      exact h
    · rw [Ideal.map_le_iff_le_comap]
      intro q hq
      rw [Ideal.mem_comap, RingHom.mem_ker]
      refine AdicCompletion.ext_evalₐ fun n => ?_
      rw [hψ, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        AdicCompletion.evalₐ_of, hg, map_zero, Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]
  -- `ψ` is surjective: lift an `m_S`-adic Cauchy sequence of `O/Q` to an `m`-adic one of `O`
  have hsurj : Function.Surjective ψ := by
    intro b
    obtain ⟨c', rfl⟩ := AdicCompletion.mk_surjective mS (O ⧸ Q) b
    have hc' : ∀ k, c'.val (k + 1) - c'.val k ∈ mS ^ k := by
      intro k
      have := AdicCompletion.AdicCauchySequence.mk_eq_mk (Nat.le_succ k) c'
      rw [Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top] at this
      exact this
    have hcomap : ∀ k, (mS ^ k).comap (Ideal.Quotient.mk Q) = m ^ k ⊔ Q := by
      intro k
      rw [← hmS, ← Ideal.map_pow, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    have step : ∀ (k : ℕ) (a : O), Ideal.Quotient.mk Q a - c'.val k ∈ mS ^ k →
        ∃ a' : O, a' - a ∈ m ^ k ∧ Ideal.Quotient.mk Q a' - c'.val (k + 1) ∈ mS ^ (k + 1) := by
      intro k a ha
      obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (c'.val (k + 1))
      have h1 : t - a ∈ m ^ k ⊔ Q := by
        rw [← hcomap, Ideal.mem_comap, map_sub, ht]
        have := Ideal.sub_mem _ (hc' k) ha
        rwa [sub_sub_sub_cancel_right] at this
      obtain ⟨e, he, q, hq, hqe⟩ := Submodule.mem_sup.mp h1
      refine ⟨a + e, by rwa [add_sub_cancel_left], ?_⟩
      have h2 : Ideal.Quotient.mk Q (a + e) = c'.val (k + 1) := by
        rw [← ht, Ideal.Quotient.eq]
        have : a + e - t = -q := by
          rw [← sub_eq_zero]
          have hqe' : e + q = t - a := hqe
          linear_combination hqe'
        rw [this]
        exact neg_mem hq
      rw [h2, sub_self]
      exact zero_mem _
    choose nxt hnxt1 hnxt2 using step
    obtain ⟨a₀, -⟩ := Ideal.Quotient.mk_surjective (c'.val 0)
    let seq : (k : ℕ) → {a : O // Ideal.Quotient.mk Q a - c'.val k ∈ mS ^ k} := fun k =>
      Nat.rec ⟨a₀, by rw [pow_zero, Ideal.one_eq_top]; trivial⟩
        (fun k a => ⟨nxt k a.1 a.2, hnxt2 k a.1 a.2⟩) k
    have hseq : ∀ k, (seq (k + 1)).1 - (seq k).1 ∈ m ^ k := fun k => hnxt1 k _ _
    let c : AdicCompletion.AdicCauchySequence m O :=
      AdicCompletion.AdicCauchySequence.mk m O (fun k => (seq k).1) fun k => by
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]
        exact neg_mem (hseq k)
    refine ⟨AdicCompletion.mk m O c, AdicCompletion.ext_evalₐ fun n => ?_⟩
    rw [hψ, AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, hg, Ideal.Quotient.eq]
    exact (seq n).2
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)⟩

/-- `Ô/QÔ` is regular when `O/Q` is (it is the completion of `O/Q`). -/
private theorem isRegularLocalRing_adicCompletion_quotient (O : Type u) [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] (Q : Ideal O) [IsRegularLocalRing (O ⧸ Q)] :
    IsRegularLocalRing ((AdicCompletion (IsLocalRing.maximalIdeal O) O) ⧸
      Q.map (algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O))) := by
  obtain ⟨e⟩ := nonempty_adicCompletion_quotient_ringEquiv O Q
  have := isRegularLocalRing_adicCompletion (O ⧸ Q)
  exact IsRegularLocalRing.of_ringEquiv e.symm

/-- A ring isomorphism `A ≅ B` carrying `I` to `J` identifies `grⁿ_I(A)` with `grⁿ_J(B)`,
semilinearly over `A/I ≅ B/J`. -/
private theorem exists_grPiece_addEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (J : Ideal B) (hIJ : I.map (e : A →+* B) = J) (n : ℕ) :
    ∃ j : GrPiece I n ≃+ GrPiece J n, ∀ (r : A ⧸ I) (m : GrPiece I n),
      j (r • m) = Ideal.quotientEquiv I J e hIJ.symm r • j m := by
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.symm (e : A →+* B) (e.symm : B →+* A)
  let f₀ : A ≃ₛₗ[(e : A →+* B)] B := e.toSemilinearEquiv
  have hpow : ∀ k, J ^ k = (I ^ k).comap (e.symm : B →+* A) := by
    intro k
    rw [← hIJ, ← Ideal.map_pow, Ideal.map_comap_of_equiv]
    rfl
  have hmap : ∀ k, Submodule.map (f₀ : A →ₛₗ[(e : A →+* B)] B) (I ^ k) = J ^ k := by
    intro k
    ext x
    rw [Submodule.mem_map, hpow k, Ideal.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [f₀] using hy
    · intro hx
      exact ⟨e.symm x, hx, by simp [f₀]⟩
  let g₀ : ↥(I ^ n) ≃ₛₗ[(e : A →+* B)] ↥(J ^ n) :=
    (f₀.submoduleMap (I ^ n)).trans (LinearEquiv.ofEq _ _ (hmap n))
  have hq : (Submodule.comap (I ^ n).subtype (I ^ (n + 1))).map
      (g₀ : ↥(I ^ n) →ₛₗ[(e : A →+* B)] ↥(J ^ n)) =
      Submodule.comap (J ^ n).subtype (J ^ (n + 1)) := by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext ⟨x, hx⟩
    show ((g₀.symm ⟨x, hx⟩ : ↥(I ^ n)) : A) ∈ I ^ (n + 1) ↔ x ∈ J ^ (n + 1)
    rw [hpow (n + 1), Ideal.mem_comap]
    rfl
  let j : GrPiece I n ≃ₛₗ[(e : A →+* B)] GrPiece J n := Submodule.Quotient.equiv _ _ g₀ hq
  refine ⟨j.toAddEquiv, fun r m => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  have h1 : (Ideal.Quotient.mk I a) • m = a • m := algebraMap_smul (A ⧸ I) a m
  have h2 : Ideal.quotientEquiv I J e hIJ.symm (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk J (e a) := rfl
  have h3 : (Ideal.Quotient.mk J (e a)) • j m = e a • j m := algebraMap_smul (B ⧸ J) (e a) (j m)
  rw [h1, h2]
  change j (a • m) = Ideal.Quotient.mk J (e a) • j m
  rw [h3]
  exact j.map_smulₛₗ a m

/-- Freeness is transported along a semilinear additive isomorphism. -/
private theorem free_of_equiv_equiv {K L M N : Type u} [CommRing K] [CommRing L]
    [AddCommGroup M] [AddCommGroup N] [Module K M] [Module L N] (i : K ≃+* L) (j : M ≃+ N)
    (hc : ∀ (r : K) (m : M), j (r • m) = i r • j m) [Module.Free K M] : Module.Free L N := by
  let : Module K N := Module.compHom N (i : K →+* L)
  let j' : M ≃ₗ[K] N := { j with map_smul' := hc }
  exact Module.Free.of_basis (((Module.Free.chooseBasis K M).map j').mapCoeffs i fun _ _ => rfl)

/-- Normal flatness is invariant under ring isomorphisms. -/
private theorem isNormallyFlatAlongIdeal_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (J : Ideal B) (hIJ : I.map (e : A →+* B) = J)
    (h : IsNormallyFlatAlongIdeal I) : IsNormallyFlatAlongIdeal J := fun n => by
  obtain ⟨j, hj⟩ := exists_grPiece_addEquiv e I J hIJ n
  have := h n
  exact free_of_equiv_equiv _ j hj

/-- `(X.primeCompl).map e = (X.map e).primeCompl` for a ring isomorphism `e`. -/
private theorem primeCompl_map_ringEquiv {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)
    (X : Ideal A) [X.IsPrime] [(X.map (e : A →+* B)).IsPrime] :
    X.primeCompl.map e.toMonoidHom = (X.map (e : A →+* B)).primeCompl := by
  ext y
  rw [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨e.symm y, hy, by simp⟩

/-- The reduction of Theorem 3, (ii) ⇒ (i), to its case `O = R/J` with `R` a complete regular
local ring ("By cor:II.3-lem9 we may assume that O is complete. By Cohen's structure theorem …,
O is a quotient ring R/J of a complete regular local ring R"): the conditions pass to the
completion `Ô` (Lemma 9, its corollary, and the regularity of `Ô/P̂`, `Ô/Q̂`), and along the
isomorphism `R/J ≅ Ô`. -/
private theorem isNormallyFlatAlongIdeal_of_complete_case [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}]
    (hcore : ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (J P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
      [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)]
      [(Q.map (Ideal.Quotient.mk J)).IsPrime], J ≤ P → P ≤ Q →
      IsNormallyFlatAlongIdeal (Q.map (Ideal.Quotient.mk J)) →
      IsNormallyFlatAlongIdeal ((P.map (Ideal.Quotient.mk J)).map
        (algebraMap (R ⧸ J) (Localization.AtPrime (Q.map (Ideal.Quotient.mk J))))) →
      IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)))
    (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (P Q : Ideal O) [P.IsPrime]
    [Q.IsPrime] (hPQ : P ≤ Q) [IsRegularLocalRing (O ⧸ P)] [IsRegularLocalRing (O ⧸ Q)]
    (hQ : IsNormallyFlatAlongIdeal Q)
    (hPQ' : IsNormallyFlatAlongIdeal (P.map (algebraMap O (Localization.AtPrime Q)))) :
    IsNormallyFlatAlongIdeal P := by
  set m := IsLocalRing.maximalIdeal O
  have : IsNoetherianRing (AdicCompletion m O) := isNoetherianRing_adicCompletion m
  have : Module.FaithfullyFlat O (AdicCompletion m O) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have := isRegularLocalRing_adicCompletion_quotient O P
  have := isRegularLocalRing_adicCompletion_quotient O Q
  have : (P.map (algebraMap O (AdicCompletion m O))).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
  have : (Q.map (algebraMap O (AdicCompletion m O))).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
  -- the conditions on the completion (Lemma 9 and its corollary)
  have hQ₁ : IsNormallyFlatAlongIdeal (Q.map (algebraMap O (AdicCompletion m O))) :=
    (isNormallyFlatAlongIdeal_iff_of_faithfullyFlat (A' := AdicCompletion m O) Q).mp hQ
  obtain ⟨_, h2⟩ := isNormallyFlatAlongIdeal_localization_iff_completion O P Q hPQ
  have hP₁ := h2.mp hPQ'
  refine (isNormallyFlatAlongIdeal_iff_of_faithfullyFlat (A' := AdicCompletion m O) P).mpr ?_
  -- Cohen's structure theorem: `Ô = R/J`
  obtain ⟨R, _, _, _, f, hf⟩ :=
    exists_surjective_of_isRegularLocalRing_of_isAdicComplete (AdicCompletion m O)
  set P₁ := P.map (algebraMap O (AdicCompletion m O))
  set Q₁ := Q.map (algebraMap O (AdicCompletion m O))
  set J := RingHom.ker f
  let e : (R ⧸ J) ≃+* AdicCompletion m O := RingHom.quotientKerEquivOfSurjective hf
  have he : (e : R ⧸ J →+* AdicCompletion m O).comp (Ideal.Quotient.mk J) = f := by
    ext r; rfl
  have hmap : ∀ I : Ideal (AdicCompletion m O),
      ((I.comap f).map (Ideal.Quotient.mk J)).map (e : R ⧸ J →+* AdicCompletion m O) = I := by
    intro I
    rw [Ideal.map_map, he, Ideal.map_comap_of_surjective _ hf]
  have hmap' : ∀ I : Ideal (AdicCompletion m O),
      I.map (e.symm : AdicCompletion m O →+* R ⧸ J) = (I.comap f).map (Ideal.Quotient.mk J) := by
    intro I
    conv_lhs => rw [← hmap I]
    rw [Ideal.map_map]
    convert Ideal.map_id _
    exact RingHom.ext fun a => e.symm_apply_apply a
  -- the primes `P' = f⁻¹(P̂)`, `Q' = f⁻¹(Q̂)` of `R`
  have hreg : ∀ I : Ideal (AdicCompletion m O), IsRegularLocalRing (AdicCompletion m O ⧸ I) →
      IsRegularLocalRing (R ⧸ I.comap f) := by
    intro I hI
    have hg : Function.Surjective ((Ideal.Quotient.mk I).comp f) :=
      Ideal.Quotient.mk_surjective.comp hf
    have hker : RingHom.ker ((Ideal.Quotient.mk I).comp f) = I.comap f := by
      rw [← RingHom.comap_ker, Ideal.mk_ker]
    exact IsRegularLocalRing.of_ringEquiv ((Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective hg)).symm
  have := hreg P₁ inferInstance
  have := hreg Q₁ inferInstance
  have hJP : J ≤ P₁.comap f := fun x hx => by
    rw [Ideal.mem_comap, RingHom.mem_ker.mp hx]
    exact zero_mem _
  have hPQ₁ : P₁.comap f ≤ Q₁.comap f := Ideal.comap_mono (Ideal.map_mono hPQ)
  have : ((Q₁.comap f).map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]; exact hJP.trans hPQ₁)
  -- transport of the hypotheses along `e`
  have hA := isNormallyFlatAlongIdeal_of_ringEquiv e.symm Q₁ _ (hmap' Q₁) hQ₁
  have hQmap : ((Q₁.comap f).map (Ideal.Quotient.mk J)).map (e : R ⧸ J →+* AdicCompletion m O) =
      Q₁ := hmap Q₁
  let E : Localization.AtPrime ((Q₁.comap f).map (Ideal.Quotient.mk J)) ≃+*
      Localization.AtPrime Q₁ :=
    IsLocalization.ringEquivOfRingEquiv (M := ((Q₁.comap f).map (Ideal.Quotient.mk J)).primeCompl)
      (T := Q₁.primeCompl) _ _ e (by
      have : (((Q₁.comap f).map (Ideal.Quotient.mk J)).map
          (e : R ⧸ J →+* AdicCompletion m O)).IsPrime := by
        rw [hQmap]; infer_instance
      rw [primeCompl_map_ringEquiv e ((Q₁.comap f).map (Ideal.Quotient.mk J))]
      ext y
      show y ∉ ((Q₁.comap f).map (Ideal.Quotient.mk J)).map (e : R ⧸ J →+* AdicCompletion m O) ↔
        y ∉ Q₁
      rw [hQmap])
  have hE : ∀ x, E (algebraMap _ _ x) = algebraMap _ (Localization.AtPrime Q₁) (e x) :=
    fun x => IsLocalization.ringEquivOfRingEquiv_eq _ x
  have hB : IsNormallyFlatAlongIdeal (((P₁.comap f).map (Ideal.Quotient.mk J)).map
      (algebraMap (R ⧸ J) (Localization.AtPrime ((Q₁.comap f).map (Ideal.Quotient.mk J))))) := by
    have h3 : (((P₁.comap f).map (Ideal.Quotient.mk J)).map (algebraMap (R ⧸ J)
        (Localization.AtPrime ((Q₁.comap f).map (Ideal.Quotient.mk J))))).map
        (E : _ →+* Localization.AtPrime Q₁) =
        P₁.map (algebraMap _ (Localization.AtPrime Q₁)) := by
      rw [Ideal.map_map, Ideal.map_map]
      conv_rhs => rw [← Ideal.map_comap_of_surjective f hf P₁, Ideal.map_map]
      congr 1
      ext r
      exact hE _
    refine isNormallyFlatAlongIdeal_of_ringEquiv E.symm _ _ ?_ hP₁
    rw [← h3, Ideal.map_map]
    convert Ideal.map_id _
    exact RingHom.ext fun a => E.symm_apply_apply a
  have hcore' := hcore R J (P₁.comap f) (Q₁.comap f) hJP hPQ₁ hA hB
  exact isNormallyFlatAlongIdeal_of_ringEquiv e _ _ (hmap P₁) hcore'

/-! ### Lemma 10 (p. 199) -/

/-- `B/JB ≅ (A/J)_{q/J}` for a localization `B` of `A` at a prime `q ⊇ J` ("gr and quotients
commute with localization"; used to localize the hypotheses of Lemma 10 at `Q`). -/
private theorem exists_ringEquiv_quotient_localization {A : Type u} [CommRing A] (q : Ideal A)
    [q.IsPrime] (J : Ideal A) (hJq : J ≤ q) (B : Type u) [CommRing B] [Algebra A B]
    [IsLocalization.AtPrime B q] [hq' : (q.map (Ideal.Quotient.mk J)).IsPrime] :
    ∃ e : B ⧸ J.map (algebraMap A B) ≃+* Localization.AtPrime (q.map (Ideal.Quotient.mk J)),
      ∀ a : A, e (Ideal.Quotient.mk _ (algebraMap A B a)) =
        algebraMap (A ⧸ J) _ (Ideal.Quotient.mk J a) := by
  set q' : Ideal (A ⧸ J) := q.map (Ideal.Quotient.mk J) with hq'def
  have hsub : Algebra.algebraMapSubmonoid (A ⧸ J) q.primeCompl = q'.primeCompl := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨b, hb, hba⟩
      show Ideal.Quotient.mk J a ∉ q'
      rw [hq'def, Ideal.mem_quotient_iff_mem hJq]
      intro ha
      apply hb
      have hba' : Ideal.Quotient.mk J b = Ideal.Quotient.mk J a := hba
      rw [Ideal.Quotient.eq] at hba'
      have := q.add_mem (hJq hba') ha
      simpa using this
    · intro ha
      refine ⟨a, fun ha' => ha ?_, rfl⟩
      exact Ideal.mem_map_of_mem _ ha'
  have : IsLocalization q'.primeCompl (B ⧸ J.map (algebraMap A B)) :=
    hsub ▸ (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ J) q.primeCompl)
      (B ⧸ J.map (algebraMap A B)))
  let e := IsLocalization.algEquiv q'.primeCompl (Localization.AtPrime q')
    (B ⧸ J.map (algebraMap A B))
  refine ⟨e.symm.toRingEquiv, fun a => ?_⟩
  have h1 : Ideal.Quotient.mk (J.map (algebraMap A B)) (algebraMap A B a) =
      algebraMap (A ⧸ J) (B ⧸ J.map (algebraMap A B)) (Ideal.Quotient.mk J a) := rfl
  show e.symm _ = _
  rw [h1, AlgEquiv.commutes]

/-- The part of Lemma 10 after localization (`Q` maximal; "we may assume that Q is the maximal
ideal of R"): flatness of `gr_{P̄}(O)` gives, via Cor. 1 of Th. 2
(`isNormallyFlatAlongIdeal_tfae_of_eq_maximalIdeal`, footnote 43), a system `(f_j)` as in
Lemma 7, and the key
step of the proof of Lemma 7 (`Qⁿ gr_P(R) ∩ gr_P(J,R) = Qⁿ gr_P(J,R)`, in its form at the level
of `R`) puts every `g ∈ J ∩ Pᵛ` whose class in `grᵛ_P(R)` lies in `Qⁿ gr_P(R)` into
`Σ_j Qⁿ P^(ν-ν_j) f_j + P^(ν+1)`. -/
private theorem exists_system_mem_sup_of_isNormallyFlatAlongIdeal (S : Type u) [CommRing S]
    [IsRegularLocalRing S] (J P : Ideal S)
    [P.IsPrime] [IsRegularLocalRing (S ⧸ P)] (hJP : J ≤ P)
    (hflat : IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J))) :
    ∃ (m : ℕ) (f : Fin m → S) (νf : Fin m → ℕ), (∀ β, f β ∈ J) ∧ (∀ β, f β ∈ P ^ νf β) ∧
      (∀ (ν n : ℕ) (g : S), g ∈ J → g ∈ P ^ ν →
        g ∈ (IsLocalRing.maximalIdeal S) ^ n * P ^ ν ⊔ P ^ (ν + 1) →
        g ∈ (∑ β ∈ Finset.univ.filter (fun β => νf β ≤ ν),
          (IsLocalRing.maximalIdeal S) ^ n * P ^ (ν - νf β) * Ideal.span {f β}) ⊔ P ^ (ν + 1)) ∧
      ∀ (μ : ℕ) (g : S), g ∈ J → g ∈ (IsLocalRing.maximalIdeal S) ^ μ →
        ∃ c : Fin m → S, (∀ β, c β ∈ (IsLocalRing.maximalIdeal S) ^ (μ - νf β)) ∧
          g - ∑ β, c β * f β ∈ (IsLocalRing.maximalIdeal S) ^ (μ + 1) := by
  classical
  set Q := IsLocalRing.maximalIdeal S with hQdef
  let _ : Field (S ⧸ Q) := Ideal.Quotient.field Q
  have hPQ : P ≤ Q := IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top'
  have hsys := ((isNormallyFlatAlongIdeal_tfae_of_eq_maximalIdeal J P Q hJP rfl).out 1 2).mp hflat
  obtain ⟨m, f, hf, h₁, h₂⟩ := hsys
  obtain ⟨N, x, Zs, hqr, hxQ, hxP⟩ :=
    exists_adapted_quasiRegular P Q hPQ inferInstance inferInstance
  set Y := Ideal.span (x '' ↑Zsᶜ) with hY
  have hQPY : Q = P ⊔ Y := by
    rw [← hxQ, ← hxP, hY, ← Ideal.span_union, ← Set.image_union, Finset.coe_compl,
      Set.union_compl_self, Set.image_univ]
  have hind : ∀ (m : ℕ) (s : Finset ℕ), (∀ a ∈ s, a ≤ m) → ∀ u : ℕ → S,
      (∀ a ∈ s, u a ∈ P ^ a * Y ^ (m - a)) → ∑ a ∈ s, u a ∈ Q ^ (m + 1) →
      ∀ a ∈ s, u a ∈ Q * (P ^ a * Y ^ (m - a)) := by
    intro m s hs u hu hsum
    rw [← hxP, ← hxQ] at *
    exact mem_mul_of_sum_mem_pow x hqr Zs m s hs u hu hsum
  have hQtop : Q ≠ ⊤ := Ideal.IsPrime.ne_top'
  set νf : Fin m → ℕ := fun β => (Ideal.ordElem Q (f β)).toNat with hνf
  have hfP : ∀ β, f β ∈ P ^ νf β := by
    intro β
    by_cases h : Ideal.ordElem Q (f β) = ⊤
    · exact Ideal.ordElem_eq_top_iff.mp (h₁ β ▸ h) _
    · rw [h₁ β] at h
      simp only [νf, h₁ β]
      exact Ideal.mem_pow_of_ordElem (ENat.natCast_toNat h).symm
  have hSB := exists_coeff_of_span_initialForm Q J f h₂
  exact ⟨m, f, νf, hf, hfP, fun ν n g hgJ hgP hg =>
    mem_sum_sup_pow_succ_of_mem_inf P Y Q J hQPY hQtop hind f νf hf hfP hSB ν n hgJ hgP hg,
    fun μ g hgJ hgQ => by
      obtain ⟨c, hc1, -, hc3⟩ := hSB μ g hgJ hgQ
      exact ⟨c, hc1, hc3⟩⟩

/-- Corollary 1 of Theorem 2 for `R_Q` (p. 201): "Applying Corollary 1 of Theorem 2, §2, to
`{R_Q, JR_Q, PR_Q, O_Q = R_Q/JR_Q}`, we get a system of elements `h_j` of `JR_Q` such that
`ν_{PR_Q}(h_j) = ν_{QR_Q}(h_j)` for all `j` and the initial forms of `h_j` in `gr_{QR_Q}(R_Q)`
generate the ideal `gr_{QR_Q}(JR_Q, R_Q)`." -/
private theorem hasInitialFormSystem_localization [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (R : Type u)
    [CommRing R] [IsRegularLocalRing R] (J P Q : Ideal R)
    [P.IsPrime] [Q.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)]
    (hJP : J ≤ P) (hPQ : P ≤ Q) [hQ' : (Q.map (Ideal.Quotient.mk J)).IsPrime]
    (hflat : IsNormallyFlatAlongIdeal ((P.map (Ideal.Quotient.mk J)).map
      (algebraMap (R ⧸ J) (Localization.AtPrime (Q.map (Ideal.Quotient.mk J)))))) :
    HasInitialFormSystem (J.map (algebraMap R (Localization.AtPrime Q)))
      (P.map (algebraMap R (Localization.AtPrime Q)))
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) := by
  classical
  set S := Localization.AtPrime Q with hS
  have : IsRegularLocalRing S := isRegularLocalRing_localization_of_isRegularLocalRing R Q
  set Jq : Ideal S := J.map (algebraMap R S) with hJq
  set Pq : Ideal S := P.map (algebraMap R S) with hPq
  have hdisj : Disjoint (Q.primeCompl : Set R) (P : Set R) :=
    Set.disjoint_left.mpr fun a ha haP => ha (hPQ haP)
  have hPqprime : Pq.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl S P
    ‹_› hdisj
  -- `S/Pq` is regular
  have : IsRegularLocalRing (S ⧸ Pq) := by
    have : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hPQ
    obtain ⟨e, -⟩ := exists_ringEquiv_quotient_localization Q P hPQ S
    have : IsRegularLocalRing (Localization.AtPrime (Q.map (Ideal.Quotient.mk P))) :=
      isRegularLocalRing_localization_of_isRegularLocalRing (R ⧸ P) _
    exact IsRegularLocalRing.of_ringEquiv e.symm
  -- transport the flatness hypothesis to `S/Jq`
  obtain ⟨e2, he2⟩ := exists_ringEquiv_quotient_localization Q J (hJP.trans hPQ) S
  have hflat' : IsNormallyFlatAlongIdeal (Pq.map (Ideal.Quotient.mk Jq)) := by
    refine isNormallyFlatAlongIdeal_of_ringEquiv e2.symm _ _ ?_ hflat
    rw [Ideal.map_map, Ideal.map_map, Ideal.map_map]
    congr 1
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [← he2 a]
    simp only [RingEquiv.symm_apply_apply]
    rfl
  let _ : Field (S ⧸ IsLocalRing.maximalIdeal S) := Ideal.Quotient.field _
  exact ((isNormallyFlatAlongIdeal_tfae_of_eq_maximalIdeal Jq Pq (IsLocalRing.maximalIdeal S)
    (Ideal.map_mono hJP) rfl).out 1 2).mp hflat'

/-- `(P ⊔ Y)ⁿ ⊆ Yⁿ ⊔ P`. -/
private theorem sup_pow_le_pow_sup {A : Type*} [CommRing A] (P Y : Ideal A) (n : ℕ) :
    (P ⊔ Y) ^ n ≤ Y ^ n ⊔ P := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (P ⊔ Y) ^ (n + 1) = (P ⊔ Y) ^ n * (P ⊔ Y) := pow_succ _ _
      _ ≤ (Y ^ n ⊔ P) * (P ⊔ Y) := Ideal.mul_mono_left ih
      _ ≤ Y ^ (n + 1) ⊔ P := by
        rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
        refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
        · exact (Ideal.mul_le_right : Y ^ n * P ≤ P).trans le_sup_right
        · rw [pow_succ]
          exact le_sup_left
        · exact (Ideal.mul_le_left : P * P ≤ P).trans le_sup_right
        · exact (Ideal.mul_le_left : P * Y ≤ P).trans le_sup_right

/-- An arbitrary minimal base `ȳ₁, …, ȳ_s` of `Q/P` in `R/P`, together with a minimal base of `P`,
forms a quasi-regular family generating `Q`: the `ȳ_j` are part of a minimal system of
generators of the maximal ideal of `R/P`, since a minimal system `S_b` of generators of the
maximal ideal of `R/P` containing a minimal base `T_b` of `Q/P` stays a system of generators when
`T_b` is replaced by `ȳ` (both generate `Q/P`), and `s ≤ #T_b`. -/
private theorem exists_isQuasiRegular_sumElim_of_span_eq_map {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P ≤ Q)
    (hP : IsRegularLocalRing (R ⧸ P)) (hQ : IsRegularLocalRing (R ⧸ Q)) {s : ℕ} (y : Fin s → R)
    (hy : Ideal.span (Set.range fun i => Ideal.Quotient.mk P (y i)) = Q.map (Ideal.Quotient.mk P))
    (hs : s = (Q.map (Ideal.Quotient.mk P)).spanFinrank) :
    ∃ (t : ℕ) (z : Fin t → R), IsQuasiRegular (Sum.elim y z) ∧
      Ideal.span (Set.range (Sum.elim y z)) = Q ∧ Ideal.span (Set.range z) = P := by
  classical
  obtain ⟨S₀, T, hS₀, hS₀card, hTS₀, hT⟩ := exists_finset_span_eq_prime R P hP
  set mk := Ideal.Quotient.mk P with hmk
  have := hP
  have hQb : (Q.map mk).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hPQ)
  have hQreg : IsRegularLocalRing ((R ⧸ P) ⧸ Q.map mk) := by
    have := hQ
    exact IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ).symm
  obtain ⟨Sb, Tb, hSb, hSbcard, hTbSb, hTb⟩ :=
    exists_finset_span_eq_prime (R ⧸ P) (Q.map mk) hQreg
  set σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := P)) with hσdef
  have hσ : ∀ b, mk (σ b) = b := Function.surjInv_eq _
  have hMbar : (IsLocalRing.maximalIdeal R).map mk = IsLocalRing.maximalIdeal (R ⧸ P) :=
    IsLocalRing.map_maximalIdeal_of_surjective mk Ideal.Quotient.mk_surjective
  have hPM : P ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top'
  have hQM : Q ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top'
  -- `s ≤ #Tb`
  have hsTb : s ≤ Tb.card := by
    rw [hs, ← hTb]
    calc _ ≤ ((Tb : Set (R ⧸ P))).ncard := Submodule.spanFinrank_span_le_ncard_of_finite
          (Finset.finite_toSet _)
      _ = Tb.card := Set.ncard_coe_finset _
  have hymem : ∀ i, mk (y i) ∈ Q.map mk := fun i => hy ▸ Ideal.subset_span ⟨i, rfl⟩
  have hyQ : ∀ i, y i ∈ Q := fun i => (Ideal.mem_quotient_iff_mem hPQ).mp (hymem i)
  -- a proper generating set of `Q/P` has at least `s` elements
  have hmin : ∀ V : Finset (R ⧸ P), Ideal.span (V : Set (R ⧸ P)) = Q.map mk → s ≤ V.card := by
    intro V hV
    rw [hs, ← hV]
    calc _ ≤ ((V : Set (R ⧸ P))).ncard := Submodule.spanFinrank_span_le_ncard_of_finite
          (Finset.finite_toSet _)
      _ = V.card := Set.ncard_coe_finset _
  -- no `ȳ_j` lies in the span of the others
  have hred : ∀ j, mk (y j) ∈ Ideal.span
      ((((Finset.univ.erase j).image fun k => mk (y k) : Finset (R ⧸ P))) : Set (R ⧸ P)) →
      False := by
    intro j hj
    set V : Finset (R ⧸ P) := (Finset.univ.erase j).image fun k => mk (y k) with hV
    have hVspan : Ideal.span (V : Set (R ⧸ P)) = Q.map mk := by
      apply le_antisymm
      · rw [Ideal.span_le]
        intro b hb
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hb
        exact hymem k
      · rw [← hy, Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        by_cases hkj : k = j
        · subst hkj; exact hj
        · exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ _⟩)))
    have h1 := hmin V hVspan
    have h2 : V.card ≤ s - 1 := by
      calc V.card ≤ (Finset.univ.erase j).card := Finset.card_image_le
        _ = s - 1 := by simp
    have : 0 < s := Fin.pos j
    omega
  have hybar : Function.Injective fun i => mk (y i) := by
    intro i j hij
    by_contra hne
    refine hred j ?_
    have hij' : mk (y i) = mk (y j) := hij
    rw [← hij']
    exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)))
  have hy0 : ∀ i, mk (y i) ≠ 0 := by
    intro i hi0
    refine hred i ?_
    rw [hi0]
    exact zero_mem _
  -- the system `S' = T ∪ σ(Sb \ Tb) ∪ {y_j}` of generators of the maximal ideal of `R`
  set L1 := (Sb \ Tb).image σ with hL1
  set Yf := (Finset.univ : Finset (Fin s)).image y with hYf
  set S' := T ∪ L1 ∪ Yf with hS'
  have hSbM : ∀ b ∈ Sb, σ b ∈ IsLocalRing.maximalIdeal R := by
    intro b hb
    have : mk (σ b) ∈ IsLocalRing.maximalIdeal (R ⧸ P) := by
      rw [hσ, ← hSb]
      exact Ideal.subset_span hb
    by_contra hn
    exact (IsLocalRing.mem_maximalIdeal _).mp this
      ((IsLocalRing.notMem_maximalIdeal.mp hn).map mk)
  have hS'span : Ideal.span (S' : Set R) = IsLocalRing.maximalIdeal R := by
    apply le_antisymm
    · rw [Ideal.span_le]
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · rcases Finset.mem_union.mp ha with ha | ha
        · exact hPM (hT ▸ Ideal.subset_span ha)
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
          exact hSbM b (Finset.mem_sdiff.mp hb).1
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
        exact hQM (hyQ i)
    · intro a ha
      have h1 : mk a ∈ (Ideal.span ((L1 ∪ Yf : Finset R) : Set R)).map mk := by
        rw [Ideal.map_span]
        have : mk a ∈ IsLocalRing.maximalIdeal (R ⧸ P) := by
          rw [← hMbar]; exact Ideal.mem_map_of_mem _ ha
        rw [← hSb] at this
        refine (Ideal.span_le.mpr ?_) this
        intro b hb
        by_cases hbT : b ∈ Tb
        · have : b ∈ Q.map mk := hTb ▸ Ideal.subset_span hbT
          rw [← hy] at this
          refine (Ideal.span_le.mpr ?_) this
          rintro _ ⟨i, rfl⟩
          exact Ideal.subset_span ⟨y i, Finset.mem_coe.mpr (Finset.mem_union_right _
            (Finset.mem_image_of_mem _ (Finset.mem_univ i))), rfl⟩
        · exact Ideal.subset_span ⟨σ b, Finset.mem_coe.mpr (Finset.mem_union_left _
            (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨hb, hbT⟩))), hσ b⟩
      rw [Ideal.mem_quotient_iff_mem_sup] at h1
      refine (sup_le (Ideal.span_mono ?_) ?_ :
        Ideal.span ((L1 ∪ Yf : Finset R) : Set R) ⊔ P ≤ Ideal.span (S' : Set R)) h1
      · rw [hS', Finset.coe_union, Finset.coe_union, Finset.coe_union]
        intro x hx
        simp only [Set.mem_union, Finset.mem_coe] at hx ⊢
        tauto
      · rw [← hT]
        refine Ideal.span_mono fun x hx => ?_
        simp only [hS', Finset.coe_union, Finset.mem_coe, Set.mem_union] at hx ⊢
        tauto
  -- the images of `S₀ \ T` generate `M/P`
  have hMbar' : Ideal.span (((S₀ \ T).image mk : Finset (R ⧸ P)) : Set (R ⧸ P)) =
      IsLocalRing.maximalIdeal (R ⧸ P) := by
    rw [← hMbar, ← hS₀, Ideal.map_span]
    apply le_antisymm
    · refine Ideal.span_mono ?_
      rw [Finset.coe_image]
      exact Set.image_mono (by simp)
    · rw [Ideal.span_le]
      rintro _ ⟨y, hy, rfl⟩
      by_cases hyT : y ∈ T
      · have : mk y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hT ▸ Ideal.subset_span hyT)
        rw [this]
        exact zero_mem _
      · exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _
          (Finset.mem_sdiff.mpr ⟨hy, hyT⟩)))
  have hcardSb : Sb.card ≤ S₀.card - T.card := by
    rw [hSbcard, ← hMbar']
    calc _ ≤ (((S₀ \ T).image mk : Finset _) : Set (R ⧸ P)).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)
      _ = ((S₀ \ T).image mk).card := Set.ncard_coe_finset _
      _ ≤ (S₀ \ T).card := Finset.card_image_le
      _ = S₀.card - T.card := Finset.card_sdiff_of_subset hTS₀
  have hS'card : S'.card = (IsLocalRing.maximalIdeal R).spanFinrank := by
    apply le_antisymm
    · have h1 : S'.card ≤ T.card + L1.card + Yf.card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      have h2 : L1.card ≤ Sb.card - Tb.card :=
        Finset.card_image_le.trans (Finset.card_sdiff_of_subset hTbSb).le
      have h3 : Yf.card ≤ s := by simpa using Finset.card_image_le (s := Finset.univ) (f := y)
      have h4 : Tb.card ≤ Sb.card := Finset.card_le_card hTbSb
      have h5 : T.card ≤ S₀.card := Finset.card_le_card hTS₀
      omega
    · rw [← hS'span, ← Set.ncard_coe_finset]
      exact Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)
  -- the family
  set t := T.card with ht
  let zT : Fin t → R := fun i => (T.equivFin.symm i : R)
  have hzTinj : Function.Injective zT := Subtype.val_injective.comp T.equivFin.symm.injective
  have hzTrange : Set.range zT = (T : Set R) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (T.equivFin.symm i).2
    · intro ha
      exact ⟨T.equivFin ⟨a, ha⟩, by simp [zT]⟩
  have hyinj : Function.Injective y := fun i j h => hybar (by simp only [h])
  have hinj : Function.Injective (Sum.elim y zT) := by
    refine Function.Injective.sumElim hyinj hzTinj fun i j h => hy0 i ?_
    have hT' : y i ∈ T := by rw [h]; exact (T.equivFin.symm j).2
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hT ▸ Ideal.subset_span hT')
  have hzS : ∀ i, Sum.elim y zT i ∈ S' := by
    rintro (i | i)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (T.equivFin.symm i).2)
  refine ⟨t, zT, ?_, ?_, ?_⟩
  · refine IsQuasiRegular.of_comp_equiv (finSumFinEquiv (m := s) (n := t)).symm ?_
    exact isQuasiRegular_of_minimal hS'span hS'card
      (hinj.comp (finSumFinEquiv (m := s) (n := t)).symm.injective) fun i => hzS _
  · rw [Set.Sum.elim_range, Ideal.span_union, hzTrange, hT]
    apply le_antisymm
    · exact sup_le (Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hyQ i)) hPQ
    · intro a ha
      have h1 : mk a ∈ (Ideal.span (Set.range y)).map mk := by
        rw [Ideal.map_span, ← Set.range_comp]
        have : mk a ∈ Q.map mk := Ideal.mem_map_of_mem _ ha
        rw [← hy] at this
        exact this
      rw [Ideal.mem_quotient_iff_mem_sup] at h1
      exact h1
  · rw [hzTrange, hT]

/-- p. 199: the `λ`-image of the initial form of `g` in `gr_Q(gr_P(R))`, for the isomorphism
`λ : gr_Q(gr_P(R)) → gr_Q(R)` determined by `(y_1, …, y_s)` (here `Y = (y_1, …, y_s)R`).

The paper builds `λ` as the composite of the canonical isomorphism
`gr⁰_{Q'}(gr_P(R)) ⊗_{R/Q} gr_{Q/P}(R/P) → gr_Q(gr_P(R))` with an isomorphism
`gr⁰_{Q'}(gr_P(R)) ⊗_{R/Q} gr_{Q/P}(R/P) → gr_Q(R)` sending the class of `ȳ_j` to that of `y_j`.
This predicate spells out the value of `λ` (`lambdaPiece`) on the initial form of an element `g ∈ R`.  With
`ν = ν_P(g)`, `n = ν_{Q/P}(Φ)` (`Φ` the initial form of `g` in `gr_P(R)`, so that `Φ_*` is the
initial form of `g` in `gr_Q(gr_P(R))`, `doubleInitialForm`), `Φ = Σ_{|m|=n} ȳ^m ⊗ [a_m]` with
`a_m ∈ Pᵛ` (`g ≡ Σ y^m a_m mod Pᵛ⁺¹`) and `λ(Φ_*)` is the class of `Σ y^m a_m` in
`Qᵛ⁺ⁿ/Qᵛ⁺ⁿ⁺¹`.  So `z` is "the `λ`-image of the initial form of `g`" iff it is the class in
`Qᵛ⁺ⁿ/Qᵛ⁺ⁿ⁺¹` of some `h ∈ Yⁿ Pᵛ` with `g - h ∈ Pᵛ⁺¹`.  (Such `h` exist, and the class does not
depend on the choice, by the independence of the bidegree components, which is what makes `λ` a
map; this is `ofGrPiece_lambdaPiece_eq_mk`.) -/
def IsLambdaImage {R : Type u} [CommRing R] (P Q Y : Ideal R) (g : R) (ν n : ℕ)
    (z : AssocGraded Q) : Prop :=
  Ideal.ordElem P g = ν ∧ doubleOrd P Q (initialForm P g) = n ∧
    ∃ h ∈ Y ^ n * P ^ ν, g - h ∈ P ^ (ν + 1) ∧
      ∃ hQ : h ∈ Q ^ (ν + n), z = AssocGraded.mk Q (ν + n) h hQ

end Theorem3

/-! ### Minimal bases of `Q/P` (p. 193) -/

section MinimalBase

variable {R : Type u} [CommRing R] (P Q : Ideal R)

/-- If the classes of `y` in `R/P` generate `Q/P` and `P ≤ Q`, then `Q = P + (y)`. -/
theorem eq_sup_span_of_span_map_eq (hPQ : P ≤ Q) {s : ℕ} (y : Fin s → R)
    (hy : Ideal.span (Set.range fun i => Ideal.Quotient.mk P (y i)) =
      Q.map (Ideal.Quotient.mk P)) :
    Q = P ⊔ Ideal.span (Set.range y) := by
  apply le_antisymm
  · intro a ha
    have h1 : Ideal.Quotient.mk P a ∈ (Ideal.span (Set.range y)).map (Ideal.Quotient.mk P) := by
      rw [Ideal.map_span, ← Set.range_comp]
      have : Ideal.Quotient.mk P a ∈ Q.map (Ideal.Quotient.mk P) := Ideal.mem_map_of_mem _ ha
      rw [← hy] at this
      exact this
    rw [Ideal.mem_quotient_iff_mem_sup] at h1
    rwa [sup_comm]
  · refine sup_le hPQ (Ideal.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    have : Ideal.Quotient.mk P (y i) ∈ Q.map (Ideal.Quotient.mk P) :=
      hy ▸ Ideal.subset_span ⟨i, rfl⟩
    exact (Ideal.mem_quotient_iff_mem hPQ).mp this

/-- The classes `ȳ_j` of a minimal base of `Q/P` in `R/P` (`span {ȳ_j} = Q/P` and
`s = spanFinrank (Q/P)`) are quasi-regular in `R/P`.  This is
`exists_isQuasiRegular_sumElim_of_span_eq_map` for the regular local ring `R/P` and its prime
ideal `(0)`: the family `(ȳ, z)` is quasi-regular with `z` spanning `(0)`, so `z = 0` and `ȳ`
alone is quasi-regular. -/
theorem isQuasiRegular_mk_of_span_eq_map_of_spanFinrank [IsRegularLocalRing R] [P.IsPrime]
    [Q.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)]
    (hPQ : P ≤ Q) {s : ℕ} (y : Fin s → R)
    (hy : Ideal.span (Set.range fun i => Ideal.Quotient.mk P (y i)) =
      Q.map (Ideal.Quotient.mk P))
    (hs : s = (Q.map (Ideal.Quotient.mk P)).spanFinrank) :
    IsQuasiRegular fun i => Ideal.Quotient.mk P (y i) := by
  classical
  have hQb : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hPQ)
  have : IsDomain (R ⧸ P) := isDomain_of_isRegularLocalRing _
  have : (⊥ : Ideal (R ⧸ P)).IsPrime := inferInstance
  have : IsRegularLocalRing ((R ⧸ P) ⧸ (⊥ : Ideal (R ⧸ P))) :=
    IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot (R ⧸ P)).symm
  have : IsRegularLocalRing ((R ⧸ P) ⧸ Q.map (Ideal.Quotient.mk P)) :=
    IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ).symm
  have hbot : ((RingEquiv.quotientBot (R ⧸ P)).symm : R ⧸ P →+* (R ⧸ P) ⧸ (⊥ : Ideal (R ⧸ P))) =
      Ideal.Quotient.mk ⊥ := RingHom.ext fun _ => rfl
  have hy' : Ideal.span (Set.range fun i => Ideal.Quotient.mk (⊥ : Ideal (R ⧸ P))
      (Ideal.Quotient.mk P (y i))) =
        (Q.map (Ideal.Quotient.mk P)).map (Ideal.Quotient.mk ⊥) := by
    rw [← hy, Ideal.map_span, ← Set.range_comp]
    rfl
  have hs' : s = ((Q.map (Ideal.Quotient.mk P)).map
      (Ideal.Quotient.mk (⊥ : Ideal (R ⧸ P)))).spanFinrank := by
    rw [hs, ← hbot]
    exact (Ideal.spanFinrank_map_eq_of_ringEquiv (RingEquiv.quotientBot (R ⧸ P)).symm _).symm
  obtain ⟨t, z, hq, hspan, hz⟩ := exists_isQuasiRegular_sumElim_of_span_eq_map
    (R := R ⧸ P) ⊥ (Q.map (Ideal.Quotient.mk P)) bot_le inferInstance inferInstance
    (fun i => Ideal.Quotient.mk P (y i)) hy' hs'
  have hz0 : ∀ i, z i = 0 := fun i => Ideal.span_eq_bot.mp hz _ ⟨i, rfl⟩
  have hI : Ideal.span (Set.range (Sum.elim (fun i => Ideal.Quotient.mk P (y i)) z)) =
      Ideal.span (Set.range fun i => Ideal.Quotient.mk P (y i)) := by
    rw [Set.Sum.elim_range, Ideal.span_union, hz, sup_bot_eq]
  intro d F hF hFx m
  have hF' := hF.rename_isHomogeneous (f := (Sum.inl : Fin s → Fin s ⊕ Fin t))
  have heval : MvPolynomial.eval (Sum.elim (fun i => Ideal.Quotient.mk P (y i)) z)
      (MvPolynomial.rename Sum.inl F) =
        MvPolynomial.eval (fun i => Ideal.Quotient.mk P (y i)) F := by
    rw [MvPolynomial.eval_rename]
    rfl
  have h := hq d _ hF' (by rw [heval, hI]; exact hFx) (m.mapDomain Sum.inl)
  rwa [MvPolynomial.coeff_rename_mapDomain _ Sum.inl_injective, hI] at h

/-- A minimal base of `Q/P` in `R/P` lifts to a family `y` of `R`. -/
theorem exists_span_eq_map_and_eq_spanFinrank [IsRegularLocalRing R] [P.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] :
    ∃ (s : ℕ) (y : Fin s → R),
      Ideal.span (Set.range fun i => Ideal.Quotient.mk P (y i)) = Q.map (Ideal.Quotient.mk P) ∧
        s = (Q.map (Ideal.Quotient.mk P)).spanFinrank := by
  classical
  have hfg : (Q.map (Ideal.Quotient.mk P)).FG := IsNoetherian.noetherian _
  obtain ⟨V, hcard, hV⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  let z : Fin V.card → R ⧸ P := fun i => (V.equivFin.symm i : R ⧸ P)
  have hrange : Set.range z = (V : Set (R ⧸ P)) := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact (V.equivFin.symm i).2
    · intro hw
      exact ⟨V.equivFin ⟨w, hw⟩, by simp [z]⟩
  refine ⟨V.card, fun i => Function.surjInv Ideal.Quotient.mk_surjective (z i), ?_, hcard⟩
  have hyz : (fun i => Ideal.Quotient.mk P
      (Function.surjInv Ideal.Quotient.mk_surjective (z i))) = z :=
    funext fun i => Function.surjInv_eq _ _
  rw [hyz, hrange]
  exact hV

end MinimalBase

section Lemma8PaperForm

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (J P Q : Ideal R) [P.IsPrime]
  [Q.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)]

/-- Lemma 8, p. 194, in the paper's form: "Notation and assumptions being as above,
`ψ' : gr⁰_{Q̄}(gr_{P̄}(O)) ⊗_{O/Q̄} gr_{Q̄/P̄}(O/P̄) → gr_{Q̄}(O)` is an isomorphism of graded
`O/Q̄ (= Ō/Q̄')`-algebras if and only if there exists a system of elements `(f₁, …, f_m)` of `J`
such that (1) `ν_Q(f_j) = ν_P(f_j)` for `1 ≤ j ≤ m`, and (2) if `φ_j` denotes the initial form of
`f_j` in `gr_Q(R)`, then `gr_Q(J, R) = (φ₁, …, φ_m) gr_Q(R)`", where `ψ'` is the map of p. 193
for "a system of elements `(y₁, …, y_s)` in `R` such that the residue classes `(ȳ₁, …, ȳ_s)` of
them in `Ō` form a minimal base of `Q̄'` (`s = dim Ō_{Q̄'}`)".

Encoding: the classes `ȳ_j` form a minimal base of `Q/P ⊆ R/P` (which is `Q̄'` under
`Ō = O/P̄ = R/P`) when they generate `Q/P` (`hy`) and `s` is the minimal number of generators of
`Q/P` (`hs`; for the regular local ring `(R/P)_{Q/P}` this is its dimension).  "`ψ'` is an
isomorphism" means bijective in each total degree (`psiDeg`).

Deviation from the paper (gap filled): the construction of `ψ'` uses, without saying so, that
`Q = P + (y)` and that the `ȳ_j` are quasi-regular in `R/P` (part of a regular system of
parameters of `R/P`; cf. the paper's p. 183, "`ȳ` a part of a regular system of parameters").
Both are proved here for every minimal base (`eq_sup_span_of_span_map_eq`,
`isQuasiRegular_mk_of_span_eq_map_of_spanFinrank`: a minimal system of generators of the maximal
ideal of `R/P` containing a minimal base of `Q/P` stays a system of generators when the minimal
base is replaced by `ȳ`) and the lemma is then proved for such a `y` by the printed argument
(`Lemma8.bijective_psiDeg_iff_hasInitialFormSystem`, `Hironaka/Ch2/Lemma8Diagram.lean`).

The printed proof (pp. 193–194), step by step: "Here the two vertical sequences are exact by
Lemma 5, and by the right exactness of tensor product. Moreover, it is easily seen that `ψ` is
isomorphic and that `ψ'` is surjective. Therefore, it follows from the diagram that `ψ'` is
isomorphic if and only if `ψ''` is surjective" (`Lemma8.bijective_iff_surjective_of_exact_columns`
for the diagram in each total degree; `Lemma8.mapJR_mapRO_exact`, `Lemma8.exact_subtype_grPieceMapQuot`;
`ψ` is bijective by Proposition 1 (1), `ψ'` is surjective by Proposition 1);
"As is easily seen, the image of `ψ''` is a graded ideal in `gr_Q(R)` which is generated by the image
of `gr_P(J, R)` by `γ`" (`Lemma8.psiDoublePrimeImage_eq_map_gammaMap`), "Therefore, `ψ'` is
isomorphic if and only if the image of `gr_P(J, R)` by `γ` in `gr_Q(R)` generates the ideal
`gr_Q(J, R)`" (`Lemma8.surjective_psiDoublePrime_iff_eq_map_gammaMap`); "Let `f` be any element of
`J`. Let `ν = ν_P(f)` and `μ = ν_Q(f)`. It is clear that `ν ≤ μ`. If `ν < μ`, then the initial form
`Φ` of `f` in `gr_P(R)` is such that `deg Φ = ν` and `Φ ∈ Q^{μ-ν} gr_P(R)`" (`Lemma8.initialForm_mem_map_pow`,
the assertion without argument, proved from the transversality `Lemma8.inf_pow_le_mixedPow`); "The
image of `Φ` in `gr⁰_Q(gr_P(R))` is then zero, hence, `γ(Φ) = 0`" (`Lemma8.gammaMap_eq_zero_of_mem_map`,
`Lemma8.gammaMap_initialForm_eq_zero`); "If `ν = μ`, then the image `γ(Φ)` of `Φ` is equal to the
initial form of `f` in `gr_Q(R)`" (`Lemma8.gammaMap_initialForm_eq`). -/
@[blueprint "lem:II.2-8"
  (statement := /-- Notation and assumptions being as above (\cref{thm:II.2-2}), let
    $(y_1,\dots,y_s)$ be a system of elements in $R$ such that the residue classes
    $(\bar y_1,\dots,\bar y_s)$ of them in $\bar O$ form a minimal base of $\bar Q'$. Then
    $\psi'\colon\operatorname{gr}^0_{\bar Q}(\operatorname{gr}_{\bar P}(O))\otimes_{O/\bar Q}
    \operatorname{gr}_{\bar Q/\bar P}(O/\bar P)\to\operatorname{gr}_{\bar Q}(O)$ is an
    isomorphism of graded $O/\bar Q$ ($=\bar O/\bar Q'$)-algebras if and only if there exists a
    system of elements $(f_1,\dots,f_m)$ of $J$ such that (1) $\nu_Q(f_j)=\nu_P(f_j)$ for
    $1\le j\le m$, and (2) if $\varphi_j$ denotes the initial form of $f_j$ in
    $\operatorname{gr}_Q(R)$, then $\operatorname{gr}_Q(J,R)=(\varphi_1,\dots,\varphi_m)
    \operatorname{gr}_Q(R)$ (\cref{def:II.2-initial-form-system}). (Lemma 8, p.~194.)

    \textbf{Formalization note (encoding).} ``Minimal base of $\bar Q'$'' is encoded as: the
    $\bar y_j$ generate $Q/P$ and $s$ is the minimal number of generators of $Q/P$ (the
    dimension of the regular local ring $(R/P)_{Q/P}$); $\psi'$ is $\psi$ of
    \cref{prop:II.1-1-psi} for $O$, $\bar P$, $\bar Q$ and the classes of the $y_j$,
    ``isomorphism'' meaning bijective in each total degree. -/)
  (proof := /-- (The paper's proof, pp.~193--194, for the map $\psi'$ of p.~193 defined by the
    system $(y_1,\dots,y_s)$.) The diagram of homomorphisms of $\bar O/\bar Q$-algebras
    \[\begin{array}{ccc}
    \operatorname{gr}^0_Q(\operatorname{gr}_P(J,R))\otimes\operatorname{gr}_{\bar Q}(\bar O)
      &\xrightarrow{\psi''}&\operatorname{gr}_Q(J,R)\\
    \downarrow&&\downarrow\\
    \operatorname{gr}^0_Q(\operatorname{gr}_P(R))\otimes\operatorname{gr}_{\bar Q}(\bar O)
      &\xrightarrow{\psi}&\operatorname{gr}_Q(R)\\
    \downarrow&&\downarrow\\
    \operatorname{gr}^0_Q(\operatorname{gr}_{\bar P}(O))\otimes\operatorname{gr}_{\bar Q}(\bar O)
      &\xrightarrow{\psi'}&\operatorname{gr}_{\bar Q}(O)
    \end{array}\]
    has exact vertical sequences by Lemma 5 and by the right exactness of the tensor product;
    moreover $\psi$ is isomorphic and $\psi'$ is surjective. Therefore $\psi'$ is isomorphic if
    and only if $\psi''$ is surjective. Let $\gamma\colon\operatorname{gr}_P(R)\to
    \operatorname{gr}_Q(R)$ be the canonical homomorphism (induced by the inclusions
    $P^\nu\subseteq Q^\nu$). The image of $\psi''$ is a graded ideal in $\operatorname{gr}_Q(R)$
    generated by the image of $\operatorname{gr}_P(J,R)$ by $\gamma$. Therefore $\psi'$ is
    isomorphic if and only if the image of $\operatorname{gr}_P(J,R)$ by $\gamma$ generates
    $\operatorname{gr}_Q(J,R)$. For $f\in J$ let $\nu=\nu_P(f)$ and $\mu=\nu_Q(f)$; then $\nu\le\mu$.
    If $\nu<\mu$, the initial form $\Phi$ of $f$ in $\operatorname{gr}_P(R)$ satisfies
    $\gamma(\Phi)=0$; if $\nu=\mu$, then $\gamma(\Phi)$ is the initial form of $f$ in
    $\operatorname{gr}_Q(R)$. Thus the lemma is verified.

    \textbf{Gap filled.} (1) ``It is easily seen that $\psi$ is isomorphic'' is Proposition 1 (1)
    for $R$, $P$, $Q$ ($\operatorname{gr}_P(R)$ is flat over $R/P$ since $R/P$ is regular), and
    ``$\psi'$ is surjective'' is the surjectivity part of Proposition 1. (2) ``As is easily
    seen, the image of $\psi''$ is a graded ideal \dots generated by the image of
    $\operatorname{gr}_P(J,R)$ by $\gamma$'' is proved as one statement: the image of $\psi''$
    (the sum of its homogeneous components) is the ideal generated by
    $\gamma(\operatorname{gr}_P(J,R))$; it consists of sums of products $\alpha(u)\beta^*(z)$ with
    $u\in\operatorname{gr}_P(J,R)$, and it is stable under multiplication by
    $\operatorname{gr}_Q(R)=\operatorname{im}\psi$. (3) ``$\Phi\in Q^{\mu-\nu}\operatorname{gr}_P(R)$''
    is asserted without argument; it is $P^\nu\cap Q^{\nu+k}\subseteq Q^kP^\nu+P^{\nu+1}$, a
    consequence of the transversality $P^a\cap Q^N\subseteq\sum_pP^{\max(p,a)}(y)^{N-p}$ of the
    $P$-adic and $Q$-adic filtrations, proved by descent on $a$ and Krull's intersection theorem
    (the argument of p.~185) from the quasi-regularity of $\bar y$ on the free $R/P$-module
    $\operatorname{gr}^a_P(R)$. (4) The finiteness of the system $(f_1,\dots,f_m)$ follows from the
    noetherianity of $\operatorname{gr}_Q(R)$.

    \textbf{Deviation from the paper (gap filled).} That a minimal base of $\bar Q'$ satisfies
    $Q=P+(y)$ with the $\bar y_j$ quasi-regular in $R/P$ (part of a regular system of
    parameters) is not stated in the paper. In Lean: a minimal system of generators of the
    maximal ideal of $R/P$ containing a minimal base of $Q/P$ remains a system of generators of
    the same cardinality when the minimal base is replaced by $\bar y$ (the argument of
    \cref{lem:II.3-10}, applied to the regular local ring $R/P$ and its prime ideal $(0)$). -/)
  (latexEnv := "lemma")]
theorem bijective_psiDeg_iff_hasInitialFormSystem_of_span_eq_map (hJP : J ≤ P) (hPQ : P ≤ Q)
    {s : ℕ} (y : Fin s → R)
    (hy : Ideal.span (Set.range fun i => Ideal.Quotient.mk P (y i)) =
      Q.map (Ideal.Quotient.mk P))
    (hs : s = (Q.map (Ideal.Quotient.mk P)).spanFinrank) :
    (∀ n, Function.Bijective (psiDeg (P.map (Ideal.Quotient.mk J)) (Q.map (Ideal.Quotient.mk J))
      (Ideal.map_mono hPQ) (fun j => Ideal.Quotient.mk J (y j))
      (isQuasiRegular_map_quotient J P y hJP
        (isQuasiRegular_mk_of_span_eq_map_of_spanFinrank P Q hPQ y hy hs))
      (span_map_mk_eq_map_quotient J P Q y (eq_sup_span_of_span_map_eq P Q hPQ y hy)) n)) ↔
        HasInitialFormSystem J P Q :=
  Lemma8.bijective_psiDeg_iff_hasInitialFormSystem J P Q y hJP hPQ
    (eq_sup_span_of_span_map_eq P Q hPQ y hy)
    (isQuasiRegular_mk_of_span_eq_map_of_spanFinrank P Q hPQ y hy hs)

local notation "𝒪" => R ⧸ J
local notation "P̄" => Ideal.map (Ideal.Quotient.mk J) P
local notation "Q̄" => Ideal.map (Ideal.Quotient.mk J) Q
local notation "Ō" => 𝒪 ⧸ P̄
local notation "Q̄'" => Ideal.map (Ideal.Quotient.mk P̄) Q̄

/-- Theorem 2, p. 195, with condition (ii), in the paper's form (see
`isNormallyFlatAlongIdeal_tfae_psiDeg` for the quoted statement and the encoding of (i), (iii),
(iv)): `ψ'` in (ii) is the homomorphism of p. 193 for a system `(y₁, …, y_s)` in `R` whose
residue classes in `Ō` form a minimal base of `Q̄'` (`hy`, `hs` as in Lemma 8,
`bijective_psiDeg_iff_hasInitialFormSystem_of_span_eq_map`), for every such system.  Since
`Q̄'` is finitely generated, such systems exist (`exists_span_eq_map_and_eq_spanFinrank`).

Deviation from the paper (gap filled): as for Lemma 8, that `Q = P + (y)` with the `ȳ_j`
quasi-regular in `R/P` holds for every minimal base is proved
(`isQuasiRegular_mk_of_span_eq_map_of_spanFinrank`); the paper takes it for granted.

The proof follows the paper (pp. 195–196), with no alternative proof left: (i) ⟹ (ii) is Proposition 1
of §1, (ii) ⟺ (iii) is Lemma 8, (iv) ⟹ (i) is the corollary to Lemma 2 of §1, and (ii) + (iii) ⟹ (iv) is
`flat_and_bijective_grModMap_of_bijective_psiDeg`, which follows the printed text: the isomorphism `ψ'`
in total degree `n` exhibits the summands `gr⁰_{Q̄}(gr^p_{P̄}(O)) ⊗ gr^q_{Q̄/P̄}(O/P̄)` of
`grⁿ_{Q̄}(O)`, `p + q = n`, as direct summands of a free module, hence free by Lemma 1 of §1
(`free_psiSummand_of_bijective_psiDeg`), whence the flatness of `gr⁰_{Q̄}(gr_{P̄}(O))`; and `φ` is
the direct sum of its components `φ_{pq}` of double grade `(p, q)`, each bijective by the doubly graded
diagram of p. 196 and Lemma 7 (`bijective_grModMap_grPiece_of_hasInitialFormSystem`,
`GrModPiece.exact_map_of_inf_le`, `injective_grModMap_of_exact`, `bijective_grModMap_assocGraded`).
Tacit steps filled in: the choice of the summand `q = 0` in
"Therefore `gr⁰_{Q̄}(gr_{P̄}(O))` is flat", the passage from the pieces `gr^p_{P̄}(O)` to the whole
algebra `gr_{P̄}(O)` and from `gr⁰` for `Q̄` over `O/Q̄` to `gr⁰` for `Q̄'` over `Ō/Q̄'`, and the use of
Lemma 7 for the homogeneous parts.

Encoding: the graded algebras are read degreewise ("isomorphic" for the graded homomorphism `ψ'` is
bijectivity in each total degree; for `φ` bijectivity in each double degree, equivalent to `φ` being
bijective since `φ` is the direct sum of the `φ_{pq}`); in (ii) the homomorphism `ψ'` is the one of
a system `(y₁, …, y_s)`, for every such system (they exist), the quantification over all systems being
the paper's "the above homomorphism" for any choice. -/
@[blueprint "thm:II.2-2-psi"
  (statement := /-- Let $R$ be a regular local ring and $J$ an ideal in $R$. Let $P$ and $Q$
    be prime ideals in $R$ such that $Q\supseteq P\supseteq J$ and that $R/P$ and $R/Q$ are
    both regular. Let $O=R/J$, $\bar Q=Q/J$, and $\bar P=P/J$. Then the following conditions
    are equivalent to each other:
    (i) $\operatorname{gr}_{\bar P}(O)$ is flat over $O/\bar P$
    (\cref{def:normally-flat-ideal}).
    (ii) $\operatorname{gr}_{\bar Q}(O)$ is flat over $O/\bar Q$ and the above homomorphism
    $\psi'$ of graded $O/\bar Q$-algebras (defined by a system $(y_1,\dots,y_s)$ in $R$ whose
    residue classes in $\bar O$ form a minimal base of $\bar Q'$) is isomorphic.
    (iii) $\operatorname{gr}_{\bar Q}(O)$ is flat over $O/\bar Q$, and there exists a system of
    elements $(f_1,\dots,f_m)$ of $J$ with $\nu_Q(f_j)=\nu_P(f_j)$ whose initial forms generate
    $\operatorname{gr}_Q(J,R)$ (\cref{def:II.2-initial-form-system}).
    (iv) $\operatorname{gr}^0_{\bar Q}(\operatorname{gr}_{\bar P}(O))$ is flat over $O/\bar Q$,
    and the canonical homomorphism $\varphi$ is isomorphic. (Theorem 2, p.~195.)

    \textbf{Formalization note (encoding).} As in \cref{lem:II.2-8}; in (ii), $\psi'$ is
    isomorphic for every system $(y_j)$ whose classes form a minimal base of $\bar Q'$ (such
    systems exist); (iii) and (iv) are encoded as in the statement of \cref{thm:II.2-2}. -/)
  (proof := /-- By Proposition 1 of \S1 (\cref{prop:II.1-1-psi}), (i)$\Rightarrow$(ii). By
    \cref{lem:II.2-8}, (ii)$\Leftrightarrow$(iii). By the corollary to Lemma 2 of \S1,
    (iv)$\Rightarrow$(i). Thus it suffices to prove that (ii) and (iii) together imply (iv).
    First of all, the isomorphism $\psi'$ of (ii) induces isomorphisms of $O/\bar Q$-modules
    $\bigoplus_{p+q=n}\operatorname{gr}^0_{\bar Q}(\operatorname{gr}^p_{\bar P}(O))\otimes
    \operatorname{gr}^q_{\bar Q/\bar P}(O/\bar P)\to\operatorname{gr}^n_{\bar Q}(O)$ for all
    non-negative integers $n$. By the assumption that $\operatorname{gr}_{\bar Q}(O)$ is flat over
    $O/\bar Q$, $\operatorname{gr}^n_{\bar Q}(O)$ must be a free $O/\bar Q$-module, and hence the
    direct summands $\operatorname{gr}^0_{\bar Q}(\operatorname{gr}^p_{\bar P}(O))\otimes
    \operatorname{gr}^q_{\bar Q/\bar P}(O/\bar P)$ are such also (Lemma 1 of \S1: a direct
    summand of a free module of finite type over a local ring is free). Note that
    $\operatorname{gr}^q_{\bar Q/\bar P}(O/\bar P)$ are free $O/\bar Q$-modules. Therefore
    $\operatorname{gr}^0_{\bar Q}(\operatorname{gr}_{\bar P}(O))$ is flat over $O/\bar Q$.
    We want to prove that $\varphi$ is an isomorphism. We have the commutative diagram of
    canonical homomorphisms of doubly graded $O/\bar Q$-algebras with the left column
    $\operatorname{gr}^0_{\bar Q}(\operatorname{gr}_P(J,R))\otimes G\to
    \operatorname{gr}^0_{\bar Q}(\operatorname{gr}_P(R))\otimes G\to
    \operatorname{gr}^0_{\bar Q}(\operatorname{gr}_{\bar P}(O))\otimes G\to0$ exact by the right
    exactness of the tensor product, the rows given by $\varphi$ for $L_q=\operatorname{gr}^q_P(J,R)$,
    $X_q=\operatorname{gr}^q_P(R)$, $N_q=\operatorname{gr}^q_{\bar P}(O)$, and the columns
    $0\to\bar Q^{p+1}M\to\bar Q^pM\to\operatorname{gr}^p_{\bar Q}(M)\to0$. The homomorphism
    $\varphi_{X_q}$ is an isomorphism since $X_q$ is free over $R/P$ (Lemma 2 of \S1), and
    $\varphi_{L_q}$, $\varphi_{N_q}$ and the arrow $\varepsilon$ onto $\operatorname{gr}^p_{\bar Q}(N_q)$
    are surjective. It is easy to see that if the right vertical sequence is proved exact, then
    $\varphi$ is an isomorphism; in order to prove $\operatorname{Ker}(\varepsilon)=
    \operatorname{Im}(\delta)$ it suffices that $\operatorname{Ker}(\varepsilon')=
    \operatorname{Im}(\delta')$, and by virtue of Lemma 7 (condition (iii)), $\operatorname{Ker}
    (\varepsilon')=\bar Q^pX_q\cap L_q=\bar Q^pL_q=\operatorname{Im}(\delta')$. $\varphi$ is the direct
    sum of the $\varphi_{pq}$ (the corollary to Lemma 2 of \S1). The version for systems with
    $Q=P+(y)$ and quasi-regular $\bar y_j$ is \cref{thm:II.2-2-quasi-regular}.

    \textbf{Deviation from the paper (gap filled).} ``Therefore
    $\operatorname{gr}^0_{\bar Q}(\operatorname{gr}_{\bar P}(O))$ is flat'': the choice of the
    summand $q=0$ (where $\operatorname{gr}^0_{\bar Q/\bar P}(O/\bar P)=O/\bar Q$), the passage from
    the pieces $\operatorname{gr}^p_{\bar P}(O)$ to $\operatorname{gr}_{\bar P}(O)=\bigoplus_p
    \operatorname{gr}^p_{\bar P}(O)$, and from $\operatorname{gr}^0$ for $\bar Q$ over $O/\bar Q$
    to $\operatorname{gr}^0$ for $\bar Q'$ over $\bar O/\bar Q'\cong O/\bar Q$, are tacit in the
    paper and proved; so is the use of Lemma 7 for the homogeneous parts $\bar Q^n
    \operatorname{gr}^q_P(R)\cap\operatorname{gr}^q_P(J,R)=\bar Q^n\operatorname{gr}^q_P(J,R)$.

    \textbf{Deviation from the paper (gap filled).} See \cref{lem:II.2-8}: a minimal base of
    $\bar Q'$ satisfies $Q=P+(y)$ with the $\bar y_j$ quasi-regular in $R/P$. -/)
  (latexEnv := "theorem")]
theorem isNormallyFlatAlongIdeal_tfae_psiDeg_of_span_eq_map (hJP : J ≤ P) (hPQ : P ≤ Q) :
    [IsNormallyFlatAlongIdeal P̄,
      IsNormallyFlatAlongIdeal Q̄ ∧ ∀ (s : ℕ) (y : Fin s → R)
        (hy : Ideal.span (Set.range fun i => Ideal.Quotient.mk P (y i)) =
          Q.map (Ideal.Quotient.mk P))
        (hs : s = (Q.map (Ideal.Quotient.mk P)).spanFinrank) (n : ℕ),
        Function.Bijective (psiDeg P̄ Q̄ (Ideal.map_mono hPQ) (fun j => Ideal.Quotient.mk J (y j))
          (isQuasiRegular_map_quotient J P y hJP
            (isQuasiRegular_mk_of_span_eq_map_of_spanFinrank P Q hPQ y hy hs))
          (span_map_mk_eq_map_quotient J P Q y (eq_sup_span_of_span_map_eq P Q hPQ y hy)) n),
      IsNormallyFlatAlongIdeal Q̄ ∧ HasInitialFormSystem J P Q,
      Module.Flat (Ō ⧸ Q̄') (GrModPiece Q̄' (AssocGraded P̄) 0) ∧
        ∀ m : ℕ, Function.Bijective (grModMap Q̄' (AssocGraded P̄) m)].TFAE := by
  have h := isNormallyFlatAlongIdeal_tfae_psiDeg J P Q hJP hPQ
  have h12 := h.out 1 2
  have h41 := h.out 4 1
  tfae_have 1 → 2 := fun h₁ => ⟨(h12.mp h₁).1, fun s y hy hs n =>
    (h12.mp h₁).2 s y (eq_sup_span_of_span_map_eq P Q hPQ y hy)
      (isQuasiRegular_mk_of_span_eq_map_of_spanFinrank P Q hPQ y hy hs) n⟩
  tfae_have 2 → 3 := fun h₂ => by
    obtain ⟨s, y, hy, hs⟩ := exists_span_eq_map_and_eq_spanFinrank P Q
    exact ⟨h₂.1,
      (bijective_psiDeg_iff_hasInitialFormSystem_of_span_eq_map J P Q hJP hPQ y hy hs).mp
        (h₂.2 s y hy hs)⟩
  tfae_have 3 → 2 := fun h₃ => ⟨h₃.1, fun s y hy hs n =>
    (bijective_psiDeg_iff_hasInitialFormSystem_of_span_eq_map J P Q hJP hPQ y hy hs).mpr h₃.2 n⟩
  -- (ii) and (iii) together imply (iv): the paper's argument through `ψ'`
  tfae_have 2 → 4 := fun h₂ => by
    obtain ⟨s, y, hy, hs⟩ := exists_span_eq_map_and_eq_spanFinrank P Q
    have hbij := h₂.2 s y hy hs
    exact flat_and_bijective_grModMap_of_bijective_psiDeg J P Q hJP hPQ h₂.1 y
      (eq_sup_span_of_span_map_eq P Q hPQ y hy)
      (isQuasiRegular_mk_of_span_eq_map_of_spanFinrank P Q hPQ y hy hs) hbij
      ((bijective_psiDeg_iff_hasInitialFormSystem_of_span_eq_map J P Q hJP hPQ y hy hs).mp hbij)
  tfae_have 4 → 1 := h41.mp
  tfae_finish

/-- Corollary 1 of Theorem 2 (pp. 196–197) with condition (ii), in the paper's form: the
statement of `isNormallyFlatAlongIdeal_tfae_psiDeg_of_eq_maximalIdeal` with `ψ'` in (ii) the
homomorphism of p. 193 for every system `(y₁, …, y_s)` in `R` whose residue classes in `Ō` form
a minimal base of `Q̄'` (`hy`, `hs` as in Lemma 8).

Deviation from the paper (gap filled): as for Lemma 8 and Theorem 2 (`isQuasiRegular_mk_of_span_eq_map_of_spanFinrank`).
The proof is the paper's ("The assertion follows Theorem 2 because every module is flat over a
field"): the flatness clauses of (iii) and (iv) hold automatically over the field `O/Q̄ = R/Q`
(`Module.Free.of_divisionRing`), and the rest is the proof of Theorem 2
(`isNormallyFlatAlongIdeal_tfae_psiDeg_of_eq_maximalIdeal`,
`flat_and_bijective_grModMap_of_bijective_psiDeg`); no alternative proof is left (the printed route
for (ii) + (iii) ⟹ (iv) is that of Theorem 2). -/
@[blueprint "cor:II.2-thm2-1-psi"
  (statement := /-- The notation and assumptions being as in \cref{thm:II.2-2-psi}, assume that
    $Q$ is the maximal ideal of $R$. Then the following conditions are equivalent to each
    other: (i) $\operatorname{gr}_{\bar P}(O)$ is flat over $O/\bar P$. (ii) The homomorphism
    $\psi'$ of graded $O/\bar Q$-algebras (defined by a system $(y_j)$ in $R$ whose classes in
    $\bar O$ form a minimal base of $\bar Q'$) is isomorphic (\cref{lem:II.2-8}). (iii) There
    exists a system of elements $(f_1,\dots,f_m)$ of $J$ with $\nu_Q(f_j)=\nu_P(f_j)$ whose
    initial forms generate $\operatorname{gr}_Q(J,R)$ (\cref{def:II.2-initial-form-system}).
    (iv) The canonical homomorphism $\varphi$ is isomorphic. (Corollary 1, pp.~196--197.)

    \textbf{Formalization note (encoding).} As in \cref{thm:II.2-2-psi}. -/)
  (proof := /-- The assertion follows \cref{thm:II.2-2-psi} because every module is flat over a
    field: $O/\bar Q=R/Q$ is a field, so the flatness conditions in (ii), (iii) and (iv) of
    \cref{thm:II.2-2-psi} hold automatically. The version for systems with $Q=P+(y)$ and
    quasi-regular $\bar y_j$ is \cref{cor:II.2-thm2-1-quasi-regular}.

    \textbf{Deviation from the paper (gap filled).} See \cref{lem:II.2-8}. -/)
  (latexEnv := "corollary")]
theorem isNormallyFlatAlongIdeal_tfae_psiDeg_of_eq_maximalIdeal_of_span_eq_map (hJP : J ≤ P)
    (hQ : Q = IsLocalRing.maximalIdeal R) :
    [IsNormallyFlatAlongIdeal P̄,
      ∀ (s : ℕ) (y : Fin s → R)
        (hy : Ideal.span (Set.range fun i => Ideal.Quotient.mk P (y i)) =
          Q.map (Ideal.Quotient.mk P))
        (hs : s = (Q.map (Ideal.Quotient.mk P)).spanFinrank) (n : ℕ),
        Function.Bijective (psiDeg P̄ Q̄
          (Ideal.map_mono (hQ ▸ IsLocalRing.le_maximalIdeal_of_isPrime P))
          (fun j => Ideal.Quotient.mk J (y j))
          (isQuasiRegular_map_quotient J P y hJP (isQuasiRegular_mk_of_span_eq_map_of_spanFinrank
            P Q (hQ ▸ IsLocalRing.le_maximalIdeal_of_isPrime P) y hy hs))
          (span_map_mk_eq_map_quotient J P Q y
            (eq_sup_span_of_span_map_eq P Q (hQ ▸ IsLocalRing.le_maximalIdeal_of_isPrime P) y hy))
          n),
      HasInitialFormSystem J P Q,
      ∀ m : ℕ, Function.Bijective (grModMap Q̄' (AssocGraded P̄) m)].TFAE := by
  have hPQ : P ≤ Q := hQ ▸ IsLocalRing.le_maximalIdeal_of_isPrime P
  have h := isNormallyFlatAlongIdeal_tfae_psiDeg_of_eq_maximalIdeal J P Q hJP hQ
  have h12 := h.out 1 2
  have h41 := h.out 4 1
  tfae_have 1 → 2 := fun h₁ s y hy hs n => (h12.mp h₁) s y
    (eq_sup_span_of_span_map_eq P Q hPQ y hy)
    (isQuasiRegular_mk_of_span_eq_map_of_spanFinrank P Q hPQ y hy hs) n
  tfae_have 2 → 3 := fun h₂ => by
    obtain ⟨s, y, hy, hs⟩ := exists_span_eq_map_and_eq_spanFinrank P Q
    exact (bijective_psiDeg_iff_hasInitialFormSystem_of_span_eq_map J P Q hJP hPQ y hy hs).mp
      (h₂ s y hy hs)
  tfae_have 3 → 2 := fun h₃ s y hy hs n =>
    (bijective_psiDeg_iff_hasInitialFormSystem_of_span_eq_map J P Q hJP hPQ y hy hs).mpr h₃ n
  -- (ii) and (iii) together imply (iv): the paper's argument through `ψ'`
  tfae_have 2 → 4 := fun h₂ => by
    obtain ⟨s, y, hy, hs⟩ := exists_span_eq_map_and_eq_spanFinrank P Q
    have hbij := h₂ s y hy hs
    have hQmax : Q.IsMaximal := hQ ▸ IsLocalRing.maximalIdeal.isMaximal R
    have hQbar : (Q̄).IsMaximal := isMaximal_map_quotientMk_of_le (hJP.trans hPQ)
    have hfree : IsNormallyFlatAlongIdeal Q̄ := fun p => by
      let _ : Field (𝒪 ⧸ Q̄) := Ideal.Quotient.field _
      exact Module.Free.of_divisionRing _ _
    exact (flat_and_bijective_grModMap_of_bijective_psiDeg J P Q hJP hPQ hfree y
      (eq_sup_span_of_span_map_eq P Q hPQ y hy)
      (isQuasiRegular_mk_of_span_eq_map_of_spanFinrank P Q hPQ y hy hs) hbij
      ((bijective_psiDeg_iff_hasInitialFormSystem_of_span_eq_map J P Q hJP hPQ y hy hs).mp
        hbij)).2
  tfae_have 4 → 1 := h41.mp
  tfae_finish

end Lemma8PaperForm

section Lemma10Lambda

variable {R : Type u} [CommRing R] (P Q : Ideal R) (hPQ : P ≤ Q) {s : ℕ} (y : Fin s → R)
  (hqr : IsQuasiRegular fun j => Ideal.Quotient.mk P (y j))
  (hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) = Q.map (Ideal.Quotient.mk P))

include hPQ hqr hz in
/-- The additive pairing `([a], [b]) ↦ α[a] · β*[b]` of `grᵖ_P(R) × grⁿ_{Q/P}(R/P)` into
`gr^{p+n}_Q(R)`: `α` is induced by `Pᵖ ⊆ Qᵖ` and `β*` sends the class of `ȳ^α` to that of `y^α`
(the map `β*` of p. 199, in degree `n`). -/
noncomputable def lamBilin (p n : ℕ) :
    GrPiece P p →+ GrPiece (Q.map (Ideal.Quotient.mk P)) n →+ GrPiece Q (p + n) :=
  AddMonoidHom.mk'
    (fun x => ((GrPiece.mulPiece Q p n (grPieceInclusion P Q hPQ p x)).comp
      ((betaStarPiece P Q hPQ y hqr hz n).restrictScalars R)).toAddMonoidHom)
    (fun x x' => by
      ext b
      simp)

include hPQ hqr hz in
theorem lamBilin_apply (p n : ℕ) (x : GrPiece P p) (b : GrPiece (Q.map (Ideal.Quotient.mk P)) n) :
    lamBilin P Q hPQ y hqr hz p n x b =
      GrPiece.mulPiece Q p n (grPieceInclusion P Q hPQ p x)
        (betaStarPiece P Q hPQ y hqr hz n b) := rfl

include hPQ hqr hz in
theorem lamBilin_balanced (p n : ℕ) (r : R ⧸ P) (x : GrPiece P p)
    (b : GrPiece (Q.map (Ideal.Quotient.mk P)) n) :
    lamBilin P Q hPQ y hqr hz p n (r • x) b = lamBilin P Q hPQ y hqr hz p n x (r • b) := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
  have h1 : (Ideal.Quotient.mk P c) • x = c • x := algebraMap_smul (R ⧸ P) c x
  have h2 : (Ideal.Quotient.mk P c) • b = (Ideal.Quotient.mk Q c) • b := rfl
  have h3 : (Ideal.Quotient.mk Q c) • (betaStarPiece P Q hPQ y hqr hz n b) =
      c • (betaStarPiece P Q hPQ y hqr hz n b) :=
    algebraMap_smul (R ⧸ Q) c _
  rw [h1, h2, lamBilin_apply, lamBilin_apply, map_smul (grPieceInclusion P Q hPQ p) c x,
    map_smul (betaStarPiece P Q hPQ y hqr hz n) (Ideal.Quotient.mk Q c) b, h3,
    map_smul (GrPiece.mulPiece Q p n) c, LinearMap.smul_apply,
    map_smul (GrPiece.mulPiece Q p n (grPieceInclusion P Q hPQ p x)) c]

include hPQ hqr hz in
/-- The additive map `λ'` of p. 199 on `gr^p_P(R) ⊗_{R/P} gr^n_{Q/P}(R/P)`: `[a] ⊗ [b] ↦
α[a] · β*[b]`, the degree `(p, n)` component of the `λ'` of the paper (before composing with
the inverse of the canonical isomorphism `Λ`). -/
noncomputable def lamTensor (p n : ℕ) :
    GrPiece P p ⊗[R ⧸ P] GrPiece (Q.map (Ideal.Quotient.mk P)) n →+ GrPiece Q (p + n) :=
  TensorProduct.liftAddHom (lamBilin P Q hPQ y hqr hz p n)
    (fun r x b => lamBilin_balanced P Q hPQ y hqr hz p n r x b)

include hPQ hqr hz in
theorem lamTensor_tmul (p n : ℕ) (x : GrPiece P p) (b : GrPiece (Q.map (Ideal.Quotient.mk P)) n) :
    lamTensor P Q hPQ y hqr hz p n (x ⊗ₜ[R ⧸ P] b) = lamBilin P Q hPQ y hqr hz p n x b := by
  simp [lamTensor]

include hPQ hqr hz in
theorem lamTensor_smul (p n : ℕ) (c : R)
    (w : GrPiece P p ⊗[R ⧸ P] GrPiece (Q.map (Ideal.Quotient.mk P)) n) :
    lamTensor P Q hPQ y hqr hz p n ((Ideal.Quotient.mk P c) • w) =
      c • lamTensor P Q hPQ y hqr hz p n w := by
  induction w using TensorProduct.inductionOn with
  | tmul x b =>
    have h1 : (Ideal.Quotient.mk P c) • x = c • x := algebraMap_smul (R ⧸ P) c x
    rw [TensorProduct.smul_tmul', lamTensor_tmul, lamTensor_tmul, lamBilin_apply, lamBilin_apply,
      h1, map_smul, map_smul, LinearMap.smul_apply]
  | add w w' hw hw' => rw [smul_add, map_add, map_add, smul_add, hw, hw']

include hPQ hqr hz in
/-- The map `λ` of p. 199 in double degree `(p, n)`: `gr^n_Q(gr^p_P(R)) → gr^{p+n}_Q(R)`, the
composite of the inverse of the canonical isomorphism `Λ = grModMap` (bijective when
`gr^p_P(R)` is flat over `R/P`) with `λ'`. -/
noncomputable def lambdaPiece (p n : ℕ)
    (hbij : Function.Bijective (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n)) :
    GrModPiece (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n →+ GrPiece Q (p + n) :=
  (lamTensor P Q hPQ y hqr hz p n).comp
    (AddEquiv.ofBijective (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n).toAddMonoidHom
      hbij).symm.toAddMonoidHom

include hPQ hqr hz in
theorem lambdaPiece_grModMap (p n : ℕ)
    (hbij : Function.Bijective (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n))
    (w : GrPiece P p ⊗[R ⧸ P] GrPiece (Q.map (Ideal.Quotient.mk P)) n) :
    lambdaPiece P Q hPQ y hqr hz p n hbij
      (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n w) =
      lamTensor P Q hPQ y hqr hz p n w := by
  unfold lambdaPiece
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
  exact congrArg (lamTensor P Q hPQ y hqr hz p n) (AddEquiv.symm_apply_apply
    (AddEquiv.ofBijective (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P p)
      n).toAddMonoidHom hbij) w)

include hPQ hqr hz in
theorem lambdaPiece_smul (p n : ℕ)
    (hbij : Function.Bijective (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n)) (c : R)
    (z : GrModPiece (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n) :
    lambdaPiece P Q hPQ y hqr hz p n hbij ((Ideal.Quotient.mk P c) • z) =
      c • lambdaPiece P Q hPQ y hqr hz p n hbij z := by
  obtain ⟨w, rfl⟩ := hbij.2 z
  rw [← map_smul, lambdaPiece_grModMap, lambdaPiece_grModMap, lamTensor_smul]

/-- Membership in a finite sum of ideals. -/
private theorem exists_eq_sum_of_mem_finset_sum {ι : Type*} (s : Finset ι)
    (I : ι → Ideal R) {g : R} (hg : g ∈ ∑ a ∈ s, I a) :
    ∃ u : ι → R, (∀ a ∈ s, u a ∈ I a) ∧ ∑ a ∈ s, u a = g := by
  classical
  induction s using Finset.induction_on generalizing g with
  | empty =>
    rw [Finset.sum_empty, Submodule.zero_eq_bot, Submodule.mem_bot] at hg
    exact ⟨0, by simp, by simp [hg]⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Submodule.add_eq_sup, Submodule.mem_sup] at hg
    obtain ⟨y, hy, z, hz, rfl⟩ := hg
    obtain ⟨u, hu, rfl⟩ := ih hz
    refine ⟨Function.update u a y, fun b hb => ?_, ?_⟩
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · simpa using hy
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hb ha)]
        exact hu b hb
    · rw [Finset.sum_insert ha, Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun b hb =>
        Function.update_of_ne (ne_of_mem_of_not_mem hb ha) _ _

section Link

private theorem quotientMk_sum {A M ι : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (N : Submodule A M) (S : Finset ι) (f : ι → M) :
    (Submodule.Quotient.mk (∑ i ∈ S, f i) : M ⧸ N) = ∑ i ∈ S, Submodule.Quotient.mk (f i) :=
  map_sum N.mkQ f S

include hPQ hqr hz in
theorem lamBilin_basis (p q : ℕ) (b : R) (hb : b ∈ P ^ p) (α : ↥(degreeFinset s q))
    (h : b * (α.1.prod fun j e => y j ^ e) ∈ Q ^ (p + q)) :
    lamBilin P Q hPQ y hqr hz p q (Submodule.Quotient.mk ⟨b, hb⟩)
      (grPieceMapBasis P Q hPQ _ hqr hz (degreeFinset s) (fun _ _ => mem_degreeFinset) q α) =
      Submodule.Quotient.mk ⟨b * (α.1.prod fun j e => y j ^ e), h⟩ := by
  rw [lamBilin_apply]
  unfold betaStarPiece
  rw [Module.Basis.constr_basis, grPieceInclusion_mk]
  rfl

include hPQ hqr hz in
/-- The `λ`-image of the class of `[g]` in `grⁿ_Q(grᵛ_P(R))` is the class of any `h ∈ Yⁿ Pᵛ` with
`g - h ∈ Pᵛ⁺¹` (`Y = (y₁, …, y_s)`): `λ` sends the class of `ȳ_j` to that of `y_j`. -/
theorem ofGrPiece_lambdaPiece_eq_mk (ν n : ℕ)
    (hbij : Function.Bijective (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P ν) n))
    {g h : R} (hgP : g ∈ P ^ ν)
    (hΦ : (Submodule.Quotient.mk ⟨g, hgP⟩ : GrPiece P ν) ∈
      (Q.map (Ideal.Quotient.mk P)) ^ n • (⊤ : Submodule (R ⧸ P) (GrPiece P ν)))
    (hh : h ∈ Ideal.span (Set.range y) ^ n * P ^ ν) (hgh : g - h ∈ P ^ (ν + 1))
    (hhQ : h ∈ Q ^ (ν + n)) :
    AssocGraded.ofGrPiece Q (ν + n) (lambdaPiece P Q hPQ y hqr hz ν n hbij
      (Submodule.Quotient.mk ⟨Submodule.Quotient.mk ⟨g, hgP⟩, hΦ⟩)) =
      AssocGraded.mk Q (ν + n) h hhQ := by
  classical
  have hD : ∀ q α, α ∈ degreeFinset s q ↔ α.degree = q := fun _ _ => mem_degreeFinset
  obtain ⟨c, hc, hsum⟩ := exists_eq_sum_mono_of_mem y (degreeFinset s) hD (P ^ ν) n
    (by rwa [mul_comm] at hh)
  have hY : Ideal.span (Set.range y) ≤ Q := span_range_le_of_span_map_eq P Q hPQ y hz
  have hyα : ∀ α : ↥(degreeFinset s n), (α.1.prod fun j e => y j ^ e) ∈ Q ^ n := fun α =>
    prod_pow_mem_pow_of_span_le Q y hY n α.1 (mem_degreeFinset.mp α.2)
  have hcα : ∀ α : ↥(degreeFinset s n), c α.1 * (α.1.prod fun j e => y j ^ e) ∈ Q ^ (ν + n) :=
    fun α => by
      rw [pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_right_mono hPQ ν (hc α.1)) (hyα α)
  have hmkprod : ∀ α : ↥(degreeFinset s n), Ideal.Quotient.mk P (α.1.prod fun j e => y j ^ e) =
      α.1.prod fun j e => (Ideal.Quotient.mk P (y j)) ^ e := fun α => by
    simp
  have hQ'mem : ∀ α : ↥(degreeFinset s n),
      (α.1.prod fun j e => (Ideal.Quotient.mk P (y j)) ^ e) ∈
        (Q.map (Ideal.Quotient.mk P)) ^ n := fun α => by
    rw [← hmkprod α, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hyα α)
  have hbas : ∀ α : ↥(degreeFinset s n),
      grPieceMapBasis P Q hPQ _ hqr hz (degreeFinset s) (fun _ _ => mem_degreeFinset) n α =
        (Submodule.Quotient.mk ⟨_, hQ'mem α⟩ : GrPiece (Q.map (Ideal.Quotient.mk P)) n) :=
    fun α => grPieceMapBasis_apply P Q hPQ _ hqr hz (degreeFinset s) (fun _ _ => mem_degreeFinset)
      n α (hQ'mem α)
  let w : GrPiece P ν ⊗[R ⧸ P] GrPiece (Q.map (Ideal.Quotient.mk P)) n :=
    ∑ α : ↥(degreeFinset s n), (Submodule.Quotient.mk ⟨c α.1, hc α.1⟩ : GrPiece P ν) ⊗ₜ[R ⧸ P]
      (grPieceMapBasis P Q hPQ _ hqr hz (degreeFinset s) (fun _ _ => mem_degreeFinset) n α)
  have hh' : h = ∑ α : ↥(degreeFinset s n), c α.1 * (α.1.prod fun j e => y j ^ e) := by
    rw [hsum]
    exact (Finset.sum_coe_sort (degreeFinset s n)
      (fun α => c α * α.prod fun j e => y j ^ e)).symm
  -- `λ'(w)` is the class of `h`
  have hlam : lamTensor P Q hPQ y hqr hz ν n w =
      (Submodule.Quotient.mk ⟨h, hhQ⟩ : GrPiece Q (ν + n)) := by
    simp only [w, map_sum, lamTensor_tmul]
    rw [Finset.sum_congr rfl (fun α _ => lamBilin_basis P Q hPQ y hqr hz ν n _ _ α (hcα α)),
      ← quotientMk_sum (Submodule.comap (Q ^ (ν + n)).subtype (Q ^ (ν + n + 1))) Finset.univ
        (fun α : ↥(degreeFinset s n) =>
          (⟨c α.1 * (α.1.prod fun j e => y j ^ e), hcα α⟩ : ↥(Q ^ (ν + n))))]
    refine congrArg _ (Subtype.ext ?_)
    rw [Submodule.coe_sum]
    exact hh'.symm
  have hhP : h ∈ P ^ ν := by
    rw [hsum]
    exact Ideal.sum_mem _ fun α _ => Ideal.mul_mem_right _ _ (hc α)
  have hAw : grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P ν) n w =
      Submodule.Quotient.mk ⟨Submodule.Quotient.mk ⟨g, hgP⟩, hΦ⟩ := by
    simp only [w, map_sum]
    simp_rw [hbas, grModMap_tmul]
    rw [← quotientMk_sum (Submodule.comap ((Q.map (Ideal.Quotient.mk P)) ^ n • (⊤ :
      Submodule (R ⧸ P) (GrPiece P ν))).subtype ((Q.map (Ideal.Quotient.mk P)) ^ (n + 1) • ⊤))
      Finset.univ]
    refine congrArg _ (Subtype.ext ?_)
    rw [Submodule.coe_sum]
    have hterm : ∀ α : ↥(degreeFinset s n),
        ((α.1.prod fun j e => (Ideal.Quotient.mk P (y j)) ^ e) •
          (Submodule.Quotient.mk ⟨c α.1, hc α.1⟩ : GrPiece P ν)) =
          Submodule.Quotient.mk ⟨c α.1 * (α.1.prod fun j e => y j ^ e),
            Ideal.mul_mem_right _ _ (hc α.1)⟩ := fun α => by
      have h1 : (α.1.prod fun j e => (Ideal.Quotient.mk P (y j)) ^ e) =
          Ideal.Quotient.mk P (α.1.prod fun j e => y j ^ e) := (hmkprod α).symm
      have h2 : (Ideal.Quotient.mk P (α.1.prod fun j e => y j ^ e)) •
          (Submodule.Quotient.mk ⟨c α.1, hc α.1⟩ : GrPiece P ν) =
          (α.1.prod fun j e => y j ^ e) •
            (Submodule.Quotient.mk ⟨c α.1, hc α.1⟩ : GrPiece P ν) :=
        algebraMap_smul (R ⧸ P) _ _
      rw [h1, h2, ← Submodule.Quotient.mk_smul]
      exact congrArg _ (Subtype.ext (by simp [smul_eq_mul, mul_comm]))
    simp only [hterm]
    rw [← quotientMk_sum (Submodule.comap (P ^ ν).subtype (P ^ (ν + 1))) Finset.univ
      (fun α : ↥(degreeFinset s n) =>
        (⟨c α.1 * (α.1.prod fun j e => y j ^ e), Ideal.mul_mem_right _ _ (hc α.1)⟩ :
          ↥(P ^ ν)))]
    rw [Submodule.Quotient.eq]
    rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_sum]
    rw [← hh']
    have := (P ^ (ν + 1)).neg_mem hgh
    simpa using this
  rw [← hAw, lambdaPiece_grModMap, hlam, AssocGraded.ofGrPiece_mk]

end Link

end Lemma10Lambda

section Lemma10Paper

open TensorProduct

/-- The canonical homomorphism `Λ : gr⁰_Q(gr_P(R)) ⊗_{R/Q} gr_{Q/P}(R/P) → gr_Q(gr_P(R))` of
p. 198 is an isomorphism, in double degree `(p, n)`: `gr_P(R)` is flat over `R/P` since `R/P` is
regular (the corollary to Lemma 2 of §1). -/
theorem grModMap_bijective_of_isRegularLocalRing_quotient {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (P : Ideal R) [P.IsPrime] [IsRegularLocalRing (R ⧸ P)]
    (I : Ideal (R ⧸ P)) (p n : ℕ) : Function.Bijective (grModMap I (GrPiece P p) n) := by
  have : Module.Free (R ⧸ P) (GrPiece P p) :=
    isNormallyFlatAlongIdeal_of_isRegularLocalRing_quotient P p
  exact ⟨grModMap_injective_of_flat I _ n, grModMap_surjective I _ n⟩

/-- p. 199: the class `Φ_*` of a form `Φ = [g]` of `gr_P(R)` of degree `ν` lying in `Qⁿ gr_P(R)`
in `grⁿ_Q(gr_P(R)) = Qⁿ gr_P(R)/Qⁿ⁺¹ gr_P(R)`, a form of double grade `(ν, n)`.  (Formalization
note (encoding): `gr_Q(gr_P(R))` is read in double degree, as `grⁿ_{Q/P}` of the `R/P`-module
`grᵛ_P(R)`; for the project's `doubleInitialForm` see `mk_mem_pow_smul_top_of_doubleOrd`.) -/
noncomputable abbrev doubleInitialFormPiece {R : Type u} [CommRing R] (P Q : Ideal R)
    (ν n : ℕ) {g : R} (hgP : g ∈ P ^ ν)
    (hΦ : (Submodule.Quotient.mk ⟨g, hgP⟩ : GrPiece P ν) ∈
      (Q.map (Ideal.Quotient.mk P)) ^ n • (⊤ : Submodule (R ⧸ P) (GrPiece P ν))) :
    GrModPiece (Q.map (Ideal.Quotient.mk P)) (GrPiece P ν) n :=
  Submodule.Quotient.mk ⟨Submodule.Quotient.mk ⟨g, hgP⟩, hΦ⟩

/-- If `ν = ν_P(g)` and `n = ν_{Q/P}(Φ)` for the initial form `Φ` of `g` in `gr_P(R)`
(`doubleOrd`), then `[g] ∈ Qⁿ grᵛ_P(R)`, so that `Φ_*` (`doubleInitialFormPiece`) is defined. -/
theorem mk_mem_pow_smul_top_of_doubleOrd {R : Type u} [CommRing R] (P Q : Ideal R) {g : R}
    {ν n : ℕ} (hν : Ideal.ordElem P g = ν) (hn : doubleOrd P Q (initialForm P g) = n) :
    (Submodule.Quotient.mk ⟨g, Ideal.mem_pow_of_ordElem hν⟩ : GrPiece P ν) ∈
      (Q.map (Ideal.Quotient.mk P)) ^ n • (⊤ : Submodule (R ⧸ P) (GrPiece P ν)) := by
  have h1 : initialForm P g ∈ (Q.map (algebraMap R (AssocGraded P))) ^ n :=
    Ideal.mem_pow_of_ordElem hn
  have h1' : initialForm P g = AssocGraded.mk P ν g (Ideal.mem_pow_of_ordElem hν) :=
    initialForm_eq_mk P hν
  rw [h1'] at h1
  have h2 := grProj_mem_pow_smul_top P Q ν n h1
  rwa [grProj_mk_same] at h2

end Lemma10Paper

section Lemma10Iso

open scoped DirectSum

section Total

variable {R : Type u} [CommRing R] (P Q : Ideal R)

/-- The summands `gr^n_{Q/P}(gr^p_P(R))`, `p + n = N`, of the homogeneous part of total degree `N`
of `gr_Q(gr_P(R))` (the target of `φ`, the source of `λ`; p. 198--199). -/
abbrev DoubleSummand (N : ℕ) : {pq : ℕ × ℕ // pq.1 + pq.2 = N} → Type u := fun pq =>
  GrModPiece (Q.map (Ideal.Quotient.mk P)) (GrPiece P pq.1.1) pq.1.2

/-- The summands `gr^p_P(R) ⊗_{R/P} gr^n_{Q/P}(R/P)` (`= gr⁰_Q(gr^p_P(R)) ⊗_{R/Q} gr^n_{Q/P}(R/P)`),
`p + n = N`, of the source of `φ` in total degree `N`. -/
abbrev PhiSummand (N : ℕ) : {pq : ℕ × ℕ // pq.1 + pq.2 = N} → Type u := fun pq =>
  GrPiece P pq.1.1 ⊗[R ⧸ P] GrPiece (Q.map (Ideal.Quotient.mk P)) pq.1.2

/-- The canonical homomorphism `φ` of p. 198 in total degree `N`:
`⊕_{p+n=N} gr^p_P(R) ⊗_{R/P} gr^n_{Q/P}(R/P) → ⊕_{p+n=N} gr^n_{Q/P}(gr^p_P(R))`, the sum of its
double-degree components `grModMap`. -/
noncomputable def phiTotal (N : ℕ) :
    (⨁ pq, PhiSummand P Q N pq) →ₗ[R] ⨁ pq, DoubleSummand P Q N pq :=
  DirectSum.lmap fun pq =>
    (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P pq.1.1) pq.1.2).restrictScalars R

theorem phiTotal_lof (N : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = N}) (w : PhiSummand P Q N pq) :
    phiTotal P Q N (DirectSum.lof R _ (PhiSummand P Q N) pq w) =
      DirectSum.lof R _ (DoubleSummand P Q N) pq
        (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P pq.1.1) pq.1.2 w) := by
  simp [phiTotal]

/-- `φ` is bijective in total degree `N` if it is bijective in every double degree. -/
theorem bijective_phiTotal (hbij : ∀ p n, Function.Bijective
    (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n)) (N : ℕ) :
    Function.Bijective (phiTotal P Q N) :=
  ⟨(DirectSum.lmap_injective _).mpr fun _ => (hbij _ _).1,
    (DirectSum.lmap_surjective _).mpr fun _ => (hbij _ _).2⟩

variable (hPQ : P ≤ Q) {s : ℕ} (y : Fin s → R)
  (hqr : IsQuasiRegular fun j => Ideal.Quotient.mk P (y j))
  (hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) = Q.map (Ideal.Quotient.mk P))

/-- `lambdaPiece` as an `R`-linear map (`R` acting through `R/P` on the source and through `R/Q` on
the target; `lambdaPiece_smul`). -/
noncomputable def lambdaLin (p n : ℕ) (hbij : Function.Bijective
    (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n)) :
    GrModPiece (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n →ₗ[R] GrPiece Q (p + n) where
  toFun := lambdaPiece P Q hPQ y hqr hz p n hbij
  map_add' := map_add _
  map_smul' c z := by
    have h : c • z = (Ideal.Quotient.mk P c) • z := (algebraMap_smul (R ⧸ P) c z).symm
    simp only [RingHom.id_apply]
    rw [h, lambdaPiece_smul]

theorem lambdaLin_apply (p n : ℕ) (hbij : Function.Bijective
    (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n))
    (z : GrModPiece (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n) :
    lambdaLin P Q hPQ y hqr hz p n hbij z = lambdaPiece P Q hPQ y hqr hz p n hbij z := rfl

/-- The isomorphism `λ = ψ φ⁻¹` of p. 199 in total degree `N`:
`⊕_{p+n=N} gr^n_{Q/P}(gr^p_P(R)) → gr^N_Q(R)`, the sum of its double-degree components
`lambdaPiece` (which need the bijectivity of `φ`). -/
noncomputable def lambdaTotal (hbij : ∀ p n, Function.Bijective
    (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n)) (N : ℕ) :
    (⨁ pq, DoubleSummand P Q N pq) →ₗ[R] GrPiece Q N :=
  DirectSum.toModule R _ _ fun pq =>
    ((GrPiece.castDeg Q pq.2).restrictScalars R).comp
      (lambdaLin P Q hPQ y hqr hz pq.1.1 pq.1.2 (hbij _ _))

theorem lambdaTotal_of (hbij : ∀ p n, Function.Bijective
    (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n)) (N : ℕ)
    (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = N}) (z : DoubleSummand P Q N pq) :
    lambdaTotal P Q hPQ y hqr hz hbij N (DirectSum.lof R _ (DoubleSummand P Q N) pq z) =
      GrPiece.castDeg Q pq.2 (lambdaPiece P Q hPQ y hqr hz pq.1.1 pq.1.2 (hbij _ _) z) := by
  simp [lambdaTotal, lambdaLin_apply]

/-- `R ⊗ = R/P ⊗`: the identification of the source of `ψ̃` with that of `φ`. -/
noncomputable def eqTensor (N : ℕ) :
    (⨁ pq, Lemma8.SummandR P Q N pq) →ₗ[R] ⨁ pq, PhiSummand P Q N pq :=
  DirectSum.lmap fun pq => (Lemma8.tensorEquivOfSurjective (A := R) (B := R ⧸ P)
    Ideal.Quotient.mk_surjective (GrPiece P pq.1.1)
      (GrPiece (Q.map (Ideal.Quotient.mk P)) pq.1.2)).toLinearMap

theorem bijective_eqTensor (N : ℕ) : Function.Bijective (eqTensor P Q N) :=
  ⟨(DirectSum.lmap_injective _).mpr fun _ => LinearEquiv.injective _,
    (DirectSum.lmap_surjective _).mpr fun _ => LinearEquiv.surjective _⟩

/-- `λ φ = ψ` (p. 199: "By means of these two isomorphisms we get `λ`"), in total degree `N`,
with the tensor products over `R/P` of `φ` and over `R` of `ψ̃` identified. -/
theorem lambdaTotal_phiTotal_eqTensor (hbij : ∀ p n, Function.Bijective
    (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n)) (N : ℕ)
    (w : ⨁ pq, Lemma8.SummandR P Q N pq) :
    lambdaTotal P Q hPQ y hqr hz hbij N (phiTotal P Q N (eqTensor P Q N w)) =
      Lemma8.psiTildeR P Q hPQ y hqr hz N w := by
  have key : lambdaTotal P Q hPQ y hqr hz hbij N ∘ₗ (phiTotal P Q N ∘ₗ eqTensor P Q N) =
      Lemma8.psiTildeR P Q hPQ y hqr hz N := by
    refine DirectSum.linearMap_ext R fun pq => ?_
    refine TensorProduct.ext' fun x z => ?_
    have h1 : eqTensor P Q N (DirectSum.lof R _ (Lemma8.SummandR P Q N) pq (x ⊗ₜ[R] z)) =
        DirectSum.lof R _ (PhiSummand P Q N) pq (x ⊗ₜ[R ⧸ P] z) := by
      simp only [eqTensor, DirectSum.lmap_lof]
      rfl
    have h2 := Lemma8.psiTildeR_lof_tmul P Q hPQ y hqr hz N pq x z
    simp only [LinearMap.comp_apply]
    rw [h1, phiTotal_lof, lambdaTotal_of, lambdaPiece_grModMap, lamTensor_tmul, lamBilin_apply, h2]
    rfl
  exact LinearMap.congr_fun key w

theorem bijective_lambdaTotal_iff (hbij : ∀ p n, Function.Bijective
    (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P p) n)) (N : ℕ) :
    Function.Bijective (lambdaTotal P Q hPQ y hqr hz hbij N) ↔
      Function.Bijective (psiDeg P Q hPQ y hqr hz N) := by
  have hc : Function.Bijective (phiTotal P Q N ∘ₗ eqTensor P Q N) :=
    (bijective_phiTotal P Q hbij N).comp (bijective_eqTensor P Q N)
  rw [← Lemma8.bijective_psiTildeR_iff P Q hPQ y hqr hz N]
  have : ⇑(Lemma8.psiTildeR P Q hPQ y hqr hz N) =
      ⇑(lambdaTotal P Q hPQ y hqr hz hbij N) ∘ ⇑(phiTotal P Q N ∘ₗ eqTensor P Q N) :=
    funext fun w => (lambdaTotal_phiTotal_eqTensor P Q hPQ y hqr hz hbij N w).symm
  rw [this]
  exact ((Equiv.bijective_comp (Equiv.ofBijective _ hc) _).symm)

/-- `λ` is bijective in each total degree (p. 199: "an isomorphism of simply graded `R/Q`-algebras",
here in each total degree), for `R` regular local and `R/P`, `R/Q` regular: `φ` is bijective
(`grModMap_bijective_of_isRegularLocalRing_quotient`) and so is `ψ` (Proposition 1, p. 184,
`psiDeg_bijective_of_isNormallyFlatAlongIdeal`, as `gr_P(R)` is flat over `R/P`). -/
theorem bijective_lambdaTotal_of_isRegularLocalRing [IsRegularLocalRing R] [P.IsPrime] [Q.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)] (N : ℕ) :
    Function.Bijective (lambdaTotal P Q hPQ y hqr hz
      (fun p n => grModMap_bijective_of_isRegularLocalRing_quotient P _ p n) N) :=
  (bijective_lambdaTotal_iff P Q hPQ y hqr hz _ N).mpr
    (psiDeg_bijective_of_isNormallyFlatAlongIdeal P Q hPQ y hqr hz
      (isNormallyFlatAlongIdeal_of_isRegularLocalRing_quotient P)
      (eq_sup_span_of_span_map_eq P Q hPQ y hz) N)

/-- The isomorphism `λ : gr_Q(gr_P(R)) → gr_Q(R)` of p. 199, in total degree `N`. -/
noncomputable def lambdaEquiv [IsRegularLocalRing R] [P.IsPrime] [Q.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)] (N : ℕ) :
    (⨁ pq, DoubleSummand P Q N pq) ≃ₗ[R] GrPiece Q N :=
  LinearEquiv.ofBijective _ (bijective_lambdaTotal_of_isRegularLocalRing P Q hPQ y hqr hz N)

end Total

end Lemma10Iso

section Lemma10Flat

/-- `φ` is bijective in every double degree when `gr_P(A)` is flat over `A/P` (Lemma 2 of §1,
the corollary to it). -/
theorem grModMap_bijective_of_isNormallyFlatAlongIdeal {A : Type u} [CommRing A] (P : Ideal A)
    (hP : IsNormallyFlatAlongIdeal P) (I : Ideal (A ⧸ P)) (p n : ℕ) :
    Function.Bijective (grModMap I (GrPiece P p) n) := by
  have := hP p
  exact ⟨grModMap_injective_of_flat I _ n, grModMap_surjective I _ n⟩

end Lemma10Flat

section Lemma10Diagram

open Lemma8

variable {R : Type u} [CommRing R] (J P Q : Ideal R) (hJP : J ≤ P) (hPQ : P ≤ Q)

/-- The identification `Ō = R/P = O/P̄` (`O = R/J`, `P̄ = P/J`) as a ring homomorphism. -/
noncomputable abbrev thetaRing : R ⧸ P →+* (R ⧸ J) ⧸ P.map (Ideal.Quotient.mk J) :=
  (DoubleQuot.quotQuotEquivQuotOfLE hJP).symm

theorem thetaRing_mk (c : R) : thetaRing J P hJP (Ideal.Quotient.mk P c) =
    Ideal.Quotient.mk (P.map (Ideal.Quotient.mk J)) (Ideal.Quotient.mk J c) :=
  DoubleQuot.quotQuotEquivQuotOfLE_symm_mk _ _

/-- `gr^ν_P(R) → gr^ν_{P̄}(O)` (Lemma 5) as a map semilinear over `Ō = R/P = O/P̄`. -/
noncomputable def grPieceMapQuotSemi (ν : ℕ) :
    GrPiece P ν →ₛₗ[thetaRing J P hJP] GrPiece (P.map (Ideal.Quotient.mk J)) ν where
  toFun := grPieceMapQuot J P ν
  map_add' := map_add _
  map_smul' r x := by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [thetaRing_mk]
    have h1 : (Ideal.Quotient.mk P c) • x = c • x := algebraMap_smul (R ⧸ P) c x
    have h2 : (Ideal.Quotient.mk (P.map (Ideal.Quotient.mk J)) (Ideal.Quotient.mk J c)) •
        grPieceMapQuot J P ν x = c • grPieceMapQuot J P ν x := by
      exact algebraMap_smul ((R ⧸ J) ⧸ P.map (Ideal.Quotient.mk J)) c _
    rw [h1, map_smul, h2]

theorem grPieceMapQuotSemi_mk (ν : ℕ) (a : ↥(P ^ ν)) :
    grPieceMapQuotSemi J P hJP ν (Submodule.Quotient.mk a) = Submodule.Quotient.mk
      ⟨Ideal.Quotient.mk J a.1, by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ a.2⟩ := rfl

/-- A semilinear map carries `Iᵏ M` into `I'ᵏ N` if `τ(I) ⊆ I'`. -/
theorem semilinear_smul_top_le {A B M N : Type*} [CommRing A] [CommRing B] (τ : A →+* B)
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] (f : M →ₛₗ[τ] N) (I : Ideal A)
    (I' : Ideal B) (h : I.map τ ≤ I') (k : ℕ) {x : M} (hx : x ∈ I ^ k • (⊤ : Submodule A M)) :
    f x ∈ I' ^ k • (⊤ : Submodule B N) := by
  refine Submodule.smul_induction_on hx (fun a ha m _ => ?_) (fun u v hu hv => ?_)
  · rw [map_smulₛₗ]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    refine Ideal.pow_right_mono h k ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  · rw [map_add]
    exact add_mem hu hv

theorem grPieceMapQuotSemi_smul_top_le (ν k : ℕ) {x : GrPiece P ν}
    (hx : x ∈ (Q.map (Ideal.Quotient.mk P)) ^ k • (⊤ : Submodule (R ⧸ P) (GrPiece P ν))) :
    grPieceMapQuotSemi J P hJP ν x ∈
      ((Q.map (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk (P.map (Ideal.Quotient.mk J)))) ^ k •
        (⊤ : Submodule ((R ⧸ J) ⧸ P.map (Ideal.Quotient.mk J))
          (GrPiece (P.map (Ideal.Quotient.mk J)) ν)) :=
  semilinear_smul_top_le _ _ _ _ (le_of_eq (map_quotQuotEquivQuotOfLE_symm J P Q hJP)) k hx

/-- The map `β` of the right square: `gr^n_{Q/P}(gr^ν_P(R)) → gr^n_{Q̄/P̄}(gr^ν_{P̄}(O))` induced by
`gr_P(R) → gr_{P̄}(O)` (Lemma 5), semilinear over `Ō = R/P = O/P̄`. -/
noncomputable def betaDouble (ν n : ℕ) :
    GrModPiece (Q.map (Ideal.Quotient.mk P)) (GrPiece P ν) n →ₛₗ[thetaRing J P hJP]
      GrModPiece ((Q.map (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk (P.map (Ideal.Quotient.mk J))))
        (GrPiece (P.map (Ideal.Quotient.mk J)) ν) n :=
  Submodule.mapQ _ _
    ((grPieceMapQuotSemi J P hJP ν).restrict fun _ hx => grPieceMapQuotSemi_smul_top_le J P Q hJP ν n hx)
    (fun _ hx => grPieceMapQuotSemi_smul_top_le J P Q hJP ν (n + 1) hx)

theorem betaDouble_mk (ν n : ℕ) (v : GrPiece P ν)
    (hb : v ∈ (Q.map (Ideal.Quotient.mk P)) ^ n • (⊤ : Submodule (R ⧸ P) (GrPiece P ν)))
    (hb' : grPieceMapQuotSemi J P hJP ν v ∈
      ((Q.map (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk (P.map (Ideal.Quotient.mk J)))) ^ n •
        (⊤ : Submodule ((R ⧸ J) ⧸ P.map (Ideal.Quotient.mk J))
          (GrPiece (P.map (Ideal.Quotient.mk J)) ν))) :
    betaDouble J P Q hJP ν n (Submodule.Quotient.mk ⟨v, hb⟩) =
      Submodule.Quotient.mk ⟨grPieceMapQuotSemi J P hJP ν v, hb'⟩ := rfl

theorem betaDouble_grModMap_tmul (ν n : ℕ) (x : GrPiece P ν)
    (b : GrPiece (Q.map (Ideal.Quotient.mk P)) n) :
    betaDouble J P Q hJP ν n (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P ν) n (x ⊗ₜ b)) =
      grModMap ((Q.map (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk (P.map (Ideal.Quotient.mk J))))
        (GrPiece (P.map (Ideal.Quotient.mk J)) ν) n
        (grPieceMapQuotSemi J P hJP ν x ⊗ₜ[(R ⧸ J) ⧸ P.map (Ideal.Quotient.mk J)]
          thetaEquiv J P Q hJP n b) := by
  induction b using Submodule.Quotient.induction_on with
  | H b =>
    obtain ⟨b0, hb0⟩ := b
    have hb0' : (DoubleQuot.quotQuotEquivQuotOfLE hJP).symm b0 ∈
        ((Q.map (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk (P.map (Ideal.Quotient.mk J)))) ^ n := by
      have := Ideal.mem_map_of_mem (thetaRing J P hJP) hb0
      rw [Ideal.map_pow, map_quotQuotEquivQuotOfLE_symm J P Q hJP] at this
      exact this
    rw [thetaEquiv_mk J P Q hJP n b0 hb0 hb0', grModMap_tmul, grModMap_tmul]
    refine congrArg _ (Subtype.ext ?_)
    exact map_smulₛₗ (grPieceMapQuotSemi J P hJP ν) b0 x

section Square

theorem lamBilin_eq_mulPieceQuot {s : ℕ} (y : Fin s → R)
    (hqr : IsQuasiRegular fun j => Ideal.Quotient.mk P (y j))
    (hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) = Q.map (Ideal.Quotient.mk P))
    (p n : ℕ) (x : GrPiece P p) (b : GrPiece (Q.map (Ideal.Quotient.mk P)) n) :
    lamBilin P Q hPQ y hqr hz p n x b = GrPiece.mulPieceQuot Q p n (grPieceInclusion P Q hPQ p x)
      (betaStarPiece P Q hPQ y hqr hz n b) := rfl

variable {s : ℕ} (y : Fin s → R)
  (hqr : IsQuasiRegular fun j => Ideal.Quotient.mk P (y j))
  (hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) = Q.map (Ideal.Quotient.mk P))
  (hqr' : IsQuasiRegular fun j => Ideal.Quotient.mk (P.map (Ideal.Quotient.mk J))
    (Ideal.Quotient.mk J (y j)))
  (hz' : Ideal.span (Set.range fun j => Ideal.Quotient.mk (P.map (Ideal.Quotient.mk J))
    (Ideal.Quotient.mk J (y j))) =
      (Q.map (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk (P.map (Ideal.Quotient.mk J))))

/-- The right-hand square of the diagram of Lemma 10 (p. 199) commutes: "`λ` induces `ψ'`", i.e. `λ`
followed by `gr_Q(R) → gr_Q̄(O)` is `gr_Q(gr_P(R)) → gr_Q̄(gr_P̄(O))` followed by
`λ' = ψ'φ'⁻¹`, in the double degree `(ν, n)`. -/
theorem grPieceMapQuot_lambdaPiece (ν n : ℕ)
    (hbij : Function.Bijective (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P ν) n))
    (hbij' : Function.Bijective (grModMap ((Q.map (Ideal.Quotient.mk J)).map
      (Ideal.Quotient.mk (P.map (Ideal.Quotient.mk J)))) (GrPiece (P.map (Ideal.Quotient.mk J)) ν) n))
    (z : GrModPiece (Q.map (Ideal.Quotient.mk P)) (GrPiece P ν) n) :
    grPieceMapQuot J Q (ν + n) (lambdaPiece P Q hPQ y hqr hz ν n hbij z) =
      lambdaPiece (P.map (Ideal.Quotient.mk J)) (Q.map (Ideal.Quotient.mk J))
        (Ideal.map_mono hPQ) (fun j => Ideal.Quotient.mk J (y j)) hqr' hz' ν n hbij'
        (betaDouble J P Q hJP ν n z) := by
  obtain ⟨w, rfl⟩ := hbij.2 z
  induction w using TensorProduct.inductionOn with
  | tmul x b =>
    rw [lambdaPiece_grModMap, betaDouble_grModMap_tmul, lambdaPiece_grModMap, lamTensor_tmul,
      lamTensor_tmul, lamBilin_eq_mulPieceQuot, lamBilin_eq_mulPieceQuot,
      grPieceMapQuot_mulPieceQuot, grPieceMapQuot_grPieceInclusion,
      grPieceMapQuot_betaStarPiece J P Q hJP hPQ y hqr hz hqr' hz']
    rfl
  | add w w' hw hw' => simp only [map_add, hw, hw']

end Square

section TopRow

/-- `gr^ν_P(J, R)` as an `R/P`-submodule of `gr^ν_P(R)` (the top row of the diagram of Lemma 10 is
`gr_Q(gr_P(J, R)) → gr_Q(gr_P(R)) → gr_Q̄(gr_P̄(O)) → 0`; `gr_P(J, R)` is a graded `R/P`-submodule of
`gr_P(R)`, which is the ideal `Q gr_P(R)`'s module). -/
noncomputable def grIdealModule (ν : ℕ) : Submodule (R ⧸ P) (GrPiece P ν) where
  carrier := grIdealPiece J P ν
  zero_mem' := zero_mem _
  add_mem' := add_mem
  smul_mem' r x hx := by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
    have h : (Ideal.Quotient.mk P c) • x = c • x := algebraMap_smul (R ⧸ P) c x
    rw [h]
    exact (grIdealPiece J P ν).smul_mem c hx

theorem mem_grIdealModule {ν : ℕ} {x : GrPiece P ν} :
    x ∈ grIdealModule J P ν ↔ x ∈ grIdealPiece J P ν := Iff.rfl

/-- `α : gr^n_{Q/P}(gr^ν_P(J, R)) → gr^n_{Q/P}(gr^ν_P(R))`, the first map of the top row. -/
noncomputable def alphaDouble (ν n : ℕ) :
    GrModPiece (Q.map (Ideal.Quotient.mk P)) ↥(grIdealModule J P ν) n →ₗ[R ⧸ P]
      GrModPiece (Q.map (Ideal.Quotient.mk P)) (GrPiece P ν) n :=
  Submodule.mapQ _ _
    (((grIdealModule J P ν).subtype).restrict fun _ hx =>
      Submodule.smul_top_le_comap_smul_top _ (grIdealModule J P ν).subtype hx)
    (fun _ hx => Submodule.smul_top_le_comap_smul_top _ (grIdealModule J P ν).subtype hx)

theorem alphaDouble_mk (ν n : ℕ) (m : ↥(grIdealModule J P ν))
    (hm : m ∈ (Q.map (Ideal.Quotient.mk P)) ^ n • (⊤ : Submodule (R ⧸ P) ↥(grIdealModule J P ν)))
    (hm' : (m : GrPiece P ν) ∈ (Q.map (Ideal.Quotient.mk P)) ^ n •
      (⊤ : Submodule (R ⧸ P) (GrPiece P ν))) :
    alphaDouble J P Q ν n (Submodule.Quotient.mk ⟨m, hm⟩) =
      Submodule.Quotient.mk ⟨(m : GrPiece P ν), hm'⟩ := rfl

/-- The top row is a complex: `β α = 0` (`gr_P(J, R)` maps to zero in `gr_P̄(O)`). -/
theorem betaDouble_alphaDouble (ν n : ℕ)
    (x : GrModPiece (Q.map (Ideal.Quotient.mk P)) ↥(grIdealModule J P ν) n) :
    betaDouble J P Q hJP ν n (alphaDouble J P Q ν n x) = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    obtain ⟨m, hm⟩ := x
    have hm' : (m : GrPiece P ν) ∈ (Q.map (Ideal.Quotient.mk P)) ^ n •
        (⊤ : Submodule (R ⧸ P) (GrPiece P ν)) :=
      Submodule.smul_top_le_comap_smul_top _ (grIdealModule J P ν).subtype hm
    have hf : grPieceMapQuotSemi J P hJP ν (m : GrPiece P ν) = 0 :=
      (grPieceMapQuot_eq_zero_iff J P ν _).mpr m.2
    rw [alphaDouble_mk J P Q ν n m hm hm', betaDouble_mk J P Q hJP ν n _ hm'
      (grPieceMapQuotSemi_smul_top_le J P Q hJP ν n hm')]
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    rw [Submodule.mem_comap]
    show grPieceMapQuotSemi J P hJP ν (m : GrPiece P ν) ∈ _
    rw [hf]
    exact zero_mem _

end TopRow

section Chase

variable {s : ℕ} (y : Fin s → R)
  (hqr : IsQuasiRegular fun j => Ideal.Quotient.mk P (y j))
  (hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) = Q.map (Ideal.Quotient.mk P))
  (hqr' : IsQuasiRegular fun j => Ideal.Quotient.mk (P.map (Ideal.Quotient.mk J))
    (Ideal.Quotient.mk J (y j)))
  (hz' : Ideal.span (Set.range fun j => Ideal.Quotient.mk (P.map (Ideal.Quotient.mk J))
    (Ideal.Quotient.mk J (y j))) =
      (Q.map (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk (P.map (Ideal.Quotient.mk J))))

/-- An element of `gr_Q(R)` of degree `N` whose image in `gr_Q̄(O)` is zero lies in `gr_Q(J, R)`
(Lemma 5, p. 190). -/
theorem ofGrPiece_mem_grIdeal_of_grPieceMapQuot_eq_zero {N : ℕ} {x : GrPiece Q N}
    (hx : grPieceMapQuot J Q N x = 0) : AssocGraded.ofGrPiece Q N x ∈ grIdeal Q J := by
  obtain ⟨a, haJ, ha, rfl⟩ := (grPieceMapQuot_eq_zero_iff J Q N x).mp hx
  rw [AssocGraded.ofGrPiece_mk]
  exact mk_mem_grIdeal Q haJ ha

include hJP hqr' hz' in
/-- **Lemma 10, p. 199, the diagram chase.**  If a form `Φ` of `gr_P(J,R)` lying in `Qⁿ gr_P(R)` lies
in `Qⁿ gr_P(J,R)` (Lemma 7; `hL7`), and `gr_P̄(O)` is flat over `O/P̄` (`hbij'`: the canonical `φ'`
for `O` is bijective, so that `λ' = ψ'φ'⁻¹` is defined), then for `g ∈ J ∩ Pᵛ` with `[g] ∈ Qⁿ gr^ν_P(R)`
the `λ`-image of the initial form `Φ_*` of `g` lies in `gr_Q(J, R)`: `Φ_*` is `α` of an element of
`gr^n_Q(gr^ν_P(J,R))` (Lemma 7), whose image under the right-hand column is `β α = 0`, so that
`γ λ(Φ_*) = λ' β(Φ_*) = 0` and `λ(Φ_*) ∈ ker γ = gr_Q(J, R)` (Lemma 5). -/
theorem lambdaPiece_mem_grIdeal_of_diagram (ν n : ℕ)
    (hL7 : ∀ (Φ : GrPiece P ν) (hJ : Φ ∈ grIdealPiece J P ν),
      Φ ∈ (Q.map (Ideal.Quotient.mk P)) ^ n • (⊤ : Submodule (R ⧸ P) (GrPiece P ν)) →
      (⟨Φ, hJ⟩ : ↥(grIdealModule J P ν)) ∈ (Q.map (Ideal.Quotient.mk P)) ^ n •
        (⊤ : Submodule (R ⧸ P) ↥(grIdealModule J P ν)))
    (hbij : Function.Bijective (grModMap (Q.map (Ideal.Quotient.mk P)) (GrPiece P ν) n))
    (hbij' : Function.Bijective (grModMap ((Q.map (Ideal.Quotient.mk J)).map
      (Ideal.Quotient.mk (P.map (Ideal.Quotient.mk J)))) (GrPiece (P.map (Ideal.Quotient.mk J)) ν) n))
    {g : R} (hgJ : g ∈ J) (hgP : g ∈ P ^ ν)
    (hΦ : (Submodule.Quotient.mk ⟨g, hgP⟩ : GrPiece P ν) ∈
      (Q.map (Ideal.Quotient.mk P)) ^ n • (⊤ : Submodule (R ⧸ P) (GrPiece P ν))) :
    AssocGraded.ofGrPiece Q (ν + n) (lambdaPiece P Q hPQ y hqr hz ν n hbij
      (Submodule.Quotient.mk ⟨Submodule.Quotient.mk ⟨g, hgP⟩, hΦ⟩)) ∈ grIdeal Q J := by
  have hJ : (Submodule.Quotient.mk ⟨g, hgP⟩ : GrPiece P ν) ∈ grIdealPiece J P ν :=
    mk_mem_grIdealPiece J P hgJ hgP
  have hmem := hL7 _ hJ hΦ
  have hα : alphaDouble J P Q ν n (Submodule.Quotient.mk ⟨⟨_, hJ⟩, hmem⟩) =
      Submodule.Quotient.mk ⟨Submodule.Quotient.mk ⟨g, hgP⟩, hΦ⟩ := rfl
  have h0 := betaDouble_alphaDouble J P Q hJP ν n (Submodule.Quotient.mk ⟨⟨_, hJ⟩, hmem⟩)
  rw [hα] at h0
  refine ofGrPiece_mem_grIdeal_of_grPieceMapQuot_eq_zero J Q ?_
  rw [grPieceMapQuot_lambdaPiece J P Q hJP hPQ y hqr hz hqr' hz' ν n hbij hbij', h0, map_zero]

end Chase

section Lemma7Piece

variable (ν n : ℕ)

/-- `JdPiece J P Q ν n u`: `u ∈ Pᵛ` has class in `gr^ν_P(J, R)` (as an element of that `R/P`-module)
lying in `Qⁿ gr^ν_P(J, R)` -- the conclusion of Lemma 7 (p. 192) for the form `[u]`. -/
def JdPiece (u : R) : Prop :=
  ∃ (hu : u ∈ P ^ ν) (hJ : (Submodule.Quotient.mk ⟨u, hu⟩ : GrPiece P ν) ∈ grIdealPiece J P ν),
    (⟨Submodule.Quotient.mk ⟨u, hu⟩, hJ⟩ : ↥(grIdealModule J P ν)) ∈
      (Q.map (Ideal.Quotient.mk P)) ^ n • (⊤ : Submodule (R ⧸ P) ↥(grIdealModule J P ν))

theorem JdPiece.zero : JdPiece J P Q ν n 0 := by
  refine ⟨zero_mem _, ?_, ?_⟩
  · have : (Submodule.Quotient.mk ⟨0, zero_mem _⟩ : GrPiece P ν) = 0 := rfl
    rw [this]
    exact zero_mem _
  · have : (⟨Submodule.Quotient.mk ⟨(0 : R), zero_mem _⟩, zero_mem _⟩ : ↥(grIdealModule J P ν)) = 0 :=
      Subtype.ext rfl
    rw [this]
    exact zero_mem _

theorem JdPiece.add {u₁ u₂ : R} (h₁ : JdPiece J P Q ν n u₁) (h₂ : JdPiece J P Q ν n u₂) :
    JdPiece J P Q ν n (u₁ + u₂) := by
  obtain ⟨hu₁, hJ₁, hb₁⟩ := h₁
  obtain ⟨hu₂, hJ₂, hb₂⟩ := h₂
  have hsum : (Submodule.Quotient.mk ⟨u₁ + u₂, add_mem hu₁ hu₂⟩ : GrPiece P ν) =
      Submodule.Quotient.mk ⟨u₁, hu₁⟩ + Submodule.Quotient.mk ⟨u₂, hu₂⟩ := rfl
  have hJ : (Submodule.Quotient.mk ⟨u₁ + u₂, add_mem hu₁ hu₂⟩ : GrPiece P ν) ∈ grIdealPiece J P ν := by
    rw [hsum]
    exact add_mem hJ₁ hJ₂
  refine ⟨add_mem hu₁ hu₂, hJ, ?_⟩
  have : (⟨Submodule.Quotient.mk ⟨u₁ + u₂, add_mem hu₁ hu₂⟩, hJ⟩ : ↥(grIdealModule J P ν)) =
      ⟨Submodule.Quotient.mk ⟨u₁, hu₁⟩, hJ₁⟩ + ⟨Submodule.Quotient.mk ⟨u₂, hu₂⟩, hJ₂⟩ :=
    Subtype.ext hsum
  rw [this]
  exact add_mem hb₁ hb₂

theorem JdPiece.mul_basic {q : R} (hq : q ∈ Q ^ n) {z : R} (hzJ : z ∈ J) (hzP : z ∈ P ^ ν) :
    JdPiece J P Q ν n (q * z) := by
  have hu : q * z ∈ P ^ ν := Ideal.mul_mem_left _ _ hzP
  have hqb : Ideal.Quotient.mk P q ∈ (Q.map (Ideal.Quotient.mk P)) ^ n := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hq
  have hsm : (Ideal.Quotient.mk P q) • (Submodule.Quotient.mk ⟨z, hzP⟩ : GrPiece P ν) =
      Submodule.Quotient.mk ⟨q * z, hu⟩ := by
    have h' : (Ideal.Quotient.mk P q) • (Submodule.Quotient.mk ⟨z, hzP⟩ : GrPiece P ν) =
        q • (Submodule.Quotient.mk ⟨z, hzP⟩ : GrPiece P ν) := algebraMap_smul (R ⧸ P) q _
    rw [h', ← Submodule.Quotient.mk_smul]
    exact congrArg _ (Subtype.ext (smul_eq_mul q z))
  have hJ : (Submodule.Quotient.mk ⟨q * z, hu⟩ : GrPiece P ν) ∈ grIdealPiece J P ν :=
    mk_mem_grIdealPiece J P (Ideal.mul_mem_left _ _ hzJ) hu
  refine ⟨hu, hJ, ?_⟩
  have : (⟨Submodule.Quotient.mk ⟨q * z, hu⟩, hJ⟩ : ↥(grIdealModule J P ν)) =
      (Ideal.Quotient.mk P q) • (⟨Submodule.Quotient.mk ⟨z, hzP⟩, mk_mem_grIdealPiece J P hzJ hzP⟩ :
        ↥(grIdealModule J P ν)) :=
    Subtype.ext hsm.symm
  rw [this]
  exact Submodule.smul_mem_smul hqb trivial

theorem JdPiece.mul_mem {k e : ℕ} (hke : k + e = ν) {x : R} (hx : x ∈ Q ^ n * P ^ k) {z : R}
    (hzJ : z ∈ J) (hze : z ∈ P ^ e) : JdPiece J P Q ν n (x * z) := by
  refine Submodule.mul_induction_on (C := fun x => JdPiece J P Q ν n (x * z)) hx
    (fun q hq a ha => ?_) (fun x₁ x₂ h₁ h₂ => ?_)
  · have hz' : a * z ∈ P ^ ν := by
      rw [← hke, pow_add]
      exact Ideal.mul_mem_mul ha hze
    rw [mul_assoc]
    exact JdPiece.mul_basic J P Q ν n hq (Ideal.mul_mem_left _ a hzJ) hz'
  · rw [add_mul]
    exact JdPiece.add J P Q ν n h₁ h₂

theorem JdPiece.of_mem_pow_succ {u : R} (hu : u ∈ P ^ (ν + 1)) : JdPiece J P Q ν n u := by
  have hu' : u ∈ P ^ ν := Ideal.pow_le_pow_right (Nat.le_succ ν) hu
  have hmk : (Submodule.Quotient.mk ⟨u, hu'⟩ : GrPiece P ν) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hu
  refine ⟨hu', ?_, ?_⟩
  · rw [hmk]
    exact zero_mem _
  · have : (⟨Submodule.Quotient.mk ⟨u, hu'⟩, by rw [hmk]; exact zero_mem _⟩ :
        ↥(grIdealModule J P ν)) = 0 := Subtype.ext hmk
    rw [this]
    exact zero_mem _

/-- Lemma 7 (p. 192, footnote 43) at the level of the form `[g]`: if `g ∈ J` has
`g ∈ Σ_β Qⁿ P^(ν-ν_β) f_β + P^(ν+1)` (the form of Lemma 7 for `R`, from the system `(f_β)` of Cor. 1
of Th. 2), then the form `[g]` of `gr_P(J,R)` lies in `Qⁿ gr_P(J,R)`. -/
theorem JdPiece.of_mem_sup {m : ℕ} (F : Fin m → R) (νf : Fin m → ℕ) (hFJ : ∀ β, F β ∈ J)
    (hFP : ∀ β, F β ∈ P ^ νf β) {u : R}
    (hu : u ∈ (∑ β ∈ Finset.univ.filter (fun β => νf β ≤ ν),
      Q ^ n * P ^ (ν - νf β) * Ideal.span {F β}) ⊔ P ^ (ν + 1)) :
    JdPiece J P Q ν n u := by
  obtain ⟨e, he, p', hp', rfl⟩ := Submodule.mem_sup.mp hu
  refine JdPiece.add J P Q ν n ?_ (JdPiece.of_mem_pow_succ J P Q ν n hp')
  obtain ⟨v, hv, rfl⟩ := exists_eq_sum_of_mem_finset_sum _ _ he
  refine Finset.sum_induction _ (fun x => JdPiece J P Q ν n x)
    (fun a b ha hb => JdPiece.add J P Q ν n ha hb)
    (JdPiece.zero J P Q ν n) (fun β hβ => ?_)
  have hβ' : νf β ≤ ν := (Finset.mem_filter.mp hβ).2
  refine Submodule.mul_induction_on (C := fun x => JdPiece J P Q ν n x) (hv β hβ)
    (fun x hx z hzF => ?_) (fun x₁ x₂ h₁ h₂ => JdPiece.add J P Q ν n h₁ h₂)
  have hzJ : z ∈ J := (Ideal.span_singleton_le_iff_mem J).mpr (hFJ β) hzF
  have hzP : z ∈ P ^ νf β := (Ideal.span_singleton_le_iff_mem _).mpr (hFP β) hzF
  exact JdPiece.mul_mem J P Q ν n (by omega) hx hzJ hzP

/-- Lemma 7 for the piece `(ν, n)`: "if `Φ` is a form in `gr_P(J,R)`, and if `Φ ∈ Qⁿ gr_P(R)`, then
`Φ ∈ Qⁿ gr_P(J,R)`" (p. 199, via footnote 43), from the system `(f_β)` of Lemma 7 for `R`. -/
theorem mem_pow_smul_top_grIdealModule_of_key {m : ℕ} (F : Fin m → R) (νf : Fin m → ℕ)
    (hFJ : ∀ β, F β ∈ J) (hFP : ∀ β, F β ∈ P ^ νf β)
    (key : ∀ (ν n : ℕ) (g : R), g ∈ J → g ∈ P ^ ν → g ∈ Q ^ n * P ^ ν ⊔ P ^ (ν + 1) →
      g ∈ (∑ β ∈ Finset.univ.filter (fun β => νf β ≤ ν),
        Q ^ n * P ^ (ν - νf β) * Ideal.span {F β}) ⊔ P ^ (ν + 1))
    (Φ : GrPiece P ν) (hJ : Φ ∈ grIdealPiece J P ν)
    (hΦ : Φ ∈ (Q.map (Ideal.Quotient.mk P)) ^ n • (⊤ : Submodule (R ⧸ P) (GrPiece P ν))) :
    (⟨Φ, hJ⟩ : ↥(grIdealModule J P ν)) ∈ (Q.map (Ideal.Quotient.mk P)) ^ n •
      (⊤ : Submodule (R ⧸ P) ↥(grIdealModule J P ν)) := by
  obtain ⟨g, hgJ, hgP, rfl⟩ := hJ
  obtain ⟨hu, hJ', hb⟩ := JdPiece.of_mem_sup J P Q ν n F νf hFJ hFP
    (key ν n g hgJ hgP (mem_mul_sup_of_mem_pow_smul_top P Q ν n hgP hΦ))
  exact hb

end Lemma7Piece

section Local

/-- Lemma 10 (p. 199) when `Q` is the maximal ideal of `R`, as printed: flatness of `gr_P̄(O)` over
`O/P̄` makes `λ' = ψ'φ'⁻¹` (for `O`) defined, the system `(f_β)` of Cor. 1 of Th. 2 gives Lemma 7, and
the chase of the diagram `lambdaPiece_mem_grIdeal_of_diagram` finishes. -/
theorem lambdaPiece_mem_grIdeal_of_isNormallyFlatAlongIdeal (S : Type u) [CommRing S]
    [IsRegularLocalRing S] (J P : Ideal S) [P.IsPrime] [IsRegularLocalRing (S ⧸ P)]
    (hJP : J ≤ P) (hPQ : P ≤ IsLocalRing.maximalIdeal S)
    (hflat : IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)))
    (hsys : ∃ (m : ℕ) (F : Fin m → S) (νf : Fin m → ℕ), (∀ β, F β ∈ J) ∧ (∀ β, F β ∈ P ^ νf β) ∧
      (∀ (ν n : ℕ) (g : S), g ∈ J → g ∈ P ^ ν →
        g ∈ (IsLocalRing.maximalIdeal S) ^ n * P ^ ν ⊔ P ^ (ν + 1) →
        g ∈ (∑ β ∈ Finset.univ.filter (fun β => νf β ≤ ν),
          (IsLocalRing.maximalIdeal S) ^ n * P ^ (ν - νf β) * Ideal.span {F β}) ⊔ P ^ (ν + 1)))
    {s : ℕ} (y : Fin s → S) (hqr : IsQuasiRegular fun j => Ideal.Quotient.mk P (y j))
    (hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) =
      (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk P))
    (ν n : ℕ) {g : S} (hgJ : g ∈ J) (hgP : g ∈ P ^ ν)
    (hΦ : (Submodule.Quotient.mk ⟨g, hgP⟩ : GrPiece P ν) ∈
      ((IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk P)) ^ n •
        (⊤ : Submodule (S ⧸ P) (GrPiece P ν))) :
    AssocGraded.ofGrPiece (IsLocalRing.maximalIdeal S) (ν + n)
      (lambdaPiece P (IsLocalRing.maximalIdeal S) hPQ y hqr hz ν n
        (grModMap_bijective_of_isRegularLocalRing_quotient P _ ν n)
        (Submodule.Quotient.mk ⟨Submodule.Quotient.mk ⟨g, hgP⟩, hΦ⟩)) ∈
      grIdeal (IsLocalRing.maximalIdeal S) J := by
  obtain ⟨m, F, νf, hFJ, hFP, key⟩ := hsys
  have hQY := eq_sup_span_of_span_map_eq P (IsLocalRing.maximalIdeal S) hPQ y hz
  have hqr' := isQuasiRegular_map_quotient J P y hJP hqr
  have hz' := span_map_mk_eq_map_quotient J P (IsLocalRing.maximalIdeal S) y hQY
  have hbij' := grModMap_bijective_of_isNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)) hflat
  exact lambdaPiece_mem_grIdeal_of_diagram J P (IsLocalRing.maximalIdeal S) hJP hPQ y hqr hz hqr' hz'
    ν n (fun Φ hJ hΦ' => mem_pow_smul_top_grIdealModule_of_key J P _ ν n F νf hFJ hFP key Φ hJ hΦ')
    (grModMap_bijective_of_isRegularLocalRing_quotient P _ ν n) (hbij' _ ν n) hgJ hgP hΦ

end Local

/-- "Then, by the assumption that `gr_P(O)` is flat over `O/P`, `λ` induces an isomorphism
`ψ' : gr_Q(gr_P(O)) → gr_Q(O)`" (p. 199), for `Q` the maximal ideal of `R` and `O = R/J`: in each
total degree, `λ' = ψ'φ'⁻¹` (built from the classes of `y_j` in `O`) is bijective, `φ'` being
bijective by flatness and `ψ'` by Proposition 1 for `O`. -/
theorem bijective_lambdaTotal_quotient (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (J P : Ideal S) [P.IsPrime] [IsRegularLocalRing (S ⧸ P)] (hJP : J ≤ P)
    (hPQ : P ≤ IsLocalRing.maximalIdeal S)
    (hflat : IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)))
    {s : ℕ} (y : Fin s → S) (hqr : IsQuasiRegular fun j => Ideal.Quotient.mk P (y j))
    (hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) =
      (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk P)) (N : ℕ) :
    Function.Bijective (lambdaTotal (P.map (Ideal.Quotient.mk J))
      ((IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk J)) (Ideal.map_mono hPQ)
      (fun j => Ideal.Quotient.mk J (y j)) (isQuasiRegular_map_quotient J P y hJP hqr)
      (span_map_mk_eq_map_quotient J P _ y (eq_sup_span_of_span_map_eq P _ hPQ y hz))
      (grModMap_bijective_of_isNormallyFlatAlongIdeal _ hflat _) N) := by
  have hQ : IsLocalRing.maximalIdeal S ≠ ⊤ := Ideal.IsPrime.ne_top'
  have hJtop : J ≠ ⊤ := ne_top_of_le_ne_top Ideal.IsPrime.ne_top' hJP
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have : IsLocalRing (S ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  have : (P.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJP)
  have : ((IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJP.trans hPQ)
  have : IsRegularLocalRing ((S ⧸ J) ⧸ P.map (Ideal.Quotient.mk J)) :=
    IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJP).symm
  have : IsRegularLocalRing (S ⧸ IsLocalRing.maximalIdeal S) := by
    let := Ideal.Quotient.field (IsLocalRing.maximalIdeal S)
    infer_instance
  have : IsRegularLocalRing ((S ⧸ J) ⧸ (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk J)) :=
    IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE (hJP.trans hPQ)).symm
  refine (bijective_lambdaTotal_iff _ _ _ _ _ _ _ N).mpr ?_
  exact psiDeg_bijective_of_isNormallyFlatAlongIdeal _ _ (Ideal.map_mono hPQ) _ _ _ hflat
    (eq_sup_span_of_span_map_eq _ _ (Ideal.map_mono hPQ) _ (span_map_mk_eq_map_quotient J P _ y
      (eq_sup_span_of_span_map_eq P _ hPQ y hz))) N

end Lemma10Diagram

section Lemma10Localization

variable {R : Type u} [CommRing R]

/-- Clearing denominators ("gr commutes with localization", p. 199): if the class of `h ∈ Qᵐ` in
`gr^m_{QR_Q}(R_Q)` lies in `gr_{QR_Q}(JR_Q, R_Q)`, then `t h ∈ J ∩ Qᵐ + Qᵐ⁺¹` for some `t ∉ Q`. -/
theorem exists_mul_mk_mem_grIdealPiece_of_map (R : Type u) [CommRing R] (J Q : Ideal R) [Q.IsPrime]
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S Q] (Q' J' : Ideal S)
    (hQ' : Q.map (algebraMap R S) = Q') (hJ' : J.map (algebraMap R S) = J')
    {m : ℕ} {h : R} (hh' : algebraMap R S h ∈ Q' ^ m)
    (hmem : (Submodule.Quotient.mk ⟨algebraMap R S h, hh'⟩ : GrPiece Q' m) ∈
      Lemma8.grIdealPiece J' Q' m) :
    ∃ t : R, t ∉ Q ∧ ∃ ht : t * h ∈ Q ^ m,
      (Submodule.Quotient.mk ⟨t * h, ht⟩ : GrPiece Q m) ∈ Lemma8.grIdealPiece J Q m := by
  subst hQ' hJ'
  obtain ⟨a, haJ, ha, hmk⟩ := hmem
  have hdiff : a - algebraMap R S h ∈ (Q.map (algebraMap R S)) ^ (m + 1) := by
    have := (Submodule.Quotient.eq _).mp hmk
    simpa using this
  obtain ⟨⟨⟨j, hjJ⟩, s0⟩, hj⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl S).mp haJ
  have h1 : algebraMap R S j ∈ (Q ^ m).map (algebraMap R S) := by
    rw [← hj, Ideal.map_pow]
    exact Ideal.mul_mem_right _ _ ha
  obtain ⟨u, hu0, hu⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff Q.primeCompl S _ _).mp h1
  have h2 : algebraMap R S (j - (s0 : R) * h) ∈ (Q ^ (m + 1)).map (algebraMap R S) := by
    rw [Ideal.map_pow, map_sub, map_mul, ← hj]
    have : a * algebraMap R S (s0 : R) - algebraMap R S (s0 : R) * algebraMap R S h =
        algebraMap R S (s0 : R) * (a - algebraMap R S h) := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hdiff
  obtain ⟨v, hv0, hv⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff Q.primeCompl S _ _).mp h2
  set e : R := v * (u * j) with he
  set r : R := u * (v * (j - (s0 : R) * h)) with hr
  have heJ : e ∈ J := Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hjJ)
  have heQ : e ∈ Q ^ m := Ideal.mul_mem_left _ _ hu
  have hrQ : r ∈ Q ^ (m + 1) := Ideal.mul_mem_left _ _ hv
  have hth : (u * v * s0) * h = e - r := by
    simp only [he, hr]
    ring
  have hrQ' : r ∈ Q ^ m := Ideal.pow_le_pow_right (Nat.le_succ m) hrQ
  have ht : (u * v * s0) * h ∈ Q ^ m := by
    rw [hth]
    exact sub_mem heQ hrQ'
  refine ⟨u * v * s0, ?_, ht, ?_⟩
  · exact Q.primeCompl.mul_mem (Q.primeCompl.mul_mem hu0 hv0) s0.2
  · refine ⟨e, heJ, heQ, ?_⟩
    rw [Submodule.Quotient.eq]
    rw [Submodule.mem_comap, Submodule.subtype_apply]
    show e - (u * v * s0) * h ∈ Q ^ (m + 1)
    rw [hth]
    simpa using hrQ

theorem ofGrPiece_mem_grIdeal_iff_mem_grIdealPiece (J I : Ideal R) (n : ℕ) (x : GrPiece I n) :
    AssocGraded.ofGrPiece I n x ∈ grIdeal I J ↔ x ∈ Lemma8.grIdealPiece J I n := by
  constructor
  · intro h
    obtain ⟨a, ⟨haJ, -⟩, ha, hmk⟩ := (grIdeal_homogeneous_eq I J n _
      (LinearMap.mem_range_self _ x)).mp h
    refine ⟨a, haJ, ha, ?_⟩
    refine AssocGraded.ofGrPiece_injective I n ?_
    rw [AssocGraded.ofGrPiece_mk]
    exact hmk
  · rintro ⟨a, haJ, ha, rfl⟩
    rw [AssocGraded.ofGrPiece_mk]
    exact mk_mem_grIdeal I haJ ha

/-- The converse of `mem_mul_sup_of_mem_pow_smul_top`: `g ∈ Qⁿ Pᵛ + Pᵛ⁺¹` means `[g] ∈ Qⁿ grᵛ_P(R)`. -/
theorem mk_mem_pow_smul_top_of_mem_mul_sup (P Q : Ideal R) (ν n : ℕ) {g : R} (hgP : g ∈ P ^ ν)
    (h : g ∈ Q ^ n * P ^ ν ⊔ P ^ (ν + 1)) :
    (Submodule.Quotient.mk ⟨g, hgP⟩ : GrPiece P ν) ∈
      (Q.map (Ideal.Quotient.mk P)) ^ n • (⊤ : Submodule (R ⧸ P) (GrPiece P ν)) := by
  have h1 := (grClassMemPow_of_mem_mul_sup (P := P) (Q := Q) hgP h).2
  have h2 := grProj_mem_pow_smul_top P Q ν n h1
  rwa [grProj_mk_same] at h2

end Lemma10Localization

section Lemma10Main

open TensorProduct

/-- The proof of Lemma 10 (p. 199), for the class `Φ_*` of any `g ∈ J ∩ Pᵛ` with `[g] ∈ Qⁿ grᵛ_P(R)`
(`lambdaPiece_mem_grIdeal_of_isNormallyFlatAlongIdeal` and the passage to `R_Q`); in the node
`exists_mul_mem_grIdeal_lambdaPiece` the orders are the exact ones, `ν = ν_P(g)` and
`n = ν_{Q/P}(Φ)` for the initial form `Φ` of `g`, and the quasi-regularity of the `ȳ_j` comes from
`ȳ` being a minimal base. -/
theorem exists_mul_mem_grIdeal_lambdaPiece_of_isQuasiRegular [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (J P Q : Ideal R)
    [P.IsPrime] [Q.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)]
    (hJP : J ≤ P) (hPQ : P ≤ Q) [(Q.map (Ideal.Quotient.mk J)).IsPrime]
    (hflat : IsNormallyFlatAlongIdeal ((P.map (Ideal.Quotient.mk J)).map
      (algebraMap (R ⧸ J) (Localization.AtPrime (Q.map (Ideal.Quotient.mk J))))))
    {s : ℕ} (y : Fin s → R)
    (hy : Ideal.span (Set.range fun i => Ideal.Quotient.mk P (y i)) = Q.map (Ideal.Quotient.mk P))
    (hqr : IsQuasiRegular fun i => Ideal.Quotient.mk P (y i))
    {g : R} (hg : g ∈ J) {ν n : ℕ} (hgP : g ∈ P ^ ν)
    (hΦ : (Submodule.Quotient.mk ⟨g, hgP⟩ : GrPiece P ν) ∈
      (Q.map (Ideal.Quotient.mk P)) ^ n • (⊤ : Submodule (R ⧸ P) (GrPiece P ν))) :
    ∃ t : R, t ∉ Q ∧ algebraMap R (AssocGraded Q) t * AssocGraded.ofGrPiece Q (ν + n)
      (lambdaPiece P Q hPQ y hqr hy
        ν n (grModMap_bijective_of_isRegularLocalRing_quotient P _ ν n)
        (Submodule.Quotient.mk ⟨Submodule.Quotient.mk ⟨g, hgP⟩, hΦ⟩)) ∈ grIdeal Q J := by
  classical
  have hQY := eq_sup_span_of_span_map_eq P Q hPQ y hy
  set Y : Ideal R := Ideal.span (Set.range y) with hY
  have hYQ : Y ≤ Q := hQY ▸ le_sup_right
  -- an element `h ∈ Yⁿ Pᵛ` with `g - h ∈ Pᵛ⁺¹` representing the class of `g`
  have hmul : Q ^ n * P ^ ν ≤ Y ^ n * P ^ ν ⊔ P ^ (ν + 1) :=
    calc Q ^ n * P ^ ν ≤ (Y ^ n ⊔ P) * P ^ ν :=
          Ideal.mul_mono_left (hQY ▸ sup_pow_le_pow_sup P Y n)
      _ = Y ^ n * P ^ ν ⊔ P ^ (ν + 1) := by rw [Ideal.sup_mul, ← pow_succ']
  have hgsup : g ∈ Y ^ n * P ^ ν ⊔ P ^ (ν + 1) :=
    sup_le hmul le_sup_right (mem_mul_sup_of_mem_pow_smul_top P Q ν n hgP hΦ)
  obtain ⟨h, hh, e, he, hhe⟩ := Submodule.mem_sup.mp hgsup
  have hgh : g - h ∈ P ^ (ν + 1) := by
    have : g - h = e := by rw [← hhe]; ring
    rw [this]
    exact he
  have hhQ : h ∈ Q ^ (ν + n) := by
    have : Y ^ n * P ^ ν ≤ Q ^ (ν + n) :=
      calc Y ^ n * P ^ ν ≤ Q ^ n * Q ^ ν :=
            Ideal.mul_mono (Ideal.pow_right_mono hYQ n) (Ideal.pow_right_mono hPQ ν)
        _ = Q ^ (ν + n) := by rw [← pow_add, add_comm]
    exact this hh
  rw [ofGrPiece_lambdaPiece_eq_mk P Q hPQ y hqr hy ν n _ hgP hΦ hh hgh hhQ]
  -- localization at `Q`: "Since gr commutes with localization, we may assume that Q is maximal"
  set S := Localization.AtPrime Q with hS
  have : IsRegularLocalRing S := isRegularLocalRing_localization_of_isRegularLocalRing R Q
  set ι : R →+* S := algebraMap R S with hι
  set Jq : Ideal S := J.map ι with hJq
  set Pq : Ideal S := P.map ι with hPq
  have hdisj : Disjoint (Q.primeCompl : Set R) (P : Set R) :=
    Set.disjoint_left.mpr fun a ha haP => ha (hPQ haP)
  have hPqprime : Pq.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl S P
    ‹_› hdisj
  have hmax : IsLocalRing.maximalIdeal S = Q.map ι :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal Q S).symm
  have hPqQ : Pq ≤ IsLocalRing.maximalIdeal S := hmax ▸ Ideal.map_mono hPQ
  have : (Q.map (Ideal.Quotient.mk P)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hPQ
  obtain ⟨eP, heP⟩ := exists_ringEquiv_quotient_localization Q P hPQ S
  have : IsRegularLocalRing (S ⧸ Pq) := by
    have : IsRegularLocalRing (Localization.AtPrime (Q.map (Ideal.Quotient.mk P))) :=
      isRegularLocalRing_localization_of_isRegularLocalRing (R ⧸ P) _
    exact IsRegularLocalRing.of_ringEquiv eP.symm
  -- the flatness hypothesis for `S/Jq`
  obtain ⟨e2, he2⟩ := exists_ringEquiv_quotient_localization Q J (hJP.trans hPQ) S
  have hflat' : IsNormallyFlatAlongIdeal (Pq.map (Ideal.Quotient.mk Jq)) := by
    refine isNormallyFlatAlongIdeal_of_ringEquiv e2.symm _ _ ?_ hflat
    rw [Ideal.map_map, Ideal.map_map, Ideal.map_map]
    congr 1
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [← he2 a]
    simp only [RingEquiv.symm_apply_apply]
    rfl
  -- the system `ι ∘ y` in `S`
  have hzS : Ideal.span (Set.range fun j => Ideal.Quotient.mk Pq (ι (y j))) =
      (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk Pq) := by
    rw [hmax, Ideal.map_map]
    let g0 : R ⧸ P →+* S ⧸ Pq := Ideal.quotientMap Pq ι (fun a ha => Ideal.mem_map_of_mem _ ha)
    have hcomp : (Ideal.Quotient.mk Pq).comp ι = g0.comp (Ideal.Quotient.mk P) := RingHom.ext fun a => rfl
    rw [hcomp, ← Ideal.map_map, ← hy, Ideal.map_span, ← Set.range_comp]
    rfl
  have hqrS : IsQuasiRegular fun j => Ideal.Quotient.mk Pq (ι (y j)) := by
    have h1 := isQuasiRegular_map_localization (Q.map (Ideal.Quotient.mk P))
      (fun j => Ideal.Quotient.mk P (y j)) hqr hy (Localization.AtPrime (Q.map (Ideal.Quotient.mk P)))
    have h2 := IsQuasiRegular.map_ringEquiv eP.symm h1
    convert h2 using 2 with j
    have := heP (y j)
    rw [eq_comm, RingEquiv.symm_apply_eq]
    exact this.symm
  -- the data for the form `Φ_*` in `S`
  have hgJ' : ι g ∈ Jq := Ideal.mem_map_of_mem _ hg
  have hgP' : ι g ∈ Pq ^ ν := by
    rw [hPq, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hgP
  have hΦ' : (Submodule.Quotient.mk ⟨ι g, hgP'⟩ : GrPiece Pq ν) ∈
      ((IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk Pq)) ^ n •
        (⊤ : Submodule (S ⧸ Pq) (GrPiece Pq ν)) := by
    refine mk_mem_pow_smul_top_of_mem_mul_sup Pq _ ν n hgP' ?_
    have := Ideal.mem_map_of_mem ι (mem_mul_sup_of_mem_pow_smul_top P Q ν n hgP hΦ)
    rwa [Ideal.map_sup, Ideal.map_mul, Ideal.map_pow, Ideal.map_pow, Ideal.map_pow, ← hmax] at this
  have hhY : ι h ∈ Ideal.span (Set.range fun j => ι (y j)) ^ n * Pq ^ ν := by
    have := Ideal.mem_map_of_mem ι hh
    rw [Ideal.map_mul, Ideal.map_pow, Ideal.map_pow, hY, Ideal.map_span, ← Set.range_comp] at this
    exact this
  have hghS : ι g - ι h ∈ Pq ^ (ν + 1) := by
    rw [← map_sub, hPq, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hgh
  have hhQS : ι h ∈ (IsLocalRing.maximalIdeal S) ^ (ν + n) := by
    rw [hmax, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hhQ
  obtain ⟨m, F, νf, hFJ, hFP, key, -⟩ := exists_system_mem_sup_of_isNormallyFlatAlongIdeal S Jq Pq
    (Ideal.map_mono hJP) hflat'
  have hcore := lambdaPiece_mem_grIdeal_of_isNormallyFlatAlongIdeal S Jq Pq
    (Ideal.map_mono hJP) hPqQ hflat' ⟨m, F, νf, hFJ, hFP, key⟩ (fun j => ι (y j)) hqrS hzS ν n
    hgJ' hgP' hΦ'
  have hxS := (ofGrPiece_mem_grIdeal_iff_mem_grIdealPiece Jq _ _ _).mp hcore
  have heq := ofGrPiece_lambdaPiece_eq_mk Pq (IsLocalRing.maximalIdeal S) hPqQ (fun j => ι (y j))
    hqrS hzS ν n (grModMap_bijective_of_isRegularLocalRing_quotient Pq _ ν n) hgP' hΦ' hhY hghS hhQS
  have hxeq : lambdaPiece Pq (IsLocalRing.maximalIdeal S) hPqQ (fun j => ι (y j)) hqrS hzS ν n
      (grModMap_bijective_of_isRegularLocalRing_quotient Pq _ ν n)
      (Submodule.Quotient.mk ⟨Submodule.Quotient.mk ⟨ι g, hgP'⟩, hΦ'⟩) =
      Submodule.Quotient.mk ⟨ι h, hhQS⟩ :=
    AssocGraded.ofGrPiece_injective _ _ (by rw [heq, AssocGraded.ofGrPiece_mk])
  rw [hxeq] at hxS
  obtain ⟨t, ht0, ht, hmem⟩ := exists_mul_mk_mem_grIdealPiece_of_map R J Q S
    (IsLocalRing.maximalIdeal S) Jq hmax.symm rfl hhQS hxS
  refine ⟨t, ht0, ?_⟩
  have h0 : algebraMap R (AssocGraded Q) t = AssocGraded.mk Q 0 t (by simp) := rfl
  rw [h0, AssocGraded.mk_mul_mk]
  have hfin := (ofGrPiece_mem_grIdeal_iff_mem_grIdealPiece J Q (ν + n) _).mpr hmem
  rw [AssocGraded.ofGrPiece_mk] at hfin
  convert hfin using 2
  simp

/-- Lemma 10, p. 199, in the paper's form, with `λ` constructed: "Notation and assumptions being as
above, let O = R/J, P̄ = P/J, and Q̄ = Q/J. Let us fix an isomorphism λ : gr_Q(gr_P(R)) → gr_Q(R)
as above. Suppose gr_{P̄O_Q̄}(O_Q̄) be flat over O_Q̄/P̄O_Q̄. Then for every element g ∈ J, the
λ-image of the initial form of g in gr_Q(gr_P(R)) is contained in gr_Q(J, R)_Q."

Here `λ = ψ φ⁻¹` is `lambdaPiece` in double degree `(ν, n)`, and in each total degree `N` it is the
isomorphism `lambdaTotal` (`lambdaEquiv`) of `⊕_{p+n=N} gr^n_{Q/P}(gr^p_P(R))` onto `gr^N_Q(R)`:
`φ = grModMap` (`phiTotal`) is bijective since `R/P` is regular
(`grModMap_bijective_of_isRegularLocalRing_quotient`), `ψ = psiDeg` is bijective by Proposition 1,
and `λ φ = ψ` (`lambdaTotal_phiTotal_eqTensor`, `bijective_lambdaTotal_of_isRegularLocalRing`);
`Λ' = lamTensor` sends `[a] ⊗ [b]` to `α[a] · β*[b]`, where `β*` sends the class of `ȳ_j` to that
of `y_j` (`betaStarPiece`).  The `λ`-image of the initial form `Φ_*` of `g` is
`lambdaPiece … (doubleInitialFormPiece …)`; "`∈ gr_Q(J,R)_Q`" is "`t · (…) ∈ gr_Q(J,R)` for some
`t ∈ R − Q`" (`gr_Q(R)` is torsion-free over `R/Q`).

The proof is the printed one:
* "Since gr commutes with localization, we may assume that Q is the maximal ideal of R": `R` is
  replaced by `S = R_Q` and `J, P` by `JS, PS`, with the system `ι ∘ y`.  The case `Q` maximal is
  `lambdaPiece_mem_grIdeal_of_isNormallyFlatAlongIdeal`.  The passage between `R` and `R_Q` is
  `λ`'s defining property (`ofGrPiece_lambdaPiece_eq_mk`: `λ(Φ_*)` is the class of any
  `h ∈ (y)ⁿ Pᵛ` with `g - h ∈ Pᵛ⁺¹`, and `ι h` is such an element in `S`) together with
  "clearing denominators" (`exists_mul_mk_mem_grIdealPiece_of_map`).
* "by the assumption that gr_P(O) is flat over O/P, λ induces an isomorphism ψ': gr_Q(gr_P(O)) →
  gr_Q(O)": `λ' = ψ'φ'⁻¹` for `O`, `P̄`, `Q̄` and the classes `ȳ_j` is `lambdaPiece` for `O`
  (`φ'` is bijective because `gr_P̄(O)` is flat); it is bijective in each total degree
  (`bijective_lambdaTotal_quotient`, Proposition 1 for `O`, i.e. Cor. 1 of Th. 2).
* "we have the following commutative diagram" with the exact row `0 → gr_Q(J,R) → gr_Q(R) →
  gr_Q̄(O) → 0` (Lemma 5, `grPieceMapQuot_eq_zero_iff`): the right square is
  `grPieceMapQuot_lambdaPiece` (`betaDouble`, `λ ↦ λ'`), the top row `gr_Q(gr_P(J,R)) → gr_Q(gr_P(R))
  → gr_Q̄(gr_P̄(O))` is `alphaDouble`, `betaDouble` (`betaDouble_alphaDouble`: a complex).
* "Moreover, by Lemma 7 (footnote 43), if Φ is a form in gr_P(J,R), and if Φ ∈ Qⁿ gr_P(R), then
  Φ ∈ Qⁿ gr_P(J,R)": `mem_pow_smul_top_grIdealModule_of_key`, from the system of Cor. 1 of Th. 2
  (`isNormallyFlatAlongIdeal_tfae_of_eq_maximalIdeal`) and the ring-level form of Lemma 7.
  "Hence, if g is an element of J, the initial form of g in gr_Q(gr_P(R)) is in the image of α."
* "It is clear from the diagram that λα(gr_Q(gr_P(J,R))) ⊆ gr_Q(J,R)": `lambdaPiece_mem_grIdeal_of_diagram`
  (`γ λ = λ' β` and `β α = 0`, so `λ α(x) ∈ ker γ = gr_Q(J,R)`).

Formalization note (encoding): the graded objects `gr_Q(gr_P(R))`, `gr_Q(R)`, … are read degreewise
(`gr^n_{Q/P}(gr^ν_P(R))` in double degree `(ν, n)`, `GrPiece Q N` in total degree `N`); `φ`, `ψ`, `λ`
are maps of modules in each (total) degree.  The diagram is
formed in each double degree.

Deviation from the paper (statement modified): `λ` depends on `(y₁, …, y_s)`; the lemma is stated
for every system `y` whose residue classes in `R/P` generate `Q/P` with `s = spanFinrank (Q/P)` (a
minimal base), and `λ` is given in each double degree `(ν, n)`; the class `Φ_*` is formed from
`ν = ν_P(g)` and `n = ν_{Q/P}(Φ)` (for `Q` maximal the diagram argument works for every `n` with
`[g] ∈ Qⁿ grᵛ_P(R)`, `lambdaPiece_mem_grIdeal_of_isNormallyFlatAlongIdeal`).

Deviation from the paper (gap filled): that the classes of a minimal base are quasi-regular in
`R/P`, so that `β*` and `λ` exist, is not stated in the paper (see
`isQuasiRegular_mk_of_span_eq_map_of_spanFinrank`); "since gr commutes with localization" is not
justified in the paper: here `λ` for `R_Q` is `λ` for `R` carried along `R → R_Q`
(`ofGrPiece_lambdaPiece_eq_mk`, the family `ι ∘ y` stays quasi-regular, `isQuasiRegular_map_localization`),
and `gr_{QR_Q}(JR_Q, R_Q) = gr_Q(J,R)_Q` is used as "`ψ ∈ gr_{QR_Q}(JR_Q, R_Q)` gives `t ψ ∈ gr_Q(J,R)`
for some `t ∉ Q`" (clearing denominators). -/
@[blueprint "lem:II.3-10"
  (statement := /-- Let $R$ be a regular local ring, $J$ an ideal in $R$, $P$ and $Q$ prime
    ideals in $R$ such that $Q\supseteq P\supseteq J$ and that $R/P$ and $R/Q$ are both regular.
    Let $(y_1,\dots,y_s)$ be a system of elements of $R$ whose residue classes in $R/P$ form a
    minimal base of $Q/P$, and $\lambda\colon\operatorname{gr}_Q(\operatorname{gr}_P(R))\to
    \operatorname{gr}_Q(R)$ the isomorphism determined by it (p.~198). Let $O=R/J$,
    $\bar P=P/J$, and $\bar Q=Q/J$. Suppose $\operatorname{gr}_{\bar PO_{\bar Q}}(O_{\bar Q})$
    is flat over $O_{\bar Q}/\bar PO_{\bar Q}$. Then for every element $g\in J$, the
    $\lambda$-image of the initial form of $g$ in $\operatorname{gr}_Q(\operatorname{gr}_P(R))$
    (\cref{def:II.3-double-initial-form}) is contained in $\operatorname{gr}_Q(J,R)_Q$.
    (Lemma 10, p.~199.)

    \textbf{Formalization note (encoding).} $\lambda=\Lambda'\Lambda^{-1}$ is constructed in each
    double degree $(\nu,n)$ and is an isomorphism in each total degree: $\Lambda\colon
    \operatorname{gr}^0_Q(\operatorname{gr}^\nu_P(R))
    \otimes\operatorname{gr}^n_{Q/P}(R/P)\to\operatorname{gr}^n_Q(\operatorname{gr}^\nu_P(R))$
    is the canonical isomorphism and $\Lambda'$ sends $[a]\otimes[b]$ to $\alpha[a]\,\beta^*[b]$
    in $\operatorname{gr}^{\nu+n}_Q(R)$, $\beta^*$ sending the class of $\bar y_j$ to that of
    $y_j$; the initial form $\Phi_*$ of $g$ is the class of the form $[g]$ of degree $\nu=\nu_P(g)$
    in $\operatorname{gr}^n_Q(\operatorname{gr}^\nu_P(R))$, $n=\nu_{Q/P}(\Phi)$. ``$\in
    \operatorname{gr}_Q(J,R)_Q$'' for an element $\varphi$ of $\operatorname{gr}_Q(R)$ is
    transcribed as ``$t\varphi\in\operatorname{gr}_Q(J,R)$ for some $t\in R-Q$''. The graded
    objects are read degreewise; the multiplicativity of $\varphi$, $\psi$, $\lambda$ is not
    recorded.

    \textbf{Deviation from the paper (statement modified).} $\lambda$ is given in each double
    degree and for every minimal base $(y_j)$ of $Q/P$ (encoded as: the $\bar y_j$ generate
    $Q/P$ and $s$ is the minimal number of generators). -/)
  (proof := /-- Since $\operatorname{gr}$ commutes with localization, we may assume that $Q$ is
    the maximal ideal of $R$. Then, by the assumption that $\operatorname{gr}_P(O)$ is flat over
    $O/P$, $\lambda$ induces an isomorphism $\psi'\colon\operatorname{gr}_Q(\operatorname{gr}_P(O))
    \to\operatorname{gr}_Q(O)$ of graded $O/Q$-algebras (\cref{cor:II.2-thm2-1}), and we have a
    commutative diagram with exact rows
    $\operatorname{gr}_Q(\operatorname{gr}_P(J,R))\to\operatorname{gr}_Q(\operatorname{gr}_P(R))\to
    \operatorname{gr}_Q(\operatorname{gr}_P(O))\to0$ and $0\to\operatorname{gr}_Q(J,R)\to
    \operatorname{gr}_Q(R)\to\operatorname{gr}_Q(O)\to0$ (the second is \cref{lem:II.2-5}).
    Moreover, by \cref{lem:II.2-7}, if $\Phi$ is a form in $\operatorname{gr}_P(J,R)$ and
    $\Phi\in Q^n\operatorname{gr}_P(R)$, then $\Phi\in Q^n\operatorname{gr}_P(J,R)$. Hence, if $g$
    is an element of $J$, the initial form of $g$ in $\operatorname{gr}_Q(\operatorname{gr}_P(R))$
    is in the image of $\alpha$. It is clear from the diagram that
    $\lambda\alpha(\operatorname{gr}_Q(\operatorname{gr}_P(J,R)))\subseteq\operatorname{gr}_Q(J,R)$.

    The Lean proof follows this argument. The localization $R\to R_Q$ carries $\lambda$ along (it
    is characterized by sending the class of $\bar y_j$ to that of $y_j$, so the $\lambda$-image of
    $\Phi_*$ is the class of any $h\in(y)^nP^\nu$ with $g-h\in P^{\nu+1}$), and the membership in
    $\operatorname{gr}_{QR_Q}(JR_Q,R_Q)$ is turned into $t\varphi\in\operatorname{gr}_Q(J,R)$ with
    $t\in R-Q$ by clearing denominators. For $Q$ maximal, $\psi'=\lambda'\varphi'$ is built for
    $O$ (with $\varphi'$ bijective by flatness and $\psi'$ bijective in every total degree), the
    right-hand square commutes because $\lambda$ and $\lambda'$ are both determined by sending the
    class of $\bar y_j$ to that of $y_j$ and its image, the top row is a complex, Lemma 7
    (footnote 43, via \cref{cor:II.2-thm2-1}) puts the initial form of $g$ into the image of
    $\alpha$, and the diagram gives $\gamma\lambda\alpha=\lambda'\beta\alpha=0$, i.e.
    $\lambda\alpha(\cdot)\in\ker\gamma=\operatorname{gr}_Q(J,R)$ by \cref{lem:II.2-5}.

    \textbf{Deviation from the paper (gap filled).} ``Since gr commutes with localization, we may
    assume that $Q$ is the maximal ideal of $R$'' is used without justification; in Lean
    $\lambda$ for $R_Q$ is shown to be $\lambda$ for $R$ carried along $R\to R_Q$ (the family
    $\iota y$ stays quasi-regular) and clearing denominators transports the conclusion. That the
    classes of a minimal base of $Q/P$ are quasi-regular in $R/P$, so that $\beta^*$ and $\lambda$
    exist, is not stated in the paper. -/)
  (latexEnv := "lemma")]
theorem exists_mul_mem_grIdeal_lambdaPiece [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (J P Q : Ideal R)
    [P.IsPrime] [Q.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)]
    (hJP : J ≤ P) (hPQ : P ≤ Q) [(Q.map (Ideal.Quotient.mk J)).IsPrime]
    (hflat : IsNormallyFlatAlongIdeal ((P.map (Ideal.Quotient.mk J)).map
      (algebraMap (R ⧸ J) (Localization.AtPrime (Q.map (Ideal.Quotient.mk J))))))
    {s : ℕ} (y : Fin s → R)
    (hy : Ideal.span (Set.range fun i => Ideal.Quotient.mk P (y i)) = Q.map (Ideal.Quotient.mk P))
    (hs : s = (Q.map (Ideal.Quotient.mk P)).spanFinrank)
    {g : R} (hg : g ∈ J) {ν n : ℕ} (hν : Ideal.ordElem P g = ν)
    (hn : doubleOrd P Q (initialForm P g) = n) :
    ∃ t : R, t ∉ Q ∧ algebraMap R (AssocGraded Q) t * AssocGraded.ofGrPiece Q (ν + n)
      (lambdaPiece P Q hPQ y (isQuasiRegular_mk_of_span_eq_map_of_spanFinrank P Q hPQ y hy hs) hy
        ν n (grModMap_bijective_of_isRegularLocalRing_quotient P _ ν n)
        (doubleInitialFormPiece P Q ν n (Ideal.mem_pow_of_ordElem hν)
          (mk_mem_pow_smul_top_of_doubleOrd P Q hν hn))) ∈ grIdeal Q J := by
  exact exists_mul_mem_grIdeal_lambdaPiece_of_isQuasiRegular R J P Q hJP hPQ hflat y hy
    (isQuasiRegular_mk_of_span_eq_map_of_spanFinrank P Q hPQ y hy hs) hg
    (Ideal.mem_pow_of_ordElem hν) (mk_mem_pow_smul_top_of_doubleOrd P Q hν hn)

/-- The `λ`-image of the initial form is the class of `h`: the old (elementwise) formulation of
Lemma 10, `exists_mul_mem_grIdeal_of_isLambdaImage_of_span_eq_map`, follows from the paper-form
`exists_mul_mem_grIdeal_lambdaPiece` (`ofGrPiece_lambdaPiece_eq_mk`: `λ` sends the class of `ȳ_j` to
that of `y_j`). -/
theorem exists_mul_mem_grIdeal_of_isLambdaImage_of_lambdaPiece [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (J P Q : Ideal R)
    [P.IsPrime] [Q.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)]
    (hJP : J ≤ P) (hPQ : P ≤ Q) [(Q.map (Ideal.Quotient.mk J)).IsPrime]
    (hflat : IsNormallyFlatAlongIdeal ((P.map (Ideal.Quotient.mk J)).map
      (algebraMap (R ⧸ J) (Localization.AtPrime (Q.map (Ideal.Quotient.mk J))))))
    {s : ℕ} (y : Fin s → R)
    (hy : Ideal.span (Set.range fun i => Ideal.Quotient.mk P (y i)) = Q.map (Ideal.Quotient.mk P))
    (hs : s = (Q.map (Ideal.Quotient.mk P)).spanFinrank)
    (g : R) (hg : g ∈ J) (ν n : ℕ) (z : AssocGraded Q)
    (hz : IsLambdaImage P Q (Ideal.span (Set.range y)) g ν n z) :
    ∃ t : R, t ∉ Q ∧ algebraMap R (AssocGraded Q) t * z ∈ grIdeal Q J := by
  obtain ⟨hν, hn, h, hh, hgh, hQ, rfl⟩ := hz
  obtain ⟨t, ht0, ht⟩ := exists_mul_mem_grIdeal_lambdaPiece R J P Q hJP hPQ hflat y hy hs hg hν hn
  refine ⟨t, ht0, ?_⟩
  rwa [ofGrPiece_lambdaPiece_eq_mk P Q hPQ y
    (isQuasiRegular_mk_of_span_eq_map_of_spanFinrank P Q hPQ y hy hs) hy ν n _
    (Ideal.mem_pow_of_ordElem hν) (mk_mem_pow_smul_top_of_doubleOrd P Q hν hn) hh hgh hQ] at ht

/-- Lemma 10, p. 199: "Notation and assumptions being as above, let O = R/J, P̄ = P/J, and
Q̄ = Q/J. Let us fix an isomorphism λ : gr_Q(gr_P(R)) → gr_Q(R) as above. Suppose
gr_{P̄O_Q̄}(O_Q̄) be flat over O_Q̄/P̄O_Q̄. Then for every element g ∈ J, the λ-image of the initial
form of g in gr_Q(gr_P(R)) is contained in gr_Q(J, R)_Q."

This is the elementwise form of Lemma 10 (`λ` is encoded by its values on initial forms,
`IsLambdaImage`), kept as a statement of its own (Theorem 3 uses the paper-form Lemma 10 directly,
`exists_mul_mem_grIdeal_lambdaPiece_of_isQuasiRegular`).  It is derived from the paper-form
`exists_mul_mem_grIdeal_lambdaPiece` (blueprint `lem:II.3-10`, the printed proof with `λ`
constructed): the `λ`-image of the initial form of `g` is the class in `Qᵛ⁺ⁿ/Qᵛ⁺ⁿ⁺¹` of any
`h ∈ Yⁿ Pᵛ` with `g - h ∈ Pᵛ⁺¹` (`ofGrPiece_lambdaPiece_eq_mk`: `λ` sends the class of `ȳ_j` to
that of `y_j`).

Here (from the paragraph preceding the lemma) `R` is a regular local ring, `J` an ideal, `P ⊆ Q`
primes with `J ⊆ P` and `R/P`, `R/Q` regular.

Formalization note (encoding): "gr_{P̄O_Q̄}(O_Q̄) is flat over O_Q̄/P̄O_Q̄" is
`IsNormallyFlatAlongIdeal` of `P̄O_Q̄` in `O_Q̄ = Localization.AtPrime Q̄`, as in Theorem 3; "`z`
is contained in `gr_Q(J, R)_Q`" for `z ∈ gr_Q(R)` is "there is `t ∈ R - Q` with `t z ∈
gr_Q(J, R)`" (`gr_Q(R)` is torsion-free over `R/Q`, so `gr_Q(R) → gr_Q(R)_Q` is injective and
this is membership in the localization; Lemma 11 turns it into `z ∈ gr_Q(J, R)` when
`gr_{Q̄}(O)` is flat over `O/Q̄`).

Deviation from the paper (statement modified): the paper says "Let us fix an isomorphism
λ : gr_Q(gr_P(R)) → gr_Q(R) as above", where λ "depends upon the choice of the system
(y₁, …, y_s)".  In this node `λ` is not mentioned; the lemma is stated for the values of `λ` on
the initial forms of elements `g ∈ J` (`IsLambdaImage`: the class in `Qᵛ⁺ⁿ/Qᵛ⁺ⁿ⁺¹` of any
`h ∈ Yⁿ Pᵛ` with `g - h ∈ Pᵛ⁺¹`, `Y = (y₁, …, y_s)R`, which is how λ acts on classes), for every
"system of elements (y₁, …, y_s) of R such that their residue classes in R/P form a minimal
base of Q/P" (`hy`, `hs`: the classes generate `Q/P` and `s = spanFinrank (Q/P)`).  The
construction of `λ` and the printed proof are in `exists_mul_mem_grIdeal_lambdaPiece`. -/
@[blueprint "lem:II.3-10-elementwise"
  (statement := /-- Let $R$ be a regular local ring, $J$ an ideal in $R$, $P$ and $Q$ prime
    ideals in $R$ such that $Q\supseteq P\supseteq J$ and that $R/P$ and $R/Q$ are both regular.
    Let $(y_1,\dots,y_s)$ be a system of elements of $R$ whose residue classes in $R/P$ form a
    minimal base of $Q/P$, and $\lambda\colon\operatorname{gr}_Q(\operatorname{gr}_P(R))\to
    \operatorname{gr}_Q(R)$ the isomorphism determined by it (p.~198). Let $O=R/J$,
    $\bar P=P/J$, and $\bar Q=Q/J$. Suppose $\operatorname{gr}_{\bar PO_{\bar Q}}(O_{\bar Q})$
    is flat over $O_{\bar Q}/\bar PO_{\bar Q}$. Then for every element $g\in J$, the
    $\lambda$-image of the initial form of $g$ in $\operatorname{gr}_Q(\operatorname{gr}_P(R))$
    (\cref{def:II.3-double-initial-form}) is contained in $\operatorname{gr}_Q(J,R)_Q$.
    (Lemma 10, p.~199.)

    \textbf{Formalization note (encoding).} ``$\in\operatorname{gr}_Q(J,R)_Q$'' for an element
    $\varphi$ of $\operatorname{gr}_Q(R)$ is transcribed as ``$t\varphi\in\operatorname{gr}_Q(J,R)$
    for some $t\in R-Q$''.

    \textbf{Deviation from the paper (statement modified).} The paper says ``Let us fix an
    isomorphism $\lambda\colon\operatorname{gr}_Q(\operatorname{gr}_P(R))\to\operatorname{gr}_Q(R)$
    as above'', determined by a system $(y_1,\dots,y_s)$ whose residue classes in $R/P$ form a
    minimal base of $Q/P$. In this node $\lambda$ is not mentioned; the lemma is stated for the values
    of $\lambda$ on initial forms (its construction is \cref{lem:II.3-10}), for every such system: if $\nu=\nu_P(g)$,
    $n=\nu_{Q/P}(\Phi)$ for the initial form $\Phi$ of $g$ in $\operatorname{gr}_P(R)$, the
    $\lambda$-image of $\Phi_*$ is the class in $Q^{\nu+n}/Q^{\nu+n+1}$ of any
    $h\in(y_1,\dots,y_s)^nP^\nu$ with $g-h\in P^{\nu+1}$. -/)
  (proof := /-- This is \cref{lem:II.3-10}: by definition $\lambda$ sends the class of $\bar y_j$
    to that of $y_j$, so the $\lambda$-image of the initial form $\Phi_*$ of $g$ in
    $\operatorname{gr}_Q(\operatorname{gr}_P(R))$ is the class in $Q^{\nu+n}/Q^{\nu+n+1}$ of any
    $h\in(y_1,\dots,y_s)^nP^\nu$ with $g-h\in P^{\nu+1}$; the paper-form Lemma 10 gives
    $t\cdot\lambda(\Phi_*)\in\operatorname{gr}_Q(J,R)$ for some $t\in R-Q$. -/)
  (latexEnv := "lemma")]
theorem exists_mul_mem_grIdeal_of_isLambdaImage_of_span_eq_map [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (J P Q : Ideal R)
    [P.IsPrime] [Q.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)]
    (hJP : J ≤ P) (hPQ : P ≤ Q) [(Q.map (Ideal.Quotient.mk J)).IsPrime]
    (hflat : IsNormallyFlatAlongIdeal ((P.map (Ideal.Quotient.mk J)).map
      (algebraMap (R ⧸ J) (Localization.AtPrime (Q.map (Ideal.Quotient.mk J))))))
    {s : ℕ} (y : Fin s → R)
    (hy : Ideal.span (Set.range fun i => Ideal.Quotient.mk P (y i)) = Q.map (Ideal.Quotient.mk P))
    (hs : s = (Q.map (Ideal.Quotient.mk P)).spanFinrank)
    (g : R) (hg : g ∈ J) (ν n : ℕ) (z : AssocGraded Q)
    (hz : IsLambdaImage P Q (Ideal.span (Set.range y)) g ν n z) :
    ∃ t : R, t ∉ Q ∧ algebraMap R (AssocGraded Q) t * z ∈ grIdeal Q J :=
  exists_mul_mem_grIdeal_of_isLambdaImage_of_lambdaPiece R J P Q hJP hPQ hflat y hy hs g hg ν n z hz

end Lemma10Main

section Theorem3Main

/-! ### Theorem 3 (ii) ⟹ (i): polynomial description of `gr_Q(R)`, coefficients, limits
(auxiliary lemmas for pp. 200–203) -/

section Theorem3Aux

open MvPolynomial IsLocalRing

section ClaimD

private theorem zFormHom_C_algebraMap' {A : Type u} [CommRing A] (Q : Ideal A) {ι : Type*}
    (z : ι → A) (hz : ∀ i, z i ∈ Q ^ 1) (t : A) :
    zFormHom Q z hz (C (Ideal.Quotient.mk Q t)) = algebraMap A (AssocGraded Q) t := by
  rw [IsScalarTower.algebraMap_apply A (A ⧸ Q) (AssocGraded Q) t]
  simp [zFormHom]

private theorem zFormHom_X' {A : Type u} [CommRing A] (Q : Ideal A) {ι : Type*}
    (z : ι → A) (hz : ∀ i, z i ∈ Q ^ 1) (i : ι) :
    zFormHom Q z hz (X i) = AssocGraded.mk Q 1 (z i) (hz i) := by
  simp [zFormHom]

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (J P Q : Ideal R) [Q.IsPrime] [IsRegularLocalRing (R ⧸ Q)] {s r : ℕ} (y : Fin s → R) (z : Fin r → R)
  (hy : ∀ i, y i ∈ Q ^ 1) (hz : ∀ i, z i ∈ Q ^ 1)

include hy hz in
/-- Theorem 3, p. 201: the passage to `K[Z, Y]`, in the paper's order.  Here `S = R_Q`, with maximal
ideal `QR_Q` (`IsLocalization.AtPrime.map_eq_maximalIdeal`), and `K = S/QS`, the residue field of
`R_Q`, is the field of quotients of `R'' = R/Q`: `residueMap` is injective and every element of `K`
is a fraction of elements of `R''` (`residueMap_injective`, `exists_residueMap_mul_eq`).
* "Let `K` denote the field of quotients of `R''`.  Then we get in a natural way the
  identification `gr_Q(R)_Q = gr_{QR_Q}(R_Q) = K[Z_1, …, Z_r, Y_1, …, Y_s]`": the ring homomorphism
  `ι : gr_Q(R) → gr_{QR_Q}(R_Q)` induced by `R → R_Q` (`AssocGraded.mapLE`), the bijection
  `Θ : K[Z][Y] → gr_{QR_Q}(R_Q)` (`yzFormHom_bijective`, the family `(y, z)` being quasi-regular in
  `R_Q` by `isQuasiRegular_map_localization`), and `Θ ∘ ρ = ι ∘ (R''[Z][Y] → gr_Q(R))` for the
  coefficientwise map `ρ : R''[Z][Y] → K[Z][Y]` (`hsq`); the localization `gr_Q(R)_Q` of
  `gr_Q(R)` at `R - Q` is identified with `gr_{QR_Q}(R_Q)` by the ring isomorphism `e0` (the map
  `IsLocalization.lift ι`: injective because `ι` is, `hιinj`, and surjective because `K` is the field of
  quotients of `R''`, `exists_residueMap_mul_eq`, and `gr_{QR_Q}(R_Q) = Θ(K[Z][Y])`).
* "Applying Corollary 1 of Theorem 2, §2, to `{R_Q, JR_Q, PR_Q, O_Q}`, we get a system of elements
  `h_j` of `JR_Q` such that `ν_{PR_Q}(h_j) = ν_{QR_Q}(h_j)` for all `j` and the initial forms of
  `h_j` in `gr_{QR_Q}(R_Q) = K[Z, Y]` generate the ideal `gr_{QR_Q}(JR_Q, R_Q) = gr_Q(J, R)_Q`":
  the hypothesis `hsys` (`hasInitialFormSystem_localization`).
* "The initial forms of such `h_j` in `K[Z, Y]` are obviously forms only in `Z_1, …, Z_r`.  Thus the
  ideal `gr_Q(J, R)_Q` in `K[Z, Y]` is generated by forms only in `Z_1, …, Z_r`": `hform` (gap
  filled: `h_j ∈ (PR_Q)^{ν}`, `PR_Q = (z)R_Q`, and `gr_Q(J, R)_Q = gr_{QR_Q}(JR_Q, R_Q)` is proved
  in both directions: `ψ ∈ gr_Q(J, R) ⟹ Θ(ρψ) ∈ gr_{QR_Q}(JR_Q, R_Q)` is `h1`, and the forms `θ_l`
  lie in `e0(gr_Q(J, R)_Q)`, `hθext`: `Θ(θ_l)` times the unit `ι(u_l)` is `ι(A_l)` with
  `A_l ∈ gr_Q(J, R)`, the third item of `hform`, from `h_j = j'/t` and the regularity of `R/Q`).
* "This implies that, if `ψ` is any element of `gr_Q(J, R)`, and if `ψ` is written in the form
  `Σ ψ_i N_i` with `ψ_i ∈ R''[Z]` and with distinct monomials `N_i` in the `Y_j`, then all the
  `ψ_i` belong to `gr_Q(J, R)_Q ∩ K[Z]` [the printed text has `= K[Z]`], because `K[Z, Y]` is a free
  `K[Z]`-module generated by all the distinct monomials in the `Y_j`": `hcoef` (the coefficient
  of a combination `Σ_l a_l θ_l` of forms in `Z` is the combination of the coefficients).
* "By Lemma 11, `gr_Q(J, R)_Q ∩ R''[Z, Y] = gr_Q(J, R)`, and therefore `gr_Q(J, R)_Q ∩ R''[Z] =
  gr_Q(J, R) ∩ R''[Z]`.  It follows that all the `ψ_i` belong to `gr_Q(J, R) ∩ R''[Z]`": the
  element `ψ_m ∈ R''[Z] ⊆ K[Z]` is a `K[Z]`-combination of the `Θ(θ_l)`, hence `ι(ψ_m)` lies in
  the ideal generated by `e0(gr_Q(J, R)_Q)` (`hfinal`), i.e. `ψ_m ∈ gr_Q(J, R)_Q` (`e0` is a ring
  isomorphism, `Ideal.comap_map_of_bijective`), and Lemma 11 in its printed intersection form
  (`mem_grIdeal_of_algebraMap_mem_map`, from `grIdeal_localization_inf_range_eq`, blueprint
  `lem:II.3-11-intersection`) gives `ψ_m ∈ gr_Q(J, R)`; no denominators of `K` are cleared. -/
private theorem coeff_mem_grIdeal_of_hasInitialFormSystem_localization
    (hqr : IsQuasiRegular (Sum.elim y z)) (hI : Ideal.span (Set.range (Sum.elim y z)) = Q)
    (hP : Ideal.span (Set.range z) = P)
    (hbij : Function.Bijective (yzFormHom Q y z hy hz))
    (hint : ∀ φ : AssocGraded Q, algebraMap (AssocGraded Q)
      (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl)) φ ∈
      (grIdeal Q J).map (algebraMap (AssocGraded Q)
        (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))) →
      φ ∈ grIdeal Q J)
    (hsys : HasInitialFormSystem (J.map (algebraMap R (Localization.AtPrime Q)))
      (P.map (algebraMap R (Localization.AtPrime Q))) (maximalIdeal (Localization.AtPrime Q)))
    {k : ℕ} {j : R} (hj : j ∈ J) (hjk : j ∈ Q ^ k)
    {ψ : MvPolynomial (Fin s) (MvPolynomial (Fin r) (R ⧸ Q))}
    (hψ : yzFormHom Q y z hy hz ψ = AssocGraded.mk Q k j hjk) (m : Fin s →₀ ℕ) :
    zFormHom Q z hz (ψ.coeff m) ∈ grIdeal Q J := by
  classical
  -- `S = R_Q`, with maximal ideal `QR_Q`, and `K = R_Q/QR_Q`, the field of quotients of `R''`
  set S := Localization.AtPrime Q with hS
  set mS : Ideal S := maximalIdeal S with hmS
  have hmax : mS = Q.map (algebraMap R S) :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal Q S).symm
  set yS : Fin s → S := fun i => algebraMap R S (y i) with hyS_def
  set zS : Fin r → S := fun i => algebraMap R S (z i) with hzS_def
  have hyS : ∀ i, yS i ∈ mS ^ 1 := fun i => by
    rw [pow_one, hmax]
    exact Ideal.mem_map_of_mem _ (by simpa using hy i)
  have hzS : ∀ i, zS i ∈ mS ^ 1 := fun i => by
    rw [pow_one, hmax]
    exact Ideal.mem_map_of_mem _ (by simpa using hz i)
  have hfun : (fun i => algebraMap R S (Sum.elim y z i)) = Sum.elim yS zS := by
    funext i
    rcases i with i | i <;> rfl
  have hqrS : IsQuasiRegular (Sum.elim yS zS) := by
    rw [← hfun]
    exact isQuasiRegular_map_localization Q (Sum.elim y z) hqr hI S
  have hIS : Ideal.span (Set.range (Sum.elim yS zS)) = mS := by
    have h := congrArg (Ideal.map (algebraMap R S)) hI
    rw [Ideal.map_span, ← Set.range_comp] at h
    rw [hmax, ← h, ← hfun]
    rfl
  -- "`gr_{QR_Q}(R_Q) = K[Z, Y]`"
  have hbijS := yzFormHom_bijective mS yS zS hyS hzS hqrS hIS
  -- "`gr_Q(R)_Q = gr_{QR_Q}(R_Q)`": the natural map `gr_Q(R) → gr_{QR_Q}(R_Q)`
  let ι : AssocGraded Q →+* AssocGraded mS :=
    AssocGraded.mapLE (algebraMap R S) Q mS (by rw [hmax])
  let κ := residueMap Q
  let ρ : MvPolynomial (Fin s) (MvPolynomial (Fin r) (R ⧸ Q)) →+*
      MvPolynomial (Fin s) (MvPolynomial (Fin r) (S ⧸ mS)) :=
    MvPolynomial.map (MvPolynomial.map κ)
  let Θ := yzFormHom mS yS zS hyS hzS
  have hzsq : ∀ a : MvPolynomial (Fin r) (R ⧸ Q),
      zFormHom mS zS hzS (MvPolynomial.map κ a) = ι (zFormHom Q z hz a) := by
    intro a
    have : (zFormHom mS zS hzS).comp (MvPolynomial.map κ) = ι.comp (zFormHom Q z hz) := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
      · obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
        simp only [RingHom.comp_apply, MvPolynomial.map_C]
        rw [residueMap_mk]
        rw [zFormHom_C_algebraMap', zFormHom_C_algebraMap', AssocGraded.mapLE_algebraMap]
      · simp only [RingHom.comp_apply, MvPolynomial.map_X]
        rw [zFormHom_X', zFormHom_X', AssocGraded.mapLE_mk]
    exact congrArg (fun f => f a) this
  have hsq : ∀ ψ, Θ (ρ ψ) = ι (yzFormHom Q y z hy hz ψ) := by
    intro ψ
    have : Θ.comp ρ = ι.comp (yzFormHom Q y z hy hz) := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · simp only [RingHom.comp_apply, ρ, MvPolynomial.map_C, Θ, yzFormHom_C]
        exact hzsq a
      · simp only [RingHom.comp_apply, ρ, MvPolynomial.map_X, Θ, yzFormHom_X]
        rw [AssocGraded.mapLE_mk]
    exact congrArg (fun f => f ψ) this
  have hρinj : Function.Injective ρ :=
    MvPolynomial.map_injective _ (MvPolynomial.map_injective _ (residueMap_injective Q))
  -- the class of `j/1`
  have h1 : Θ (ρ ψ) ∈ grIdeal mS (J.map (algebraMap R S)) := by
    rw [hsq, hψ, AssocGraded.mapLE_mk]
    exact mk_mem_grIdeal mS (Ideal.mem_map_of_mem _ hj) _
  -- "Applying Corollary 1 of Theorem 2, §2, to `{R_Q, JR_Q, PR_Q, O_Q}`"
  obtain ⟨M, f, hfJ, h₁, h₂⟩ := hsys
  have hPS : P.map (algebraMap R S) = Ideal.span (Set.range zS) := by
    rw [← hP, Ideal.map_span, ← Set.range_comp]
    rfl
  -- the initial forms of the `f_l` are forms in `Z` only, and `gr_Q(J, R)_Q` contains them
  have hform : ∀ l : Fin M, ∃ (θ : MvPolynomial (Fin r) (S ⧸ mS)) (u : R)
      (A : MvPolynomial (Fin r) (R ⧸ Q)), Θ (C θ) = initialForm mS (f l) ∧ u ∉ Q ∧
      zFormHom Q z hz A ∈ grIdeal Q J ∧
      MvPolynomial.map κ A = C (κ (Ideal.Quotient.mk Q u)) * θ := by
    intro l
    by_cases hord : Ideal.ordElem mS (f l) = ⊤
    · refine ⟨0, 1, 0, ?_, ?_, ?_, ?_⟩
      · simp [initialForm, hord]
      · exact Q.primeCompl.one_mem
      · simp
      · simp
    · obtain ⟨ν, hν⟩ := ENat.ne_top_iff_exists.mp hord
      have hfν : f l ∈ mS ^ ν := Ideal.mem_pow_of_ordElem hν.symm
      have hfP : f l ∈ (P.map (algebraMap R S)) ^ ν :=
        Ideal.mem_pow_of_ordElem (by rw [← h₁ l]; exact hν.symm)
      rw [hPS] at hfP
      obtain ⟨B, hBh, hBe⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous zS (f l)).mp hfP
      have hBQ : eval zS B ∈ mS ^ ν := eval_mem_pow_of_isHomogeneous mS zS hzS hBh
      have hini : initialForm mS (f l) = AssocGraded.mk mS ν (f l) hfν :=
        initialForm_eq_mk mS hν.symm
      have hΘθ : Θ (C (B.map (Ideal.Quotient.mk mS))) = initialForm mS (f l) := by
        rw [hini, yzFormHom_C, zFormHom_map_of_isHomogeneous mS zS hzS hBh]
        exact mk_congr_of_eq mS rfl hBe _ _
      -- `f_l = j'/t` with `j' ∈ J`, `t ∈ R - Q`
      obtain ⟨⟨a, t⟩, hat⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl S).mp (hfJ l)
      have hj'ν : (a : R) ∈ Q ^ ν := by
        have h2 : algebraMap R S (a : R) ∈ mS ^ ν := by
          rw [← hat]; exact Ideal.mul_mem_right _ _ hfν
        rw [hmax, ← Ideal.map_pow] at h2
        obtain ⟨u, hu0, hu⟩ :=
          (IsLocalization.algebraMap_mem_map_algebraMap_iff Q.primeCompl S _ _).mp h2
        exact mem_pow_of_mul_mem_pow_of_isRegularLocalRing_quotient Q inferInstance ν u a hu0 hu
      obtain ⟨ψ', hψ'⟩ := hbij.2 (AssocGraded.mk Q ν (a : R) hj'ν)
      have hΘψ' : Θ (ρ ψ') = Θ (C (C (κ (Ideal.Quotient.mk Q (t : R))) *
          B.map (Ideal.Quotient.mk mS))) := by
        rw [hsq, hψ', AssocGraded.mapLE_mk, C_mul, map_mul, hΘθ, yzFormHom_C, residueMap_mk,
          zFormHom_C_algebraMap', hini]
        have h0 : algebraMap S (AssocGraded mS) (algebraMap R S (t : R)) =
            AssocGraded.mk mS 0 (algebraMap R S (t : R)) (by simp) := rfl
        rw [h0, AssocGraded.mk_mul_mk]
        refine mk_congr_of_eq mS (zero_add ν).symm ?_ _ _
        rw [mul_comm]
        exact hat.symm
      have hρψ' := hbijS.1 hΘψ'
      have hc0 : MvPolynomial.map κ (ψ'.coeff 0) =
          C (κ (Ideal.Quotient.mk Q (t : R))) * B.map (Ideal.Quotient.mk mS) := by
        have := congrArg (fun p => p.coeff 0) hρψ'
        simpa [ρ, coeff_map, coeff_C] using this
      have hψ'C : ψ' = C (ψ'.coeff 0) := by
        apply hρinj
        rw [hρψ']
        simp only [ρ, MvPolynomial.map_C]
        rw [hc0]
      refine ⟨B.map (Ideal.Quotient.mk mS), t, ψ'.coeff 0, hΘθ, t.2, ?_, hc0⟩
      have hh := hψ'
      rw [hψ'C, yzFormHom_C] at hh
      rw [hh]
      exact mk_mem_grIdeal Q a.2 hj'ν
  choose θ u A hθ hu hAJ hAκ using hform
  -- "the ideal `gr_Q(J, R)_Q` in `K[Z, Y]` is generated by forms only in `Z`"
  have hψK : ρ ψ ∈ Ideal.span (Set.range fun l =>
      (C (θ l) : MvPolynomial (Fin s) (MvPolynomial (Fin r) (S ⧸ mS)))) := by
    have h3 : Θ (ρ ψ) ∈ Ideal.span (Set.range fun l => Θ (C (θ l))) := by
      simp only [hθ]
      rw [h₂]
      exact h1
    have h4 : Ideal.span (Set.range fun l => Θ (C (θ l))) =
        (Ideal.span (Set.range fun l =>
          (C (θ l) : MvPolynomial (Fin s) (MvPolynomial (Fin r) (S ⧸ mS))))).map Θ := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    rw [h4] at h3
    have h5 : ρ ψ ∈ Ideal.comap Θ (Ideal.map Θ (Ideal.span (Set.range fun l =>
        (C (θ l) : MvPolynomial (Fin s) (MvPolynomial (Fin r) (S ⧸ mS)))))) := h3
    rwa [Ideal.comap_map_of_bijective Θ hbijS] at h5
  -- "if `ψ = Σ ψ_i N_i` …, all the `ψ_i` belong to `gr_Q(J, R)_Q ∩ K[Z]`, because `K[Z, Y]` is a
  -- free `K[Z]`-module generated by the monomials in the `Y_j`"
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hψK
  have hcoef : MvPolynomial.map κ (ψ.coeff m) = ∑ l, (a l).coeff m * θ l := by
    have := congrArg (fun p => p.coeff m) ha
    have hl : ∀ l, (a l * C (θ l)).coeff m = (a l).coeff m * θ l := fun l => by
      rw [mul_comm, coeff_C_mul]
      exact mul_comm _ _
    simp only [coeff_sum, hl, ρ, coeff_map] at this
    exact this.symm
  -- "gr_Q(R)_Q = gr_{QR_Q}(R_Q)": the localization of `gr_Q(R)` at `R - Q` is identified with
  -- `gr_{QS}(S) = K[Z, Y]` through the map `ι`
  have hιinj : Function.Injective ι := by
    intro a b hab
    obtain ⟨ψa, rfl⟩ := hbij.2 a
    obtain ⟨ψb, rfl⟩ := hbij.2 b
    rw [← hsq, ← hsq] at hab
    exact congrArg (yzFormHom Q y z hy hz) (hρinj (hbijS.1 hab))
  have hunit : ∀ v : Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl, IsUnit (ι v) := by
    rintro ⟨_, t, ht, rfl⟩
    show IsUnit (ι (algebraMap R (AssocGraded Q) t))
    rw [AssocGraded.mapLE_algebraMap]
    exact (IsLocalization.map_units S (⟨t, ht⟩ : Q.primeCompl)).map (algebraMap S (AssocGraded mS))
  let e0 : Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl) →+*
      AssocGraded mS := IsLocalization.lift hunit
  have he0 : ∀ x, e0 (algebraMap (AssocGraded Q) _ x) = ι x := fun x =>
    IsLocalization.lift_eq hunit x
  have he0inj : Function.Injective e0 := by
    refine (IsLocalization.lift_injective_iff hunit).mpr fun x y => ⟨fun h => ?_, fun h => ?_⟩
    · rw [← he0, ← he0, h]
    · rw [hιinj h]
  -- surjectivity: `gr_{QS}(S) = Θ(K[Z][Y])` and `K` is the field of quotients of `R''`
  have hrangeι : ∀ x, ι x ∈ e0.range := fun x => ⟨_, he0 x⟩
  have hΘX : ∀ j, Θ (X j) = ι (AssocGraded.mk Q 1 (y j) (hy j)) := fun j => by
    simp only [Θ, yzFormHom_X]
    rw [AssocGraded.mapLE_mk]
  have hΘCX : ∀ i, Θ (C (X i)) = ι (AssocGraded.mk Q 1 (z i) (hz i)) := fun i => by
    simp only [Θ, yzFormHom_C]
    rw [zFormHom_X', AssocGraded.mapLE_mk]
  have hΘCC : ∀ t : R, Θ (C (C (κ (Ideal.Quotient.mk Q t)))) =
      ι (algebraMap R (AssocGraded Q) t) := by
    intro t
    have := hzsq (C (Ideal.Quotient.mk Q t))
    rw [MvPolynomial.map_C, zFormHom_C_algebraMap'] at this
    simp only [Θ, yzFormHom_C]
    exact this
  have hΘK : ∀ k, Θ (C (C k)) ∈ e0.range := by
    intro k
    obtain ⟨t, a, ht, hta⟩ := exists_residueMap_mul_eq Q k
    have hta' : κ (Ideal.Quotient.mk Q t) * k = κ (Ideal.Quotient.mk Q a) := hta
    have h3 : ι (algebraMap R (AssocGraded Q) a) =
        ι (algebraMap R (AssocGraded Q) t) * Θ (C (C k)) := by
      rw [← hΘCC a, ← hΘCC t, ← map_mul, ← C_mul, ← C_mul, hta']
    refine ⟨IsLocalization.mk' _ (algebraMap R (AssocGraded Q) a)
      (⟨algebraMap R (AssocGraded Q) t, t, ht, rfl⟩ :
        Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl), ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    exact h3
  have hrangeΘ : ∀ f, Θ f ∈ e0.range := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C p =>
      induction p using MvPolynomial.induction_on with
      | C k => exact hΘK k
      | add p q hp hq => rw [C_add, map_add]; exact add_mem hp hq
      | mul_X p i hp => rw [C_mul, map_mul, hΘCX]; exact mul_mem hp (hrangeι _)
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | mul_X f j hf => rw [map_mul, hΘX]; exact mul_mem hf (hrangeι _)
  have he0bij : Function.Bijective e0 :=
    ⟨he0inj, fun w => by
      obtain ⟨f, rfl⟩ := hbijS.2 w
      exact hrangeΘ f⟩
  -- "gr_{QR_Q}(JR_Q, R_Q) = gr_Q(J, R)_Q": the initial forms `Θ(θ_l)` lie in `gr_Q(J, R)_Q`
  have hθext : ∀ l, Θ (C (θ l)) ∈ Ideal.map e0 ((grIdeal Q J).map (algebraMap (AssocGraded Q)
      (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl)))) := by
    intro l
    have h0 := congrArg (zFormHom mS zS hzS) (hAκ l)
    rw [hzsq, map_mul] at h0
    have h1 : zFormHom mS zS hzS (C (κ (Ideal.Quotient.mk Q (u l)))) =
        ι (algebraMap R (AssocGraded Q) (u l)) := by
      have := hΘCC (u l)
      simp only [Θ, yzFormHom_C] at this
      exact this
    rw [h1] at h0
    -- `ι(u_l) · Θ(θ_l) = ι(A_l)`, `ι(u_l)` is a unit
    have hmem : ι (zFormHom Q z hz (A l)) ∈ Ideal.map e0 ((grIdeal Q J).map
        (algebraMap (AssocGraded Q) (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q)
          Q.primeCompl)))) := by
      rw [← he0]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hAJ l))
    obtain ⟨v, hv⟩ := (IsLocalization.map_units S (⟨u l, hu l⟩ : Q.primeCompl)).map
      (algebraMap S (AssocGraded mS))
    have hvι : (v : AssocGraded mS) = ι (algebraMap R (AssocGraded Q) (u l)) := by
      rw [hv, AssocGraded.mapLE_algebraMap]
    have h2 : Θ (C (θ l)) = (↑v⁻¹ : AssocGraded mS) * ι (zFormHom Q z hz (A l)) := by
      have h3 : zFormHom mS zS hzS (θ l) = Θ (C (θ l)) := by simp only [Θ, yzFormHom_C]
      rw [h3, ← hvι] at h0
      rw [h0, Units.inv_mul_cancel_left]
    rw [h2]
    exact Ideal.mul_mem_left _ _ hmem
  -- "all the `ψ_i` belong to `gr_Q(J, R)_Q ∩ K[Z]`": the element `ψ_m ∈ R''[Z] ⊆ K[Z]` is
  -- a combination of the `θ_l`
  have hfinal : Θ (C (MvPolynomial.map κ (ψ.coeff m))) ∈ Ideal.map e0 ((grIdeal Q J).map
      (algebraMap (AssocGraded Q) (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q)
        Q.primeCompl)))) := by
    have hCsum : (C (MvPolynomial.map κ (ψ.coeff m)) :
        MvPolynomial (Fin s) (MvPolynomial (Fin r) (S ⧸ mS))) =
        ∑ l, C ((a l).coeff m) * C (θ l) := by
      rw [hcoef, map_sum]
      exact Finset.sum_congr rfl fun l _ => C_mul
    rw [hCsum, map_sum]
    refine Ideal.sum_mem _ fun l _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (hθext l)
  have hψm : Θ (C (MvPolynomial.map κ (ψ.coeff m))) = e0 (algebraMap (AssocGraded Q) _
      (zFormHom Q z hz (ψ.coeff m))) := by
    rw [he0]
    simp only [Θ, yzFormHom_C]
    exact hzsq _
  rw [hψm] at hfinal
  have hext : algebraMap (AssocGraded Q) _ (zFormHom Q z hz (ψ.coeff m)) ∈ (grIdeal Q J).map
      (algebraMap (AssocGraded Q) (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q)
        Q.primeCompl))) := by
    have h5 : _ ∈ Ideal.comap e0 (Ideal.map e0 ((grIdeal Q J).map (algebraMap (AssocGraded Q)
      (Localization (Algebra.algebraMapSubmonoid (AssocGraded Q) Q.primeCompl))))) := hfinal
    rwa [Ideal.comap_map_of_bijective e0 he0bij] at h5
  -- "By Lemma 11, `gr_Q(J, R)_Q ∩ R''[Z, Y] = gr_Q(J, R)`"
  exact hint _ hext

end ClaimD

section Limit

variable {R : Type u} [CommRing R]

/-- A sequence with `seq (n+1) - seq n ∈ Iⁿ` converges in an `I`-adically complete ring:
`f - seq n ∈ Iⁿ` for all `n`. -/
private theorem exists_forall_sub_mem_pow_of_isAdicComplete (I : Ideal R) [IsAdicComplete I R]
    (seq : ℕ → R) (h : ∀ n, seq (n + 1) - seq n ∈ I ^ n) : ∃ f : R, ∀ n, f - seq n ∈ I ^ n := by
  have hmn : ∀ m n, m ≤ n → seq n - seq m ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have : seq (n + 1) - seq m = (seq (n + 1) - seq n) + (seq n - seq m) := by ring
      rw [this]
      exact add_mem (Ideal.pow_le_pow_right hmn (h n)) ih
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (M := R) seq (fun {m n} hmn' => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have := hmn m n hmn'
    exact (neg_sub (seq n) (seq m) ▸ (I ^ m).neg_mem this))
  refine ⟨L, fun n => ?_⟩
  have := (SModEq.sub_mem.mp (hL n))
  rw [smul_eq_mul, Ideal.mul_top] at this
  simpa using (I ^ n).neg_mem this

/-- Krull: in a noetherian local ring, `f ∈ I + Mⁿ` for all `n` implies `f ∈ I`. -/
private theorem mem_of_forall_mem_sup_pow_maximalIdeal [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (f : R) (h : ∀ n : ℕ, f ∈ I ⊔ maximalIdeal R ^ n) : f ∈ I := by
  by_cases hI : I = ⊤
  · rw [hI]; trivial
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  have hM : (maximalIdeal R).map (Ideal.Quotient.mk I) ≠ ⊤ := by
    rw [IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  have : Ideal.Quotient.mk I f ∈ ⨅ n : ℕ, ((maximalIdeal R).map (Ideal.Quotient.mk I)) ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) (h n)
    rw [Ideal.map_sup, Ideal.map_pow] at this
    have hI0 : I.map (Ideal.Quotient.mk I) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    rwa [hI0, bot_sup_eq] at this
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hM, Ideal.mem_bot,
    Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

end Limit

section Step

variable {R : Type u} [CommRing R]

private theorem prod_pow_mem_pow_degree {s : ℕ} (y : Fin s → R) (m : Fin s →₀ ℕ) :
    ∏ j, y j ^ m j ∈ Ideal.span (Set.range y) ^ m.degree := by
  classical
  rw [Finsupp.degree_eq_sum]
  have key : ∀ S : Finset (Fin s), ∏ j ∈ S, y j ^ m j ∈
      Ideal.span (Set.range y) ^ ∑ j ∈ S, m j := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self a)) _) ih
  exact key Finset.univ

/-- `P^d ∩ Q^k ⊆ Y^(k-d) P^d + P^(d+1)` for `k ≥ d`, `Q = P + Y` with independent bidegree
components (the paper's "g ∈ P^{ν_i} + Q^{ν_i+1}, hence d + μ > ν_i", p. 201). -/
private theorem inf_pow_le_pow_mul_sup_succ (P Y Q : Ideal R) (hQ : Q = P ⊔ Y)
    (hind : ∀ (m : ℕ) (s : Finset ℕ), (∀ a ∈ s, a ≤ m) → ∀ u : ℕ → R,
      (∀ a ∈ s, u a ∈ P ^ a * Y ^ (m - a)) → ∑ a ∈ s, u a ∈ Q ^ (m + 1) →
      ∀ a ∈ s, u a ∈ Q * (P ^ a * Y ^ (m - a)))
    (d k : ℕ) (hdk : d ≤ k) : P ^ d ⊓ Q ^ k ≤ Y ^ (k - d) * P ^ d ⊔ P ^ (d + 1) := by
  refine (inf_pow_le_sum P Y Q hQ hind d k hdk).trans ?_
  refine Finset.sum_induction _ (· ≤ Y ^ (k - d) * P ^ d ⊔ P ^ (d + 1))
    (fun a b ha hb => sup_le ha hb) bot_le fun a ha => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
  rcases h1.eq_or_lt with rfl | hlt
  · exact le_sup_of_le_left (by rw [mul_comm])
  · exact le_sup_of_le_right
      ((Ideal.mul_le_left : P ^ a * Y ^ (k - a) ≤ P ^ a).trans
        (Ideal.pow_le_pow_right hlt))

end Step

section Step2

variable {R : Type u} [CommRing R]

/-- The lifting property used at the degrees below `ν_i`: every `b ∈ P^d` whose class in
`Q^d/Q^(d+1)` is the class of an element of `J` is congruent modulo `Q^(d+1)` to an element
of `J ∩ P^d`. -/
private def ZLift (J P Q : Ideal R) (d : ℕ) : Prop :=
  ∀ b ∈ P ^ d, (∃ j ∈ J, j - b ∈ Q ^ (d + 1)) →
    ∃ f ∈ J, f ∈ P ^ d ∧ f - b ∈ Q ^ (d + 1)

variable (J P Q Y : Ideal R) {s r : ℕ} (y : Fin s → R) (z : Fin r → R)
  (hy : ∀ i, y i ∈ Q ^ 1) (hz : ∀ i, z i ∈ Q ^ 1)

include hy hz in
/-- The step of the construction of the sequence `g_k` (pp. 201–202): given `g ∈ J` with
`g - a ∈ Q^(ν+1)`, `g ∈ P^d` (`d < ν`) and `g ∈ Y^μ P^d + P^(d+1)` with `d + μ > ν`, there is
`g₁` with the same properties for `μ + 1`, and `g - g₁ ∈ Q^(d+μ)`.  Lemma 10 (`hL10`),
Lemma 11 and the coefficient closure of `gr_Q(J,R)` (`hD`) give that `ψ ∈ gr_Q(J,R)` and that
its `Y`-coefficients `ψ_α` lie in `gr_Q(J,R)`; `ZLift d` replaces the paper's expression of `ψ_α`
by `Σ_{β<i} λ_{αβ} φ_β`, `h_{αβ}` and `f_β`. -/
private theorem exists_next_approx (hQY : Q = P ⊔ Y) (hY : Y = Ideal.span (Set.range y))
    (hP : P = Ideal.span (Set.range z))
    (hL10 : ∀ (d μ : ℕ) (g h : R), g ∈ J → h ∈ Y ^ μ * P ^ d → g - h ∈ P ^ (d + 1) →
      ∃ hQ : h ∈ Q ^ (d + μ), AssocGraded.mk Q (d + μ) h hQ ∈ grIdeal Q J)
    (hD : ∀ (k : ℕ) (j : R) (_hj : j ∈ J) (hjk : j ∈ Q ^ k)
      (ψ : MvPolynomial (Fin s) (MvPolynomial (Fin r) (R ⧸ Q))),
      yzFormHom Q y z hy hz ψ = AssocGraded.mk Q k j hjk → ∀ m,
        zFormHom Q z hz (ψ.coeff m) ∈ grIdeal Q J)
    (hind : ∀ (m : ℕ) (s : Finset ℕ), (∀ a ∈ s, a ≤ m) → ∀ u : ℕ → R,
      (∀ a ∈ s, u a ∈ P ^ a * Y ^ (m - a)) → ∑ a ∈ s, u a ∈ Q ^ (m + 1) →
      ∀ a ∈ s, u a ∈ Q * (P ^ a * Y ^ (m - a)))
    {ν d μ : ℕ} (hμ : ν < d + μ) {a : R} (hZ : ZLift J P Q d) {g : R} (hgJ : g ∈ J)
    (hga : g - a ∈ Q ^ (ν + 1)) (hgP : g ∈ P ^ d) (hgY : g ∈ Y ^ μ * P ^ d ⊔ P ^ (d + 1)) :
    ∃ g₁ : R, g₁ ∈ J ∧ g₁ - a ∈ Q ^ (ν + 1) ∧ g₁ ∈ P ^ d ∧
      g₁ ∈ Y ^ (μ + 1) * P ^ d ⊔ P ^ (d + 1) ∧ g - g₁ ∈ Q ^ (d + μ) := by
  classical
  have hPQ : P ≤ Q := hQY ▸ le_sup_left
  have hYQ : Y ≤ Q := hQY ▸ le_sup_right
  obtain ⟨h₀, hh₀, p, hp, hsum⟩ := Submodule.mem_sup.mp hgY
  have hgh₀ : g - h₀ ∈ P ^ (d + 1) := by rw [← hsum]; simpa using hp
  obtain ⟨hQ0, hmk0⟩ := hL10 d μ g h₀ hgJ hh₀ hgh₀
  obtain ⟨j₀, ⟨hj₀J, hj₀Q⟩, hj₀', hj₀mk⟩ := (grIdeal_homogeneous_eq Q J (d + μ) _
    (AssocGraded.mk_mem_homogeneous Q hQ0)).mp hmk0
  obtain ⟨H, hbi, hev, hQ', hHmk⟩ := exists_isBiHomogeneous_evYZ_eq_of_mem_mul_pow Q y z hy hz
    (μ := μ) (d := d) (h₀ := h₀) (by rwa [hY, hP] at hh₀)
  have hcoef : ∀ m, zFormHom Q z hz ((redYZ Q H).coeff m) ∈ grIdeal Q J := by
    refine hD (d + μ) j₀ hj₀J hj₀Q (redYZ Q H) ?_
    rw [hHmk]
    exact (mk_congr_of_eq Q (add_comm μ d) rfl _ _).trans hj₀mk.symm
  -- the `Y`-coefficients
  have hfm : ∀ m : Fin s →₀ ℕ, ∃ f ∈ J, f ∈ P ^ d ∧
      f - eval z (H.coeff m) ∈ Q ^ (d + 1) := by
    intro m
    have hA := (hbi m).1
    have hmemP : eval z (H.coeff m) ∈ P ^ d := by
      rw [hP]; exact (Ideal.mem_span_pow_iff_exists_isHomogeneous z _).mpr ⟨_, hA, rfl⟩
    refine hZ _ hmemP ?_
    have h1 := hcoef m
    have h2 : (redYZ Q H).coeff m = (H.coeff m).map (Ideal.Quotient.mk Q) := by
      simp [redYZ, coeff_map]
    rw [h2, zFormHom_map_of_isHomogeneous Q z hz hA] at h1
    obtain ⟨jm, ⟨hjmJ, hjmQ⟩, hjm', hjmmk⟩ := (grIdeal_homogeneous_eq Q J d _
      (AssocGraded.mk_mem_homogeneous Q _)).mp h1
    exact ⟨jm, hjmJ, sub_mem_pow_succ_of_mk_eq_mk Q hjmQ _ hjmmk⟩
  choose f hfJ hfP hfsub using hfm
  set h : R := ∑ m ∈ H.support, (∏ j, y j ^ m j) * f m with hh
  have hmdeg : ∀ m ∈ H.support, m.degree = μ := fun m hm => (hbi m).2 (mem_support_iff.mp hm)
  have hhJ : h ∈ J := Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (hfJ m)
  have hhYP : h ∈ Y ^ μ * P ^ d := Ideal.sum_mem _ fun m hm => by
    have := prod_pow_mem_pow_degree y m
    rw [hmdeg m hm, ← hY] at this
    exact Ideal.mul_mem_mul this (hfP m)
  have hh₀h : h₀ - h ∈ Q ^ (d + μ + 1) := by
    have hexp : h₀ - h = ∑ m ∈ H.support, (eval z (H.coeff m) - f m) * ∏ j, y j ^ m j := by
      rw [hh, ← hev, evYZ]
      show eval₂ (eval z) y H - _ = _
      rw [eval₂_eq', ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [sub_mul]
      ring
    rw [hexp]
    refine Ideal.sum_mem _ fun m hm => ?_
    have h1 := prod_pow_mem_pow_degree y m
    rw [hmdeg m hm, ← hY] at h1
    have h2 : (∏ j, y j ^ m j) ∈ Q ^ μ := Ideal.pow_right_mono hYQ μ h1
    have h3 : eval z (H.coeff m) - f m ∈ Q ^ (d + 1) := by
      simpa using (Q ^ (d + 1)).neg_mem (hfsub m)
    have := Ideal.mul_mem_mul h3 h2
    rwa [← pow_add, show d + 1 + μ = d + μ + 1 by omega] at this
  have hhQ : h ∈ Q ^ (d + μ) := by
    have : Y ^ μ * P ^ d ≤ Q ^ (d + μ) := by
      calc Y ^ μ * P ^ d ≤ Q ^ μ * Q ^ d :=
            Ideal.mul_mono (Ideal.pow_right_mono hYQ μ) (Ideal.pow_right_mono hPQ d)
        _ = Q ^ (d + μ) := by rw [← pow_add, add_comm]
    exact this hhYP
  have hhP : h ∈ P ^ d := (Ideal.mul_le_right : Y ^ μ * P ^ d ≤ P ^ d) hhYP
  have hh₀P : h₀ ∈ P ^ d := (Ideal.mul_le_right : Y ^ μ * P ^ d ≤ P ^ d) hh₀
  refine ⟨g - h, sub_mem hgJ hhJ, ?_, sub_mem hgP hhP, ?_, by simpa using hhQ⟩
  · have : g - h - a = (g - a) - h := by ring
    rw [this]
    exact sub_mem hga (Ideal.pow_le_pow_right (by omega) hhQ)
  · have hsplit : g - h = (g - h₀) + (h₀ - h) := by ring
    rw [hsplit]
    refine add_mem (Ideal.mem_sup_right hgh₀) ?_
    have := inf_pow_le_pow_mul_sup_succ P Y Q hQY hind d (d + μ + 1) (by omega)
      ⟨sub_mem hh₀P hhP, hh₀h⟩
    rwa [show d + μ + 1 - d = μ + 1 by omega] at this

end Step2

section GrClass

variable {R : Type u} [CommRing R] {P Q Y : Ideal R}

/-- `Q^μ P^d ⊆ Y^μ P^d + P^{d+1}` for `Q = P + Y`. -/
theorem pow_mul_le_pow_mul_sup_succ (hQ : Q = P ⊔ Y) (d μ : ℕ) :
    Q ^ μ * P ^ d ≤ Y ^ μ * P ^ d ⊔ P ^ (d + 1) := by
  calc Q ^ μ * P ^ d ≤ (Y ^ μ ⊔ P) * P ^ d := Ideal.mul_mono_left (hQ ▸ sup_pow_le_pow_sup P Y μ)
    _ = Y ^ μ * P ^ d ⊔ P ^ (d + 1) := by rw [Ideal.sup_mul, pow_succ' P d]

/-- `Y^μ P^d + P^{d+1} ⊆ Q^μ P^d + P^{d+1}` for `Y ≤ Q`. -/
theorem pow_mul_sup_succ_le_pow_mul_sup_succ (hYQ : Y ≤ Q) (d μ : ℕ) :
    Y ^ μ * P ^ d ⊔ P ^ (d + 1) ≤ Q ^ μ * P ^ d ⊔ P ^ (d + 1) :=
  sup_le_sup_right (Ideal.mul_mono_left (Ideal.pow_right_mono hYQ μ)) _

/-- "`∩_k Q^{μ_k} gr^d_P(R) = (0)`" (p. 203; Krull's intersection theorem for the finite module
`gr^d_P(R)` over the local ring `R/P`, `Q̄ ⊆ m`): if `[g] ∈ Q^μ gr^d_P(R)` for all `μ`, then
`g ∈ P^{d+1}`, i.e. the initial form is zero. -/
theorem mem_pow_succ_of_forall_grClassMemPow [IsLocalRing R] [IsNoetherianRing R]
    (hQM : Q ≤ maximalIdeal R) {d : ℕ} {g : R} (h : ∀ μ, GrClassMemPow P Q d μ g) :
    g ∈ P ^ (d + 1) := by
  refine mem_of_forall_mem_sup_pow_maximalIdeal _ g fun n => ?_
  obtain ⟨-, hg⟩ := (h n).mem_mul_sup
  refine (?_ : Q ^ n * P ^ d ⊔ P ^ (d + 1) ≤ P ^ (d + 1) ⊔ maximalIdeal R ^ n) hg
  exact sup_le (le_sup_of_le_right
    ((Ideal.mul_le_left : Q ^ n * P ^ d ≤ Q ^ n).trans (Ideal.pow_right_mono hQM n)))
    le_sup_left

/-- "Let `μ` be the largest integer such that `Ψ ∈ Q^μ gr^d_P(R)`": it exists for `ν_P(g) = d`,
by `mem_pow_succ_of_forall_grClassMemPow` (the initial form `Ψ ≠ 0`). -/
theorem exists_maximal_grClassMemPow [IsLocalRing R] [IsNoetherianRing R]
    (hQM : Q ≤ maximalIdeal R) {d : ℕ} {g : R} (hg : g ∈ P ^ d) (hnot : g ∉ P ^ (d + 1)) :
    ∃ μ, GrClassMemPow P Q d μ g ∧ ¬ GrClassMemPow P Q d (μ + 1) g := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ μ, GrClassMemPow P Q d μ g := by
    intro μ
    induction μ with
    | zero => exact grClassMemPow_zero hg
    | succ μ ih => exact hcon μ ih
  exact hnot (mem_pow_succ_of_forall_grClassMemPow hQM hall)

end GrClass

section Core

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R]
variable (J P Q Y : Ideal R) {s r : ℕ} (y : Fin s → R) (z : Fin r → R)
  (hy : ∀ i, y i ∈ Q ^ 1) (hz : ∀ i, z i ∈ Q ^ 1)

include hy hz in
/-- The construction of pp. 201–203 for one index `i` (`ν = ν_i`, `a` a lift of `φ_i`): if the
lifting property `ZLift d` holds for the degrees `d < ν` (this is where the elements `f_β`,
`β < i`, are used), then there is `f ∈ J ∩ P^ν` with `f - a ∈ Q^(ν+1)`, i.e. `φ_i` is the initial
form of `f` in `gr_Q(R)` and `ν_P(f) = ν`.  The paper argues by contradiction, and so does this
proof:
* "let `d` be the largest integer such that there exists `g ∈ J` with `ν_P(g) = d` and with `φ_i`
  as its initial form in `gr_Q(R)`.  We must have `d < ν_i`": `G k` (`g ∈ J`, `g - a ∈ Q^{ν+1}`,
  `g ∈ P^k`), `d = Nat.findGreatest G ν`; `hmaxd` is "by the assumption on the integer `d`, we
  must have `ν_P(g) = d`".
* "Let `Ψ` be the initial form in `gr_P(R)` of an element `g ∈ J` with the above property.  Let
  `μ` be the largest integer such that `Ψ ∈ Q^μ gr^d_P(R)`" (`GrClassMemPow`,
  `exists_maximal_grClassMemPow`).  "Since the initial form `φ_i` of `g` in `gr_Q(R)` is a form
  only in `Z` of degree `ν_i`, we have `g ∈ P^{ν_i} + Q^{ν_i+1}`, and hence `d + μ > ν_i`"
  (`hlow`, `hmu`; gap filled: it rests on `P^d ∩ Q^{ν+1} ⊆ Y^{ν+1-d}P^d + P^{d+1}`).
* "We claim that there exists `g₁ ∈ J` such that (1) …, (2) `ν_P(g₁) = d` and `Ψ₁ ∈ Q^{μ₁}
  gr^d_P(R)` with `μ₁ > μ`, and (3) `g - g₁ ∈ Q^{d+μ}`", with Lemma 10 (`exists_next_approx`)
  (`hstep`).
* "By repeating the process, we get a convergent sequence `{g_k}` in `J` such that … `ν_P(g_k) = d`
  and … `Ψ_k ∈ Q^{μ_k} gr^d_P(R)` where the sequence `μ_k` is monotone increasing": `seq`.
* "By the completeness of `R`, we have `f_i = lim g_k` which is in `J`.  Clearly `φ_i` must be the
  initial form of `f_i` in `gr_Q(R)` and `ν_P(f_i) ≥ d`" (`hfJ`, `hfa`, `hfP`; Krull's
  intersection theorem for the closedness of the ideals `J`, `Q^{ν+1}`, `P^d`).  "But, by the
  assumption on `d`, we must have `ν_P(f_i) = d` and, on the other hand, since `Ψ_k ∈ Q^{μ_k}
  gr^d_P(R)` and `μ_{k+1} > μ_k` for all `k`, the initial form of `f_i` in `gr_P(R)` must be in
  `⋂_k Q^{μ_k} gr^d_P(R) = (0)`": `hGr` (gap filled: `f - g_k ∈ P^d ∩ Q^{d+μ_k}`, so the initial
  form of `f` and that of `g_k` agree modulo `Q^{μ_k} gr^d_P(R)`), then
  `mem_pow_succ_of_forall_grClassMemPow`, giving `f ∈ P^{d+1}`: a contradiction. -/
private theorem exists_mem_of_zLift_of_lt (hQY : Q = P ⊔ Y) (hY : Y = Ideal.span (Set.range y))
    (hP : P = Ideal.span (Set.range z)) (hQM : Q ≤ maximalIdeal R)
    (hL10 : ∀ (d μ : ℕ) (g h : R), g ∈ J → h ∈ Y ^ μ * P ^ d → g - h ∈ P ^ (d + 1) →
      ∃ hQ : h ∈ Q ^ (d + μ), AssocGraded.mk Q (d + μ) h hQ ∈ grIdeal Q J)
    (hD : ∀ (k : ℕ) (j : R) (_hj : j ∈ J) (hjk : j ∈ Q ^ k)
      (ψ : MvPolynomial (Fin s) (MvPolynomial (Fin r) (R ⧸ Q))),
      yzFormHom Q y z hy hz ψ = AssocGraded.mk Q k j hjk → ∀ m,
        zFormHom Q z hz (ψ.coeff m) ∈ grIdeal Q J)
    (hind : ∀ (m : ℕ) (s : Finset ℕ), (∀ a ∈ s, a ≤ m) → ∀ u : ℕ → R,
      (∀ a ∈ s, u a ∈ P ^ a * Y ^ (m - a)) → ∑ a ∈ s, u a ∈ Q ^ (m + 1) →
      ∀ a ∈ s, u a ∈ Q * (P ^ a * Y ^ (m - a)))
    {ν : ℕ} {a : R} (ha : a ∈ P ^ ν) (hZ : ∀ d < ν, ZLift J P Q d)
    (hex : ∃ j ∈ J, j - a ∈ Q ^ (ν + 1)) :
    ∃ f ∈ J, f ∈ P ^ ν ∧ f - a ∈ Q ^ (ν + 1) := by
  classical
  have hPQ : P ≤ Q := hQY ▸ le_sup_left
  have hYQ : Y ≤ Q := hQY ▸ le_sup_right
  -- "Let `d` be the largest integer such that there exists `g ∈ J` with `ν_P(g) = d` and with
  -- `φ_i` as its initial form in `gr_Q(R)`"
  set G : ℕ → Prop := fun k => ∃ g, g ∈ J ∧ g - a ∈ Q ^ (ν + 1) ∧ g ∈ P ^ k with hG
  have hG0 : G 0 := by
    obtain ⟨j, hj, hja⟩ := hex
    exact ⟨j, hj, hja, by simp⟩
  set d := Nat.findGreatest G ν with hd
  have hGd : G d := Nat.findGreatest_spec (Nat.zero_le ν) hG0
  have hdle : d ≤ ν := Nat.findGreatest_le ν
  by_cases hdν : d = ν
  · obtain ⟨g, hgJ, hga, hgP⟩ := hGd
    exact ⟨g, hgJ, hdν ▸ hgP, hga⟩
  exfalso
  -- "We must have `d < ν_i`"
  have hdlt : d < ν := lt_of_le_of_ne hdle hdν
  obtain ⟨g₀, hg₀J, hg₀a, hg₀P⟩ := hGd
  -- "by the assumption on the integer `d`, we must have `ν_P(g) = d`"
  have hmaxd : ∀ g, g ∈ J → g - a ∈ Q ^ (ν + 1) → g ∈ P ^ d → g ∉ P ^ (d + 1) := by
    intro g hgJ hga hgP hg1
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self d) hdlt ⟨g, hgJ, hga, hg1⟩
  -- "Since the initial form `φ_i` of `g` in `gr_Q(R)` is a form only in `Z` of degree `ν_i`, we
  -- have `g ∈ P^{ν_i} + Q^{ν_i+1}`, and hence `d + μ > ν_i`": `Ψ ∈ Q^{ν+1-d} gr^d_P(R)`
  have hlow : ∀ g, g - a ∈ Q ^ (ν + 1) → g ∈ P ^ d → GrClassMemPow P Q d (ν + 1 - d) g := by
    intro g hga hgP
    have haPd : a ∈ P ^ d := Ideal.pow_le_pow_right hdle ha
    have h1 := inf_pow_le_pow_mul_sup_succ P Y Q hQY hind d (ν + 1) (by omega)
      ⟨sub_mem hgP haPd, hga⟩
    have h2 : a ∈ P ^ (d + 1) := Ideal.pow_le_pow_right hdlt ha
    have h3 : g ∈ Y ^ (ν + 1 - d) * P ^ d ⊔ P ^ (d + 1) := by
      have : g = (g - a) + a := by ring
      rw [this]
      exact add_mem h1 (Ideal.mem_sup_right h2)
    exact grClassMemPow_of_mem_mul_sup hgP
      (pow_mul_sup_succ_le_pow_mul_sup_succ (P := P) hYQ d _ h3)
  have hmu : ∀ g μ, g - a ∈ Q ^ (ν + 1) → g ∈ P ^ d → ¬ GrClassMemPow P Q d (μ + 1) g →
      ν < d + μ := by
    intro g μ hga hgP hnot
    by_contra hcon
    exact hnot ((hlow g hga hgP).mono (by omega))
  -- the construction of `g₁` and `Ψ₁` (pp. 201–202)
  have hstep : ∀ g μ, g ∈ J → g - a ∈ Q ^ (ν + 1) → g ∈ P ^ d → GrClassMemPow P Q d μ g →
      ¬ GrClassMemPow P Q d (μ + 1) g →
      ∃ g₁ μ₁, (g₁ ∈ J ∧ g₁ - a ∈ Q ^ (ν + 1) ∧ g₁ ∈ P ^ d) ∧ GrClassMemPow P Q d μ₁ g₁ ∧
        ¬ GrClassMemPow P Q d (μ₁ + 1) g₁ ∧ μ < μ₁ ∧ g - g₁ ∈ Q ^ (d + μ) := by
    intro g μ hgJ hga hgP hμ hμ'
    have hμd : ν < d + μ := hmu g μ hga hgP hμ'
    have hgY : g ∈ Y ^ μ * P ^ d ⊔ P ^ (d + 1) :=
      (sup_le (pow_mul_le_pow_mul_sup_succ hQY d μ) le_sup_right) hμ.mem_mul_sup.2
    obtain ⟨g₁, h1, h2, h3, h4, h5⟩ := exists_next_approx J P Q Y y z hy hz hQY hY hP hL10 hD
      hind (ν := ν) (d := d) (μ := μ) hμd (hZ d hdlt) hgJ hga hgP hgY
    -- `ν_P(g₁) = d`, by the assumption on `d`; `Ψ₁ ∈ Q^{μ+1} gr^d_P(R)`
    have hg₁1 : g₁ ∉ P ^ (d + 1) := hmaxd g₁ h1 h2 h3
    have hΨ₁ : GrClassMemPow P Q d (μ + 1) g₁ :=
      grClassMemPow_of_mem_mul_sup h3 (pow_mul_sup_succ_le_pow_mul_sup_succ (P := P) hYQ d _ h4)
    -- "if `μ₁` is the maximal integer such that `Ψ₁ ∈ Q^{μ₁} gr^d_P(R)`"
    obtain ⟨μ₁, hμ₁, hμ₁'⟩ := exists_maximal_grClassMemPow hQM h3 hg₁1
    have hlt : μ < μ₁ := by
      by_contra hcon
      exact hμ₁' (hΨ₁.mono (by omega))
    exact ⟨g₁, μ₁, ⟨h1, h2, h3⟩, hμ₁, hμ₁', hlt, h5⟩
  -- the sequence `g_k`, with the (maximal) integers `μ_k`
  have hg₀1 : g₀ ∉ P ^ (d + 1) := hmaxd g₀ hg₀J hg₀a hg₀P
  obtain ⟨μ₀, hμ₀, hμ₀'⟩ := exists_maximal_grClassMemPow (P := P) (Q := Q) hQM hg₀P hg₀1
  let St : Type u := {p : R × ℕ // (p.1 ∈ J ∧ p.1 - a ∈ Q ^ (ν + 1) ∧ p.1 ∈ P ^ d) ∧
    GrClassMemPow P Q d p.2 p.1 ∧ ¬ GrClassMemPow P Q d (p.2 + 1) p.1}
  have hnx : ∀ p : St, ∃ q : St, p.1.2 < q.1.2 ∧ p.1.1 - q.1.1 ∈ Q ^ (d + p.1.2) := by
    intro p
    obtain ⟨⟨g, μ⟩, ⟨hgJ, hga, hgP⟩, hμ, hμ'⟩ := p
    obtain ⟨g₁, μ₁, h1, h2, h3, h4, h5⟩ := hstep g μ hgJ hga hgP hμ hμ'
    exact ⟨⟨(g₁, μ₁), h1, h2, h3⟩, h4, h5⟩
  choose nxt hnxt using hnx
  let seq : ℕ → St := fun k =>
    Nat.rec ⟨(g₀, μ₀), ⟨hg₀J, hg₀a, hg₀P⟩, hμ₀, hμ₀'⟩ (fun _ p => nxt p) k
  set sq : ℕ → R := fun k => (seq k).1.1 with hsq
  set mu : ℕ → ℕ := fun k => (seq k).1.2 with hmu_def
  have hsqInv : ∀ k, (sq k ∈ J ∧ sq k - a ∈ Q ^ (ν + 1) ∧ sq k ∈ P ^ d) ∧
      GrClassMemPow P Q d (mu k) (sq k) := fun k => ⟨(seq k).2.1, (seq k).2.2.1⟩
  have hmu_lt : ∀ k, mu k < mu (k + 1) := fun k => (hnxt (seq k)).1
  have hsq_succ : ∀ k, sq k - sq (k + 1) ∈ Q ^ (d + mu k) := fun k => (hnxt (seq k)).2
  have hmu_ge : ∀ k, k ≤ mu k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hmu_lt k))
  have hmu_mono : Monotone mu := monotone_nat_of_le_succ fun k => (hmu_lt k).le
  have hdiff : ∀ k, sq (k + 1) - sq k ∈ maximalIdeal R ^ k := fun k => by
    have := (Q ^ (d + mu k)).neg_mem (hsq_succ k)
    have h2 : Q ^ (d + mu k) ≤ maximalIdeal R ^ k :=
      (Ideal.pow_le_pow_right (by have := hmu_ge k; omega)).trans (Ideal.pow_right_mono hQM k)
    simpa using h2 this
  -- "By the completeness of `R`, we have `f_i = lim g_k` which is in `J`"
  obtain ⟨f, hf⟩ := exists_forall_sub_mem_pow_of_isAdicComplete (maximalIdeal R) sq hdiff
  have hlim : ∀ I : Ideal R, (∀ k, sq k ∈ I) → f ∈ I := fun I hI =>
    mem_of_forall_mem_sup_pow_maximalIdeal I f fun n => by
      have : f = sq n + (f - sq n) := by ring
      rw [this]
      exact add_mem (Ideal.mem_sup_left (hI n)) (Ideal.mem_sup_right (hf n))
  have hfJ : f ∈ J := hlim J fun k => (hsqInv k).1.1
  have hfP : f ∈ P ^ d := hlim _ fun k => (hsqInv k).1.2.2
  -- "Clearly `φ_i` must be the initial form of `f_i` in `gr_Q(R)`": `f - a ∈ Q^{ν+1}`
  have hfa : f - a ∈ Q ^ (ν + 1) := by
    refine mem_of_forall_mem_sup_pow_maximalIdeal _ _ fun n => ?_
    have : f - a = (sq n - a) + (f - sq n) := by ring
    rw [this]
    exact add_mem (Ideal.mem_sup_left (hsqInv n).1.2.1) (Ideal.mem_sup_right (hf n))
  -- `f - g_k ∈ Q^{d + μ_k}` (the limit of the differences `g_k - g_n`, `n ≥ k`)
  have htel : ∀ k N, k ≤ N → sq k - sq N ∈ Q ^ (d + mu k) := by
    intro k N hkN
    induction N, hkN using Nat.le_induction with
    | base => simp
    | succ N hkN ih =>
      have : sq k - sq (N + 1) = (sq k - sq N) + (sq N - sq (N + 1)) := by ring
      rw [this]
      exact add_mem ih (Ideal.pow_le_pow_right (by have := hmu_mono hkN; omega) (hsq_succ N))
  have hfk : ∀ k, f - sq k ∈ Q ^ (d + mu k) := by
    intro k
    refine mem_of_forall_mem_sup_pow_maximalIdeal _ _ fun n => ?_
    have hN := htel k (max n k) (le_max_right n k)
    have : f - sq k = (f - sq (max n k)) - (sq k - sq (max n k)) := by ring
    rw [this]
    exact sub_mem (Ideal.mem_sup_right (Ideal.pow_le_pow_right (le_max_left n k) (hf _)))
      (Ideal.mem_sup_left hN)
  -- "since `Ψ_k ∈ Q^{μ_k} gr^d_P(R)`": the initial form of `f` agrees with that of `g_k` modulo
  -- `Q^{μ_k} gr^d_P(R)`, since `f - g_k ∈ P^d ∩ Q^{d+μ_k}`
  have hGr : ∀ k, GrClassMemPow P Q d (mu k) f := by
    intro k
    have h1 : f - sq k ∈ Y ^ (mu k) * P ^ d ⊔ P ^ (d + 1) := by
      have := inf_pow_le_pow_mul_sup_succ P Y Q hQY hind d (d + mu k) (Nat.le_add_right d _)
        ⟨sub_mem hfP (hsqInv k).1.2.2, hfk k⟩
      rwa [Nat.add_sub_cancel_left] at this
    have h2 : f - sq k ∈ Q ^ (mu k) * P ^ d ⊔ P ^ (d + 1) :=
      pow_mul_sup_succ_le_pow_mul_sup_succ (P := P) hYQ d _ h1
    have h3 := (hsqInv k).2.mem_mul_sup.2
    have : f = sq k + (f - sq k) := by ring
    refine grClassMemPow_of_mem_mul_sup hfP ?_
    rw [this]
    exact add_mem h3 h2
  have hall : ∀ μ, GrClassMemPow P Q d μ f := fun μ => (hGr μ).mono (hmu_ge μ)
  -- "the initial form of `f_i` in `gr_P(R)` must be in `⋂_k Q^{μ_k} gr^d_P(R) = (0)`"
  have hfP1 : f ∈ P ^ (d + 1) := mem_pow_succ_of_forall_grClassMemPow hQM hall
  exact hmaxd f hfJ hfa hfP hfP1

end Core

section Generators

variable {R : Type u} [CommRing R] (J Q : Ideal R) {r : ℕ} (z : Fin r → R)
  (hz : ∀ i, z i ∈ Q ^ 1)

include hz in
/-- The homogeneous components of an element `θ` of `(R/Q)[Z]` whose image in `gr_Q(R)` lies in
`gr_Q(J, R)` have the same property (`gr_Q(J, R)` is a graded ideal). -/
private theorem zFormHom_homogeneousComponent_mem_grIdeal {θ : MvPolynomial (Fin r) (R ⧸ Q)}
    (hθ : zFormHom Q z hz θ ∈ grIdeal Q J) (e : ℕ) :
    zFormHom Q z hz (homogeneousComponent e θ) ∈ grIdeal Q J := by
  classical
  by_cases heN : θ.totalDegree < e
  · rw [homogeneousComponent_eq_zero e θ heN, map_zero]
    exact zero_mem _
  push Not at heN
  have hlift : ∀ n, ∃ B : MvPolynomial (Fin r) R, B.IsHomogeneous n ∧
      B.map (Ideal.Quotient.mk Q) = homogeneousComponent n θ := fun n =>
    exists_isHomogeneous_map_eq Q (homogeneousComponent_isHomogeneous n θ)
  choose B hBh hBm using hlift
  have hcomp : ∀ n, zFormHom Q z hz (homogeneousComponent n θ) =
      AssocGraded.mk Q n (eval z (B n)) (eval_mem_pow_of_isHomogeneous Q z hz (hBh n)) := by
    intro n
    rw [← hBm n]
    exact zFormHom_map_of_isHomogeneous Q z hz (hBh n)
  have hsum : zFormHom Q z hz θ = ∑ n ∈ Finset.range (θ.totalDegree + 1),
      AssocGraded.mk Q n (eval z (B n)) (eval_mem_pow_of_isHomogeneous Q z hz (hBh n)) := by
    conv_lhs => rw [← sum_homogeneousComponent θ]
    rw [map_sum]
    exact Finset.sum_congr rfl fun n _ => hcomp n
  have hbound := grIdeal_le_bound Q J hθ e
  have hproj : grProj Q e (zFormHom Q z hz θ) =
      Submodule.Quotient.mk ⟨eval z (B e), eval_mem_pow_of_isHomogeneous Q z hz (hBh e)⟩ := by
    rw [hsum, map_sum, Finset.sum_eq_single e]
    · exact grProj_mk_same Q e _ _
    · intro n _ hne
      exact grProj_mk_ne Q hne _ _
    · intro hne
      exact absurd (Finset.mem_range.mpr (by omega)) hne
  obtain ⟨a, haJ, haQ, hamk⟩ := hbound
  rw [hproj, Submodule.Quotient.eq] at hamk
  have hsub : a - eval z (B e) ∈ Q ^ (e + 1) := hamk
  have heq := mk_eq_mk_of_sub_mem_pow_succ Q (eval_mem_pow_of_isHomogeneous Q z hz (hBh e)) haQ
    (by have := (Q ^ (e + 1)).neg_mem hsub; simpa using this)
  rw [hcomp e, heq]
  exact mk_mem_grIdeal Q haJ haQ

include hz in
/-- Finitely many homogeneous generators of the ideal `{θ | θ(Z) ∈ gr_Q(J, R)}` of `(R/Q)[Z]`,
sorted by degree: the paper's `φ_1, …, φ_m` "forms only in `Z_1, …, Z_r`", with
`ν_1 ≤ … ≤ ν_m` (p. 201, (a), (b), (c)). -/
private theorem exists_homogeneous_generators [IsNoetherianRing R] :
    ∃ (m : ℕ) (θ : Fin m → MvPolynomial (Fin r) (R ⧸ Q)) (ν : Fin m → ℕ), Monotone ν ∧
      (∀ j, (θ j).IsHomogeneous (ν j)) ∧ (∀ j, zFormHom Q z hz (θ j) ∈ grIdeal Q J) ∧
      ∀ A, zFormHom Q z hz A ∈ grIdeal Q J → A ∈ Ideal.span (Set.range θ) := by
  classical
  set I₀ : Ideal (MvPolynomial (Fin r) (R ⧸ Q)) :=
    Ideal.comap (zFormHom Q z hz) (grIdeal Q J) with hI₀
  set Hs : Set (MvPolynomial (Fin r) (R ⧸ Q)) :=
    {θ | (∃ e, θ.IsHomogeneous e) ∧ θ ∈ I₀} with hHs
  have hspan : Ideal.span Hs = I₀ := by
    refine le_antisymm (Ideal.span_le.mpr fun θ hθ => hθ.2) fun θ hθ => ?_
    rw [← sum_homogeneousComponent θ]
    exact Ideal.sum_mem _ fun e _ => Ideal.subset_span
      ⟨⟨e, homogeneousComponent_isHomogeneous e θ⟩,
        zFormHom_homogeneousComponent_mem_grIdeal J Q z hz hθ e⟩
  obtain ⟨t, htH, hts⟩ := (Submodule.fg_span_iff_fg_span_finset_subset Hs).mp
    (IsNoetherian.noetherian (Ideal.span Hs))
  set e0 : Fin t.card ≃ t := (t.equivFin).symm with he0
  set θ0 : Fin t.card → MvPolynomial (Fin r) (R ⧸ Q) := fun j => (e0 j).1 with hθ0
  have hhom : ∀ j, ∃ n, (θ0 j).IsHomogeneous n := fun j => (htH (e0 j).2).1
  choose ν0 hν0 using hhom
  set σ := Tuple.sort ν0 with hσ
  have hrange : Set.range (θ0 ∘ σ) = (t : Set (MvPolynomial (Fin r) (R ⧸ Q))) := by
    rw [σ.surjective.range_comp]
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact (e0 j).2
    · intro hx
      exact ⟨e0.symm ⟨x, hx⟩, by simp [hθ0]⟩
  refine ⟨t.card, θ0 ∘ σ, ν0 ∘ σ, Tuple.monotone_sort ν0, fun j => hν0 (σ j), fun j => ?_,
    fun A hA => ?_⟩
  · have : (θ0 (σ j)) ∈ I₀ := (htH (e0 (σ j)).2).2
    exact this
  · have hsp : Ideal.span (Set.range (θ0 ∘ σ)) = I₀ := by
      rw [hrange]
      exact hts.symm.trans hspan
    rw [hsp]
    exact hA

end Generators

section HomogComp

variable {K : Type u} [CommRing K] {σ : Type*}

/-- `(λ θ)_d = λ_{d-ν} θ` for `θ` homogeneous of degree `ν ≤ d`, and `0` for `ν > d`. -/
private theorem homogeneousComponent_mul_of_isHomogeneous {θ : MvPolynomial σ K} {ν : ℕ}
    (hθ : θ.IsHomogeneous ν) (lam : MvPolynomial σ K) (d : ℕ) :
    homogeneousComponent d (lam * θ) =
      if ν ≤ d then homogeneousComponent (d - ν) lam * θ else 0 := by
  classical
  have hsum : lam * θ = ∑ e ∈ Finset.range (lam.totalDegree + 1),
      homogeneousComponent e lam * θ := by
    conv_lhs => rw [← sum_homogeneousComponent lam]
    rw [Finset.sum_mul]
  rw [hsum, map_sum]
  have hterm : ∀ e, homogeneousComponent d (homogeneousComponent e lam * θ) =
      if d = e + ν then homogeneousComponent e lam * θ else 0 := fun e =>
    homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous e lam).mul hθ)
  simp only [hterm]
  by_cases hνd : ν ≤ d
  · simp only [hνd, ↓reduceIte]
    have : ∀ e, (d = e + ν) ↔ (e = d - ν) := fun e => by omega
    simp only [this]
    rw [Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · rw [homogeneousComponent_eq_zero (d - ν) lam (by
        rw [Finset.mem_range] at hmem; omega), zero_mul]
  · simp only [hνd, ↓reduceIte]
    exact Finset.sum_eq_zero fun e _ => by simp only [show ¬ d = e + ν by omega, ↓reduceIte]

end HomogComp

section ZLiftOfGood

variable {R : Type u} [CommRing R] (J P Q : Ideal R) {r : ℕ} (z : Fin r → R)
  (hz : ∀ i, z i ∈ Q ^ 1)

include hz in
/-- The lifting property `ZLift d` for `d < ν_i`, from the elements `f_β` (`β < i`) already
constructed: a form `ψ_α` of degree `d < ν_i` in `gr_Q(J, R) ∩ R''[Z]` is
`Σ_{β<i} λ_{αβ} φ_β` with forms `λ_{αβ}` of degree `d - ν_β` (all `φ_β` with `ν_β > d` have
index `≥ i` is the paper's "deg ψ_α = d < ν_i ≤ ν_j for j ≥ i"), and lifting the `λ_{αβ}` to
`h_{αβ} ∈ P^{d-ν_β}` gives `Σ_β h_{αβ} f_β`. -/
private theorem zLift_of_forall_good (hPQ : P ≤ Q) (hP : P = Ideal.span (Set.range z))
    {m : ℕ} (θ : Fin m → MvPolynomial (Fin r) (R ⧸ Q)) (ν : Fin m → ℕ) (hmono : Monotone ν)
    (hθh : ∀ j, (θ j).IsHomogeneous (ν j))
    (hgen : ∀ A, zFormHom Q z hz A ∈ grIdeal Q J → A ∈ Ideal.span (Set.range θ))
    (B : Fin m → MvPolynomial (Fin r) R) (hBh : ∀ j, (B j).IsHomogeneous (ν j))
    (hBθ : ∀ j, (B j).map (Ideal.Quotient.mk Q) = θ j)
    {i : Fin m} (f : Fin m → R)
    (hf : ∀ j, j < i → f j ∈ J ∧ f j ∈ P ^ ν j ∧ f j - eval z (B j) ∈ Q ^ (ν j + 1))
    {d : ℕ} (hd : d < ν i) : ZLift J P Q d := by
  classical
  intro b hb hex
  obtain ⟨j0, hj0J, hj0b⟩ := hex
  rw [hP] at hb
  obtain ⟨B', hB'h, hB'e⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous z b).mp hb
  rw [← hP] at hb
  have hbQ : b ∈ Q ^ d := hB'e ▸ eval_mem_pow_of_isHomogeneous Q z hz hB'h
  have hj0Q : j0 ∈ Q ^ d := by
    have : j0 = (j0 - b) + b := by ring
    rw [this]
    exact add_mem (Ideal.pow_le_pow_right (Nat.le_succ d) hj0b) hbQ
  set A : MvPolynomial (Fin r) (R ⧸ Q) := B'.map (Ideal.Quotient.mk Q) with hA
  have hAh : A.IsHomogeneous d := hB'h.map _
  have hzA : zFormHom Q z hz A = AssocGraded.mk Q d b hbQ := by
    rw [hA, zFormHom_map_of_isHomogeneous Q z hz hB'h]
    exact mk_congr_of_eq Q rfl hB'e _ _
  have hAI : zFormHom Q z hz A ∈ grIdeal Q J := by
    rw [hzA, ← mk_eq_mk_of_sub_mem_pow_succ Q hj0Q hbQ hj0b]
    exact mk_mem_grIdeal Q hj0J hj0Q
  obtain ⟨lam, hlam⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hgen A hAI)
  set lam' : Fin m → MvPolynomial (Fin r) (R ⧸ Q) :=
    fun j => if ν j ≤ d then homogeneousComponent (d - ν j) (lam j) else 0 with hlam'
  have hlam'h : ∀ j, (lam' j).IsHomogeneous (d - ν j) := fun j => by
    by_cases h : ν j ≤ d
    · simp only [hlam', h, ↓reduceIte]
      exact homogeneousComponent_isHomogeneous _ _
    · simp only [hlam', h, ↓reduceIte]
      exact isHomogeneous_zero _ _ _
  have hAsum : A = ∑ j, lam' j * θ j := by
    have h1 : A = homogeneousComponent d A := (homogeneousComponent_eq_self hAh).symm
    rw [h1, ← hlam, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [homogeneousComponent_mul_of_isHomogeneous (hθh j)]
    by_cases h : ν j ≤ d <;> simp [hlam', h]
  choose Λ hΛh hΛm using fun j => exists_isHomogeneous_map_eq Q (hlam'h j)
  have hjlt : ∀ j, ν j ≤ d → j < i := fun j hj => by
    by_contra hji
    push Not at hji
    have := hmono hji
    omega
  set T : Fin m → R := fun j => if ν j ≤ d then eval z (Λ j) * f j else 0 with hT
  have hTP : ∀ j, T j ∈ P ^ d := fun j => by
    by_cases h : ν j ≤ d
    · simp only [hT, h, ↓reduceIte]
      have h1 : eval z (Λ j) ∈ P ^ (d - ν j) := by
        rw [hP]; exact (Ideal.mem_span_pow_iff_exists_isHomogeneous z _).mpr ⟨_, hΛh j, rfl⟩
      have h2 := Ideal.mul_mem_mul h1 (hf j (hjlt j h)).2.1
      rwa [← pow_add, Nat.sub_add_cancel h] at h2
    · simp only [hT, h, ↓reduceIte]; exact zero_mem _
  have hTJ : ∀ j, T j ∈ J := fun j => by
    by_cases h : ν j ≤ d
    · simp only [hT, h, ↓reduceIte]
      exact Ideal.mul_mem_left _ _ (hf j (hjlt j h)).1
    · simp only [hT, h, ↓reduceIte]; exact zero_mem _
  have hTQ : ∀ j, T j ∈ Q ^ d := fun j => Ideal.pow_right_mono hPQ d (hTP j)
  have hTmk : ∀ j, AssocGraded.mk Q d (T j) (hTQ j) =
      zFormHom Q z hz (lam' j) * zFormHom Q z hz (θ j) := fun j => by
    by_cases h : ν j ≤ d
    · have hfj := hf j (hjlt j h)
      have hfQ : f j ∈ Q ^ ν j := Ideal.pow_right_mono hPQ _ hfj.2.1
      have h3 : eval z (B j) ∈ Q ^ ν j := eval_mem_pow_of_isHomogeneous Q z hz (hBh j)
      have e1 : zFormHom Q z hz (lam' j) =
          AssocGraded.mk Q (d - ν j) (eval z (Λ j))
            (eval_mem_pow_of_isHomogeneous Q z hz (hΛh j)) := by
        rw [← hΛm j, zFormHom_map_of_isHomogeneous Q z hz (hΛh j)]
      have e2 : zFormHom Q z hz (θ j) = AssocGraded.mk Q (ν j) (f j) hfQ := by
        rw [← hBθ j, zFormHom_map_of_isHomogeneous Q z hz (hBh j)]
        exact mk_eq_mk_of_sub_mem_pow_succ Q h3 hfQ
          (by simpa using (Q ^ (ν j + 1)).neg_mem hfj.2.2)
      rw [e1, e2, AssocGraded.mk_mul_mk Q]
      exact mk_congr_of_eq Q (Nat.sub_add_cancel h).symm (by simp [hT, h]) _ _
    · have : lam' j = 0 := by simp [hlam', h]
      rw [this, map_zero, zero_mul]
      refine (AssocGraded.mk_eq_zero_iff Q (hTQ j)).mpr ?_
      simp [hT, h]
  have hsumQ : ∑ j, T j ∈ Q ^ d := Ideal.sum_mem _ fun j _ => hTQ j
  refine ⟨∑ j, T j, Ideal.sum_mem _ fun j _ => hTJ j, Ideal.sum_mem _ fun j _ => hTP j, ?_⟩
  refine sub_mem_pow_succ_of_mk_eq_mk Q hsumQ hbQ ?_
  rw [mk_finset_sum Q d Finset.univ T hTQ, ← hzA, hAsum, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [hTmk j, map_mul]

end ZLiftOfGood

section Assembly

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R]
variable (J P Q Y : Ideal R) {s r : ℕ} (y : Fin s → R) (z : Fin r → R)
  (hy : ∀ i, y i ∈ Q ^ 1) (hz : ∀ i, z i ∈ Q ^ 1)

omit [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] in
private theorem initialForm_zero_eq (I : Ideal R) : initialForm I (0 : R) = 0 := by
  have htop : Ideal.ordElem I (0 : R) = ⊤ := Ideal.ordElem_eq_top_iff.mpr fun _ => zero_mem _
  simp [initialForm, htop]

include hy hz in
/-- The heart of the proof of Theorem 3, (ii) ⟹ (i) (pp. 200–203): the system of initial forms. -/
private theorem hasInitialFormSystem_of_data (hQY : Q = P ⊔ Y) (hY : Y = Ideal.span (Set.range y))
    (hP : P = Ideal.span (Set.range z)) (hQM : Q ≤ maximalIdeal R)
    (hbij : Function.Bijective (yzFormHom Q y z hy hz))
    (hL10 : ∀ (d μ : ℕ) (g h : R), g ∈ J → h ∈ Y ^ μ * P ^ d → g - h ∈ P ^ (d + 1) →
      ∃ hQ : h ∈ Q ^ (d + μ), AssocGraded.mk Q (d + μ) h hQ ∈ grIdeal Q J)
    (hD : ∀ (k : ℕ) (j : R) (_hj : j ∈ J) (hjk : j ∈ Q ^ k)
      (ψ : MvPolynomial (Fin s) (MvPolynomial (Fin r) (R ⧸ Q))),
      yzFormHom Q y z hy hz ψ = AssocGraded.mk Q k j hjk → ∀ m,
        zFormHom Q z hz (ψ.coeff m) ∈ grIdeal Q J)
    (hind : ∀ (m : ℕ) (s : Finset ℕ), (∀ a ∈ s, a ≤ m) → ∀ u : ℕ → R,
      (∀ a ∈ s, u a ∈ P ^ a * Y ^ (m - a)) → ∑ a ∈ s, u a ∈ Q ^ (m + 1) →
      ∀ a ∈ s, u a ∈ Q * (P ^ a * Y ^ (m - a))) :
    HasInitialFormSystem J P Q := by
  classical
  have hPQ : P ≤ Q := hQY ▸ le_sup_left
  obtain ⟨m, θ, ν, hmono, hθh, hθJ, hgen⟩ := exists_homogeneous_generators J Q z hz
  have hlift : ∀ j, ∃ B : MvPolynomial (Fin r) R, B.IsHomogeneous (ν j) ∧
      B.map (Ideal.Quotient.mk Q) = θ j := fun j => exists_isHomogeneous_map_eq Q (hθh j)
  choose B hBh hBθ using hlift
  have haQ : ∀ j, eval z (B j) ∈ Q ^ ν j := fun j => eval_mem_pow_of_isHomogeneous Q z hz (hBh j)
  have haP : ∀ j, eval z (B j) ∈ P ^ ν j := fun j => by
    rw [hP]; exact (Ideal.mem_span_pow_iff_exists_isHomogeneous z _).mpr ⟨_, hBh j, rfl⟩
  have hφ : ∀ j, zFormHom Q z hz (θ j) = AssocGraded.mk Q (ν j) (eval z (B j)) (haQ j) :=
    fun j => by rw [← hBθ j, zFormHom_map_of_isHomogeneous Q z hz (hBh j)]
  -- the elements `f_j`: the paper's maximal index `i` is the first index for which none exists
  have hgood : ∀ j, ∃ f : R, f ∈ J ∧ f ∈ P ^ ν j ∧ f - eval z (B j) ∈ Q ^ (ν j + 1) := by
    by_contra hcon
    push Not at hcon
    set bad : Finset (Fin m) := Finset.univ.filter fun j => ∀ f : R, f ∈ J → f ∈ P ^ ν j →
      f - eval z (B j) ∉ Q ^ (ν j + 1) with hbad
    obtain ⟨j₀, hj₀⟩ := hcon
    have hne : bad.Nonempty := ⟨j₀, by simpa [hbad] using hj₀⟩
    set i := bad.min' hne with hi
    have hibad : ∀ f : R, f ∈ J → f ∈ P ^ ν i → f - eval z (B i) ∉ Q ^ (ν i + 1) := by
      have := bad.min'_mem hne
      simpa [hbad] using this
    have hprev : ∀ j, j < i → ∃ f : R, f ∈ J ∧ f ∈ P ^ ν j ∧ f - eval z (B j) ∈ Q ^ (ν j + 1) := by
      intro j hji
      by_contra hno
      have : j ∈ bad := by simpa [hbad] using hno
      exact absurd (bad.min'_le j this) (not_le.mpr hji)
    choose! f hf using hprev
    have hZ : ∀ d < ν i, ZLift J P Q d := fun d hd =>
      zLift_of_forall_good J P Q z hz hPQ hP θ ν hmono hθh hgen B hBh hBθ f
        (fun j hji => hf j hji) hd
    have hex : ∃ j ∈ J, j - eval z (B i) ∈ Q ^ (ν i + 1) := by
      have h1 := hθJ i
      rw [hφ i] at h1
      obtain ⟨j, ⟨hjJ, hjQ⟩, hj', hjmk⟩ := (grIdeal_homogeneous_eq Q J (ν i) _
        (AssocGraded.mk_mem_homogeneous Q _)).mp h1
      exact ⟨j, hjJ, sub_mem_pow_succ_of_mk_eq_mk Q hjQ (haQ i) hjmk⟩
    obtain ⟨g, hgJ, hgP, hga⟩ := exists_mem_of_zLift_of_lt J P Q Y y z hy hz hQY hY hP hQM hL10 hD
      hind (haP i) hZ hex
    exact hibad g hgJ hgP hga
  choose f hfJ hfP hfa using hgood
  have hinj : Function.Injective (zFormHom Q z hz) := by
    intro A A' h
    apply MvPolynomial.C_injective (Fin s) (MvPolynomial (Fin r) (R ⧸ Q))
    apply hbij.1
    rw [yzFormHom_C, yzFormHom_C, h]
  -- the paper's claim: `φ_j` is the initial form of `f_j` and `ν_Q(f_j) = ν_P(f_j)`
  set f' : Fin m → R := fun j => if θ j = 0 then 0 else f j with hf'
  have hordQ : ∀ j, θ j ≠ 0 → Ideal.ordElem Q (f j) = ν j := by
    intro j hθj
    have hfQ : f j ∈ Q ^ ν j := Ideal.pow_right_mono hPQ _ (hfP j)
    refine le_antisymm (Ideal.ordElem_le_of_notMem ?_) (Ideal.le_ordElem hfQ)
    intro hmem
    apply hθj
    apply hinj
    rw [hφ j, map_zero]
    refine (AssocGraded.mk_eq_zero_iff Q (haQ j)).mpr ?_
    have : eval z (B j) = f j - (f j - eval z (B j)) := by ring
    rw [this]
    exact sub_mem hmem (Ideal.pow_le_pow_right (Nat.le_refl _) (hfa j) |> fun h => h)
  have hordeq : ∀ j, Ideal.ordElem Q (f' j) = Ideal.ordElem P (f' j) := by
    intro j
    by_cases hθj : θ j = 0
    · simp only [hf', hθj, ite_true]
      rw [Ideal.ordElem_eq_top_iff.mpr fun _ => zero_mem _,
        Ideal.ordElem_eq_top_iff.mpr fun _ => zero_mem _]
    · simp only [hf', hθj, ite_false]
      refine le_antisymm ?_ ?_
      · rw [hordQ j hθj]
        exact Ideal.le_ordElem (hfP j)
      · exact Ideal.ordElem_le fun k hk => Ideal.le_ordElem (Ideal.pow_right_mono hPQ k hk)
  have hinit : ∀ j, initialForm Q (f' j) = zFormHom Q z hz (θ j) := by
    intro j
    by_cases hθj : θ j = 0
    · simp only [hf', hθj, ite_true, map_zero]
      exact initialForm_zero_eq Q
    · simp only [hf', hθj, ite_false]
      rw [initialForm_eq_mk Q (hordQ j hθj), hφ j]
      refine mk_eq_mk_of_sub_mem_pow_succ Q _ (haQ j) ?_
      exact hfa j
  refine ⟨m, f', fun j => ?_, hordeq, ?_⟩
  · by_cases hθj : θ j = 0 <;> simp [hf', hθj, hfJ j]
  · simp only [hinit]
    refine le_antisymm (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hθJ j)) ?_
    -- `gr_Q(J, R)` is generated by the `φ_j`: coefficients of `Y`-polynomials (Claim D)
    have hspanθ : ∀ A, zFormHom Q z hz A ∈ grIdeal Q J →
        zFormHom Q z hz A ∈ Ideal.span (Set.range fun j => zFormHom Q z hz (θ j)) := by
      intro A hA
      have h1 := Ideal.mem_map_of_mem (zFormHom Q z hz) (hgen A hA)
      rw [Ideal.map_span, ← Set.range_comp] at h1
      exact h1
    rw [grIdeal, Ideal.span_le]
    rintro _ ⟨g, hgJ, rfl⟩
    by_cases htop : Ideal.ordElem Q g = ⊤
    · simp [initialForm, htop]
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp htop
      have hgk : g ∈ Q ^ k := Ideal.mem_pow_of_ordElem hk.symm
      rw [initialForm_eq_mk Q hk.symm]
      obtain ⟨ψ, hψ⟩ := hbij.2 (AssocGraded.mk Q k g hgk)
      have hcoef := hD k g hgJ hgk ψ hψ
      rw [← hψ, ψ.as_sum, map_sum]
      refine Ideal.sum_mem _ fun v _ => ?_
      have : yzFormHom Q y z hy hz (monomial v (ψ.coeff v)) = zFormHom Q z hz (ψ.coeff v) *
          (v.prod fun j e => AssocGraded.mk Q 1 (y j) (hy j) ^ e) := by
        simp [yzFormHom, eval₂_monomial]
      rw [this]
      exact Ideal.mul_mem_right _ _ (hspanθ _ (hcoef v))

end Assembly

end Theorem3Aux

/-- The main argument of Theorem 3, (ii) ⟹ (i), for `O = R/J` with `R` a complete regular local
ring (pp. 200–203): the hypothesis `hcore` of `isNormallyFlatAlongIdeal_of_complete_case`. -/
private theorem isNormallyFlatAlongIdeal_map_of_flat_quotient_of_complete [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (R : Type u)
    [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (J P Q : Ideal R) [P.IsPrime] [Q.IsPrime] [IsRegularLocalRing (R ⧸ P)]
    [IsRegularLocalRing (R ⧸ Q)] [(Q.map (Ideal.Quotient.mk J)).IsPrime] (hJP : J ≤ P)
    (hPQ : P ≤ Q) (hQflat : IsNormallyFlatAlongIdeal (Q.map (Ideal.Quotient.mk J)))
    (hflat : IsNormallyFlatAlongIdeal ((P.map (Ideal.Quotient.mk J)).map
      (algebraMap (R ⧸ J) (Localization.AtPrime (Q.map (Ideal.Quotient.mk J)))))) :
    IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)) := by
  classical
  -- "We take and fix a system of elements `(z₁, …, z_r, y₁, …, y_s)` of `R` such that
  -- `P = (z₁, …, z_r)R` and `Q = (z₁, …, z_r, y₁, …, y_s)R`": `ȳ` a minimal base of `Q/P` and `z`
  -- a minimal base of `P`, so that `(y, z)` is quasi-regular (`exists_isQuasiRegular_sumElim_of_span_eq_map`)
  obtain ⟨s, y, hyb, hsb⟩ := exists_span_eq_map_and_eq_spanFinrank P Q
  obtain ⟨r, z, hqr', hI, hPz⟩ := exists_isQuasiRegular_sumElim_of_span_eq_map P Q hPQ inferInstance
    inferInstance y hyb hsb
  have hqrbar := isQuasiRegular_mk_of_span_eq_map_of_spanFinrank P Q hPQ y hyb hsb
  have hP : P = Ideal.span (Set.range z) := hPz.symm
  set Y : Ideal R := Ideal.span (Set.range y) with hYdef
  have hQY : Q = P ⊔ Y := by
    rw [← hI, Set.Sum.elim_range, Ideal.span_union, ← hP]
    exact sup_comm _ _
  set Zs : Finset (Fin s ⊕ Fin r) := Finset.univ.filter fun i => i.isRight = true with hZs
  have hxZ : (Sum.elim y z) '' ↑Zs = Set.range z := by
    ext a
    constructor
    · rintro ⟨i, hi, rfl⟩
      rcases i with i | i
      · simp [hZs] at hi
      · exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Sum.inr i, by simp [hZs], rfl⟩
  have hxY : (Sum.elim y z) '' ↑Zsᶜ = Set.range y := by
    ext a
    constructor
    · rintro ⟨i, hi, rfl⟩
      rcases i with i | i
      · exact ⟨i, rfl⟩
      · simp [hZs] at hi
    · rintro ⟨i, rfl⟩
      exact ⟨Sum.inl i, by simp [hZs], rfl⟩
  have hind : ∀ (m : ℕ) (s : Finset ℕ), (∀ a ∈ s, a ≤ m) → ∀ u : ℕ → R,
      (∀ a ∈ s, u a ∈ P ^ a * Y ^ (m - a)) → ∑ a ∈ s, u a ∈ Q ^ (m + 1) →
      ∀ a ∈ s, u a ∈ Q * (P ^ a * Y ^ (m - a)) := by
    intro m s hs u hu hsum
    have hYx : Y = Ideal.span ((Sum.elim y z) '' ↑Zsᶜ) := by rw [hYdef, hxY]
    have hxP : Ideal.span ((Sum.elim y z) '' ↑Zs) = P := by rw [hxZ, ← hP]
    rw [hYx] at hu ⊢
    rw [← hxP] at hu ⊢
    rw [← hI] at hsum ⊢
    exact mem_mul_of_sum_mem_pow (Sum.elim y z) hqr' Zs m s hs u hu hsum
  have hQM : Q ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top'
  have hy1 : ∀ i, y i ∈ Q ^ 1 := fun i => by
    rw [pow_one, ← hI]; exact Ideal.subset_span ⟨Sum.inl i, rfl⟩
  have hz1 : ∀ i, z i ∈ Q ^ 1 := fun i => by
    rw [pow_one, ← hI]; exact Ideal.subset_span ⟨Sum.inr i, rfl⟩
  have hbij := yzFormHom_bijective Q y z hy1 hz1 hqr' hI
  -- Lemma 11, as printed: `gr_Q(J,R)_Q ∩ gr_Q(R) = gr_Q(J,R)`
  have hint := fun φ => mem_grIdeal_of_algebraMap_mem_map R J P Q hJP hPQ hQflat (φ := φ)
  -- Lemma 10 and Lemma 11
  have hL10 : ∀ (d μ : ℕ) (g h : R), g ∈ J → h ∈ Y ^ μ * P ^ d → g - h ∈ P ^ (d + 1) →
      ∃ hQ : h ∈ Q ^ (d + μ), AssocGraded.mk Q (d + μ) h hQ ∈ grIdeal Q J := by
    intro d μ g h hg hh hgh
    have hYQ : Y ≤ Q := hQY ▸ le_sup_right
    have hhQ : h ∈ Q ^ (d + μ) := by
      have : Y ^ μ * P ^ d ≤ Q ^ (d + μ) := by
        calc Y ^ μ * P ^ d ≤ Q ^ μ * Q ^ d :=
              Ideal.mul_mono (Ideal.pow_right_mono hYQ μ) (Ideal.pow_right_mono hPQ d)
          _ = Q ^ (d + μ) := by rw [← pow_add, add_comm]
      exact this hh
    refine ⟨hhQ, ?_⟩
    -- Lemma 10 (p. 199) for the class `Ψ_*` of `g`, `g ∈ J ∩ P^d`, `[g] ∈ Q^μ gr^d_P(R)`
    have hgP : g ∈ P ^ d := by
      have : g = h + (g - h) := by ring
      rw [this]
      exact add_mem ((Ideal.mul_le_right : Y ^ μ * P ^ d ≤ P ^ d) hh)
        (Ideal.pow_le_pow_right (Nat.le_succ d) hgh)
    have hgsup : g ∈ Q ^ μ * P ^ d ⊔ P ^ (d + 1) := by
      have : g = h + (g - h) := by ring
      rw [this]
      exact add_mem (Ideal.mem_sup_left (Ideal.mul_mono_left (Ideal.pow_right_mono hYQ μ) hh))
        (Ideal.mem_sup_right hgh)
    have hΦ := mk_mem_pow_smul_top_of_mem_mul_sup P Q d μ hgP hgsup
    obtain ⟨t, ht, hmem⟩ := exists_mul_mem_grIdeal_lambdaPiece_of_isQuasiRegular R J P Q hJP hPQ
      hflat y hyb hqrbar hg hgP hΦ
    -- "λ sends the class of `ȳ_j` to that of `y_j`": the `λ`-image of `Ψ_*` is the class of `h`
    rw [ofGrPiece_lambdaPiece_eq_mk P Q hPQ y hqrbar hyb d μ _ hgP hΦ hh hgh hhQ] at hmem
    -- "ψ ∈ gr_Q(J,R)_Q, and hence, by Lemma 11, ψ ∈ gr_Q(J,R)"
    exact mem_grIdeal_of_algebraMap_mem_map R J P Q hJP hPQ hQflat
      (algebraMap_mem_map_grIdeal_of_mul_mem R J Q ht hmem)
  -- "Applying Corollary 1 of Theorem 2, §2, to `{R_Q, JR_Q, PR_Q, O_Q}`", and the passage to
  -- `K[Z, Y]`: the `Y`-coefficients of an element of `gr_Q(J, R)` lie in `gr_Q(J, R)`
  have hsysQ := hasInitialFormSystem_localization R J P Q hJP hPQ hflat
  have hD : ∀ (k : ℕ) (j : R) (hj : j ∈ J) (hjk : j ∈ Q ^ k)
      (ψ : MvPolynomial (Fin s) (MvPolynomial (Fin r) (R ⧸ Q))),
      yzFormHom Q y z hy1 hz1 ψ = AssocGraded.mk Q k j hjk → ∀ m,
        zFormHom Q z hz1 (ψ.coeff m) ∈ grIdeal Q J := fun k j hj hjk ψ hψ m =>
    coeff_mem_grIdeal_of_hasInitialFormSystem_localization J P Q y z hy1 hz1 hqr' hI hP.symm hbij
      hint hsysQ hj hjk hψ m
  have hsys := hasInitialFormSystem_of_data J P Q Y y z hy1 hz1 hQY hYdef hP hQM hbij hL10 hD hind
  refine ((isNormallyFlatAlongIdeal_tfae J P Q hJP hPQ).out 2 1).mp ?_
  exact ⟨hQflat, hsys⟩

/-- Theorem 3, p. 200: "Let O be a local ring. Let P and Q be prime ideals in O such that Q ⊇ P
and that O/P and O/Q are both regular. Then the following two conditions are equivalent to each
other: (i) gr_P(O) is flat over O/P; (ii) gr_Q(O) is flat over O/Q and gr_{PO_Q}(O_Q) is flat
over O_Q/PO_Q."

Encoding: "gr_P(O) is flat over O/P" is `IsNormallyFlatAlongIdeal P` (Definition 1 of Ch. 0),
and likewise for `Q` and for `PO_Q` in the noetherian local ring `O_Q = Localization.AtPrime Q`.

Deviation from the paper (gap filled): in (i) ⟹ (ii), "`gr_{PO_Q}(O_Q) = gr_P(O)_Q`" is proved
as the flat base change isomorphism of Lemma 9 (`nonempty_grModPiece_baseChange_equiv`).  The
reduction of (ii) ⟹ (i) to complete `O` ("By Corollary of Lemma 9, we may assume that O is
complete", `isNormallyFlatAlongIdeal_of_complete_case`) needs Lemma 9 itself besides its
Corollary, the noetherianity of `Ô` and the regularity of `Ô/P̂`, `Ô/Q̂`.

(ii) ⟹ (i) for `O = R/J`, `R` complete regular local, is
`isNormallyFlatAlongIdeal_map_of_flat_quotient_of_complete`; its steps (all the names are private
helpers of this file) are, in the paper's order:
* "`P = (z₁, …, z_r)R` and `Q = (z₁, …, z_r, y₁, …, y_s)R`", `gr_Q(R) = R''[Z, Y]`
  (`yzFormHom_bijective`): `ȳ` is a minimal base of `Q/P` (`exists_span_eq_map_and_eq_spanFinrank`)
  and `z` a minimal base of `P`, so that `(y, z)` is quasi-regular
  (`exists_isQuasiRegular_sumElim_of_span_eq_map`) and `ȳ` is quasi-regular in `R/P`
  (`isQuasiRegular_mk_of_span_eq_map_of_spanFinrank`, needed for `λ`);
* "Let `K` denote the field of quotients of `R''`.  Then we get in a natural way the identification
  `gr_Q(R)_Q = gr_{QR_Q}(R_Q) = K[Z, Y]`.  Applying Corollary 1 of Theorem 2 to `{R_Q, JR_Q, PR_Q,
  O_Q}` … the ideal `gr_Q(J, R)_Q` in `K[Z, Y]` is generated by forms only in `Z`.  This implies
  that, if `ψ` is any element of `gr_Q(J, R)` … then all the `ψ_i` belong to `gr_Q(J, R)_Q ∩
  K[Z]` … By Lemma 11 … all the `ψ_i` belong to `gr_Q(J, R) ∩ R''[Z]`": Cor. 1 of Th. 2 for `R_Q`
  is `hasInitialFormSystem_localization`, the rest is
  `coeff_mem_grIdeal_of_hasInitialFormSystem_localization` (see its docstring);
* "We take a system of elements `(φ₁, …, φ_m)` in `gr_Q(J, R)` such that (a), (b), (c)":
  `exists_homogeneous_generators`;
* "We claim that for each `j` there exists an element `f_j ∈ J` such that `φ_j` is the initial form
  of `f_j` in `gr_Q(R)`, and `ν_Q(f_j) = ν_P(f_j)`", via the largest index `i` for which this
  fails to hold below (`hasInitialFormSystem_of_data`), the integer `d`, the sequence `g_k` built
  with Lemma 10 (`exists_next_approx`; Lemma 10 is `hL10`, the paper-form Lemma 10 for the class of
  `Ψ` in `gr^d_P(R)`, `exists_mul_mem_grIdeal_lambdaPiece_of_isQuasiRegular`, giving `ψ ∈ gr_Q(J,R)_Q`
  with `λ(ψ)` the class of `h` (`ofGrPiece_lambdaPiece_eq_mk`), followed by Lemma 11 in its printed
  intersection form), the maximal integers `μ_k` (`GrClassMemPow`), its limit by
  completeness, and the contradiction (`exists_mem_of_zLift_of_lt`); "then the conclusion (i) follows from the equivalence of (i) and
  (iii) of Theorem 2" (`isNormallyFlatAlongIdeal_tfae`).

Deviations from the paper in that proof:
* (gap filled) "`gr_Q(J, R)_Q = gr_{QR_Q}(JR_Q, R_Q)`" and "the initial forms of such `h_j` in `K[Z, Y]`
  are obviously forms only in `Z`": both inclusions of the equality are proved, with `K = R_Q/QR_Q`
  (shown to be the field of quotients of `R''`), `gr_Q(R) → gr_{QR_Q}(R_Q)` the natural map
  (`AssocGraded.mapLE`), `K[Z, Y] = gr_{QR_Q}(R_Q)` (`yzFormHom_bijective`, with the quasi-regularity
  of `(y, z)` in `R_Q`, `isQuasiRegular_map_localization`), and `h_j ∈ (z)^{ν}R_Q`; the
  identification `gr_Q(R)_Q = gr_{QR_Q}(R_Q)` is the ring isomorphism `e0`, and Lemma 11 is used in
  its printed intersection form (`mem_grIdeal_of_algebraMap_mem_map`, blueprint
  `lem:II.3-11-intersection`).
* (encoding) "By Lemma 10, `ψ ∈ gr_Q(J,R)_Q`" (pp. 201–202): Lemma 10 is applied to the class
  `Ψ_*` of `[g] ∈ Q^μ gr^d_P(R)` for `g ∈ J ∩ P^d`, in the form
  `exists_mul_mem_grIdeal_lambdaPiece_of_isQuasiRegular` (the printed proof, which does not use that
  `d = ν_P(g)` and `μ` are the exact orders; the node `exists_mul_mem_grIdeal_lambdaPiece` is its
  special case for the exact orders), because the induction (`exists_next_approx`) does not carry
  the exactness of `ν_P(g_k) = d` and `μ_k`; with `λ` the isomorphism determined by the minimal
  base `ȳ`.
* (gap filled) The existence of finitely many homogeneous generators `φ₁, …, φ_m` of
  `gr_Q(J, R)` that are forms in `Z` only, ordered by degree, is asserted by the paper; here it
  is the noetherianity of `(R/Q)[Z]` and the homogeneity of the ideal `{θ | θ(Z) ∈ gr_Q(J, R)}`
  (`zFormHom_homogeneousComponent_mem_grIdeal`).
* (encoding) "Let `i` be the largest integer such that there exists `f_j` for every
  `j < i`; suppose `i ≤ m`": the index `i` is the first index for which no `f_i` exists, which is the
  same integer (an `f_j` exists for every `j < i` and not for `j = i`); `ν_P(f_j) = ν_Q(f_j)` and
  "`φ_j` is the initial form of `f_j`" are encoded as `f_j ∈ J ∩ P^{ν_j}` and
  `f_j - a_j ∈ Q^{ν_j+1}` for a lift `a_j ∈ P^{ν_j}` of `φ_j`, an equivalent description of the
  `f_j` (`ν_Q(f_j) ≥ ν_j = ν_P(f_j)` with initial form `φ_j` in degree `ν_j`); for `φ_j = 0` the
  element `f_j = 0` is used at the end.  The proof is by contradiction at that index, as printed
  (`hasInitialFormSystem_of_data`, `exists_mem_of_zLift_of_lt`).
* (gap filled) "Let `μ` be the largest integer such that `Ψ ∈ Q^μ gr^d_P(R)`.  Since the initial form
  `φ_i` of `g` is a form only in `Z` … `g ∈ P^{ν_i} + Q^{ν_i+1}`, and hence `d + μ > ν_i`": `μ` is
  the largest integer (`GrClassMemPow`, `exists_maximal_grClassMemPow`, by Krull); the inequality
  is proved (`hlow`, `hmu`): `P^d ∩ Q^{ν_i+1} ⊆ Y^{ν_i+1-d}P^d + P^{d+1}` (independence of the
  bidegree components, `inf_pow_le_pow_mul_sup_succ`) gives `Ψ ∈ Q^{ν_i+1-d} gr^d_P(R)`.
* (gap filled) "`deg ψ_α = d < ν_i ≤ ν_j` for `j ≥ i`, so `ψ_α ∈ (φ₁, …, φ_{i-1})R''[Z]`" and "let
  us write `ψ_α = Σ λ_{αβ} φ_β` with forms `λ_{αβ}` of degree `d - ν_β`": the homogeneous components
  of a product (`homogeneousComponent_mul_of_isHomogeneous`) and the lifts of the forms `λ_{αβ}` to
  `P^{d-ν_β}` (`exists_isHomogeneous_map_eq`) are written out (`zLift_of_forall_good`).
* (gap filled) "from the above expression of `h` … `Ψ₁ ∈ Q^{μ₁} gr^d_P(R)` with `μ₁ > μ`": proved
  as `g₁ ∈ Y^{μ+1}P^d + P^{d+1}` from `h₀ - h ∈ P^d ∩ Q^{d+μ+1}` (`exists_next_approx`), i.e.
  `Ψ₁ ∈ Q^{μ+1} gr^d_P(R)` (`grClassMemPow_of_mem_mul_sup`).  Difference that remains: the passage
  from `Ψ` to `ψ` (the initial form of `Ψ` in `gr_{Q'}(gr_P(R)) = R''[Z, Y]`) is done at the level
  of representatives: `Ψ ∈ Q^μ gr^d_P(R)` gives `g = h₀ + p` with `h₀ ∈ Y^μP^d`, `p ∈ P^{d+1}`,
  and `ψ` is the reduction of a bihomogeneous `H` with `H(z, y) = h₀`
  (`exists_isBiHomogeneous_evYZ_eq_of_mem_mul_pow`).
* (gap filled) "By the completeness of `R`, we have `f_i = lim g_k` which is in `J`.  Clearly `φ_i`
  must be the initial form of `f_i` in `gr_Q(R)` and `ν_P(f_i) ≥ d`": the limit exists since `R` is
  `𝔪`-adically complete (`exists_forall_sub_mem_pow_of_isAdicComplete`); that it lies in `J`,
  `P^d` and satisfies `f - a ∈ Q^{ν_i+1}` is Krull's intersection theorem
  (`mem_of_forall_mem_sup_pow_maximalIdeal`).  "… the initial form of `f_i` in `gr_P(R)` must be
  in `⋂_k Q^{μ_k} gr^d_P(R) = (0)`": `f - g_k ∈ Q^{d+μ_k}` (Krull again), so `f - g_k ∈ P^d ∩
  Q^{d+μ_k} ⊆ Y^{μ_k}P^d + P^{d+1}` and `Ψ ∈ Q^{μ_k} gr^d_P(R)` for all `k` (`hGr`);
  `⋂_μ Q^μ gr^d_P(R) = 0` is `mem_pow_succ_of_forall_grClassMemPow` (Krull's intersection theorem
  for the finite `R/P`-module `gr^d_P(R)`); so `ν_P(f_i) > d`, against the choice of `d`.
-/
@[blueprint "thm:II.3-3"
  (statement := /-- Let $O$ be a local ring. Let $P$ and $Q$ be prime ideals in $O$ such that
    $Q\supseteq P$ and that $O/P$ and $O/Q$ are both regular. Then the following two
    conditions are equivalent to each other: (i) $\operatorname{gr}_P(O)$ is flat over $O/P$;
    (ii) $\operatorname{gr}_Q(O)$ is flat over $O/Q$ and $\operatorname{gr}_{PO_Q}(O_Q)$ is
    flat over $O_Q/PO_Q$. (p.~200.) -/)
  (proof := /-- (pp.~200--203.) (i)$\Rightarrow$(ii) is clear from \cref{prop:II.1-1} and the
    fact that $\operatorname{gr}_{PO_Q}(O_Q)=\operatorname{gr}_P(O)_Q$. We prove
    (ii)$\Rightarrow$(i). By \cref{cor:II.3-lem9} we may assume that $O$ is complete. By
    Cohen's structure theorem of a complete local ring, $O$ is a quotient ring $R/J$ of a
    complete regular local ring $R$ by an ideal $J$; fix such $R$ and $J$, the prime ideals
    of $R$ lifting $P$ and $Q$ (again written $P$, $Q$), and a system
    $(z_1,\dots,z_r,y_1,\dots,y_s)$ of $R$ with $P=(z_1,\dots,z_r)R$,
    $Q=(z_1,\dots,z_r,y_1,\dots,y_s)R$, $r=\dim R_P$, $r+s=\dim R_Q$. Fix the identifications
    $\operatorname{gr}_P(R)=R'[Z_1,\dots,Z_r]$ with $R'=R/P=O/P$,
    $\operatorname{gr}_Q(R)=R''[Z_1,\dots,Z_r,Y_1,\dots,Y_s]$ with $R''=R/Q=O/Q$, and
    $\operatorname{gr}_Q(\operatorname{gr}_P(R))=\operatorname{gr}^0_{Q'}(\operatorname{gr}_P(R))
    \otimes_{R''}\operatorname{gr}_{Q'}(R')=R''[Z,Y]$ with $Q'=Q/P$ (recall the isomorphisms
    $\varphi$, $\psi$ and $\lambda$ in the paragraph preceding Lemma 10; cf.\
    \cref{def:II.3-double-initial-form}); with $K$ the
    field of quotients of $R''$, $\operatorname{gr}_Q(R)_Q=\operatorname{gr}_{QR_Q}(R_Q)=
    K[Z,Y]$. Applying \cref{cor:II.2-thm2-1} to $\{R_Q,JR_Q,PR_Q,O_Q=R_Q/JR_Q\}$ we get
    elements $h_j\in JR_Q$ with $\nu_{PR_Q}(h_j)=\nu_{QR_Q}(h_j)$ whose initial forms in
    $K[Z,Y]$, obviously forms in $Z_1,\dots,Z_r$ only, generate
    $\operatorname{gr}_{QR_Q}(JR_Q,R_Q)=\operatorname{gr}_Q(J,R)_Q$. Since $K[Z,Y]$ is a free
    $K[Z]$-module on the monomials in the $Y_j$, the $Z$-coefficients of any element of
    $\operatorname{gr}_Q(J,R)$ lie in $\operatorname{gr}_Q(J,R)_Q\cap K[Z]$; by
    \cref{lem:II.3-11-intersection}, $\operatorname{gr}_Q(J,R)_Q\cap R''[Z,Y]=\operatorname{gr}_Q(J,R)$,
    so they lie in $\operatorname{gr}_Q(J,R)\cap R''[Z]$. Thus $\operatorname{gr}_Q(J,R)$ is
    generated by forms $\varphi_1,\dots,\varphi_m$ in $Z_1,\dots,Z_r$ only, with
    $\nu_1\le\dots\le\nu_m$, $\nu_j=\deg\varphi_j$. We claim that for each $j$ there is
    $f_j\in J$ with $\varphi_j$ the initial form of $f_j$ in $\operatorname{gr}_Q(R)$ and
    $\nu_Q(f_j)=\nu_P(f_j)$; then (i) follows from the equivalence of (i) and (iii) of
    \cref{thm:II.2-2}. Let $i$ be the largest integer such that such $f_j$ exist for all
    $j<i$, and suppose $i\le m$. Let $d$ be the largest integer with $\nu_P(g)=d$ for some
    $g\in J$ having $\varphi_i$ as initial form in $\operatorname{gr}_Q(R)$; then $d<\nu_i$.
    Let $\Psi$ be the initial form in $\operatorname{gr}_P(R)$ of such a $g$ and $\mu$ the
    largest integer with $\Psi\in Q^\mu\operatorname{gr}^d_P(R)$. Since the initial form
    $\varphi_i$ of $g$ in $\operatorname{gr}_Q(R)$ is a form only in $Z_1,\dots,Z_r$ of degree
    $\nu_i$, we have $g\in P^{\nu_i}+Q^{\nu_i+1}$, and hence $d+\mu>\nu_i$. Let $\psi$ be the
    initial form of $\Psi$ in $\operatorname{gr}_{Q'}(\operatorname{gr}_P(R))=R''[Z,Y]$,
    homogeneous of degree $d$ in $Z$ and $\mu$ in $Y$, written
    $\psi=\sum_\alpha T_\alpha(Y)\psi_\alpha(Z)$ with distinct monomials $T_\alpha$ of degree
    $\mu$ and forms $\psi_\alpha(Z)$ of degree $d$. By \cref{lem:II.3-10} (Lemma 10, p.~199), $\psi\in\operatorname{gr}_Q(J,R)_Q$, and therefore, by
    \cref{lem:II.3-11-intersection}, $\psi\in\operatorname{gr}_Q(J,R)=(\varphi_1,\dots,\varphi_m)$;
    hence $\psi_\alpha\in(\varphi_1,\dots,\varphi_m)R''[Z]$ and, as $\deg\psi_\alpha=d<\nu_i
    \le\deg\varphi_j$ for $j\ge i$, $\psi_\alpha=\sum_{\beta<i}\lambda_{\alpha,\beta}
    \varphi_\beta$ with forms $\lambda_{\alpha,\beta}\in R''[Z]$ of degree $d-\nu_\beta$.
    Choosing $h_{\alpha,\beta}\in(z_1,\dots,z_r)^{d-\nu_\beta}R$ with initial form
    $\lambda_{\alpha,\beta}$ in $\operatorname{gr}_Q(R)$ and setting
    $h=\sum_\alpha T_\alpha(y)\sum_{\beta<i}h_{\alpha,\beta}f_\beta$ and $g_1=g-h$, we get $g_1\in J$ with (1) initial form $\varphi_i$ in
    $\operatorname{gr}_Q(R)$ (since $\nu_Q(h)\ge\mu+d>\nu_i$), (2) $\nu_P(g_1)=d$ (since
    $\nu_P(h)\ge d$ and by the choice of $d$) and the initial form $\Psi_1$ of $g_1$ in
    $\operatorname{gr}_P(R)$ lying in $Q^{\mu_1}\operatorname{gr}_P(R)$ with $\mu_1>\mu$, and
    (3) $g-g_1=h\in Q^{d+\mu}$. Repeating the process we get a convergent sequence $\{g_k\}$
    in $J$ with initial form $\varphi_i$ in $\operatorname{gr}_Q(R)$, $\nu_P(g_k)=d$, and
    initial forms $\Psi_k\in Q^{\mu_k}\operatorname{gr}_P(R)$ with $\mu_k$ strictly
    increasing. By the completeness of $R$, $f_i=\lim_kg_k\in J$; $\varphi_i$ is the initial
    form of $f_i$ in $\operatorname{gr}_Q(R)$ and $\nu_P(f_i)\ge d$, so $\nu_P(f_i)=d$ by the
    choice of $d$, while the initial form of $f_i$ in $\operatorname{gr}_P(R)$ lies in
    $\bigcap_kQ^{\mu_k}\operatorname{gr}_P(R)=(0)$. This is a contradiction.

    \textbf{Paper misprint.} The text above silently corrects four misprints of pp.~201--202:
    ``all the $\psi_i$ belong to $\operatorname{gr}_Q(J,R)_Q=K[Z]$'' (meant:
    $\operatorname{gr}_Q(J,R)_Q\cap K[Z]$); ``$T_\alpha(Y)$ are distinct polynomials'' (meant:
    monomials); ``$\psi_\alpha(Z)$ are forms only in $Z_1,\dots,Z_s$'' (meant: $Z_1,\dots,Z_r$);
    ``$\Psi_1\in Q^{\mu_1}\mathrm{gp}^d_P(R)$'' (meant: $\operatorname{gr}^d_P(R)$).

    \textbf{Gap in the paper filled.} In (i)$\Rightarrow$(ii), the fact
    $\operatorname{gr}_{PO_Q}(O_Q)=\operatorname{gr}_P(O)_Q$ is proved in Lean as the flat base
    change isomorphism $\varepsilon_n$ of \cref{lem:II.3-9} for $O\to O_Q$. The reduction
    ``we may assume that $O$ is complete'' needs \cref{lem:II.3-9} itself, applied to
    $O\to\hat O$, besides \cref{cor:II.3-lem9}: to pass the flatness of
    $\operatorname{gr}_Q(O)$ to $\hat O$ and to bring the flatness of
    $\operatorname{gr}_{\hat P}(\hat O)$ back to $O$; it also uses that $\hat O$ is noetherian and
    that $\hat O/\hat P$, $\hat O/\hat Q$ are regular.

    \textbf{Gap in the paper filled.} The passage to $K[Z,Y]$ is done as printed: $K$ is
    $R_Q/QR_Q$ (shown to be the field of quotients of $R''$), $\operatorname{gr}_Q(R)\to
    \operatorname{gr}_{QR_Q}(R_Q)$ is the natural map and $\operatorname{gr}_{QR_Q}(R_Q)=K[Z,Y]$ is the
    bijection $((R_Q/QR_Q)[Z])[Y]\to\operatorname{gr}_{QR_Q}(R_Q)$ ($(y,z)$ being quasi-regular in
    $R_Q$); the initial forms of the $h_j$ are forms in $Z$ only ($h_j\in(PR_Q)^{\nu}$,
    $PR_Q=(z)R_Q$), and $\operatorname{gr}_Q(J,R)_Q=\operatorname{gr}_{QR_Q}(JR_Q,R_Q)$ is proved in
    both directions; $\operatorname{gr}_Q(R)_Q\to\operatorname{gr}_{QR_Q}(R_Q)$ is a ring
    isomorphism, and Lemma 11 is used in its printed intersection form
    (\cref{lem:II.3-11-intersection}). The finitely many homogeneous
    generators $\varphi_1,\dots,\varphi_m$ of $\operatorname{gr}_Q(J,R)$ that are forms in $Z$ only,
    ordered by degree (``We take a system of elements \dots such that (a), (b), (c)''), are obtained
    from the noetherianity of $(R/Q)[Z]$ and the fact that the ideal of $\theta$ with
    $\theta(Z)\in\operatorname{gr}_Q(J,R)$ is homogeneous.

    \textbf{Formalization note (encoding).} ``Let $i$ be the largest integer
    $(\ge1)$ such that there exists $f_j\in J$ with $\nu_P(f_j)=\nu_Q(f_j)$ and $\varphi_j$ its
    initial form for every $j<i$. Suppose $i\le m$'': $i$ is the first index for which no $f_i$
    exists, the same integer; ``$\varphi_j$ is the initial form of $f_j$ in
    $\operatorname{gr}_Q(R)$ and $\nu_Q(f_j)=\nu_P(f_j)$'' is encoded as $f_j\in J\cap
    P^{\nu_j}$ and $f_j-a_j\in Q^{\nu_j+1}$ for a lift $a_j\in P^{\nu_j}$ of $\varphi_j$ (and
    $f_j=0$ if $\varphi_j=0$), an equivalent description of the $f_j$.

    \textbf{Gap in the paper filled.} ``Since the initial form $\varphi_i$ of $g$ in
    $\operatorname{gr}_Q(R)$ is a form only in $Z_1,\dots,Z_r$ of degree $\nu_i$, we have $g\in
    P^{\nu_i}+Q^{\nu_i+1}$, and hence $d+\mu>\nu_i$'' (with $\mu$ the largest integer such that
    $\Psi\in Q^\mu\operatorname{gr}^d_P(R)$): Lean proves $P^d\cap Q^{\nu_i+1}\subseteq
    Y^{\nu_i+1-d}P^d+P^{d+1}$ (independence of the bidegree components), so $\Psi\in
    Q^{\nu_i+1-d}\operatorname{gr}^d_P(R)$ and $\mu\ge\nu_i+1-d$. ``Clearly $\varphi_i$ must be the
    initial form of $f_i$ in $\operatorname{gr}_Q(R)$ and $\nu_P(f_i)\ge d$'' and ``the initial form
    of $f_i$ in $\operatorname{gr}_P(R)$ must be in $\bigcap_kQ^{\mu_k}\operatorname{gr}^d_P(R)=(0)$'':
    $f_i\in J$, $f_i\in P^d$ and $f_i-a_i\in Q^{\nu_i+1}$ follow from Krull's intersection theorem
    ($J$, $P^d$, $Q^{\nu_i+1}$ closed), $f_i-g_k\in P^d\cap Q^{d+\mu_k}$ so that the initial forms
    of $f_i$ and $g_k$ agree modulo $Q^{\mu_k}\operatorname{gr}^d_P(R)$, and
    $\bigcap_\mu Q^\mu\operatorname{gr}^d_P(R)=0$ is Krull's intersection theorem for the finite
    $R/P$-module $\operatorname{gr}^d_P(R)$. The passage from $\Psi$ to $\psi$ (the initial form of
    $\Psi$ in $\operatorname{gr}_{Q'}(\operatorname{gr}_P(R))$) is done at the level of
    representatives ($g=h_0+p$ with $h_0\in Y^\mu P^d$, $p\in P^{d+1}$).

    \textbf{Gap in the paper filled.} ``$\deg\psi_\alpha=d<\nu_i\le\deg\varphi_j$ for $j>i$,
    and therefore $\psi_\alpha\in(\varphi_1,\dots,\varphi_{i-1})R''[Z]$'' and the choice of
    $h_{\alpha\beta}$ are written out: the homogeneous components of $\sum_\beta\lambda_\beta
    \varphi_\beta$ in degree $d$ involve only the $\lambda_\beta$ of degree $d-\nu_\beta$, which are
    lifted to homogeneous polynomials over $R$. -/)
  (latexEnv := "theorem")]
theorem isNormallyFlatAlongIdeal_iff_of_le [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (O : Type u) [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] (P Q : Ideal O) [P.IsPrime] [Q.IsPrime] (hPQ : P ≤ Q)
    [IsRegularLocalRing (O ⧸ P)] [IsRegularLocalRing (O ⧸ Q)] :
    IsNormallyFlatAlongIdeal P ↔
      (IsNormallyFlatAlongIdeal Q ∧
        IsNormallyFlatAlongIdeal (P.map (algebraMap O (Localization.AtPrime Q)))) := by
  refine ⟨fun h => ⟨(isNormallyFlatAlongIdeal_of_le P Q hPQ h).2, ?_⟩, fun h => ?_⟩
  · -- `gr_{PO_Q}(O_Q) = gr_P(O)_Q`, and localization preserves freeness.
    intro n
    obtain ⟨e₁⟩ := GrPiece.nonempty_equiv_grModPiece P n
    obtain ⟨e₂⟩ := GrPiece.nonempty_equiv_grModPiece
      (P.map (algebraMap O (Localization.AtPrime Q))) n
    -- `grⁿ_{PO_Q}(O_Q) ≅ grⁿ_P(O) ⊗_{O/P} O_Q/PO_Q`, `O_Q` being flat over `O`.
    obtain ⟨e⟩ := nonempty_grModPiece_baseChange_equiv
      (IsBaseChange.linearMap O (Localization.AtPrime Q)) P n
    have := h n
    have : Module.Free (O ⧸ P) (GrModPiece P O n) := Module.Free.of_equiv e₁
    exact Module.Free.of_equiv (e ≪≫ₗ e₂.symm)
  · exact isNormallyFlatAlongIdeal_of_complete_case
      isNormallyFlatAlongIdeal_map_of_flat_quotient_of_complete O P Q hPQ h.1 h.2

end Theorem3Main

/-! ### Corollary to Theorem 3 (p. 203) -/

namespace Subscheme

variable {X : Scheme.{u}} [IsAlgebraicScheme X]

/-- Normal flatness is preserved by flat base change (Lemma 9's isomorphism
`grⁿ_{IA'}(A') ≅ grⁿ_I(A) ⊗_{A/I} A'/IA'`). -/
private theorem isNormallyFlatAlongIdeal_map_of_flat {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] [Module.Flat A A'] (I : Ideal A) (h : IsNormallyFlatAlongIdeal I) :
    IsNormallyFlatAlongIdeal (I.map (algebraMap A A')) := fun n => by
  obtain ⟨e₁⟩ := GrPiece.nonempty_equiv_grModPiece I n
  obtain ⟨e₂⟩ := GrPiece.nonempty_equiv_grModPiece (I.map (algebraMap A A')) n
  obtain ⟨e⟩ := nonempty_grModPiece_baseChange_equiv (IsBaseChange.linearMap A A') I n
  have := h n
  have : Module.Free (A ⧸ I) (GrModPiece I A n) := Module.Free.of_equiv e₁
  exact Module.Free.of_equiv (e ≪≫ₗ e₂.symm)

/-- Normal flatness is invariant under ring isomorphisms. -/
private theorem isNormallyFlatAlongIdeal_map_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (h : IsNormallyFlatAlongIdeal I) :
    IsNormallyFlatAlongIdeal (I.map (e : A →+* B)) := by
  let := (e : A →+* B).toAlgebra
  have : Module.Flat A B := RingHom.Flat.of_bijective (f := (e : A →+* B)) e.bijective
  exact isNormallyFlatAlongIdeal_map_of_flat I h

/-- On an affine open `V ∋ y`, the stalk `D_y` is generated by the germs of `D(V)`. -/
private theorem stalkIdeal_eq_map_germ {Y : Scheme.{u}} (D : Subscheme Y) (V : Y.affineOpens)
    {y : Y} (hy : y ∈ (V : Y.Opens)) :
    D.stalkIdeal y = (D.ideal V).map (Y.presheaf.germ (V : Y.Opens) y hy).hom := by
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨U, hyU, s, hs, rfl⟩
    obtain ⟨_, ⟨U', hU', rfl⟩, hyU', hU'le⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ (U : Y.Opens) ⊓ V from ⟨hyU, hy⟩)
        ((U : Y.Opens) ⊓ V).isOpen
    let U'' : Y.affineOpens := ⟨U', hU'⟩
    have h1 : U'' ≤ U := fun z hz => (hU'le hz).1
    have h2 : U'' ≤ V := fun z hz => (hU'le hz).2
    have hs' : Y.presheaf.map (CategoryTheory.homOfLE h1).op s ∈ (D.ideal V).map (Y.presheaf.map
        (CategoryTheory.homOfLE h2).op).hom := by
      rw [D.map_ideal h2]
      exact D.ideal_le_comap_ideal h1 hs
    have hle : (D.ideal V).map (Y.presheaf.map (CategoryTheory.homOfLE h2).op).hom ≤
        ((D.ideal V).map (Y.presheaf.germ (V : Y.Opens) y hy).hom).comap
          (Y.presheaf.germ (U'' : Y.Opens) y hyU').hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro t ht
      have e : (Y.presheaf.germ (U'' : Y.Opens) y hyU').hom
          ((Y.presheaf.map (CategoryTheory.homOfLE h2).op).hom t) =
          (Y.presheaf.germ (V : Y.Opens) y hy).hom t := Y.presheaf.germ_res_apply _ _ _ _
      rw [Ideal.mem_comap, Ideal.mem_comap, e]
      exact Ideal.mem_map_of_mem _ ht
    have e : (Y.presheaf.germ (U'' : Y.Opens) y hyU').hom
        ((Y.presheaf.map (CategoryTheory.homOfLE h1).op).hom s) =
        (Y.presheaf.germ (U : Y.Opens) y hyU).hom s := Y.presheaf.germ_res_apply _ _ _ _
    show (Y.presheaf.germ (U : Y.Opens) y hyU).hom s ∈ _
    rw [← e]
    exact hle hs'
  · rw [Ideal.map_le_iff_le_comap]
    intro s hs
    exact Ideal.subset_span ⟨V, hy, s, hs, rfl⟩

/-- If `D_y` is prime and `D_η` is the maximal ideal of `O_η` for a generization `η ⤳ y`, then
`D_y` is the prime of `O_y` corresponding to `η`. -/
private theorem comap_maximalIdeal_stalkSpecializes_eq {Y : Scheme.{u}} (D : Subscheme Y)
    {η y : Y} (h : η ⤳ y) [(D.stalkIdeal y).IsPrime]
    (hη : D.stalkIdeal η = IsLocalRing.maximalIdeal (Y.presheaf.stalk η)) :
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk η)).comap (Y.presheaf.stalkSpecializes h).hom =
      D.stalkIdeal y := by
  let := (Y.presheaf.stalkSpecializes h).hom.toAlgebra
  have hloc := isLocalization_stalkSpecializes_of_specializes h
  have hmap : D.stalkIdeal η = (D.stalkIdeal y).map (algebraMap _ (Y.presheaf.stalk η)) :=
    stalkIdeal_eq_map_stalkSpecializes D h
  have hle : D.stalkIdeal y ≤ (IsLocalRing.maximalIdeal (Y.presheaf.stalk η)).comap
      (Y.presheaf.stalkSpecializes h).hom := by
    intro a ha
    rw [Ideal.mem_comap, ← hη, hmap]
    exact Ideal.mem_map_of_mem _ ha
  refine le_antisymm ?_ hle
  intro a ha
  rw [Ideal.mem_comap, ← hη, hmap] at ha
  have := IsLocalization.under_map_of_isPrime_disjoint (((IsLocalRing.maximalIdeal
    (Y.presheaf.stalk η)).comap (Y.presheaf.stalkSpecializes h).hom).primeCompl)
    (Y.presheaf.stalk η) (I := D.stalkIdeal y) inferInstance (by
      rw [Set.disjoint_left]
      intro b hb hb'
      exact hb (hle hb'))
  rw [← this]
  exact ha

/-- With `η ⤳ y`, `D_y` prime and `D_η` maximal: normal flatness of `Y` along `W` at `η` gives
normal flatness of `(O_y)_{D_y}` along `W_y (O_y)_{D_y}`. -/
private theorem isNormallyFlatAlongIdeal_localization_of_generization {Y : Scheme.{u}}
    (W D : Subscheme Y) {η y : Y} (h : η ⤳ y) [(D.stalkIdeal y).IsPrime]
    (hη : D.stalkIdeal η = IsLocalRing.maximalIdeal (Y.presheaf.stalk η))
    (hW : IsNormallyFlatAlongIdeal (W.stalkIdeal η)) :
    IsNormallyFlatAlongIdeal ((W.stalkIdeal y).map
      (algebraMap (Y.presheaf.stalk y) (Localization.AtPrime (D.stalkIdeal y)))) := by
  let := (Y.presheaf.stalkSpecializes h).hom.toAlgebra
  have hloc := isLocalization_stalkSpecializes_of_specializes h
  have hsub : ((IsLocalRing.maximalIdeal (Y.presheaf.stalk η)).comap
      (Y.presheaf.stalkSpecializes h).hom).primeCompl = (D.stalkIdeal y).primeCompl := by
    ext a
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff,
      comap_maximalIdeal_stalkSpecializes_eq D h hη]
  have : IsLocalization (D.stalkIdeal y).primeCompl (Y.presheaf.stalk η) := by
    rw [← hsub]
    exact hloc
  let e := IsLocalization.algEquiv (D.stalkIdeal y).primeCompl (Y.presheaf.stalk η)
    (Localization.AtPrime (D.stalkIdeal y))
  have hmap : W.stalkIdeal η = (W.stalkIdeal y).map (algebraMap _ (Y.presheaf.stalk η)) :=
    stalkIdeal_eq_map_stalkSpecializes W h
  have := isNormallyFlatAlongIdeal_map_ringEquiv e.toRingEquiv _ hW
  rwa [hmap, Ideal.map_map, show (e.toRingEquiv : Y.presheaf.stalk η →+*
      Localization.AtPrime (D.stalkIdeal y)).comp (algebraMap _ (Y.presheaf.stalk η)) =
      algebraMap _ _ from RingHom.ext fun a => e.commutes a] at this

/-- `x = ι(y)` is a simple point of the subscheme `W` iff `y` is a simple point of the scheme
`W` (`O_{W,y} ≅ O_{X,x}/W_x`). -/
private theorem isSimpleAt_ι_iff {Y : Scheme.{u}} (W : Subscheme Y) (y : W.toScheme) :
    W.IsSimpleAt (W.ι y) ↔ W.toScheme.IsSimpleAt y := by
  obtain ⟨e⟩ := nonempty_stalk_quot_equiv W y
  have hy : W.ι y ∈ W.pts := by
    show W.ι y ∈ (W.support : Set Y)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨y, rfl⟩
  constructor
  · rintro ⟨-, h⟩
    exact IsRegularLocalRing.of_ringEquiv e
  · intro h
    have : IsRegularLocalRing (W.toScheme.presheaf.stalk y) := h
    exact ⟨hy, IsRegularLocalRing.of_ringEquiv e.symm⟩

/-- Every point of the support of a subscheme is in the image of its closed immersion. -/
private theorem exists_ι_eq {Y : Scheme.{u}} (W : Subscheme Y) {x : Y} (hx : x ∈ W.pts) :
    ∃ y : W.toScheme, W.ι y = x := by
  have : x ∈ Set.range W.ι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hx
  exact this

/-- `D ⊆ W` gives `W_x ⊆ D_x`. -/
private theorem stalkIdeal_le_of_isContainedIn {Y : Scheme.{u}} {W D : Subscheme Y}
    (hDW : D.IsContainedIn W) (x : Y) : W.stalkIdeal x ≤ D.stalkIdeal x := by
  refine Ideal.span_mono ?_
  rintro _ ⟨U, hxU, s, hs, rfl⟩
  exact ⟨U, hxU, s, hDW U hs, rfl⟩

/-- For `D ⊆ W`, the total transform `D' = ι_W⁻¹(D)` of `D` in the scheme `W` is isomorphic to
`D`: the square `D → W → X`, `D = D → X` is cartesian, `ι_W` being a monomorphism. -/
private theorem nonempty_totalTransform_iso {Y : Scheme.{u}} {W D : Subscheme Y}
    (hDW : D.IsContainedIn W) : Nonempty ((totalTransform W.ι D).toScheme ≅ D.toScheme) := by
  have hWD : W ≤ D := fun U => hDW U
  have hsq : CategoryTheory.IsPullback (Scheme.IdealSheafData.inclusion hWD)
      (CategoryTheory.CategoryStruct.id D.toScheme) W.ι D.ι :=
    CategoryTheory.IsPullback.of_vert_isIso_mono ⟨by
      rw [Scheme.IdealSheafData.inclusion_subschemeι, CategoryTheory.Category.id_comp]⟩
  exact ⟨D.comapIso W.ι ≪≫ hsq.isoPullback.symm⟩

/-- A scheme isomorphic to a non-singular scheme is non-singular. -/
private theorem isNonsingular_of_iso {A B : Scheme.{u}} (e : A ≅ B) (hB : B.IsNonsingular) :
    A.IsNonsingular := by
  intro a
  have : IsRegularLocalRing (B.presheaf.stalk (e.hom a)) := hB (e.hom a)
  exact IsRegularLocalRing.of_ringEquiv (CategoryTheory.asIso
    (e.hom.stalkMap a)).commRingCatIsoToRingEquiv

/-- A scheme isomorphic to an irreducible scheme is irreducible. -/
private theorem irreducibleSpace_of_iso {A B : Scheme.{u}} (e : A ≅ B) [IrreducibleSpace B] :
    IrreducibleSpace A := by
  have hsurj : Function.Surjective e.inv := fun a => ⟨e.hom a, by
    rw [← Scheme.Hom.comp_apply, CategoryTheory.Iso.hom_inv_id]
    rfl⟩
  rw [irreducibleSpace_def]
  have := (IrreducibleSpace.isIrreducible_univ B).image e.inv e.inv.continuous.continuousOn
  rwa [Set.image_univ, hsurj.range_eq] at this

/-- First half of the Corollary to Theorem 3: Corollary 4 of Proposition 1 applied to the
scheme `W` and its subscheme `D' = ι_W⁻¹(D) ≅ D`. -/
private theorem forall_isSimpleAt_of_normallyFlat_chain [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] (W D : Subscheme X)
    (hDW : D.IsContainedIn W) (hD : D.IsNonsingular) (hirr : D.IsIrreducible)
    (hW : W.IsNormallyFlatAlong' D) {x₀ : X} (hx₀ : x₀ ∈ D.pts) (hs : W.IsSimpleAt x₀) :
    ∀ x ∈ D.pts, W.IsSimpleAt x := by
  have := isAlgebraicScheme_toScheme W
  obtain ⟨e⟩ := nonempty_totalTransform_iso hDW
  have : IrreducibleSpace D.toScheme := hirr
  have hD' : (totalTransform W.ι D).IsNonsingular := isNonsingular_of_iso e hD
  have hirr' : (totalTransform W.ι D).IsIrreducible := irreducibleSpace_of_iso e
  have hpts : ∀ y : W.toScheme, y ∈ (totalTransform W.ι D).pts ↔ W.ι y ∈ D.pts := fun y => by
    show y ∈ ((D.comap W.ι).support : Set W.toScheme) ↔ _
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have hnf : (totalTransform W.ι D).IsNormallyFlatAlong := by
    intro y hy
    obtain ⟨y', hy', hnf⟩ := hW (W.ι y) ((hpts y).mp hy)
    rwa [W.ι.isEmbedding.injective hy'] at hnf
  have hsimple : ∃ y ∈ (totalTransform W.ι D).pts, W.toScheme.IsSimpleAt y := by
    obtain ⟨y, rfl⟩ := exists_ι_eq W (pts_subset_of_isContainedIn hDW hx₀)
    exact ⟨y, (hpts y).mpr hx₀, (isSimpleAt_ι_iff W y).mp hs⟩
  have h := forall_isSimpleAt_of_isNormallyFlatAlong (X := W.toScheme) (totalTransform W.ι D)
    hD' hirr' hnf hsimple
  intro x hx
  obtain ⟨y, rfl⟩ := exists_ι_eq W (pts_subset_of_isContainedIn hDW hx)
  exact (isSimpleAt_ι_iff W y).mpr (h y ((hpts y).mpr hx))

/-- Corollary to Theorem 3, p. 203: "Let V be an algebraic scheme, W a subscheme of V, and D a
non-singular irreducible subscheme of W. Suppose that both V and W are normally flat along D,
and that there exists at least one simple point of W which is contained in D and at which V is
normally flat along W. Then W has no multiple points in D and V is normally flat along W at
every point of D."

Encoding: `V = X`; "V is normally flat along D" is `D.IsNormallyFlatAlong`; "W is normally
flat along D" is `W.IsNormallyFlatAlong' D`; "V is normally flat along W at x" is
`W.IsNormallyFlatAlongAt x`; "x is a simple point of W" is `W.IsSimpleAt x`, and "W has no
multiple points in D" is "every point of D is a simple point of W".

The proof is the paper's: Corollary 4 of Proposition 1 gives that `D` contains no multiple point
of `W`; "By the assumption that `V` is normally flat along `W` at some point of `D`, `V` is normally
flat along `W` at the generic point of `D`.  (See Theorem 1, §1.)" is Theorem 1 of §1, in the form
`exists_isOpen_isNormallyFlatAlongAt` (Theorem 1 applied to `A/I` and `gr_I(A)`, as in the proof of
the corollary to Theorem 1, p. 189): the points of `W` at which `V` is normally flat along `W` form
the trace on `W` of an open subset `U₀` of `V`.  The given point of `D` lies in `U₀`, hence so does
its generization, the generic point of `D`; the rest is Theorem 3.  (This openness holds for an
arbitrary subscheme `W`; reducedness is needed only for the density in the corollary to Theorem 1,
`Subscheme.exists_isOpen_dense_isNormallyFlatAlong`.)  Theorem 3 is fully proved, so the
result rests only on cited results. -/
@[blueprint "cor:II.3-thm3"
  (statement := /-- Let $V$ be an algebraic scheme, $W$ a subscheme of $V$, and $D$ a
    non-singular irreducible subscheme of $W$. Suppose that both $V$ and $W$ are normally
    flat along $D$, and that there exists at least one simple point of $W$ which is contained
    in $D$ and at which $V$ is normally flat along $W$. Then $W$ has no multiple points in $D$
    and $V$ is normally flat along $W$ at every point of $D$. (p.~203.) -/)
  (proof := /-- It follows from \cref{cor:II.1-prop1-4} (applied to $W$ and $D$) that $D$
    contains no multiple points of $W$. By the assumption that $V$ is normally flat along $W$
    at some point of $D$, $V$ is normally flat along $W$ at the generic point of $D$ (see
    \cref{thm:II.1-1}). Since $D$ is non-singular and $W$ has no multiple points in $D$, it
    is sufficient, for the normal flatness of $V$ along $W$ at every point of $D$, that $V$
    is normally flat along $D$ (see \cref{thm:II.3-3}).

    \textbf{Proof in Lean.} The normal flatness at the generic point of $D$ is Theorem~1 of
    \S1 (\cref{thm:II.1-1}) as in the proof of its corollary (\cref{cor:II.1-thm1}): applied to
    $A/I$ and $\operatorname{gr}_I(A)$, it shows that the points of $W$ at which $V$ is normally
    flat along $W$ form the trace on $W$ of an open subset $U_0$ of $V$ (for an arbitrary
    subscheme $W$; reducedness is needed only for the density in the corollary). The given point
    of $D$ lies in $U_0$, hence so does its generization, the generic point of $D$. -/)
  (latexEnv := "corollary")]
theorem isSimpleAt_and_isNormallyFlatAlongAt_of_normallyFlat_chain [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (W D : Subscheme X)
    (hDW : D.IsContainedIn W) (hD : D.IsNonsingular) (hirr : D.IsIrreducible)
    (hV : D.IsNormallyFlatAlong) (hW : W.IsNormallyFlatAlong' D)
    (hx : ∃ x ∈ D.pts, W.IsSimpleAt x ∧ W.IsNormallyFlatAlongAt x) :
    (∀ x ∈ D.pts, W.IsSimpleAt x) ∧ ∀ x ∈ D.pts, W.IsNormallyFlatAlongAt x := by
  obtain ⟨x₀, hx₀, hs₀, hnf₀⟩ := hx
  -- By Corollary 4 of Proposition 1 (applied to `W` and `D`), `D` contains no multiple point
  -- of `W`.
  have hsimple := forall_isSimpleAt_of_normallyFlat_chain W D hDW hD hirr hW hx₀ hs₀
  refine ⟨hsimple, fun x hx => ⟨pts_subset_of_isContainedIn hDW hx, ?_⟩⟩
  have := IsAlgebraicScheme.isNoetherian X
  -- The generic point `η` of `D`; `D_η` is the maximal ideal of `O_{X,η}` (`D` is reduced).
  have : IrreducibleSpace D.toScheme := hirr
  have hred : D.IsReduced := by
    have : ∀ z : D.toScheme, _root_.IsReduced (D.toScheme.presheaf.stalk z) := fun z => by
      have : IsRegularLocalRing (D.toScheme.presheaf.stalk z) := hD z
      have := isDomain_of_isRegularLocalRing (D.toScheme.presheaf.stalk z)
      infer_instance
    exact isReduced_of_isReduced_stalk D.toScheme
  have hDη : D.stalkIdeal (D.ι (genericPoint D.toScheme)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (D.ι (genericPoint D.toScheme))) :=
    stalkIdeal_eq_maximalIdeal_of_isReduced D hred _ (by
      rw [irreducibleComponents_eq_singleton, (genericPoint_spec D.toScheme).def]
      exact Set.mem_singleton _)
  have hsp : ∀ y ∈ D.pts, D.ι (genericPoint D.toScheme) ⤳ y := by
    intro y hy
    obtain ⟨z, rfl⟩ := exists_ι_eq D hy
    exact (genericPoint_specializes z).map D.ι.continuous
  -- "By the assumption that `V` is normally flat along `W` at some point of `D`, `V` is normally
  -- flat along `W` at the generic point of `D`.  (See Theorem 1, §1.)"  By Theorem 1 of §1 the
  -- points of `W` at which `V` is normally flat along `W` are those of an open subset `U₀`;
  -- it contains `x₀`, hence the generic point `η` of `D`, a generization of `x₀`.
  obtain ⟨U₀, hU₀, hU₀iff⟩ := exists_isOpen_isNormallyFlatAlongAt W
  have hηD : D.ι (genericPoint D.toScheme) ∈ D.pts := by
    show D.ι (genericPoint D.toScheme) ∈ (D.support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨_, rfl⟩
  have hx₀U : x₀ ∈ U₀ := (hU₀iff x₀ (pts_subset_of_isContainedIn hDW hx₀)).mpr hnf₀
  have hηU : D.ι (genericPoint D.toScheme) ∈ U₀ := (hsp x₀ hx₀).mem_open hU₀ hx₀U
  have hnfη : IsNormallyFlatAlongIdeal (W.stalkIdeal (D.ι (genericPoint D.toScheme))) :=
    ((hU₀iff _ (pts_subset_of_isContainedIn hDW hηD)).mp hηU).2
  -- At `x ∈ D`: `O = O_{X,x}`, `P = W_x ⊆ Q = D_x`, `O/P` and `O/Q` regular.
  obtain ⟨y, rfl⟩ := exists_ι_eq D hx
  obtain ⟨eQ⟩ := nonempty_stalk_quot_equiv D y
  have : IsRegularLocalRing (D.toScheme.presheaf.stalk y) := hD y
  have : IsRegularLocalRing (X.presheaf.stalk (D.ι y) ⧸ D.stalkIdeal (D.ι y)) :=
    IsRegularLocalRing.of_ringEquiv eQ.symm
  have : (D.stalkIdeal (D.ι y)).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp
    (isDomain_of_isRegularLocalRing _)
  have : IsRegularLocalRing (X.presheaf.stalk (D.ι y) ⧸ W.stalkIdeal (D.ι y)) :=
    (hsimple _ hx).2
  have : (W.stalkIdeal (D.ι y)).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp
    (isDomain_of_isRegularLocalRing _)
  -- `gr_{PO_Q}(O_Q) = gr_{W_η}(O_{X,η})` is flat, and `gr_Q(O)` is flat; apply Theorem 3.
  exact (isNormallyFlatAlongIdeal_iff_of_le _ _ _ (stalkIdeal_le_of_isContainedIn hDW _)).mpr
    ⟨(hV _ hx).2, isNormallyFlatAlongIdeal_localization_of_generization W D (hsp _ hx) hDη hnfη⟩

end Subscheme

end Hironaka

