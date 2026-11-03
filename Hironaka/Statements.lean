/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Architect

/-!
# The declarations of the compared statements

The definitions (and the few lemmas used in them) that the statements compared by `lake comparator` need — the
fundamental theorems, the main theorems and the statements of Ch. 0 — together with the classes of the cited results
(`HironakaCitedResults`, `HironakaCitedResultsCh0`). Each of the three Challenges (`Challenge.lean`,
`ChallengeMainCh0.lean`, `ChallengeCh0.lean`, one per registry entry) restates the declarations its statements need, in
the order of this file and with shorter docstrings, and Comparator checks that they are identical: Lean reuses an
identical matcher or auxiliary proof only within a module, so they are kept together in one module. Each declaration
keeps its docstring and blueprint node; the chapter files that use them import this module.
-/

@[expose] public section

noncomputable section

universe v₁ u₁ u
open IsLocalRing CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

namespace Hironaka
section
variable {O : Type u} [CommRing O]
/-- The `p`-th graded piece `Pᵖ / Pᵖ⁺¹` of the associated graded ring `gr_P(O)`, as an
`O`-module: the submodule `Pᵖ ⊆ O` modulo the preimage of `Pᵖ⁺¹`. -/
abbrev GrPiece (P : Ideal O) (p : ℕ) : Type u :=
  ↥(P ^ p) ⧸ (Submodule.comap (P ^ p).subtype (P ^ (p + 1)))

/-- `P` annihilates `Pᵖ/Pᵖ⁺¹`, so it is an `O/P`-module. -/
theorem grPiece_isTorsionBySet (P : Ideal O) (p : ℕ) :
    Module.IsTorsionBySet O (GrPiece P p) (P : Set O) := by
  intro m a
  induction m using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_smul, smul_eq_mul, pow_succ']
    exact Ideal.mul_mem_mul a.2 x.2

noncomputable instance GrPiece.module (P : Ideal O) (p : ℕ) : Module (O ⧸ P) (GrPiece P p) :=
  (grPiece_isTorsionBySet P p).module

end
/-- The regular locus of `Spec A`, as a set of primes. -/
def regularLocus (A : Type u) [CommRing A] : Set (PrimeSpectrum A) :=
  {p | IsRegularLocalRing (Localization.AtPrime p.asIdeal)}

/-- The cited result `Hironaka.isRegularLocalRing_of_flat_of_isRegularLocalRing` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResults`. -/
class _root_.Hironaka.Cited.IsRegularLocalRingOfFlatOfIsRegularLocalRing : Prop where
  /-- The statement of `Hironaka.isRegularLocalRing_of_flat_of_isRegularLocalRing`. -/
  isRegularLocalRing_of_flat_of_isRegularLocalRing : ∀ {R R' : Type u} [CommRing R]
      [CommRing R'] [IsLocalRing R] [IsNoetherianRing R] [Algebra R R'] [Module.Flat R R']
      [IsRegularLocalRing R'] [IsLocalHom (algebraMap R R')],
      IsRegularLocalRing R

/-- The cited result `Hironaka.exists_flat_isLocalHom_adicCompletion_of_flat` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResults`. -/
class _root_.Hironaka.Cited.ExistsFlatIsLocalHomAdicCompletionOfFlat : Prop where
  /-- The statement of `Hironaka.exists_flat_isLocalHom_adicCompletion_of_flat`. -/
  exists_flat_isLocalHom_adicCompletion_of_flat : ∀ {R R' : Type u} [CommRing R] [CommRing R']
      [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing R'] [IsNoetherianRing R'] [Algebra R R']
      [Module.Flat R R'] [IsLocalHom (algebraMap R R')],
      ∃ φ : AdicCompletion (maximalIdeal R) R →+* AdicCompletion (maximalIdeal R') R',
        (∀ x : R, φ (algebraMap R (AdicCompletion (maximalIdeal R) R) x) =
          algebraMap R' (AdicCompletion (maximalIdeal R') R') (algebraMap R R' x)) ∧
        φ.Flat ∧ IsLocalHom φ

/-- Coefficientwise application of an additive map `d : R → R` to the polynomial ring `R[σ]`. -/
def mapCoeffsFun {R : Type*} (σ : Type*) [CommRing R] {F : Type*} [FunLike F R R]
    [AddMonoidHomClass F R R] (d : F) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange d (map_zero d) (AddMonoidAlgebra.coeff p))

theorem coeff_mapCoeffsFun {R : Type*} (σ : Type*) [CommRing R] {F : Type*} [FunLike F R R]
    [AddMonoidHomClass F R R] (d : F) (p : MvPolynomial σ R) (m : σ →₀ ℕ) :
    (mapCoeffsFun σ d p).coeff m = d (p.coeff m) := rfl

section
variable {k R σ : Type*} [CommRing k] [CommRing R] [Algebra k R]
theorem mapCoeffsFun_add (d : Derivation k R R) (p q : MvPolynomial σ R) :
    mapCoeffsFun σ d (p + q) = mapCoeffsFun σ d p + mapCoeffsFun σ d q := by
  ext m
  rw [coeff_mapCoeffsFun]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, coeff_mapCoeffsFun]

theorem mapCoeffsFun_smul (d : Derivation k R R) (c : k) (p : MvPolynomial σ R) :
    mapCoeffsFun σ d (c • p) = c • mapCoeffsFun σ d p := by
  ext m
  rw [coeff_mapCoeffsFun]
  simp [coeff_mapCoeffsFun]

theorem mapCoeffsFun_mul (d : Derivation k R R) (p q : MvPolynomial σ R) :
    mapCoeffsFun σ d (p * q) = p * mapCoeffsFun σ d q + q * mapCoeffsFun σ d p := by
  classical
  ext m
  rw [coeff_mapCoeffsFun]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_mul, map_sum,
    coeff_mapCoeffsFun, Derivation.leibniz, smul_eq_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_equiv (Equiv.prodComm _ _) (by intro x; simp [add_comm]) (by intro x _; rfl)

variable (k σ) in
/-- Coefficientwise application of a derivation `d` of `R` to the polynomial ring `R[σ]`: the
partial derivative of a polynomial with respect to its coefficients. -/
def mapCoeffsDerivation (d : Derivation k R R) :
    Derivation k (MvPolynomial σ R) (MvPolynomial σ R) where
  toLinearMap :=
    { toFun := mapCoeffsFun σ d
      map_add' := mapCoeffsFun_add d
      map_smul' := mapCoeffsFun_smul d }
  map_one_eq_zero' := by
    ext m
    show d ((1 : MvPolynomial σ R).coeff m) = 0
    classical
    rw [MvPolynomial.coeff_one]
    split_ifs
    · exact Derivation.map_one_eq_zero d
    · exact map_zero d
  leibniz' := fun p q => by
    simpa [smul_eq_mul] using mapCoeffsFun_mul d p q

end
/-- The ring `k⟦t₁,…,t_n⟧[x₁,…,x_m]` of footnote 30: a polynomial ring in `m` variables over a
formal power series ring in `n` variables over a field `k`.  A `def` (not an `abbrev`) so that all
instances on it come from the single `CommRing` instance below; this avoids an instance diamond
between `Ideal.Quotient.semiring` and `CommSemiring.toSemiring` for `MvPolynomial` over
`MvPowerSeries`. -/
def PowerSeriesPolynomialRing (k : Type u) [Field k] (n m : ℕ) : Type u :=
  MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)

end Hironaka
namespace Hironaka.PowerSeriesPolynomialRing
section
variable (k : Type u) [Field k] (n m : ℕ)
instance : CommRing (PowerSeriesPolynomialRing k n m) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))

instance : Algebra k (PowerSeriesPolynomialRing k n m) :=
  inferInstanceAs (Algebra k (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))

/-- The partial derivation `∂/∂t_j` of `k⟦t⟧[x]` (differentiating the coefficients). -/
def pderivT (j : Fin n) :
    Derivation k (PowerSeriesPolynomialRing k n m) (PowerSeriesPolynomialRing k n m) :=
  mapCoeffsDerivation k (Fin m)
    (MvPowerSeries.pderiv j : Derivation k (MvPowerSeries (Fin n) k) (MvPowerSeries (Fin n) k))

/-- The partial derivation `∂/∂x_l` of `k⟦t⟧[x]` (the formal derivative in the polynomial
variable `x_l`). -/
def pderivX (l : Fin m) :
    Derivation k (PowerSeriesPolynomialRing k n m) (PowerSeriesPolynomialRing k n m) :=
  (MvPolynomial.pderiv l : Derivation (MvPowerSeries (Fin n) k)
    (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))
    (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).restrictScalars k

/-- The `n + m` partial derivations `∂/∂t₁, …, ∂/∂t_n, ∂/∂x₁, …, ∂/∂x_m` of `k⟦t⟧[x]`. -/
def pderiv (j : Fin (n + m)) :
    Derivation k (PowerSeriesPolynomialRing k n m) (PowerSeriesPolynomialRing k n m) :=
  Fin.addCases (motive := fun _ => Derivation k (PowerSeriesPolynomialRing k n m)
    (PowerSeriesPolynomialRing k n m)) (pderivT k n m) (pderivX k n m) j

end
section
variable (k : Type u) [Field k] (n m : ℕ)
variable {k n m}
/-- The jacobian matrix `J(f₁,…,f_r) = (∂f_i/∂u_j)` of `r` elements of `k⟦t⟧[x]` with respect to
the `n + m` variables `u = (t, x)` (Nagata [14], p. 428). -/
def jacobian {r : ℕ} (f : Fin r → PowerSeriesPolynomialRing k n m) :
    Matrix (Fin r) (Fin (n + m)) (PowerSeriesPolynomialRing k n m) :=
  Matrix.of fun i j => pderiv k n m j (f i)

/-- Reduction modulo a prime `𝔮` of `T`, with values in the fraction field of `T/𝔮` (the residue
field of `T_𝔮`): "modulo 𝔮" in Nagata's theorem. -/
def residueMap (𝔮 : Ideal (PowerSeriesPolynomialRing k n m)) [𝔮.IsPrime] :
    PowerSeriesPolynomialRing k n m →+* FractionRing (PowerSeriesPolynomialRing k n m ⧸ 𝔮) :=
  (algebraMap _ _).comp (Ideal.Quotient.mk 𝔮)

end
end Hironaka.PowerSeriesPolynomialRing
namespace Hironaka
/-- The cited result `Hironaka.exists_surjective_mvPowerSeries_of_isAdicComplete` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResults`. -/
class _root_.Hironaka.Cited.ExistsSurjectiveMvPowerSeriesOfIsAdicComplete : Prop where
  /-- The statement of `Hironaka.exists_surjective_mvPowerSeries_of_isAdicComplete`. -/
  exists_surjective_mvPowerSeries_of_isAdicComplete : ∀ (S : Type u) [CommRing S]
      [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
      [CharZero (ResidueField S)],
      ∃ (n : ℕ) (k : Type u) (_ : Field k) (_ : CharZero k) (f : MvPowerSeries (Fin n) k →+* S),
        Function.Surjective f

open PowerSeriesPolynomialRing in
/-- The cited result `Hironaka.isRegularLocalRing_localization_iff_rank_jacobian_eq_height` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResults`. -/
class _root_.Hironaka.Cited.IsRegularLocalRingLocalizationIffRankJacobianEqHeight : Prop where
  /-- The statement of `Hironaka.isRegularLocalRing_localization_iff_rank_jacobian_eq_height`. -/
  isRegularLocalRing_localization_iff_rank_jacobian_eq_height : ∀ (k : Type u) [Field k]
      [CharZero k] (n m : ℕ) (𝔭 : Ideal (PowerSeriesPolynomialRing k n m)) [𝔭.IsPrime]
      (𝔮' : Ideal (PowerSeriesPolynomialRing k n m ⧸ 𝔭)) [𝔮'.IsPrime] {r : ℕ}
      (f : Fin r → PowerSeriesPolynomialRing k n m) (hf : Ideal.span (Set.range f) = 𝔭),
      IsRegularLocalRing (Localization.AtPrime 𝔮') ↔
        (((jacobian f).map (residueMap (𝔮'.comap (Ideal.Quotient.mk 𝔭)))).rank : ℕ∞) =
          𝔭.height

/-- The cited result `Hironaka.isRegularLocalRing_localization_of_isRegularLocalRing` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResults`. -/
class _root_.Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing : Prop where
  /-- The statement of `Hironaka.isRegularLocalRing_localization_of_isRegularLocalRing`. -/
  isRegularLocalRing_localization_of_isRegularLocalRing : ∀ (R : Type u) [CommRing R]
      [IsRegularLocalRing R] (P : Ideal R) [P.IsPrime],
      IsRegularLocalRing (Localization.AtPrime P)

/-- Hironaka's class 𝔅 (p. 161): the local rings `S` such that (i) `S` is noetherian with residue
field of characteristic zero, and (ii) for every `S`-algebra `A` of finite type, a prime of
`A ⊗_S Ŝ` is a regular point if and only if its contraction to `A` is (the singular locus of
`Spec(A ⊗_S Ŝ)` is the preimage of that of `Spec A`), where `Ŝ` is the `𝔪_S`-adic completion of
`S`.  The formulation is attributed by Hironaka to Grothendieck (footnote 30). -/
@[blueprint "def:class-A"
  (statement := /-- The class $\mathfrak{B}$ consists of the local rings $S$ such that
    (i) $S$ is noetherian with residue field of characteristic zero, and
    (ii) for every $S$-algebra of finite type $A$, the singular locus of
    $\operatorname{Spec}(A\otimes_S\hat S)$ is the preimage of that of $\operatorname{Spec}A$
    under the canonical morphism, where $\hat S$ is the completion of $S$.
    Formalization note (encoding): (ii) is stated through the regular loci (the complements of
    the singular loci), and $\hat S$ is the $\mathfrak m_S$-adic completion. -/)
  (latexEnv := "definition")]
class IsHironakaBase (S : Type u) [CommRing S] [IsLocalRing S] : Prop
    extends IsNoetherianRing S where
  charZero_residueField : CharZero (ResidueField S)
  completion_singularLocus :
    ∀ (A : Type u) [CommRing A] [Algebra S A] [Algebra.FiniteType S A]
      (q : PrimeSpectrum (TensorProduct S A (AdicCompletion (maximalIdeal S) S))),
      q ∈ regularLocus _ ↔
        PrimeSpectrum.comap (algebraMap A (TensorProduct S A (AdicCompletion (maximalIdeal S) S))) q
          ∈ regularLocus A

attribute [instance] IsHironakaBase.charZero_residueField

/-- The cited result `Hironaka.IsHironakaBase.isClosed_singularLocus` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResults`. -/
class _root_.Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus : Prop where
  /-- The statement of `Hironaka.IsHironakaBase.isClosed_singularLocus`. -/
  isClosed_singularLocus : ∀ (S : Type u) [CommRing S] [IsLocalRing S]
      [IsHironakaBase S] (A : Type u) [CommRing A] [Algebra S A] [Algebra.FiniteType S A],
      IsClosed (regularLocus A)ᶜ

end Hironaka
namespace AlgebraicGeometry.Scheme
section
variable (X : Scheme.{u})
/-- `X` is simple (= regular, non-singular) at `x`: the local ring is regular (footnote 29). -/
def IsSimpleAt (x : X) : Prop := IsRegularLocalRing (X.presheaf.stalk x)

/-- A non-singular scheme. -/
def IsNonsingular : Prop := ∀ x : X, X.IsSimpleAt x

end
end AlgebraicGeometry.Scheme
namespace Hironaka
/-- Subschemes of `X` are (closed) subschemes, i.e. quasi-coherent sheaves of ideals; on the
locally noetherian schemes of this paper these are exactly the coherent ones. -/
abbrev Subscheme (X : Scheme.{u}) := X.IdealSheafData

end Hironaka
namespace Hironaka.Subscheme
section
variable {X : Scheme.{u}}
/-- The underlying set of points of a subscheme. -/
def pts (D : Subscheme X) : Set X := (D.support : Set X)

/-- The associated scheme and its closed immersion into `X`. -/
abbrev toScheme (D : Subscheme X) : Scheme.{u} := D.subscheme

abbrev ι (D : Subscheme X) : D.toScheme ⟶ X := D.subschemeι

/-- The stalk of the ideal sheaf at a point, as an ideal of the local ring `O_{X,x}`
(generated by the germs of sections over affine opens containing `x`). -/
def stalkIdeal (D : Subscheme X) (x : X) : Ideal (X.presheaf.stalk x) :=
  Ideal.span {a | ∃ (U : X.affineOpens) (hx : x ∈ (U : Opens X)) (s : Γ(X, U)),
    s ∈ D.ideal U ∧ X.presheaf.germ (U : Opens X) x hx s = a}

/-- The empty subscheme (ideal sheaf `O_X`). -/
def empty : Subscheme X := ⊤

def IsIrreducible (D : Subscheme X) : Prop := IrreducibleSpace D.toScheme

def IsNonsingular (D : Subscheme X) : Prop := D.toScheme.IsNonsingular

/-- `x` is a simple point of the subscheme `D`. -/
def IsSimpleAt (D : Subscheme X) (x : X) : Prop :=
  x ∈ D.pts ∧ IsRegularLocalRing ((X.presheaf.stalk x) ⧸ D.stalkIdeal x)

/-- The ideal sheaf of `D` is *invertible*: locally principal, generated by a non-zero-divisor
(Ch. 0 §2 "invertible", Ch. 0 §5 Def. 2). -/
def IsInvertibleIdeal (D : Subscheme X) : Prop :=
  ∀ x : X, ∃ (U : X.affineOpens) (_ : x ∈ (U : Opens X)) (a : Γ(X, U)),
    D.ideal U = Ideal.span {a} ∧ a ∈ nonZeroDivisors Γ(X, U)

end
/-- The *total transform* `f⁻¹(D)` of a subscheme `D ⊆ X` by a morphism `f : X' ⟶ X`: the
subscheme of `X'` defined by the sheaf of ideals generated by that of `D` (footnote 35).
We realize it as the kernel of the base change of the closed immersion `D ↪ X` along `f`,
which is the same closed subscheme. -/
@[blueprint "def:total-transform"
  (statement := /-- Let $f\colon X'\to X$ be a morphism of schemes and $B$ a subscheme of $X$.
    The \emph{total transform} $f^{-1}(B)$ is the subscheme of $X'$ defined by the sheaf of
    ideals on $X'$ generated by that of $B$ on $X$. (Footnote 35, p.\ 168.)
    Formalization note (encoding): it is realized as the kernel of the base change of the
    closed immersion $B\hookrightarrow X$ along $f$, i.e.\ the pull-back of the ideal sheaf. -/)
  (latexEnv := "definition")]
noncomputable def totalTransform {X X' : Scheme.{u}} (f : X' ⟶ X) (D : Subscheme X) :
    Subscheme X' :=
  (pullback.fst f D.ι).ker

end Hironaka.Subscheme
namespace Hironaka
/-- A *monoidal transformation of `X` with center `B`*: a morphism `f : X' ⟶ X` such that the
total transform of `B` is invertible and which is universal for this property. -/
@[blueprint "def:monoidal-transformation"
  (statement := /-- Let $X$ be a scheme and $B$ a subscheme with sheaf of ideals $I$. A
    \emph{monoidal transformation of $X$ with center $B$} is a morphism $f\colon X'\to X$
    such that (i) $f^{-1}(I)$ is invertible, and (ii) for every morphism $f'\colon X''\to X$
    with $f'^{-1}(I)$ invertible there is a unique $h\colon X''\to X'$ with $f'=f\circ h$.
    (p.\ 166; the universal property may be taken over all schemes.)
    Formalization note (encoding): a monoidal transformation is data $(X',f)$ satisfying (i)
    and (ii), with (ii) quantified over all schemes (p.~166: ``remains equivalent''; this
    equivalence is not proved in Lean); the center is part of the type, as on pp.~129, 167;
    ``invertible'' is ``locally generated by a non-zero-divisor''. -/)
  (latexEnv := "definition")]
structure MonoidalTransformation (X : Scheme.{u}) (B : Subscheme X) where
  /-- The blown-up scheme `X'`. -/
  X' : Scheme.{u}
  /-- The morphism `f : X' ⟶ X`. -/
  f : X' ⟶ X
  /-- (i): `f⁻¹(B)` is defined by an invertible sheaf of ideals. -/
  invertible : (Subscheme.totalTransform f B).IsInvertibleIdeal
  /-- (ii): universality among morphisms with invertible pullback of `I_B`. -/
  universal : ∀ (X'' : Scheme.{u}) (f' : X'' ⟶ X),
    (Subscheme.totalTransform f' B).IsInvertibleIdeal → ∃! h : X'' ⟶ X', h ≫ f = f'

end Hironaka
namespace Hironaka.MonoidalTransformation
section
variable {X : Scheme.{u}} {B : Subscheme X}
/-- The cited result `Hironaka.MonoidalTransformation.exists_isProper` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResults`. -/
class _root_.Hironaka.Cited.MonoidalTransformationExistsIsProper : Prop where
  /-- The statement of `Hironaka.MonoidalTransformation.exists_isProper`. -/
  exists_isProper : ∀ (X : Scheme.{u}) (B : Subscheme X),
      ∃ t : MonoidalTransformation X B, IsLocallyNoetherian X → IsProper t.f

end
end Hironaka.MonoidalTransformation
namespace Hironaka
/-- A (finite) *succession of monoidal transformations* `{fᵢ : Xᵢ₊₁ → Xᵢ}` starting at `X₀`
and ending at `Y`, with specified centers `Bᵢ ⊆ Xᵢ` (Def. 8, p. 169, and p. 170:
"whenever we speak of a succession of monoidal transformations, say f: X' → X, we mean a
specific factorization of the morphism f into monoidal transformations with specific
centers"). -/
@[blueprint "def:succession"
  (statement := /-- A succession of monoidal transformations of $X$ is a chain
    $f=\{f_i\colon X_{i+1}\to X_i\}_{0\le i<m}$, $X_0=X$, where $f_i$ is the monoidal
    transformation of $X_i$ with a specified center $B_i\subseteq X_i$. The empty succession
    ($m=0$) is allowed and is the identity.
    Formalization note (encoding): an inductive chain recording each center; the strict
    transform by a succession is the iterated strict transform (``in an obvious manner'',
    p.~167). -/)
  (latexEnv := "definition")]
inductive MonoidalSuccession : Scheme.{u} → Scheme.{u} → Type (u + 1)
  | nil (X : Scheme.{u}) : MonoidalSuccession X X
  | cons {X : Scheme.{u}} (B : Subscheme X) (t : MonoidalTransformation X B) {Y : Scheme.{u}}
      (rest : MonoidalSuccession t.X' Y) : MonoidalSuccession X Y

end Hironaka
namespace Hironaka.MonoidalSuccession
/-- The composed morphism `X_m ⟶ X_0` of a succession. -/
def composite : {X Y : Scheme.{u}} → MonoidalSuccession X Y → (Y ⟶ X)
  | _, _, nil X => 𝟙 X
  | _, _, cons _ t rest => rest.composite ≫ t.f

end Hironaka.MonoidalSuccession
namespace Hironaka
section
open Polynomial Filter
/-- The function `H_R(n)` of p. 133: "the sum of ranks of the `(A/m)`-modules `gr^i_m(A)` with
`0 ≤ i ≤ p`".  Ch. II §1, p. 187, calls `F_x(n) = Σ_{i≤n} dim_{O/m}(mⁱ/mⁱ⁺¹)` the *Samuel
characteristic function* of `X` at `x`. -/
@[blueprint "def:hilbert-samuel-function"
  (statement := /-- For a local ring $R$ with maximal ideal $M$, the function
    $H_R(n)=\sum_{i=0}^{n}\operatorname{rank}_{R/M}(M^i/M^{i+1})$, $n\ge0$ (p.~133); it is
    called the \emph{Samuel characteristic function} on p.~187. -/)
  (latexEnv := "definition")]
noncomputable def hilbertSamuel (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), Module.finrank (R ⧸ maximalIdeal R) (GrPiece (maximalIdeal R) i)

/-- `dim R` as a natural number (`0` if the Krull dimension is `⊥` or `∞`). -/
noncomputable def dimNat (R : Type u) [CommRing R] : ℕ := WithBot.recBotCoe (0 : ℕ) ENat.toNat (ringKrullDim R)

/-- The cited result `Hironaka.exists_hilbertSamuelPoly` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResults`. -/
class _root_.Hironaka.Cited.ExistsHilbertSamuelPoly : Prop where
  /-- The statement of `Hironaka.exists_hilbertSamuelPoly`. -/
  exists_hilbertSamuelPoly : ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      ∃ p : ℚ[X], (∀ᶠ n : ℕ in atTop, p.eval (n : ℚ) = (hilbertSamuel R n : ℚ)) ∧
        p.natDegree = dimNat R ∧
        ∃ e : ℕ, 0 < e ∧ ((dimNat R).factorial : ℚ) * p.leadingCoeff = e

end
section
open Polynomial
/-- The cited result `Hironaka.curve_finite_integralClosure` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResults`. -/
class _root_.Hironaka.Cited.CurveFiniteIntegralClosure : Prop where
  /-- The statement of `Hironaka.curve_finite_integralClosure`. -/
  curve_finite_integralClosure : ∀ (S : Type u) [CommRing S] [IsDomain S] [IsLocalRing S]
      [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S],
      Module.Finite S (integralClosure S (FractionRing S))

end
section
open Classical
/-- A *center*: a non-singular irreducible subscheme `B` of `X` (possibly empty, p. 168).
Formalization note (encoding): "empty, or non-singular and irreducible", following the
agreement of p. 163 that the empty subscheme counts as non-singular irreducible. -/
def Subscheme.IsCenter {X : Scheme.{u}} (B : Subscheme X) : Prop :=
  B = Subscheme.empty ∨ (B.IsNonsingular ∧ B.IsIrreducible)

end
/-- Separability of a (not necessarily algebraic) field extension `k'/k` in the sense used
throughout Ch. III (pp. 211–212, \cref{def:III.2-residually}): "for every purely inseparable
extension `k''` over `k` the tensor product `k' ⊗_k k''` has no nilpotent elements".  This is
the field-level notion underlying `RingHom.IsResiduallySeparable`
(`isResiduallySeparable_iff`); p. 223 recalls MacLane's characterization
(`isSeparableFieldExtension_iff`). -/
def IsSeparableFieldExtension (k k' : Type u) [Field k] [Field k'] [Algebra k k'] : Prop :=
  ∀ (k'' : Type u) [Field k''] [Algebra k k''], IsPurelyInseparable k k'' →
    IsReduced (TensorProduct k k' k'')

/-- The cited result `Hironaka.isSeparableFieldExtension_iff` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResults`. -/
class _root_.Hironaka.Cited.IsSeparableFieldExtensionIff : Prop where
  /-- The statement of `Hironaka.isSeparableFieldExtension_iff`. -/
  isSeparableFieldExtension_iff : ∀ (K K' : Type u) [Field K] [Field K'] [Algebra K K'],
      IsSeparableFieldExtension K K' ↔
        ∀ L : IntermediateField K K',
          (∃ s : Finset K', L = IntermediateField.adjoin K (s : Set K')) →
          ∃ (ι : Type u) (x : ι → L), AlgebraicIndependent K x ∧
            Algebra.IsSeparable (IntermediateField.adjoin K (Set.range x)) L

section
open TensorProduct
/-- The cited result `Hironaka.exists_surjective_of_isRegularLocalRing_of_isAdicComplete` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResults`. -/
class _root_.Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete : Prop where
  /-- The statement of `Hironaka.exists_surjective_of_isRegularLocalRing_of_isAdicComplete`. -/
  exists_surjective_of_isRegularLocalRing_of_isAdicComplete : ∀ (O : Type u) [CommRing O]
      [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O],
      ∃ (R : Type u) (_ : CommRing R) (_ : IsRegularLocalRing R)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (f : R →+* O),
        Function.Surjective f

end
/-- The cited result `Hironaka.exists_residue_comp_eq_id_of_isAdicComplete_of_ringChar_eq` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResults`. -/
class _root_.Hironaka.Cited.ExistsResidueCompEqIdOfIsAdicCompleteOfRingCharEq : Prop where
  /-- The statement of `Hironaka.exists_residue_comp_eq_id_of_isAdicComplete_of_ringChar_eq`. -/
  exists_residue_comp_eq_id_of_isAdicComplete_of_ringChar_eq : ∀ (R : Type u) [CommRing R]
      [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
      (hchar : ringChar R = ringChar (ResidueField R)),
      ∃ σ : ResidueField R →+* R, (IsLocalRing.residue R).comp σ = RingHom.id _

/-- The cited result `Hironaka.finite_integralClosure_of_essFiniteType` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResults`. -/
class _root_.Hironaka.Cited.FiniteIntegralClosureOfEssFiniteType : Prop where
  /-- The statement of `Hironaka.finite_integralClosure_of_essFiniteType`. -/
  finite_integralClosure_of_essFiniteType : ∀ {S A : Type u} [CommRing S] [IsLocalRing S]
      [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S] [CommRing A] [IsDomain A]
      [Algebra S A] [Algebra.EssFiniteType S A],
      Module.Finite A (integralClosure A (FractionRing A))

/-- The cited result `Hironaka.isClosed_compl_regularLocus_of_finiteType` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResults`. -/
class _root_.Hironaka.Cited.IsClosedComplRegularLocusOfFiniteType : Prop where
  /-- The statement of `Hironaka.isClosed_compl_regularLocus_of_finiteType`. -/
  isClosed_compl_regularLocus_of_finiteType : ∀ (k : Type u) [Field k] [PerfectField k]
      (B : Type u) [CommRing B] [Algebra k B] [Algebra.FiniteType k B],
      IsClosed (regularLocus B)ᶜ

/-- The cited result `Hironaka.ringKrullDim_adicCompletion_quotient_eq` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResults`. -/
class _root_.Hironaka.Cited.RingKrullDimAdicCompletionQuotientEq : Prop where
  /-- The statement of `Hironaka.ringKrullDim_adicCompletion_quotient_eq`. -/
  ringKrullDim_adicCompletion_quotient_eq : ∀ (R : Type u) [CommRing R] [IsLocalRing R]
      [IsNoetherianRing R] (Q : Ideal R),
      ringKrullDim (AdicCompletion (maximalIdeal R) R ⧸
        Q.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) = ringKrullDim (R ⧸ Q)

/-- The 15 results cited by the paper (without proof) that the fundamental theorems and the main theorems use. -/
class HironakaCitedResults : Prop extends
    Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u},
    Hironaka.Cited.MonoidalTransformationExistsIsProper.{u},
    Hironaka.Cited.CurveFiniteIntegralClosure.{u},
    Hironaka.Cited.ExistsFlatIsLocalHomAdicCompletionOfFlat.{u},
    Hironaka.Cited.ExistsHilbertSamuelPoly.{u},
    Hironaka.Cited.ExistsResidueCompEqIdOfIsAdicCompleteOfRingCharEq.{u},
    Hironaka.Cited.ExistsSurjectiveMvPowerSeriesOfIsAdicComplete.{u},
    Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u},
    Hironaka.Cited.FiniteIntegralClosureOfEssFiniteType.{u},
    Hironaka.Cited.IsClosedComplRegularLocusOfFiniteType.{u},
    Hironaka.Cited.IsRegularLocalRingLocalizationIffRankJacobianEqHeight.{u},
    Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u},
    Hironaka.Cited.IsRegularLocalRingOfFlatOfIsRegularLocalRing.{u},
    Hironaka.Cited.IsSeparableFieldExtensionIff.{u},
    Hironaka.Cited.RingKrullDimAdicCompletionQuotientEq.{u}

section
open MvPolynomial DirectSum
attribute [local instance] MvPolynomial.gradedAlgebra
variable {B : Type u} [Field B] {n : ℕ}
/-- p. 132: "a quotient ring `H`, graded in a natural way, of a polynomial ring with coefficients in `B`": the
quotient `B[T₀, …, T_{n-1}] ⧸ 𝔞` by a homogeneous ideal `𝔞`, graded by the images of the forms of degree `d`. -/
@[blueprint "def:0-quotient-grading"
  (statement := /-- Let $B$ be a field and $\mathfrak a$ a homogeneous ideal of the polynomial ring
    $B[T_0,\dots,T_{n-1}]$. The quotient ring $H=B[T]/\mathfrak a$ is \emph{graded in the natural way}: $H_d$ is the
    image of the forms of degree $d$. (p.~132; this grading is a graded-ring structure, \cref{def:0-quotient-grading}'s
    instance.) -/)
  (latexEnv := "definition")]
noncomputable def quotientGrading (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B)) :
    ℕ → Submodule B (MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal) :=
  fun d => (homogeneousSubmodule (Fin n) B d).map (Ideal.Quotient.mkₐ B 𝔞.toIdeal).toLinearMap

/-- The restriction of the quotient map to the forms of degree `d`. -/
noncomputable def quotientRestrict (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B)) (d : ℕ) :
    homogeneousSubmodule (Fin n) B d →ₗ[B] quotientGrading 𝔞 d :=
  ((Ideal.Quotient.mkₐ B 𝔞.toIdeal).toLinearMap.restrict (p := homogeneousSubmodule (Fin n) B d)
    (q := quotientGrading 𝔞 d) fun x hx => ⟨x, hx, rfl⟩)

/-- The map `A → ⨁ ℳ_d`, `a ↦ (mk a_d)_d`. -/
noncomputable def quotientDecomposeAux (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B)) :
    MvPolynomial (Fin n) B →ₗ[B] ⨁ d, quotientGrading 𝔞 d :=
  (DirectSum.lmap (quotientRestrict 𝔞)) ∘ₗ
    (DirectSum.decomposeLinearEquiv (homogeneousSubmodule (Fin n) B)).toLinearMap

theorem quotientDecomposeAux_apply (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))
    (a : MvPolynomial (Fin n) B) (d : ℕ) :
    ((quotientDecomposeAux 𝔞 a d : quotientGrading 𝔞 d) : MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal) =
      Ideal.Quotient.mk 𝔞.toIdeal
        (DirectSum.decompose (homogeneousSubmodule (Fin n) B) a d : MvPolynomial (Fin n) B) := rfl

theorem quotientDecomposeAux_eq_zero (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))
    {a : MvPolynomial (Fin n) B} (ha : a ∈ 𝔞.toIdeal) : quotientDecomposeAux 𝔞 a = 0 := by
  ext d
  rw [quotientDecomposeAux_apply]
  show _ = ((0 : quotientGrading 𝔞 d) : MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal)
  rw [ZeroMemClass.coe_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact 𝔞.isHomogeneous d ha

/-- The decomposition `A/𝔞 → ⨁ ℳ_d`, additively. -/
noncomputable def quotientDecomposeHom (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B)) :
    (MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal) →+ ⨁ d, quotientGrading 𝔞 d :=
  QuotientAddGroup.lift 𝔞.toIdeal.toAddSubgroup (quotientDecomposeAux 𝔞).toAddMonoidHom
    (fun _ ha => quotientDecomposeAux_eq_zero 𝔞 ha)

theorem quotientDecomposeHom_mk (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))
    (a : MvPolynomial (Fin n) B) :
    quotientDecomposeHom 𝔞 (Ideal.Quotient.mk 𝔞.toIdeal a) = quotientDecomposeAux 𝔞 a := rfl

theorem coe_quotientDecomposeAux (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))
    (a : MvPolynomial (Fin n) B) :
    DirectSum.coeAddMonoidHom (quotientGrading 𝔞) (quotientDecomposeAux 𝔞 a) =
      Ideal.Quotient.mk 𝔞.toIdeal a := by
  classical
  have h : ∀ x : ⨁ d, homogeneousSubmodule (Fin n) B d,
      DirectSum.coeAddMonoidHom (quotientGrading 𝔞) (DirectSum.lmap (quotientRestrict 𝔞) x) =
        Ideal.Quotient.mk 𝔞.toIdeal
          (DirectSum.coeAddMonoidHom (homogeneousSubmodule (Fin n) B) x) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of d x =>
      simp only [DirectSum.lmap_of, DirectSum.coeAddMonoidHom_of]
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  have := h (DirectSum.decompose (homogeneousSubmodule (Fin n) B) a)
  have e : DirectSum.coeAddMonoidHom (homogeneousSubmodule (Fin n) B)
      (DirectSum.decompose (homogeneousSubmodule (Fin n) B) a) = a :=
    DirectSum.Decomposition.left_inv a
  rw [e] at this
  exact this

/-- Mathlib has no grading on the quotient of a graded ring by a homogeneous ideal. -/
noncomputable instance quotientDecomposition (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B)) :
    DirectSum.Decomposition (quotientGrading 𝔞) :=
  DirectSum.Decomposition.ofAddHom _ (quotientDecomposeHom 𝔞)
    (by
      ext x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact coe_quotientDecomposeAux 𝔞 a)
    (by
      refine DirectSum.addHom_ext fun d x => ?_
      obtain ⟨a, ha, hax⟩ := x.2
      have e1 : (x : MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal) = Ideal.Quotient.mk 𝔞.toIdeal a :=
        hax.symm
      simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
      rw [e1, quotientDecomposeHom_mk]
      have e2 : DirectSum.decompose (homogeneousSubmodule (Fin n) B) a =
          DirectSum.of (fun i => homogeneousSubmodule (Fin n) B i) d ⟨a, ha⟩ :=
        DirectSum.decompose_of_mem _ ha
      have e3 : x = quotientRestrict 𝔞 d ⟨a, ha⟩ := Subtype.ext hax.symm
      simp only [quotientDecomposeAux, LinearMap.comp_apply, LinearEquiv.coe_coe,
        DirectSum.decomposeLinearEquiv_apply, e2, DirectSum.lmap_of]
      rw [e3])

instance quotientGradedMonoid (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B)) :
    SetLike.GradedMonoid (quotientGrading 𝔞) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, rfl⟩
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.GradedMul.mul_mem ha hb, rfl⟩

noncomputable instance quotientGradedRing (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B)) :
    GradedRing (quotientGrading 𝔞) :=
  { quotientGradedMonoid 𝔞, quotientDecomposition 𝔞 with }

end
section
open MvPolynomial DirectSum
attribute [local instance] MvPolynomial.gradedAlgebra
variable {B : Type u} [Field B] {n : ℕ} (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))
/-- The structure morphism `Proj H ⟶ Spec H₀ ⟶ Spec B` of `Proj(H)` as a `B`-scheme (p. 132). -/
noncomputable def projStructure : Proj (quotientGrading 𝔞) ⟶ Spec (CommRingCat.of B) :=
  Proj.toSpecZero (quotientGrading 𝔞) ≫
    Spec.map (CommRingCat.ofHom (algebraMap B (quotientGrading 𝔞 0)))

/-- p. 132, "projective": the `B`-scheme `X` is of the form `Proj(H)` with `H` a quotient ring, graded in the natural
way, of a polynomial ring with coefficients in `B`. -/
@[blueprint "def:0-projective-scheme"
  (statement := /-- A $B$-scheme $X$ is \emph{projective} if it is of the form $\operatorname{Proj}(H)$ with a quotient ring
    $H$, graded in a natural way, of a polynomial ring with coefficients in $B$. (p.~132.)
    Formalization note (encoding): $H=B[T_0,\dots,T_{n-1}]/\mathfrak a$ with $\mathfrak a$ a homogeneous ideal, graded by
    \cref{def:0-quotient-grading}; the isomorphism $X\cong\operatorname{Proj}(H)$ is over $\operatorname{Spec}B$ for the
    structure morphism $\operatorname{Proj}(H)\to\operatorname{Spec}H_0\to\operatorname{Spec}B$. The first definition of
    ``projective'' (pp.~126--127) is not formalized; the paper does not show that the two agree. -/)
  (latexEnv := "definition")]
def IsProjectiveOver (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of B)) : Prop :=
  ∃ (n : ℕ) (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))
    (e : X ≅ Proj (quotientGrading 𝔞)), e.hom ≫ projStructure 𝔞 = p

end
section
variable {B : Type u} [CommRing B]
/-- The `B`-algebra structure of the function field of an irreducible `B`-scheme `p : X ⟶ Spec B` (p. 130):
`B ≅ Γ(Spec B) → Γ(X, O_X) → O_{X,η} = K(X)`. -/
noncomputable def functionFieldAlgebraMap {X : Scheme.{u}} [IrreducibleSpace X]
    (p : X ⟶ Spec (CommRingCat.of B)) : B →+* X.functionField :=
  have : Nonempty (⊤ : X.Opens) := ⟨⟨(inferInstance : Nonempty X).some, trivial⟩⟩
  (X.germToFunctionField ⊤).hom.comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)

end
section
variable (R : Type u) [CommRing R] [IsLocalRing R]
/-- Ch. I / Ch. III usage: a *regular system of parameters* of a local ring `R` is a finite
set of elements generating the maximal ideal whose cardinality equals the Krull dimension. -/
@[blueprint "def:rsop"
  (statement := /-- Let $R$ be a local ring with maximal ideal $M$. A finite subset
    $(z_1,\dots,z_r)\subseteq R$ is a \emph{regular system of parameters} of $R$ if
    $M=(z_1,\dots,z_r)$ and $r=\dim R$. -/)
  (latexEnv := "definition")]
def IsRegularSystemOfParameters (s : Finset R) : Prop :=
  Ideal.span (s : Set R) = maximalIdeal R ∧ (s.card : WithBot ℕ∞) = ringKrullDim R

end
section
variable {S : Type u} [CommRing S]
/-- The order `ν_M(J)` of an ideal `J` with respect to an ideal `M` (p. 165):
the largest `ν` with `J ⊆ M^ν`, or `∞` if `J ⊆ M^ν` for all `ν`. -/
@[blueprint "def:order-nu"
  (statement := /-- For ideals $M,J$ of a ring $S$, $\nu_M(J)$ is the largest integer $\nu$
    with $M^\nu\supseteq J$, or $\infty$ if no largest such integer exists. For $S$ local
    with maximal ideal $M$ we write $\nu(J)$. -/)
  (latexEnv := "definition")]
noncomputable def Ideal.ord (M J : Ideal S) : ℕ∞ :=
  ⨆ (ν : ℕ) (_ : J ≤ M ^ ν), (ν : ℕ∞)

/-- `ν(J)` for a local ring: order with respect to the maximal ideal. -/
noncomputable abbrev Ideal.nu [IsLocalRing S] (J : Ideal S) : ℕ∞ :=
  Ideal.ord (maximalIdeal S) J

end
/-- An *algebraic scheme* is a scheme admitting a morphism of finite type to `Spec S` with
`S ∈ 𝔅` (p. 162).  We record the existence only; morphisms of algebraic schemes are arbitrary
morphisms of schemes (p. 162).

Deviation from the paper (more general statement): the paper's schemes are separated (p. 118); an
algebraic scheme is not required to be separated here, so a statement that takes an algebraic scheme
as a hypothesis is more general than the printed one. -/
@[blueprint "def:algebraic-scheme"
  (statement := /-- A scheme $V$ is an \emph{algebraic scheme} if there is a morphism of
    finite type $p\colon V\to\operatorname{Spec}(S)$ for some $S\in\mathfrak B$.
    Formalization note (encoding): ``of finite type'' is ``locally of finite type and
    quasi-compact''; only the existence of $(S,p)$ is recorded. Deviation from the paper (more
    general statement): the paper's schemes are separated (p.~118); separatedness is not required
    here. -/)
  (latexEnv := "definition")]
class IsAlgebraicScheme (X : Scheme.{u}) : Prop where
  exists_base : ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : IsHironakaBase S)
    (p : X ⟶ Spec (CommRingCat.of S)), LocallyOfFiniteType p ∧ QuasiCompact p

end Hironaka
namespace AlgebraicGeometry.Scheme
section
variable (X : Scheme.{u})
/-- p. 163: "The Krull-dimension of `O_{V,x}` will be called the dimension of `V` at the point
`x`, and denoted by `dim_x(V)`." -/
@[blueprint "def:I.0-dimension-at"
  (statement := /-- The \emph{dimension of $V$ at the point $x$}, $\dim_x(V)$, is the Krull
    dimension of the local ring $\mathcal O_{V,x}$. (p.~163.) -/)
  (latexEnv := "definition")]
noncomputable def dimAt (x : X) : WithBot ℕ∞ := ringKrullDim (X.presheaf.stalk x)

/-- p. 163: "The maximum of `dim_x(V)` for all the points `x` of an algebraic scheme `V` is a
non-negative integer, provided `V` is not empty. This integer will be called the dimension of
`V`, denoted by `dim(V)`. We take the integer `-1` as the dimension of the empty scheme."
The supremum over the empty scheme is `⊥`, which plays the role of `-1`. -/
@[blueprint "def:I.0-dimension"
  (statement := /-- The \emph{dimension} of $V$ is $\dim(V)=\max_{x\in V}\dim_x(V)$
    (\cref{def:I.0-dimension-at}), and $\dim(\emptyset)=-1$. (p.~163.)
    Formalization note (encoding): the dimension is the supremum in
    $\mathbb N\cup\{\pm\infty\}$, with $-\infty$ playing the role of $-1$; the paper's remark
    that it is a non-negative integer for non-empty algebraic $V$ is not formalized here. -/)
  (latexEnv := "definition")]
noncomputable def dim : WithBot ℕ∞ := ⨆ x : X, X.dimAt x

end
end AlgebraicGeometry.Scheme
namespace Hironaka.Subscheme
section
variable {X : Scheme.{u}}
/-- "One subscheme is contained in another if the sheaf of ideals of the first contains that
of the second" (p. 165). -/
def IsContainedIn (D D' : Subscheme X) : Prop := ∀ U : X.affineOpens, D'.ideal U ≤ D.ideal U

/-- Union of subschemes: defined by the intersection of the ideal sheaves (p. 165). -/
def union (D D' : Subscheme X) : Subscheme X := D ⊓ D'

/-- The reduced subscheme structure on a closed subset. -/
def ofClosed (Z : Closeds X) : Subscheme X := Scheme.IdealSheafData.vanishingIdeal Z

/-- Reducedness, irreducibility, non-singularity of a subscheme, via its scheme. -/
def IsReduced (D : Subscheme X) : Prop := AlgebraicGeometry.IsReduced D.toScheme

/-- Dimension of a subscheme (p. 163: "W is necessarily algebraic because V is so"; its
dimension is that of the scheme `W`). -/
noncomputable def dim (D : Subscheme X) : WithBot ℕ∞ := D.toScheme.dim

/-- p. 163: "If x is a point of W, then the codimension of W in V at x is defined to be the
codimension of Spec(O_{W,x}) in Spec(O_{V,x}), where the first spectrum is viewed in a
canonical way as a subscheme of the second."  The codimension of the closed subset `V(P)` of
`Spec O` is the infimum of the heights of the minimal primes of `P`, i.e. Mathlib's
`Ideal.height P`. -/
@[blueprint "def:I.0-codimension-at"
  (statement := /-- For a point $x$ of a subscheme $W$ of $V$, the \emph{codimension of $W$
    in $V$ at $x$} is the codimension of $\operatorname{Spec}(\mathcal O_{W,x})$ in
    $\operatorname{Spec}(\mathcal O_{V,x})$, i.e.\ the height of the ideal of $W$ in
    $\mathcal O_{V,x}$. (p.~163.)
    Formalization note (encoding): the codimension of $V(I)$ in $\operatorname{Spec}\mathcal
    O_{V,x}$ is the height of $I$, the minimum of the heights of the minimal primes of $I$. -/)
  (latexEnv := "definition")]
noncomputable def codimAt (W : Subscheme X) (x : X) : ℕ∞ := (W.stalkIdeal x).height

/-- The codimension of `W`: the infimum of the codimensions `codimAt W x` over the points `x` of
`W` (`⊤` if `W` is empty).

p. 163: "If W is not empty, then we define the codimension of W in V to be the minimum of
dim_x(V) for all the points x of W. … We can see that the codimension of W in V is equal to the
minimum of the codimensions of W in V at the points of W, provided W is not empty."
For the empty subscheme the infimum is `⊤`; p. 163 agrees that "any integer can be the
codimension of the empty subscheme", and the predicates below treat the empty subscheme
separately.

Deviation from the paper (statement modified): the definition is taken in the second form
quoted above (the minimum of the codimensions `codimAt` at the points of `W`), which p. 163
asserts ("we can see") to equal the printed definition.  The printed definition is correct
(it is not a misprint: the points of `W` include its generic points, where `dim_x(V)` is the
codimension of the corresponding component), and its equivalence with the form used here is
`Subscheme.isLeast_dimAt_codim` (`Hironaka/Compat/CodimDefinition.lean`, downstream of this
file): for non-empty `W`, `codim W` is the least of the `dim_x(V)`, `x ∈ W`. -/
@[blueprint "def:I.0-codimension"
  (statement := /-- For a non-empty subscheme $W$ of $V$, the \emph{codimension of $W$ in
    $V$} is the minimum of $\dim_x(V)$ for all the points $x$ of $W$; it is equal to the
    minimum of the codimensions of $W$ in $V$ at the points of $W$
    (\cref{def:I.0-codimension-at}). Any integer may serve as the codimension of the empty
    subscheme. (p.~163.)
    \textbf{Deviation from the paper (statement modified).} The Lean definition is the minimum
    of the codimensions of $W$ at its points, which p.~163 asserts (``we can see'') to equal
    the printed minimum of $\dim_x(V)$; the two agree (the minimum of $\dim_x(V)$ is attained
    at generic points of components of $W$), which is \cref{def:I.0-codimension-printed}. -/)
  (latexEnv := "definition")]
noncomputable def codim (W : Subscheme X) : ℕ∞ := ⨅ x ∈ W.pts, W.codimAt x

/-- p. 163: "We shall say that W is everywhere of codimension s in V, if W has codimension s in
V at every point of W." -/
@[blueprint "def:I.0-everywhere-codimension"
  (statement := /-- $W$ is \emph{everywhere of codimension $s$ in $V$} if $W$ has codimension
    $s$ in $V$ at every point of $W$ (\cref{def:I.0-codimension-at}). (p.~163.) -/)
  (latexEnv := "definition")]
def IsEverywhereOfCodim (W : Subscheme X) (s : ℕ) : Prop := ∀ x ∈ W.pts, W.codimAt x = s

/-- The irreducible components of a subscheme, as reduced subschemes ("a maximal reduced
irreducible subscheme", Def. 2 of Ch. 0 §5): the reduced structures on the closed subsets of `X`
that are maximal among the irreducible closed subsets contained in `D`.  (These are exactly the
images of the irreducible components of the subspace `D.pts`, since it is closed.) -/
def irreducibleComponents (D : Subscheme X) : Set (Subscheme X) :=
  {C | ∃ Z : Closeds X,
    Maximal (fun Z : Closeds X => _root_.IsIrreducible (Z : Set X) ∧ (Z : Set X) ⊆ D.pts) Z ∧
    C = ofClosed Z}

/-- "E is everywhere of codimension one on X" (Def. 3 (I)(i), p. 164), in the sense of p. 163.
The empty subscheme satisfies this vacuously, in accordance with the agreement of p. 163 ("we
shall often view the empty subscheme as a non-singular irreducible subscheme which is
everywhere of codimension one"). -/
def IsEverywhereCodimOne (E : Subscheme X) : Prop := E.IsEverywhereOfCodim 1

/-- A "non-singular irreducible subscheme of X of codimension one" (the `E_i` of Def. 3 (II),
p. 165, and the restrictions `F` of Def. 5, p. 166).  By the agreement of p. 163 the empty
subscheme is allowed ("the empty subscheme of X may appear and may even be repeated among E
and E_i", p. 165). -/
def IsNonsingularIrreducibleCodimOne (F : Subscheme X) : Prop :=
  F = empty ∨ (F.IsNonsingular ∧ F.IsIrreducible ∧ F.codim = 1)

end
end Hironaka.Subscheme
namespace Hironaka.MonoidalTransformation
section
variable {X : Scheme.{u}} {B : Subscheme X}
/-- The exceptional subscheme `f⁻¹(B)` (this is `E_{α+1}` in Def. 7). -/
noncomputable def exceptional (t : MonoidalTransformation X B) : Subscheme t.X' :=
  Subscheme.totalTransform t.f B

end
end Hironaka.MonoidalTransformation
namespace Hironaka.Subscheme
/-- The *strict transform* of a subscheme `V ⊆ X` by a monoidal transformation `g : X' → X`
with center `B` (p. 167): "the smallest subscheme `V'` of `X'` such that the restriction of
`V'` to `X' − g⁻¹(B)` is equal to the preimage of `V − B` by the morphism `g`".
Smallest subscheme = largest ideal sheaf; agreement on the open complement of `g⁻¹(B)` is
expressed on stalks. -/
@[blueprint "def:strict-transform"
  (statement := /-- Let $g\colon X'\to X$ be a monoidal transformation with center $B$ and
    $V$ a subscheme of $X$. The \emph{strict transform} of $V$ by $g$ is the smallest
    subscheme $V'$ of $X'$ whose restriction to $X'-g^{-1}(B)$ equals the preimage of
    $V-B$ under $g$. (p.\ 167.)
    Formalization note (encoding): ``smallest subscheme'' is the supremum of the ideal sheaves
    whose stalks agree with those of $g^{-1}(V)$ at the points off $g^{-1}(B)$; by
    \cref{lem:strict-transform-saturation} it lies in that set. -/)
  (latexEnv := "definition")]
noncomputable def strictTransform {X : Scheme.{u}} {B : Subscheme X}
    (t : MonoidalTransformation X B) (V : Subscheme X) : Subscheme t.X' :=
  sSup {V' : Subscheme t.X' |
    ∀ x' : t.X', x' ∉ t.exceptional.pts →
      V'.stalkIdeal x' = (totalTransform t.f V).stalkIdeal x'}

/-- Division of a sheaf of ideals by the `ν`-th power of an invertible sheaf of ideals `P`
(Ch. 0 §5, p. 142: "f⁻¹(J) is divisible by the m-th power of the sheaf of ideals of f⁻¹(D) on
X'. The sheaf of ideals on X' obtained by this division will be called the weak transform of
J"; used in Def. 7, p. 168, as `f⁻¹(J)P⁻ᵛ`).  The paper defines the quotient only when `I` is
divisible by `Pᵛ`, as the unique `K` with `K · Pᵛ = I` (unique because `P` is invertible).
Formalization note (encoding): we encode it as the largest `K` with `K · Pᵛ ⊆ I` on stalks, which
coincides with the paper's quotient whenever the latter is defined (cancel the non-zero-divisor
generator of `P` on stalks) and is total. -/
noncomputable def divPow {X : Scheme.{u}} (I P : Subscheme X) (ν : ℕ) : Subscheme X :=
  sSup {K : Subscheme X | ∀ x : X, K.stalkIdeal x * (P.stalkIdeal x) ^ ν ≤ I.stalkIdeal x}

end Hironaka.Subscheme
namespace Hironaka.MonoidalSuccession
/-- Strict transform of a subscheme by a succession (p. 167: "we define in an obvious manner
the strict transform of a subscheme by a finite succession of monoidal transformations"). -/
noncomputable def strictTransform : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    Subscheme X → Subscheme Y
  | _, _, nil _, V => V
  | _, _, cons _ t rest, V => rest.strictTransform (Subscheme.strictTransform t V)

/-- Total transform of a subscheme by (the composite of) a succession. -/
noncomputable def totalTransform {X Y : Scheme.{u}} (s : MonoidalSuccession X Y)
    (V : Subscheme X) : Subscheme Y :=
  Subscheme.totalTransform s.composite V

end Hironaka.MonoidalSuccession
namespace Hironaka.Subscheme
section
variable {X : Scheme.{u}}
/-- Definition 2: `E` has only normal crossings with `D` at `x` (the hypotheses "X
non-singular, E reduced with invertible ideal sheaf" are *not* built into the predicate; they
are carried by the resolution data that use it). -/
@[blueprint "def:0.2-normal-crossings-with-at"
  (statement := /-- Let $X$ be non-singular, $E\subseteq X$ reduced and everywhere of
    codimension one, $D\subseteq X$ a subscheme and $x\in D$. Then $E$ \emph{has only normal
    crossings with $D$ at $x$} if there is a regular system of parameters $(z_1,\dots,z_n)$
    of $\mathcal O_{X,x}$ such that the ideal of each irreducible component of $E$ through
    $x$ is generated by one of the $z_i$ and the ideal of $D$ at $x$ is generated by some of
    the $z_i$. (Ch.\ 0, Def.\ 2.)
    Formalization note (encoding): the standing hypotheses on $X$ and $E$ are not built into
    the predicate (they are carried by the data that use it); the regular system of parameters
    is a finite set; irreducible components are the reduced structures on the maximal
    irreducible closed subsets of $E$; $x\in D$ is implied by the condition on $D$. -/)
  (latexEnv := "definition")]
def HasOnlyNormalCrossingsWithAt (E D : Subscheme X) (x : X) : Prop :=
  ∃ z : Finset (X.presheaf.stalk x),
    IsRegularSystemOfParameters (X.presheaf.stalk x) z ∧
    (∀ C ∈ E.irreducibleComponents, x ∈ C.pts →
      ∃ a ∈ z, C.stalkIdeal x = Ideal.span {a}) ∧
    (∃ t : Finset (X.presheaf.stalk x), t ⊆ z ∧
      D.stalkIdeal x = Ideal.span (t : Set (X.presheaf.stalk x)))

/-- "E has only normal crossings at x" (the case `D = X`). -/
@[blueprint "def:0.2-normal-crossings-at"
  (statement := /-- $E$ \emph{has only normal crossings at $x$} if it has only normal crossings
    with $D=X$ at $x$. -/)
  (latexEnv := "definition")]
def HasOnlyNormalCrossingsAt (E : Subscheme X) (x : X) : Prop :=
  E.HasOnlyNormalCrossingsWithAt ⊥ x

/-- "E has only normal crossings" (at every point of `X`). -/
@[blueprint "def:0.2-normal-crossings"
  (statement := /-- $E$ \emph{has only normal crossings} if it has only normal crossings at
    every point of $X$. -/)
  (latexEnv := "definition")]
def HasOnlyNormalCrossings (E : Subscheme X) : Prop :=
  ∀ x : X, E.HasOnlyNormalCrossingsAt x

/-- "E has only normal crossings with D" (at every point of `D`). -/
@[blueprint "def:0.2-normal-crossings-with"
  (statement := /-- $E$ \emph{has only normal crossings with $D$} if it does so at every point
    of $D$. -/)
  (latexEnv := "definition")]
def HasOnlyNormalCrossingsWith (E D : Subscheme X) : Prop :=
  ∀ x ∈ D.pts, E.HasOnlyNormalCrossingsWithAt D x

end
end Hironaka.Subscheme
namespace Hironaka
section
variable {O : Type u} [CommRing O]
/-- The stalk form of Definition 1: `O` is *normally flat along `P`* if every graded piece
`Pᵖ/Pᵖ⁺¹` is a free `O/P`-module. -/
@[blueprint "def:normally-flat-ideal"
  (statement := /-- A local ring $O$ is \emph{normally flat along} an ideal $P$ if
    $P^p/P^{p+1}$ is a free $O/P$-module for every $p\ge0$. -/)
  (latexEnv := "definition")]
def IsNormallyFlatAlongIdeal (P : Ideal O) : Prop :=
  ∀ p : ℕ, Module.Free (O ⧸ P) (GrPiece P p)

end
end Hironaka
namespace Hironaka.Subscheme
section
variable {X : Scheme.{u}}
/-- Definition 1: `X` is normally flat along the subscheme `D` at the point `x ∈ D`. -/
@[blueprint "def:0.1-normally-flat-at"
  (statement := /-- Let $D\subseteq X$ be a subscheme with ideal sheaf $J$ and $x\in D$. Then
    $X$ is \emph{normally flat along $D$ at $x$} if the stalk of $\operatorname{gr}^p_D(X)=
    J^p/J^{p+1}|_D$ at $x$ is a free $\mathcal O_{D,x}$-module for all $p\ge0$.
    (Ch.\ 0, Def.\ 1.)
    Formalization note (encoding): with $O=\mathcal O_{X,x}$ and $P=J_x$, the stalk of
    $\operatorname{gr}^p_D(X)$ is $P^p/P^{p+1}$ as an $O/P=\mathcal O_{D,x}$-module
    (\cref{def:normally-flat-ideal}); $D$ is a subscheme (the paper allows local-ringed
    subspaces). -/)
  (latexEnv := "definition")]
def IsNormallyFlatAlongAt (D : Subscheme X) (x : X) : Prop :=
  x ∈ D.pts ∧ IsNormallyFlatAlongIdeal (D.stalkIdeal x)

/-- Normal flatness of a subscheme `V ⊆ X` along a subscheme `W ⊆ V` (as used in Def. 4 (I)(ii):
"all the V_j are normally flat along W at x"): normal flatness of the scheme `V` along the
subscheme `W ∩ V` of `V`.  Formalization note (encoding): `W ∩ V` is the pull-back of `W` to
`V`, which is `W` when `W ⊆ V`. -/
def IsNormallyFlatAlongAt' (V W : Subscheme X) (x : X) : Prop :=
  ∃ x' : V.toScheme, V.ι.base x' = x ∧
    (totalTransform V.ι W).IsNormallyFlatAlongAt x'

end
section
variable {X : Scheme.{u}} {B : Subscheme X}
open Classical in
/-- The weak transform of a coherent sheaf of ideals by a monoidal transformation (Remark 2,
p. 214): "Let `ξ` be the generic point of `B`; we assume that `B` is not empty. … Let `J'` be
the sheaf of ideals on `X'` which is the increasing union of `f⁻¹(J)·P_E⁻ᵛ` for all
`ν ≤ ν(J_ξ)`. … If `B` is empty, we have `X' = X` with the identity `f` and we put `J' = J`.
We shall call `J'` the *weak transform* of `J` on `X'` by the monoidal transformation `f`."

Formalization note (encoding): the generic point `ξ` of `B` is chosen (`Classical.choose`) among the
points with `IsGenericPoint ξ B.pts`; this is the paper's `ξ` when `B` is irreducible and
non-empty.  When no such point exists, the weak transform is `f⁻¹(J)`: for `B` empty, `X' ≅ X` and
this is the paper's "`J' = J`"; a non-empty `B` without a generic point (a reducible center) is
outside the paper's definition, which assumes `B` irreducible.  `f⁻¹(J)·P_E⁻ᵛ` is
`Subscheme.divPow` (Ch. 0 §5). -/
@[blueprint "def:III.2-weak-transform-sheaf"
  (statement := /-- Let $X$ be a non-singular algebraic scheme, $B$ an irreducible non-singular
    subscheme of $X$, $J$ a coherent sheaf of ideals on $X$, $f\colon X'\to X$ the monoidal
    transformation with center $B$, $E=f^{-1}(B)$ with sheaf of ideals $P_E$, and $\xi$ the
    generic point of $B$ ($B$ non-empty). The \emph{weak transform} of $J$ on $X'$ by $f$ is
    the sheaf of ideals $J'$ on $X'$ which is the increasing union of $f^{-1}(J)P_E^{-\nu}$
    for all $\nu\le\nu(J_\xi)$. If $B$ is empty, $X'=X$ with the identity $f$ and $J'=J$.
    (Remark 2, p.~214.) -/)
  (latexEnv := "definition")]
noncomputable def weakTransform (t : MonoidalTransformation X B) (J : Subscheme X) :
    Subscheme t.X' :=
  if h : ∃ ξ : X, IsGenericPoint ξ B.pts then
    ⨆ (ν : ℕ) (_ : (ν : ℕ∞) ≤ Ideal.nu (J.stalkIdeal h.choose)),
      divPow (totalTransform t.f J) t.exceptional ν
  else totalTransform t.f J

end
end Hironaka.Subscheme
namespace Hironaka.DatumI
section
open Classical
/-- The tuple `(E; V₁, …, V_β; W)`. -/
structure Raw (X : Scheme.{u}) where
  E : Subscheme X
  β : ℕ
  V : Fin β → Subscheme X
  W : Subscheme X

end
section
open Classical
variable {X : Scheme.{u}}
/-- Definition 3 (I), conditions (i)–(iii); (iv) `N = dim X`, `n = dim W` are notations. -/
@[blueprint "def:I.3-I"
  (statement := /-- A resolution datum of type $\mathfrak R^{N,n}_{\mathrm I}$ on $X$ is an
    object $\mathfrak R=(E;V_1,\dots,V_\beta;W)$ where (i) $E$ is a reduced subscheme of $X$
    which is everywhere of codimension one and has only normal crossings; (ii) $\beta\ge0$
    and the $V_j$ are subschemes of $X$; (iii) $W$ is a reduced subscheme of $X$ contained in
    $\bigcap_j V_j$; (iv) $N=\dim X$, $n=\dim W$. (Def.\ 3 (I), p.\ 164.) -/)
  (latexEnv := "definition")]
def Raw.IsDatum (ℜ : Raw X) : Prop :=
  ℜ.E.IsReduced ∧ ℜ.E.IsEverywhereCodimOne ∧ ℜ.E.HasOnlyNormalCrossings ∧
  ℜ.W.IsReduced ∧ ∀ j, ℜ.W.IsContainedIn (ℜ.V j)

/-- `n = dim W` (Def. 3 (I)(iv)). -/
noncomputable def Raw.n (ℜ : Raw X) : WithBot ℕ∞ := ℜ.W.dim

/-- The *principal subscheme* `W` of a datum (p. 170). -/
abbrev Raw.principal (ℜ : Raw X) : Subscheme X := ℜ.W

/-- Definition 4 (I): `ℜ` is resolved at a point `x` of `W`. -/
@[blueprint "def:I.4-I"
  (statement := /-- $\mathfrak R^{N,n}_{\mathrm I}$ is \emph{resolved at a point $x\in W$} if
    (i) $x$ is a simple point of $W$; (ii) all $V_j$ are normally flat along $W$ at $x$;
    (iii) $E$ has only normal crossings with $W$ at $x$ on $X$. (Def.\ 4 (I), p.\ 165.) -/)
  (latexEnv := "definition")]
def Raw.ResolvedAt (ℜ : Raw X) (x : X) : Prop :=
  ℜ.W.IsSimpleAt x ∧
  (∀ j, Subscheme.IsNormallyFlatAlongAt' (ℜ.V j) ℜ.W x) ∧
  ℜ.E.HasOnlyNormalCrossingsWithAt ℜ.W x

/-- "Resolved everywhere", i.e. at every point of the principal subscheme (p. 170). -/
def Raw.ResolvedEverywhere (ℜ : Raw X) : Prop := ∀ x ∈ ℜ.W.pts, ℜ.ResolvedAt x

/-- The tuple `(E; V₁, …, V_β, W; B)` obtained by adjoining `W` to the `V`'s and replacing the
principal subscheme by `B` (Def. 6). -/
def Raw.extendBy (ℜ : Raw X) (B : Subscheme X) : Raw X where
  E := ℜ.E
  β := ℜ.β + 1
  V := Fin.snoc ℜ.V ℜ.W
  W := B

end
end Hironaka.DatumI
namespace Hironaka
section
open Classical
/-- A resolution datum of type ℜ^{N,n}_I. -/
abbrev DatumI (X : Scheme.{u}) := {ℜ : DatumI.Raw X // ℜ.IsDatum}

end
end Hironaka
namespace Hironaka.DatumII
section
open Classical
/-- The tuple `(E₁, …, E_α; J; b; a₁, …, a_α)`. -/
structure Raw (X : Scheme.{u}) where
  α : ℕ
  E : Fin α → Subscheme X
  a : Fin α → ℕ
  J : Subscheme X
  b : ℕ

end
section
open Classical
variable {X : Scheme.{u}}
/-- The union `E₁ ∪ ⋯ ∪ E_α` (defined by the intersection of the ideal sheaves). -/
def Raw.eUnion (ℜ : Raw X) : Subscheme X := ⨅ i, ℜ.E i

/-- Definition 3 (II), conditions (i)–(iii).  Condition (iii), "J is a coherent sheaf of
non-zero ideals on X", is read as: every stalk `J_x` is a non-zero ideal of `O_{X,x}`.  This is
what p. 142 needs ("we have defined an integer ν(J_x)", which is finite only for `J_x ≠ 0`), and
on the irreducible non-singular `X` of Def. 3 it is equivalent to `J ≠ 0`. -/
@[blueprint "def:I.3-II"
  (statement := /-- A resolution datum of type $\mathfrak R^{N}_{\mathrm{II}}$ on $X$ is an
    object $\mathfrak R=\big(E_1,\dots,E_\alpha\,\big|\,J,b\,\big|\,a_1,\dots,a_\alpha\big)$
    where (i) $\alpha,a_i\ge0$ and $b>0$ are integers; (ii) the $E_i$ are non-singular
    irreducible subschemes of codimension one such that $\bigcup E_i$ has only normal
    crossings; (iii) $J$ is a coherent sheaf of non-zero ideals on $X$; (iv) $N=\dim X$.
    (Def.\ 3 (II), pp.\ 164–165.)

    Formalization note (encoding): $J$ is an ideal sheaf (a subscheme of $X$) and (iii) is
    read as ``every stalk $J_x$ is non-zero'', equivalent to $J\ne0$ on the irreducible
    non-singular $X$ of Definition~3; the empty subscheme is allowed among the $E_i$ (p.~165). -/)
  (latexEnv := "definition")]
def Raw.IsDatum (ℜ : Raw X) : Prop :=
  0 < ℜ.b ∧
  (∀ i, (ℜ.E i).IsNonsingularIrreducibleCodimOne) ∧
  ℜ.eUnion.HasOnlyNormalCrossings ∧
  ∀ x : X, ℜ.J.stalkIdeal x ≠ ⊥

/-- The weighted count `∑_{x ∈ E_i} a_i` at a point `x`. -/
noncomputable def Raw.weight (ℜ : Raw X) (x : X) : ℕ :=
  ∑ i ∈ (Finset.univ.filter fun i => x ∈ (ℜ.E i).pts), ℜ.a i

/-- `ν(J_x)`, the order of the stalk of `J` at `x` in the local ring `O_{X,x}`. -/
noncomputable def Raw.nuAt (ℜ : Raw X) (x : X) : ℕ∞ :=
  Ideal.nu (ℜ.J.stalkIdeal x)

/-- Definition 4 (II): resolved at `x`: `∑_{x∈E_i} a_i + ν(J_x) < b`. -/
@[blueprint "def:I.4-II"
  (statement := /-- $\mathfrak R^N_{\mathrm{II}}$ is \emph{resolved at $x\in X$} if
    $\sum_{x\in E_i}a_i+\nu(J_x)<b$. (Def.\ 4 (II), p.\ 165.) -/)
  (latexEnv := "definition")]
def Raw.ResolvedAt (ℜ : Raw X) (x : X) : Prop :=
  (ℜ.weight x : ℕ∞) + ℜ.nuAt x < ℜ.b

def Raw.ResolvedEverywhere (ℜ : Raw X) : Prop := ∀ x : X, ℜ.ResolvedAt x

/-- `S(ℜ) = {x ∈ X | ∑_{x∈E_i} a_i + ν(J_x) ≥ b}` (p. 165). -/
@[blueprint "def:I.S"
  (statement := /-- $S(\mathfrak R)=\{x\in X\mid \sum_{x\in E_i}a_i+\nu(J_x)\ge b\}$. -/)
  (latexEnv := "definition")]
def Raw.S (ℜ : Raw X) : Set X := {x | (ℜ.b : ℕ∞) ≤ (ℜ.weight x : ℕ∞) + ℜ.nuAt x}

/-- `ν(ℜ) = max_{x ∈ S(ℜ)} ν(J_x)` if `S(ℜ) ≠ ∅`, and `0` otherwise (p. 165).

Formalization note (encoding): the maximum is encoded as the supremum in `ℕ∞` (which is `0` on
the empty set).  The paper's "max" presupposes that the values `ν(J_x)` are bounded; this is
proved in `DatumII.Raw.nu_ne_top` (Deviation from the paper (gap filled)), and a bounded supremum of natural numbers is attained
(`DatumII.Raw.exists_mem_S_nuAt_eq_nu`, node `lem:I.nu-attained`). -/
@[blueprint "def:I.nu"
  (statement := /-- $\nu(\mathfrak R)=\max_{x\in S(\mathfrak R)}\nu(J_x)$ if $S(\mathfrak R)$
    is non-empty, and $0$ otherwise. (Def.~4, p.~165.)

    Formalization note (encoding): the maximum is the supremum in $\mathbb N\cup\{\infty\}$
    ($0$ on the empty set). \textbf{Gap in the paper filled.} The paper's ``max'' presupposes
    that the orders $\nu(J_x)$ are bounded on $X$; Lean proves this (Krull's intersection
    theorem and the upper semicontinuity of Ch.~III, Cor.~1 of Th.~2, on the quasi-compact
    $X$) in \cref{rem:I.1-transform-is-datum-II}; and that the supremum is attained, so it is the
    printed maximum, in \cref{lem:I.nu-attained}. -/)
  (latexEnv := "definition")]
noncomputable def Raw.nu (ℜ : Raw X) : ℕ∞ := ⨆ x ∈ ℜ.S, ℜ.nuAt x

/-- `S_ν(ℜ) = {x ∈ S(ℜ) | ν(J_x) ≥ ν}`. -/
@[blueprint "def:I.S-nu"
  (statement := /-- $S_\nu(\mathfrak R)=\{x\in S(\mathfrak R)\mid\nu(J_x)\ge\nu\}$. -/)
  (latexEnv := "definition")]
def Raw.sNu (ℜ : Raw X) (ν : ℕ∞) : Set X := {x ∈ ℜ.S | ν ≤ ℜ.nuAt x}

/-- `S*(ℜ) = S_{ν(ℜ)}(ℜ)`. -/
@[blueprint "def:I.S-star"
  (statement := /-- $S^*(\mathfrak R)=S_{\nu}(\mathfrak R)$ with $\nu=\nu(\mathfrak R)$. -/)
  (latexEnv := "definition")]
def Raw.sStar (ℜ : Raw X) : Set X := ℜ.sNu ℜ.nu

end
end Hironaka.DatumII
namespace Hironaka
section
open Classical
/-- A resolution datum of type ℜ^N_{II}. -/
abbrev DatumII (X : Scheme.{u}) := {ℜ : DatumII.Raw X // ℜ.IsDatum}

end
end Hironaka
namespace Hironaka.DatumI.Raw
section
open Classical
variable {X : Scheme.{u}}
/-- Definition 5 (I.1): a closed restriction `F` for a datum of type ℜ^{N,n}_I. -/
@[blueprint "def:I.5-I.1"
  (statement := /-- A resolution datum of type $\mathfrak R^{N,n}_{\mathrm I}$ \emph{with closed
    restriction $F$} is a pair $(\mathfrak R,F)$ with $F$ a non-singular irreducible subscheme
    of codimension one such that (i) $E\cup F$ has only normal crossings on $X$, and
    (ii) $W-W\cap F$ is dense in $W$. (Def.\ 5 (I.1), pp.\ 165–166.) -/)
  (latexEnv := "definition")]
def IsClosedRestriction (ℜ : Raw X) (F : Subscheme X) : Prop :=
  F.IsNonsingularIrreducibleCodimOne ∧
  (ℜ.E.union F).HasOnlyNormalCrossings ∧
  ℜ.W.pts ⊆ closure (ℜ.W.pts \ F.pts)

/-- Definition 5 (I.2): an open restriction `U` for a datum of type ℜ^{N,n}_I. -/
@[blueprint "def:I.5-I.2"
  (statement := /-- A resolution datum of type $\mathfrak R^{N,n}_{\mathrm I}$ \emph{with open
    restriction $U$} is a pair $(\mathfrak R,U)$ with $U$ a dense open subset of $W$ such that
    $\mathfrak R$ is resolved at every point of $U$. (Def.\ 5 (I.2), p.\ 166.) -/)
  (latexEnv := "definition")]
def IsOpenRestriction (ℜ : Raw X) (U : Set X) : Prop :=
  (∃ U₀ : Set X, IsOpen U₀ ∧ U = U₀ ∩ ℜ.W.pts) ∧
  ℜ.W.pts ⊆ closure U ∧
  ∀ x ∈ U, ℜ.ResolvedAt x

end
end Hironaka.DatumI.Raw
namespace Hironaka.DatumII.Raw
section
open Classical
variable {X : Scheme.{u}}
/-- Definition 5 (II.1): a closed restriction `F` for a datum of type ℜ^N_{II}. -/
@[blueprint "def:I.5-II.1"
  (statement := /-- A resolution datum of type $\mathfrak R^N_{\mathrm{II}}$ \emph{with closed
    restriction $F$} is a pair $(\mathfrak R,F)$ with $F$ a non-singular irreducible
    subscheme of codimension one such that $E_1\cup\dots\cup E_\alpha\cup F$ has only normal
    crossings on $X$. (Def.\ 5 (II.1), p.\ 166.) -/)
  (latexEnv := "definition")]
def IsClosedRestriction (ℜ : Raw X) (F : Subscheme X) : Prop :=
  F.IsNonsingularIrreducibleCodimOne ∧ (ℜ.eUnion.union F).HasOnlyNormalCrossings

end
end Hironaka.DatumII.Raw
namespace Hironaka.DatumI.Raw
section
open Classical
variable {X : Scheme.{u}}
/-- Definition 6 for type I: the monoidal transformation with center `B` is *permissible*
for `ℜ = (E; V; W)` if `(E; V₁, …, V_β, W; B)` is a resolution datum of type ℜ^{N,m}_I
(`m = dim B`) which is resolved at every point of `B`. -/
@[blueprint "def:I.6-I"
  (statement := /-- Let $B$ be a non-singular irreducible subscheme of $X$ and $f\colon X'\to X$
    the monoidal transformation with center $B$. Then $f$ is \emph{permissible} for
    $\mathfrak R^{N,n}_{\mathrm I}=(E;V_1,\dots,V_\beta;W)$ if $(E;V_1,\dots,V_\beta,W;B)$
    is a resolution datum of type $\mathfrak R^{N,m}_{\mathrm I}$, $m=\dim B$, which is
    resolved everywhere. (Def.\ 6, p.\ 167.) -/)
  (latexEnv := "definition")]
def IsPermissible (ℜ : Raw X) (B : Subscheme X) : Prop :=
  B.IsCenter ∧ (ℜ.extendBy B).IsDatum ∧ (ℜ.extendBy B).ResolvedEverywhere

/-- Permissibility for `(ℜ, F)`: permissible for `ℜ` and `B ⊆ W ∩ F`. -/
@[blueprint "def:I.6-I-closed"
  (statement := /-- $f$ is permissible for $(\mathfrak R^{N,n}_{\mathrm I},F)$ if it is so for
    $\mathfrak R^{N,n}_{\mathrm I}$ and $B\subseteq W\cap F$. (p.\ 168.) -/)
  (latexEnv := "definition")]
def IsPermissibleClosed (ℜ : Raw X) (F B : Subscheme X) : Prop :=
  ℜ.IsPermissible B ∧ B.pts ⊆ ℜ.W.pts ∩ F.pts

/-- Permissibility for `(ℜ, U)`: permissible for `ℜ` and `B ⊆ W − U`. -/
@[blueprint "def:I.6-I-open"
  (statement := /-- $f$ is permissible for $(\mathfrak R^{N,n}_{\mathrm I},U)$ if it is so for
    $\mathfrak R^{N,n}_{\mathrm I}$ and $B\subseteq W-U$. (p.\ 168.) -/)
  (latexEnv := "definition")]
def IsPermissibleOpen (ℜ : Raw X) (U : Set X) (B : Subscheme X) : Prop :=
  ℜ.IsPermissible B ∧ B.pts ⊆ ℜ.W.pts \ U

end
end Hironaka.DatumI.Raw
namespace Hironaka.DatumII.Raw
section
open Classical
variable {X : Scheme.{u}}
/-- Definition 6 for type II: permissible if `B ⊆ S*(ℜ)` and `E₁ ∪ ⋯ ∪ E_α` has only normal
crossings with `B`. -/
@[blueprint "def:I.6-II"
  (statement := /-- $f$ (with center $B$) is \emph{permissible} for $\mathfrak R^N_{\mathrm{II}}$
    if $B\subseteq S^*(\mathfrak R)$ and $E_1\cup\dots\cup E_\alpha$ has only normal
    crossings with $B$ on $X$. (Def.\ 6, pp.\ 167–168.) -/)
  (latexEnv := "definition")]
def IsPermissible (ℜ : Raw X) (B : Subscheme X) : Prop :=
  B.IsCenter ∧ B.pts ⊆ ℜ.sStar ∧ ℜ.eUnion.HasOnlyNormalCrossingsWith B

/-- Permissibility for `(ℜ, F)`: permissible for `ℜ` and `B ⊆ F`. -/
@[blueprint "def:I.6-II-closed"
  (statement := /-- $f$ is permissible for $(\mathfrak R^N_{\mathrm{II}},F)$ if it is so for
    $\mathfrak R^N_{\mathrm{II}}$ and $B\subseteq F$. (p.\ 168.) -/)
  (latexEnv := "definition")]
def IsPermissibleClosed (ℜ : Raw X) (F B : Subscheme X) : Prop :=
  ℜ.IsPermissible B ∧ B.pts ⊆ F.pts

end
end Hironaka.DatumII.Raw
namespace Hironaka.DatumI.Raw
section
open Classical
variable {X : Scheme.{u}}
/-- Definition 7 (type I): `f*(E; V; W) = (E' ∪ E'_{α+1}; V'; W')` with primes denoting strict
transforms and `E'_{α+1} = f⁻¹(B)` (the paper's notation, used for both types of data; in the
code comments of this file it is sometimes called `E_{β+1}`).

Formalization note (encoding): the transform is a total function, defined for every center;
the paper defines it only for permissible ones. -/
@[blueprint "def:I.7-I"
  (statement := /-- For a permissible monoidal transformation $f\colon X'\to X$ with center $B$,
    $f^*(E;V_1,\dots,V_\beta;W)=(E'\cup E'_{\alpha+1};V_1',\dots,V_\beta';W')$, where $'$
    denotes strict transform and $E'_{\alpha+1}=f^{-1}(B)$ (the total transform of $B$).
    (Def.\ 7, p.\ 168.)

    Formalization note (encoding): in Lean the transform is a total function, defined for
    every center. -/)
  (latexEnv := "definition")]
noncomputable def transform (ℜ : Raw X) {B : Subscheme X} (t : MonoidalTransformation X B) :
    Raw t.X' where
  E := (Subscheme.strictTransform t ℜ.E).union t.exceptional
  β := ℜ.β
  V := fun j => Subscheme.strictTransform t (ℜ.V j)
  W := Subscheme.strictTransform t ℜ.W

/-- Transform of an open restriction: `U' = f⁻¹(U)`. -/
def transformOpen {B : Subscheme X} (t : MonoidalTransformation X B) (U : Set X) : Set t.X' :=
  t.f.base ⁻¹' U

end
end Hironaka.DatumI.Raw
namespace Hironaka.DatumII.Raw
section
open Classical
variable {X : Scheme.{u}}
/-- Definition 7 (type II):
`f*(E₁,…,E_α; J; b; a) = (E₁',…,E_α', E_{α+1}; f⁻¹(J)·P^{-ν}; b; a₁,…,a_α, a_{α+1})` where
`ν = ν(ℜ)`, `E_{α+1} = f⁻¹(B)` with ideal sheaf `P`, and
`a_{α+1} = (∑_{B ⊆ E_i} a_i) + ν − b`.

Formalization note (encoding): `f⁻¹(J)·P^{-ν}` is `Subscheme.divPow`, the colon ideal sheaf
`(f⁻¹(J) : P^ν)`.  The paper's quotient is the sheaf `K` with `K·P^ν = f⁻¹(J)` (p. 142, p. 176: "the
quotient obtained by this division"), which exists because `f⁻¹(J)` is divisible by `P^ν`
(`DatumII.Raw.totalTransform_le_exceptional_pow_nu`, proved from Ch. III, Remark 2, p. 214) and is
unique because `P` is invertible; `DatumII.Raw.transform_J_mul_exceptional_pow` and
`DatumII.Raw.le_exceptional_pow_and_existsUnique_mul_eq` show that the colon ideal is this quotient.
`ν` enters as `ν.toNat` (`ν(ℜ) < ∞` by `DatumII.Raw.nu_ne_top`).

Deviation from the paper (statement corrected): `a_{α+1}` is computed in `ℕ`, with truncated
subtraction.  For a non-empty permissible center the paper's integer is `≥ 0` (at the generic
point `η` of `B ⊆ S_ν(ℜ)` one has `∑_{η ∈ E_i} a_i + ν ≥ b`; proved in
`DatumII.Raw.printedExponent_nonneg_of_isPermissible`, `lem:I.7-II-exponent-nonneg`) and the two agree
(`DatumII.Raw.transform_a_last_eq_toNat_printedExponent`).  For the empty center, which Def. 6 declares permissible for every datum, the
empty subscheme is contained in every `E_i` (p. 165) and the printed integer can be negative
(e.g. `α = 0`, `J = O_X`, `b = 1`: `a₁ = −1`), so the printed transform is not a datum of type
`ℜ_II`; Lean's value is `0` (irrelevant, since `E_{α+1} = f⁻¹(∅) = ∅`). -/
@[blueprint "def:I.7-II"
  (statement := /-- For a permissible monoidal transformation $f$ with center $B$,
    $f^*\big(E_1,\dots,E_\alpha\,\big|\,J,b\,\big|\,a\big)=\big(E_1',\dots,E_\alpha',E_{\alpha+1}
    \,\big|\,f^{-1}(J)P^{-\nu},b\,\big|\,a_1,\dots,a_\alpha,a_{\alpha+1}\big)$ where
    $\nu=\nu(\mathfrak R)$, $E_{\alpha+1}=f^{-1}(B)$ has ideal sheaf $P$, and
    $a_{\alpha+1}=\big(\sum_{B\subseteq E_i}a_i\big)+\nu-b$. (Def.\ 7, p.\ 168.)

    Formalization note (encoding): $f^{-1}(J)P^{-\nu}$ is encoded as the colon ideal sheaf
    $(f^{-1}(J):P^{\nu})$. The paper's quotient is the sheaf $K$ with $KP^{\nu}=f^{-1}(J)$
    (pp.~142, 176); it exists because $f^{-1}(J)$ is divisible by $P^\nu$ and is unique because
    $P$ is invertible, and the colon ideal is this quotient (\cref{lem:I.7-II-divisible}).

    \textbf{Correction of the paper (statement).} For the empty center, which Definition~6
    declares permissible for every datum, the empty subscheme is contained in every $E_i$
    (p.~165) and the printed $a_{\alpha+1}$ can be negative (e.g.\ $\alpha=0$, $J=\mathcal
    O_X$, $b=1$ give $a_1=-1$), so the printed transform is not a resolution datum of type
    $\mathfrak R^N_{\mathrm{II}}$, contrary to Remark~1. Lean computes $a_{\alpha+1}$ with
    truncated subtraction (value $0$ in this case; harmless, as $E_{\alpha+1}=\emptyset$). For
    a non-empty permissible center the printed integer is $\ge0$
    (\cref{lem:I.7-II-exponent-nonneg}), so the two agree. -/)
  (latexEnv := "definition")]
noncomputable def transform (ℜ : Raw X) {B : Subscheme X} (t : MonoidalTransformation X B) :
    Raw t.X' where
  α := ℜ.α + 1
  E := Fin.snoc (fun i => Subscheme.strictTransform t (ℜ.E i)) t.exceptional
  a := Fin.snoc ℜ.a
    ((∑ i ∈ (Finset.univ.filter fun i => B.IsContainedIn (ℜ.E i)), ℜ.a i) +
      (ℜ.nu.toNat) - ℜ.b)
  J := Subscheme.divPow (Subscheme.totalTransform t.f ℜ.J) t.exceptional ℜ.nu.toNat
  b := ℜ.b

end
end Hironaka.DatumII.Raw
namespace Hironaka.MonoidalSuccession
section
open Classical
variable {X Y : Scheme.{u}}
/-- Transform of a type I raw datum along a succession. -/
noncomputable def transformI : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    DatumI.Raw X → DatumI.Raw Y
  | _, _, nil _, ℜ => ℜ
  | _, _, cons _ t rest, ℜ => rest.transformI (ℜ.transform t)

/-- Transform of a type II raw datum along a succession. -/
noncomputable def transformII : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    DatumII.Raw X → DatumII.Raw Y
  | _, _, nil _, ℜ => ℜ
  | _, _, cons _ t rest, ℜ => rest.transformII (ℜ.transform t)

/-- Definition 8 for `(ℜ, F)`, type I. -/
def IsPermissibleIClosed : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    DatumI.Raw X → Subscheme X → Prop
  | _, _, nil _, _, _ => True
  | _, _, cons B t rest, ℜ, F =>
      ℜ.IsPermissibleClosed F B ∧
      rest.IsPermissibleIClosed (ℜ.transform t) (Subscheme.strictTransform t F)

/-- Definition 8 for `(ℜ, U)`, type I. -/
def IsPermissibleIOpen : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    DatumI.Raw X → Set X → Prop
  | _, _, nil _, _, _ => True
  | _, _, cons B t rest, ℜ, U =>
      ℜ.IsPermissibleOpen U B ∧
      rest.IsPermissibleIOpen (ℜ.transform t) (DatumI.Raw.transformOpen t U)

/-- Definition 8 for type II data without restriction. -/
def IsPermissibleII : {X Y : Scheme.{u}} → MonoidalSuccession X Y → DatumII.Raw X → Prop
  | _, _, nil _, _ => True
  | _, _, cons B t rest, ℜ => ℜ.IsPermissible B ∧ rest.IsPermissibleII (ℜ.transform t)

/-- Definition 8 for `(ℜ, F)`, type II. -/
def IsPermissibleIIClosed : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    DatumII.Raw X → Subscheme X → Prop
  | _, _, nil _, _, _ => True
  | _, _, cons B t rest, ℜ, F =>
      ℜ.IsPermissibleClosed F B ∧
      rest.IsPermissibleIIClosed (ℜ.transform t) (Subscheme.strictTransform t F)

end
end Hironaka.MonoidalSuccession
namespace Hironaka
/-- The standing hypothesis of §2 (p. 170): "we denote by X any non-singular irreducible
algebraic scheme of dimension N ≧ 0" (cf. Def. 3, p. 164: "We always assume that dim(X) ≧ 0").

The definition does not require `0 < N`, in accordance with the paper's `N ≧ 0`: such a conjunct
would make the cases `N = 0` of Theorems II₁^N, II₂^N vacuous, whereas in the paper they are
(trivially true) statements about a point.  The cases `N = 0` are proved in
`FundamentalTheorem.II₁_zero_and_II₂_zero`. -/
def IsAmbient (X : Scheme.{u}) (N : ℕ) : Prop :=
  IsAlgebraicScheme X ∧ X.IsNonsingular ∧ IrreducibleSpace X ∧ X.dim = (N : WithBot ℕ∞)

/-- Theorem I₁^{N,n}: "Given any resolution datum `(ℜ^{N,n}_I, F)` on `X`, there exists a
finite succession of monoidal transformations `f : X' → X`, permissible for `(ℜ, F)`, such
that if `f*(ℜ, F) = (f*ℜ, F')` then `F'` has no common points with the principal subscheme
of `f*ℜ`."

Deviation from the paper (statement modified): `n : ℕ`, so the paper's instances with
`n = -1` (empty `W`, "absolutely trivial", p. 171) are not covered by this declaration; they are
the separate declaration `FundamentalTheorem.I₁Bot` (proved in `FundamentalTheorem.I₁Bot_and_I₂Bot`). -/
@[blueprint "thm:I.2-I1"
  (statement := /-- \textbf{Theorem $\mathrm I_1^{N,n}$.} Given any resolution datum
    $(\mathfrak R^{N,n}_{\mathrm I},F)$ on $X$, there exists a finite succession of monoidal
    transformations $f\colon X'\to X$, permissible for $(\mathfrak R^{N,n}_{\mathrm I},F)$,
    such that if $f^*(\mathfrak R^{N,n}_{\mathrm I},F)=(f^*(\mathfrak R^{N,n}_{\mathrm I}),F')$
    then $F'$ has no common points with the principal subscheme of
    $f^*(\mathfrak R^{N,n}_{\mathrm I})$. (p.\ 170.)

    \textbf{Deviation from the paper (statement modified).} Only $n\ge0$ is stated ($n$ is a
    natural number): the paper's instances with $n=-1$ (empty $W$), ``absolutely trivial''
    (p.~171), are the separate statement \cref{thm:I.2-I1-minus-one}. -/)
  (latexEnv := "theorem")]
def FundamentalTheorem.I₁ (N n : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAmbient X N →
  ∀ (ℜ : DatumI X) (F : Subscheme X), (ℜ : DatumI.Raw X).IsClosedRestriction F →
    (ℜ : DatumI.Raw X).n = (n : WithBot ℕ∞) →
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
    s.IsPermissibleIClosed ℜ F ∧
    (s.transformI ℜ).principal.pts ∩ (s.strictTransform F).pts = ∅

/-- Theorem I₂^{N,n}: "Given any resolution datum `(ℜ^{N,n}_I, U)` on `X`, there exists a
finite succession of monoidal transformations `f`, permissible for `(ℜ, U)`, such that
`f*ℜ` is resolved everywhere (i.e. at every point of the principal subscheme of `f*ℜ`)."

Deviation from the paper (statement modified): only `n : ℕ`; the trivial instances with
`n = -1` are the separate declaration `FundamentalTheorem.I₂Bot` (proved in
`FundamentalTheorem.I₁Bot_and_I₂Bot`). -/
@[blueprint "thm:I.2-I2"
  (statement := /-- \textbf{Theorem $\mathrm I_2^{N,n}$.} Given any resolution datum
    $(\mathfrak R^{N,n}_{\mathrm I},U)$ on $X$, there exists a finite succession of monoidal
    transformations $f\colon X'\to X$, permissible for $(\mathfrak R^{N,n}_{\mathrm I},U)$,
    such that $f^*(\mathfrak R^{N,n}_{\mathrm I})$ is resolved everywhere. (p.\ 170.)

    \textbf{Deviation from the paper (statement modified).} Only $n\ge0$ is stated; the
    ``absolutely trivial'' instances with $n=-1$ (empty $W$, p.~171) are the separate statement
    \cref{thm:I.2-I2-minus-one}. -/)
  (latexEnv := "theorem")]
def FundamentalTheorem.I₂ (N n : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAmbient X N →
  ∀ (ℜ : DatumI X) (U : Set X), (ℜ : DatumI.Raw X).IsOpenRestriction U →
    (ℜ : DatumI.Raw X).n = (n : WithBot ℕ∞) →
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
    s.IsPermissibleIOpen ℜ U ∧ (s.transformI ℜ).ResolvedEverywhere

/-- Theorem II₁^N: "Given any resolution datum `(ℜ^N_{II}, F)` on `X` such that
`ν(ℜ) > 0`, there exists a finite succession of monoidal transformations `f`, permissible
for `(ℜ, F)`, such that if `f*(ℜ, F) = (f*ℜ, F')`, then `F'` has no points contained in
`S_ν(f*ℜ)` where `ν = ν(ℜ)`." -/
@[blueprint "thm:I.2-II1"
  (statement := /-- \textbf{Theorem $\mathrm{II}_1^N$.} Given any resolution datum
    $(\mathfrak R^N_{\mathrm{II}},F)$ on $X$ such that $\nu(\mathfrak R^N_{\mathrm{II}})>0$,
    there exists a finite succession of monoidal transformations $f\colon X'\to X$,
    permissible for $(\mathfrak R^N_{\mathrm{II}},F)$, such that if
    $f^*(\mathfrak R^N_{\mathrm{II}},F)=(f^*(\mathfrak R^N_{\mathrm{II}}),F')$ then $F'$ has
    no points contained in $S_\nu(f^*(\mathfrak R^N_{\mathrm{II}}))$ where
    $\nu=\nu(\mathfrak R^N_{\mathrm{II}})$. (p.\ 170.)

    (The Lean predicate \texttt{IsAmbient} does not require $0<N$: the paper allows $N\ge0$,
    p.~170, and requiring $0<N$ would make the case $N=0$ vacuous.) -/)
  (latexEnv := "theorem")]
def FundamentalTheorem.II₁ (N : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAmbient X N →
  ∀ (ℜ : DatumII X) (F : Subscheme X), (ℜ : DatumII.Raw X).IsClosedRestriction F →
    0 < (ℜ : DatumII.Raw X).nu →
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
    s.IsPermissibleIIClosed ℜ F ∧
    (s.strictTransform F).pts ∩ (s.transformII ℜ).sNu (ℜ : DatumII.Raw X).nu = ∅

/-- Theorem II₂^N: "Given any resolution datum `ℜ^N_{II}` without restriction on `X`, there
exists a finite succession of monoidal transformations `f`, permissible for `ℜ`, such that
`f*ℜ` is resolved everywhere." -/
@[blueprint "thm:I.2-II2"
  (statement := /-- \textbf{Theorem $\mathrm{II}_2^N$.} Given any resolution datum
    $\mathfrak R^N_{\mathrm{II}}$ without restriction on $X$, there exists a finite succession
    of monoidal transformations $f\colon X'\to X$, permissible for
    $\mathfrak R^N_{\mathrm{II}}$, such that $f^*(\mathfrak R^N_{\mathrm{II}})$ is resolved
    everywhere. (pp.\ 170–171.)

    (As for \cref{thm:I.2-II1}, \texttt{IsAmbient} does not require $0<N$: the paper allows
    $N\ge0$, and requiring $0<N$ would make the case $N=0$ vacuous.) -/)
  (latexEnv := "theorem")]
def FundamentalTheorem.II₂ (N : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAmbient X N →
  ∀ (ℜ : DatumII X),
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
    s.IsPermissibleII ℜ ∧ (s.transformII ℜ).ResolvedEverywhere

/-- Theorem I₁^{N,-1} (p. 171): Theorem I₁^{N,n} (`FundamentalTheorem.I₁`) for `n = -1`, i.e. for
data `ℜ` with `dim W = -1` (`ℜ.n = ⊥`), that is, with empty `W` (`DatumI.Raw.n_eq_bot_iff`).  The
statement is that of `FundamentalTheorem.I₁` with the hypothesis `ℜ.n = ⊥` in place of
`ℜ.n = n`.  (`FundamentalTheorem.I₁` itself, indexed by `n : ℕ`, is unchanged.)

The paper's instances with `n = -1`; proved in `FundamentalTheorem.I₁Bot_and_I₂Bot`. -/
@[blueprint "thm:I.2-I1-minus-one"
  (statement := /-- \textbf{Theorem $\mathrm I_1^{N,-1}$.} Given any resolution datum
    $(\mathfrak R^{N,-1}_{\mathrm I},F)$ on $X$ (that is, with $\dim W=-1$: $W$ empty), there
    exists a finite succession of monoidal transformations $f\colon X'\to X$, permissible for
    $(\mathfrak R^{N,-1}_{\mathrm I},F)$, such that if
    $f^*(\mathfrak R^{N,-1}_{\mathrm I},F)=(f^*(\mathfrak R^{N,-1}_{\mathrm I}),F')$ then $F'$
    has no common points with the principal subscheme of $f^*(\mathfrak R^{N,-1}_{\mathrm I})$.
    (p.\ 170, instance $n=-1$, listed on p.~171.)

    Formalization note (encoding): $n=-1$ is the hypothesis $\dim W=\bot$ in
    $\mathbb N\cup\{\pm\infty\}$ (the dimension of the empty scheme, p.~163). The statement of
    \cref{thm:I.2-I1} is unchanged and covers $n\ge0$. -/)
  (latexEnv := "theorem")]
def FundamentalTheorem.I₁Bot (N : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAmbient X N →
  ∀ (ℜ : DatumI X) (F : Subscheme X), (ℜ : DatumI.Raw X).IsClosedRestriction F →
    (ℜ : DatumI.Raw X).n = ⊥ →
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
    s.IsPermissibleIClosed ℜ F ∧
    (s.transformI ℜ).principal.pts ∩ (s.strictTransform F).pts = ∅

/-- Theorem I₂^{N,-1} (p. 171): Theorem I₂^{N,n} (`FundamentalTheorem.I₂`) for `n = -1`, i.e. for
data `ℜ` with `dim W = -1` (`ℜ.n = ⊥`), that is, with empty `W` (`DatumI.Raw.n_eq_bot_iff`).
(`FundamentalTheorem.I₂` itself, indexed by `n : ℕ`, is unchanged.)

The paper's instances with `n = -1`; proved in `FundamentalTheorem.I₁Bot_and_I₂Bot`. -/
@[blueprint "thm:I.2-I2-minus-one"
  (statement := /-- \textbf{Theorem $\mathrm I_2^{N,-1}$.} Given any resolution datum
    $(\mathfrak R^{N,-1}_{\mathrm I},U)$ on $X$ (that is, with $\dim W=-1$: $W$ empty), there
    exists a finite succession of monoidal transformations $f\colon X'\to X$, permissible for
    $(\mathfrak R^{N,-1}_{\mathrm I},U)$, such that $f^*(\mathfrak R^{N,-1}_{\mathrm I})$ is
    resolved everywhere. (p.\ 170, instance $n=-1$, listed on p.~171.)

    Formalization note (encoding): as for \cref{thm:I.2-I1-minus-one}. -/)
  (latexEnv := "theorem")]
def FundamentalTheorem.I₂Bot (N : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAmbient X N →
  ∀ (ℜ : DatumI X) (U : Set X), (ℜ : DatumI.Raw X).IsOpenRestriction U →
    (ℜ : DatumI.Raw X).n = ⊥ →
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
    s.IsPermissibleIOpen ℜ U ∧ (s.transformI ℜ).ResolvedEverywhere

/-- Theorem I₁^{N,n} for every `n ≧ −1` (`n : WithBot ℕ`, `⊥ = −1`): `FundamentalTheorem.I₁Bot`
for `n = −1` and `FundamentalTheorem.I₁` for `n ≧ 0`. -/
def FundamentalTheorem.I₁WithBot (N : ℕ) : WithBot ℕ → Prop :=
  WithBot.recBotCoe (FundamentalTheorem.I₁Bot.{u} N) (FundamentalTheorem.I₁.{u} N)

/-- Theorem I₂^{N,n} for every `n ≧ −1` (`n : WithBot ℕ`, `⊥ = −1`): `FundamentalTheorem.I₂Bot`
for `n = −1` and `FundamentalTheorem.I₂` for `n ≧ 0`. -/
def FundamentalTheorem.I₂WithBot (N : ℕ) : WithBot ℕ → Prop :=
  WithBot.recBotCoe (FundamentalTheorem.I₂Bot.{u} N) (FundamentalTheorem.I₂.{u} N)

end Hironaka
namespace Hironaka.MonoidalSuccession
/-- The properties (1)–(4) of Main Theorem II(N) (p. 176) of a finite succession of monoidal
transformations `{f_i : X_{i+1} → X_i}` with centers `B_i`, for the sheaves `J = J_0` and `E = E_0`:

* a succession with no transformation (`r = 0`) has the property (4): `E_0` has only normal
  crossings and `J_0 = O_X`;
* otherwise, for the first transformation `f_0` with center `B_0`: (1) `B_0` is a non-singular
  irreducible subscheme (possibly empty, p. 163); (2) the maximal integer `d_0` attained by `ν(J_y)`,
  `y ∈ X`, exists, is positive, and `ν(J_z) = d_0` for all `z ∈ B_0`; (3) `E_0` has only normal
  crossings with `B_0`; and the rest of the succession has the properties for the weak transform
  `J_1` of `J_0` by `f_0` and the reduced subscheme `E_1 = red(f_0⁻¹(E_0 ∪ B_0))`. -/
def IsMainSuccession : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Subscheme X →
    Subscheme X → Prop
  | _, _, nil _, J, E => E.HasOnlyNormalCrossings ∧ J = ⊤
  | _, _, cons B t rest, J, E =>
      B.IsCenter ∧
      (∃ d : ℕ, 0 < d ∧ IsGreatest (Set.range fun y => Ideal.nu (J.stalkIdeal y)) (d : ℕ∞) ∧
        ∀ z ∈ B.pts, Ideal.nu (J.stalkIdeal z) = d) ∧
      E.HasOnlyNormalCrossingsWith B ∧
      rest.IsMainSuccession (Subscheme.weakTransform t J)
        (Subscheme.totalTransform t.f (E.union B)).radical

end Hironaka.MonoidalSuccession
namespace Hironaka
/-- Main Theorem II(N) (p. 176).

Formalization notes (encoding): "a coherent sheaf of non-zero ideals" is read as in Definition 3
(`DatumII.Raw.IsDatum`): every stalk `J_x` is a non-zero ideal; the sheaves are subschemes (ideal
sheaves), `⊤ = O_X` is the unit ideal; "a non-singular irreducible subscheme" may be empty
(`Subscheme.IsCenter`, the agreement of p. 163); the finite succession with the properties
(1)–(4) is `MonoidalSuccession.IsMainSuccession`.  The dimension `N` is the dimension of `X`. -/
@[blueprint "thm:I.3-main-II"
  (statement := /-- \textbf{Main Theorem II($N$).} Let $X$ be a non-singular algebraic scheme of
    dimension $N$. Let $J$ be a coherent sheaf of non-zero ideals on $X$, and $E$ a reduced
    subscheme of $X$ which is everywhere of codimension one and has only normal crossings. Then
    there exists a finite succession of monoidal transformations
    $\{f_i\colon X_{i+1}\to X_i\}$ with centers $B_i$ in $X_i$, where $0\le i<r$ and $X_0=X$,
    which has the following properties:
    (1) $B_i$ is a non-singular irreducible subscheme of $X_i$;
    (2) if $J_{i+1}$ is the weak transform of $J_i$ by the monoidal transformations $f_i$ for all
    $i$, where $J_0=J$, and if $d_i$ is the maximal integer attained by $\nu(J_{iy})$ for the
    points $y$ of $X_i$, then $d_i$ is a positive integer and $\nu(J_{iz})=d_i$ for all the
    points $z$ of $B_i$;
    (3) if $E_{i+1}$ denotes the reduced subscheme $\operatorname{red}(f_i^{-1}(E_i\cup B_i))$ of
    $X_{i+1}$ for all $i$, where $E_0=E$, then $E_i$ has only normal crossings with $B_i$; and
    (4) $E_r$ has only normal crossings and $J_r$ is equal to $\mathcal O_{X_r}$. (p.~176.)

    Formalization notes (encoding): ``a coherent sheaf of non-zero ideals'' is read as in
    \cref{def:I.3-II}: every stalk $J_x$ is a non-zero ideal; the properties (1)--(4) of the
    succession are carried along it (as in \cref{def:I.8}); ``a non-singular irreducible
    subscheme'' may be empty (the agreement of p.~163). -/)
  (proof := /-- If $X$ is irreducible, apply the fundamental theorem $\mathrm{II}_2^N$
    (\cref{thm:I.2-II2}) to the resolution datum $\mathfrak R^N_{\mathrm{II}}=(E_1,\dots,E_\alpha
    \mid J,b)$ on $X$ with $b=1$, the $E_i$ the irreducible components of $E$ and all
    $a_i=0$. If $\{f_i\}_{0\le i<r'}$ is the permissible succession so obtained, take the smallest
    $r$ such that $\mathcal O_{X_r}$ is the sheaf of ideals attached to the transform of
    $\mathfrak R^N_{\mathrm{II}}$ by $\{f_i\}_{0\le i<r}$. This succession of $r$ monoidal
    transformations has the properties (1)--(4) (\cref{lem:I.3-main-II-properties}). For a
    non-irreducible $X$ the fundamental theorem is first extended to non-singular algebraic
    schemes (\cref{lem:I.3-main-II-components}).

    \textbf{Deviation from the paper (gap filled).} ``As is easily seen, the proof of the main
    theorem can be reduced to the case in which $X$ is irreducible'' (p.~176) is proved in
    \cref{lem:I.3-main-II-components}. -/)
  (proofUses := ["thm:I.2-II2", "lem:I.3-main-II-components", "lem:I.3-main-II-properties"])
  (latexEnv := "theorem")]
def MainTheorem.II (N : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAlgebraicScheme X → X.IsNonsingular → X.dim = (N : WithBot ℕ∞) →
  ∀ (J : Subscheme X), (∀ x, J.stalkIdeal x ≠ ⊥) →
  ∀ (E : Subscheme X), E.IsReduced → E.IsEverywhereCodimOne → E.HasOnlyNormalCrossings →
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainSuccession J E

end Hironaka
namespace Hironaka.MonoidalTransformation
section
variable {X : Scheme.{u}} {B : Subscheme X}
/-- The open subscheme `X − B` of `X`. -/
def complOpens (B : Subscheme X) : X.Opens := ⟨B.ptsᶜ, B.support.isClosed.isOpen_compl⟩

end
end Hironaka.MonoidalTransformation
namespace Hironaka.Subscheme
section
variable {X : Scheme.{u}}
/-- `red(D)`: the associated reduced scheme of a subscheme (p. 143: "where red( ) denotes the associated reduced
scheme"): the subscheme with the radical ideal sheaf.  `red(⊥)` is `red(X)`. -/
abbrev red (D : Subscheme X) : Subscheme X := Scheme.IdealSheafData.radical D

end
end Hironaka.Subscheme
namespace Hironaka
section
variable {X : Scheme.{u}} {β : ℕ}
/-- p. 174: the systems `V_0, V_1, …, V_β`; `V_0` is the scheme itself (written `V₀` in the paper), the subscheme
`⊥` of `X`. -/
@[blueprint "def:I.3-main-system"
  (statement := /-- The systems $V_0,V_1,\dots,V_\beta$ of Main Theorem~I($n$) (p.~174): $V_0=\mathbf V_0$ is the scheme itself (the subscheme with zero sheaf of ideals) and $V_j$ ($1\le j\le\beta$) are the given subschemes. Formalization note (encoding): $V_0$ is the subscheme $\bot$ and \texttt{mainSystem}~$V=\mathrm{Fin.cons}~\bot~V$; at the later stages $V_0(i)$ is the strict transform of $V_0$, which is again the whole scheme. -/)
  (latexEnv := "definition")]
def mainSystem (V : Fin β → Subscheme X) : Fin (β + 1) → Subscheme X :=
  Fin.cons ⊥ V

/-- p. 173 and p. 174: "those points of `W(i)` which are simple points of `W(i)` and at which all the
`V_j(i)` (`0 ≤ j ≤ β`) are normally flat along `W(i)`". -/
@[blueprint "def:I.3-main-resolved"
  (statement := /-- Let $V_0,V_1,\dots,V_\beta$ and $W$ be subschemes. A point $x$ of $W$ is \emph{resolved} if it is a simple point of $W$ at which all the $V_j$ for $0\le j\le\beta$ are normally flat along $W$ (p.~174: ``those simple points of $W(r)$ at which all the $V_j(r)$ for $0\le j\le\beta$ are normally flat along $W(r)$''; p.~173: ``those points of $W(i)$ which are simple points of $W(i)$ and at which all the $V_j(i)$ ($1\le j\le\beta$) are normally flat along $W(i)$''). -/)
  (latexEnv := "definition")]
def Subscheme.IsMainResolvedAt (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) (x : X) : Prop :=
  W.IsSimpleAt x ∧ ∀ j, Subscheme.IsNormallyFlatAlongAt' (V j) W x

/-- Conditions (1), (2), (3) of Main Theorem I(n) for a center `B` at one stage (pp. 173–174), with the shape of
the center left as a parameter `Cen` (`Subscheme.IsCenter` for (1) as printed, `Subscheme.IsNonsingular` for the
hatted centers `B̂_i = c_i⁻¹(B_i)`, which need not be irreducible). -/
@[blueprint "def:I.3-main-step-with"
  (statement := /-- Conditions (1), (2) and (3) of Main Theorem~I($n$) (p.~174) for a center $B$ at one stage $(V_0,\dots,V_\beta;W)$: (1) $B$ is a subscheme of $W$ of a given shape (non-singular irreducible, as printed, or only non-singular); (2) $B$ does not contain any simple point of $W$ at which all the $V_j$ for $0\le j\le\beta$ are normally flat along $W$; (3) all the $V_j$ ($0\le j\le\beta$) and $W$ are normally flat along $B$. Formalization note (encoding): the shape of the center is a parameter, since the completed centers $\hat B_i=c_i^{-1}(B_i)$ are non-singular but need not be irreducible (p.~175: ``Obviously, $\hat B_i$, $\hat W(i)$ and the $\hat V_j(i)$ for all $j$ satisfy the conditions (1), (2) and (3)'', imprecise on irreducibility). -/)
  (latexEnv := "definition")]
def Subscheme.IsMainStepWith (Cen : Subscheme X → Prop) (V : Fin (β + 1) → Subscheme X)
    (W B : Subscheme X) : Prop :=
  (Cen B ∧ B.IsContainedIn W) ∧
  (∀ x ∈ B.pts, ¬ Subscheme.IsMainResolvedAt V W x) ∧
  (∀ x ∈ B.pts, (∀ j, Subscheme.IsNormallyFlatAlongAt' (V j) B x) ∧
    Subscheme.IsNormallyFlatAlongAt' W B x)

/-- Condition (4) of Main Theorem I(n) for the data `(V; W)`: "`W` is non-singular and all the `V_j` for
`0 ≤ j ≤ β` are normally flat along `W`". -/
@[blueprint "def:I.3-main-4-data"
  (statement := /-- Condition (4) of Main Theorem~I($n$) for the data $(V_0,\dots,V_\beta;W)$ (p.~174): ``$W$ is non-singular and all the $V_j$ for $0\le j\le\beta$ are normally flat along $W$''. -/)
  (latexEnv := "definition")]
def Subscheme.IsMain4Data (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) : Prop :=
  W.IsNonsingular ∧ ∀ j, ∀ x ∈ W.pts, Subscheme.IsNormallyFlatAlongAt' (V j) W x

end
end Hironaka
namespace Hironaka.MonoidalSuccession
/-- Conditions (1), (2), (3) of Main Theorem I(n) "for all `i`" (p. 174: "any succession of monoidal
transformations with centers `B_i` in `V₀(i)`, which satisfy the conditions (1), (2) and (3) for all `i`"), with
the shape of the centers as a parameter.  `V_j(i+1)`, `W(i+1)` are the strict transforms of `V_j(i)`, `W(i)`. -/
@[blueprint "def:I.3-main-123-with"
  (statement := /-- Conditions (1), (2) and (3) of Main Theorem~I($n$) ``for all $i$'' (p.~174: ``any succession of monoidal transformations with centers $B_i$ in $V_0(i)$, where $V_0(0)=V_0$, which satisfy the conditions (1), (2) and (3) for all $i$''), the shape of the centers being a parameter. Here $V_j(i+1)$ and $W(i+1)$ are the strict transforms of $V_j(i)$ and $W(i)$ by $f_i$ (the monoidal transformations ``induced by $f_i$'', p.~173). -/)
  (latexEnv := "definition")]
def IsMain123With (Cen : ∀ {X : Scheme.{u}}, Subscheme X → Prop) :
    {X Y : Scheme.{u}} → MonoidalSuccession X Y → {β : ℕ} → (Fin (β + 1) → Subscheme X) →
      Subscheme X → Prop
  | _, _, nil _, _, _, _ => True
  | _, _, cons B t rest, _, V, W =>
      Subscheme.IsMainStepWith (fun D => Cen D) V W B ∧
      rest.IsMain123With Cen (fun j => Subscheme.strictTransform t (V j)) (Subscheme.strictTransform t W)

/-- (1), (2), (3) for all `i`, as printed. -/
@[blueprint "def:I.3-main-123"
  (statement := /-- The conditions (1), (2), (3) of Main Theorem~I($n$) for all $i$, as printed (the centers are non-singular irreducible subschemes, \cref{def:I.3-main-step}; p.~174). -/)
  (latexEnv := "definition")]
abbrev IsMain123 {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {β : ℕ}
    (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) : Prop :=
  s.IsMain123With (fun {_} D => Subscheme.IsCenter D) V W

/-- Condition (4): "`W(r)` is non-singular and all the `V_j(r)` for `0 ≤ j ≤ β` are normally flat along `W(r)`". -/
@[blueprint "def:I.3-main-4"
  (statement := /-- Condition (4) of Main Theorem~I($n$) for a succession $\{f_i\}_{0\le i<r}$ (p.~174): ``$W(r)$ is non-singular and all the $V_j(r)$ for $0\le j\le\beta$ are normally flat along $W(r)$'', $V_j(r)$, $W(r)$ being the strict transforms by the succession. -/)
  (latexEnv := "definition")]
def IsMain4 {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {β : ℕ}
    (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) : Prop :=
  Subscheme.IsMain4Data (fun j => s.strictTransform (V j)) (s.strictTransform W)

/-- The conclusion of Main Theorem I(n): (1), (2), (3) for all `i < r` and (4). -/
@[blueprint "def:I.3-main-I-conclusion"
  (statement := /-- The conclusion of Main Theorem~I($n$) (p.~174) for a succession $\{f_i\}_{0\le i<r}$: the conditions (1), (2), (3) for all $i<r$ and the condition (4) for the last stage. -/)
  (latexEnv := "definition")]
def IsMainI {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {β : ℕ}
    (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) : Prop :=
  s.IsMain123 V W ∧ s.IsMain4 V W

end Hironaka.MonoidalSuccession
namespace Hironaka.MainTheorem
/-- **Main Theorem I(n)** (p. 174).  `V` are the `V_j` for `1 ≤ j ≤ β`, `V_0 = V₀` is the scheme itself
(`mainSystem`); the induced monoidal transformations are the strict transforms. -/
@[blueprint "def:I.3-main-I-statement"
  (statement := /-- \textbf{Main Theorem I($n$)} (p.~174). Let $V_0$ be an arbitrary algebraic scheme, $V_j$ ($1\le j\le\beta$) a finite number of subschemes of $V_0$, and $W$ a reduced subscheme of $V_0$ of dimension $n$ which is contained in $\bigcap_{j=1}^{\beta}V_j$. Then there exists a finite succession of monoidal transformations $\{f_i\colon V_0(i+1)\to V_0(i)\}$ with centers $B_i$ in $V_0(i)$ for $0\le i<r$, where $V_0(0)=V_0$, such that if $\{V_j(i+1)\to V_j(i)\}$ and $\{W(i+1)\to W(i)\}$ are the monoidal transformations induced by $f_i$, where $V_j(0)=V_j$ and $W(0)=W$, then (1) $B_i$ is a non-singular irreducible subscheme of $W(i)$; (2) $B_i$ does not contain any simple point of $W(i)$ at which all the $V_j(i)$ for $0\le j\le\beta$ are normally flat along $W(i)$; (3) all the $V_j(i)$ ($0\le j\le\beta$) and $W(i)$ are normally flat along $B_i$; and finally (4) $W(r)$ is non-singular and all the $V_j(r)$ for $0\le j\le\beta$ are normally flat along $W(r)$. (The induced monoidal transformations are encoded by strict transforms.) -/)
  (latexEnv := "definition")]
def I (n : ℕ) : Prop :=
  ∀ (V₀ : Scheme.{u}) [IsAlgebraicScheme V₀] (β : ℕ) (V : Fin β → Subscheme V₀) (W : Subscheme V₀),
    W.IsReduced → W.dim = (n : WithBot ℕ∞) → (∀ j, W.IsContainedIn (V j)) →
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession V₀ Y), s.IsMainI (mainSystem V) W

end Hironaka.MainTheorem
namespace Hironaka.MonoidalSuccession
/-- The properties (i)–(iv) of Main Theorem II (p. 142) of a finite succession of monoidal transformations
`{f_i : X_{i+1} → X_i}` with centers `D_i`, for the sheaves `J = J_0` and `E = E_0` and the integer `d`:

* a succession with no transformation (`r = 0`) has the property (iv): `E_0` has only normal crossings and
  `ν(J_y) < d` for every point `y` of `X`;
* otherwise, for the first transformation `f_0` with center `D_0`: (i) `D_0` is a non-singular irreducible subscheme
  (possibly empty, p. 163); (ii) `ν(J_z) ≧ d` for all `z ∈ D_0`; (iii) `E_0` has only normal crossings with `D_0`; and
  the rest of the succession has the properties for the weak transform `J_1` of `J_0` by `f_0` and the reduced
  subscheme `E_1 = red(f_0⁻¹(E_0) ∪ f_0⁻¹(D_0))`.  (The data `J_i`, `E_i` are carried along the succession, as in
  Definition 8 and in `IsMainSuccession`.) -/
def IsMainIIZero (d : ℕ) : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Subscheme X →
    Subscheme X → Prop
  | _, _, nil _, J, E => E.HasOnlyNormalCrossings ∧ ∀ y, Ideal.nu (J.stalkIdeal y) < d
  | _, _, cons B t rest, J, E =>
      B.IsCenter ∧ (∀ z ∈ B.pts, (d : ℕ∞) ≤ Ideal.nu (J.stalkIdeal z)) ∧
      E.HasOnlyNormalCrossingsWith B ∧
      rest.IsMainIIZero d (Subscheme.weakTransform t J)
        (Subscheme.totalTransform t.f (E.union B)).radical

section
variable {e : ℕ}
/-- The weak transforms `J_j(i)` of a system `(J_j)` of sheaves of ideals, carried along the succession:
`J_j(0) = J_j` and `J_j(i + 1)` is the weak transform of `J_j(i)` by `f_i`.  The value at the end of the
succession is `J_j(r)`. -/
noncomputable def weakTransformFamily : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    (Fin e → Subscheme X) → Fin e → Subscheme Y
  | _, _, nil _, J => J
  | _, _, cons _ t rest, J => rest.weakTransformFamily fun j => Subscheme.weakTransform t (J j)

/-- Property (1) of Corollary 1 (p. 143) for a succession `{f_i : X(i + 1) → X(i)}` with centers `D(i)` and the
system `J_j = J_j(0)`: every center `D(i)` is a non-singular irreducible subscheme (possibly empty, p. 163), and
for every pair `(i, j)` the order `ν(J_j(i)_y)` is a positive constant for the points `y` of `D(i)`, where
`J_j(i + 1)` is the weak transform of `J_j(i)` by `f_i`.  (The data `J_j(i)` are carried along the succession, as in
Definition 8.) -/
def IsTrivializingSteps : {X Y : Scheme.{u}} → MonoidalSuccession X Y → (Fin e → Subscheme X) → Prop
  | _, _, nil _, _ => True
  | _, _, cons B t rest, J =>
      B.IsCenter ∧ (∀ j, ∃ c : ℕ, 0 < c ∧ ∀ y ∈ B.pts, Ideal.nu ((J j).stalkIdeal y) = c) ∧
      rest.IsTrivializingSteps fun j => Subscheme.weakTransform t (J j)

end
section
variable {X Y : Scheme.{u}} {e : ℕ}
/-- The properties (1) and (2) of Corollary 1 (p. 143): (1) is `IsTrivializingSteps`, and (2) says that for every
point `x` of `X(r)` we have `J_j(r)_x = O_{X(r),x}` for at least one `j`. -/
def IsTrivializing (s : MonoidalSuccession X Y) (J : Fin e → Subscheme X) : Prop :=
  s.IsTrivializingSteps J ∧ ∀ x : Y, ∃ j, (s.weakTransformFamily J j).stalkIdeal x = ⊤

end
/-- The strong form of Main Theorem I (pp. 132-133) for a succession `{f_i : X_{i+1} → X_i}` with centers `D_i`:
(a) `D_i` is non-singular, (b) `D_i` does not contain any simple point of `X_i`, (c) `X_i` is normally flat along `D_i`
(`X_i` is the subscheme `⊥` of itself), for `0 ≦ i < r`, and `X̃ = X_r` is non-singular. -/
def IsStrongResolution : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, _, nil X => X.IsNonsingular
  | _, _, @cons X B _ _ rest =>
      B.IsNonsingular ∧ (∀ x ∈ B.pts, ¬ X.IsSimpleAt x) ∧
        (∀ x ∈ B.pts, Subscheme.IsNormallyFlatAlongAt' (⊥ : Subscheme X) B x) ∧ rest.IsStrongResolution

/-- Main Theorem I* (p. 138) for a succession `{f_i : X_{i+1} → X_i}` with centers `D_i`: (a) `D_i` is non-singular;
(b) every point of `D_i` is either a multiple point of `red(X_i)`, or such that `X_i` is not normally flat along
`red(X_i)` at the point (the printed `X_r` is a misprint for `X_i`); (c) `X_i` is normally flat along `D_i`; and (d)
`red(X_r)` is non-singular and `X_r` is normally flat along `red(X_r)`. -/
def IsMainIStar : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, _, nil X =>
      (Subscheme.red (⊥ : Subscheme X)).IsNonsingular ∧
        ∀ x ∈ (Subscheme.red (⊥ : Subscheme X)).pts,
          Subscheme.IsNormallyFlatAlongAt' (⊥ : Subscheme X) (Subscheme.red (⊥ : Subscheme X)) x
  | _, _, @cons X B _ _ rest =>
      B.IsNonsingular ∧
        (∀ x ∈ B.pts, ¬ (Subscheme.red (⊥ : Subscheme X)).IsSimpleAt x ∨
          ¬ Subscheme.IsNormallyFlatAlongAt' (⊥ : Subscheme X) (Subscheme.red (⊥ : Subscheme X)) x) ∧
        (∀ x ∈ B.pts, Subscheme.IsNormallyFlatAlongAt' (⊥ : Subscheme X) B x) ∧ rest.IsMainIStar

section
variable {X Y Z : Scheme.{u}}
/-- The centers `D_i` of a succession are non-singular and (ii) of Corollary 3 (p. 146): `D_i` is contained in
`f̄_i⁻¹(W)`, where `f̄_i` is the composition of the `f_j`, `0 ≦ j < i`.  The total transforms are carried along the
succession: `W_0 = W`, `W_{i+1} = f_i⁻¹(W_i)`, which is `f̄_{i+1}⁻¹(W)` (`Subscheme.totalTransform_comp`). -/
def HasNonsingularCentersIn : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Subscheme X → Prop
  | _, _, nil _, _ => True
  | _, _, cons B t rest, W => B.IsNonsingular ∧ B.IsContainedIn W ∧
      rest.HasNonsingularCentersIn (Subscheme.totalTransform t.f W)

/-- The conclusions of Corollary 3 (p. 146) except (i): non-singular centers `D_i` with (ii) `D_i ⊆ f̄_i⁻¹(W)`, and
(iii) the associated reduced scheme `red(f̄_r⁻¹(W))` is defined by an invertible sheaf of ideals on `X_r` and has only
normal crossings.  ((i), the non-singularity of `X_r`, is stated separately.) -/
def IsBoundarySimplification (s : MonoidalSuccession X Y) (W : Subscheme X) : Prop :=
  s.HasNonsingularCentersIn W ∧ (Subscheme.red (s.totalTransform W)).IsInvertibleIdeal ∧
    (Subscheme.red (s.totalTransform W)).HasOnlyNormalCrossings

end
end Hironaka.MonoidalSuccession
namespace AlgebraicGeometry.Scheme
section
variable {X X' X'' Y Z : Scheme.{u}}
/-- The hypothesis of the composition of p. 139 on the first factor `a : X' ⟶ X`: the inverse image of every open dense
subset of `X` is dense in `X'`.

Encoding: in the paper the condition is "`f⁻¹(V)` is open and dense for every open dense subset `V`"; the openness is
automatic here (`a` is continuous). -/
@[blueprint "def:0.5-preimage-dense"
  (statement := /-- A morphism $a\colon X'\to X$ \emph{has dense preimages} if $a^{-1}(V)$ is dense in $X'$ for every
    open dense subset $V$ of $X$. This is the hypothesis ``$f^{-1}(V)$ is open and dense for every open dense subset
    $V$'' of the composition of rational applications (p.~139). Formalization note (encoding): openness is automatic;
    Mathlib's composition of rational maps asks only that the first factor be dominant and the source irreducible, which
    is weaker on a reducible source. -/)
  (latexEnv := "definition")]
def Hom.PreimageDense (a : X' ⟶ X) : Prop :=
  ∀ V : X.Opens, Dense (V : Set X) → Dense ((a ⁻¹ᵁ V : X'.Opens) : Set X')

end
end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.Hom.PreimageDense
section
variable {X X' X'' Y Z : Scheme.{u}}
/-- The identity has dense preimages. -/
theorem id (X : Scheme.{u}) : (𝟙 X : X ⟶ X).PreimageDense := fun V hV => by simpa using hV

end
end AlgebraicGeometry.Scheme.Hom.PreimageDense
namespace AlgebraicGeometry.Scheme.PartialMap
section
variable {X X' X'' Y Z : Scheme.{u}}
/-- The composition `g ∘ a` of a partial map `g : X ⤏ Y` with a morphism `a : X' ⟶ X` with dense preimages: the
domain is `a⁻¹(g.domain)` (dense because `a` has dense preimages). -/
noncomputable def precomp (g : X.PartialMap Y) (a : X' ⟶ X) (ha : a.PreimageDense) : X'.PartialMap Y where
  domain := a ⁻¹ᵁ g.domain
  dense_domain := ha _ g.dense_domain
  hom := (a ∣_ g.domain) ≫ g.hom

@[simp] theorem precomp_domain (g : X.PartialMap Y) (a : X' ⟶ X) (ha : a.PreimageDense) :
    (g.precomp a ha).domain = a ⁻¹ᵁ g.domain := rfl

@[simp] theorem precomp_hom (g : X.PartialMap Y) (a : X' ⟶ X) (ha : a.PreimageDense) :
    (g.precomp a ha).hom = (a ∣_ g.domain) ≫ g.hom := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Precomposition commutes with restriction of the partial map to a smaller dense open set. -/
theorem precomp_restrict (g : X.PartialMap Y) (a : X' ⟶ X) (ha : a.PreimageDense) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ g.domain) :
    (g.restrict U hU hU').precomp a ha =
      (g.precomp a ha).restrict (a ⁻¹ᵁ U) (ha U hU) (a.preimage_mono hU') := by
  refine PartialMap.ext _ _ rfl ?_
  simp [morphismRestrict_homOfLE_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Precomposition respects the equivalence of partial maps. -/
theorem precomp_equiv {g₁ g₂ : X.PartialMap Y} (h : g₁.equiv g₂) (a : X' ⟶ X) (ha : a.PreimageDense) :
    (g₁.precomp a ha).equiv (g₂.precomp a ha) := by
  obtain ⟨W, hW, hW₁, hW₂, e⟩ := h
  have e' : g₁.restrict W hW hW₁ = g₂.restrict W hW hW₂ :=
    PartialMap.ext _ _ rfl (by simpa [Scheme.isoOfEq_hom] using e)
  have := congrArg (fun g => PartialMap.precomp g a ha) e'
  simp only [precomp_restrict] at this
  exact equiv_of_restrict_eq _ _ this

end
end AlgebraicGeometry.Scheme.PartialMap
namespace AlgebraicGeometry.Scheme
section
variable {X X' X'' Y Z : Scheme.{u}}
/-- The composition `f ∘ a` of a rational map `f : X ⤏ Y` with a morphism `a : X' ⟶ X` having dense preimages: the
class of the composites `g ∘ a`, `g` a representative of `f` (p. 139: "the class of composed morphisms of those in `f`
and those in `g`", with the first factor the morphism `a`).

Encoding: this is the composition of p. 139 for a first factor which is a morphism (the only case used: `h`, a
monoidal transformation, p. 139, and the composites of such, p. 140). -/
@[blueprint "def:0.5-rational-precomposition"
  (statement := /-- Let $f\colon X\dashrightarrow Y$ be a rational application and $a\colon X'\to X$ a morphism with
    dense preimages. The \emph{composition} $f\circ a$ is the rational application of $X'$ to $Y$ which is the class of
    the composed morphisms $g\circ a$, where $g$ runs over the morphisms of the class $f$ (p.~139). It is well
    defined because $a^{-1}$ of a dense open set is a dense open set. -/)
  (latexEnv := "definition")]
noncomputable def RationalMap.precomp (f : X ⤏ Y) (a : X' ⟶ X) (ha : a.PreimageDense) : X' ⤏ Y :=
  Quotient.liftOn f (fun g => (g.precomp a ha).toRationalMap) fun _ _ h =>
    PartialMap.toRationalMap_eq_iff.mpr (PartialMap.precomp_equiv h a ha)

end
end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.RationalMap
section
variable {X Y : Scheme.{u}}
/-- "The rational application `f` is a morphism": the domain of definition contains all the points of `X` and there
is a unique morphism `X → Y` belonging to the class (p. 139).

> For instance, we say that *the rational application `f` is a morphism*, meaning that the domain of definition `W` of
> `f` contains all the points of `X` and there exists a unique morphism `f : X → Y` belonging to the class.  (p. 139)

Encoding: `φ.toRationalMap` is the class of the morphism `φ` (on the dense open set `⊤`). -/
@[blueprint "def:0.5-is-morphism"
  (statement := /-- The rational application $f$ of $X$ to $Y$ \emph{is a morphism} if its domain of definition $W$
    contains all the points of $X$ and there exists a unique morphism $X\to Y$ belonging to the class $f$. (p.~139.)
    -/)
  (latexEnv := "definition")]
def IsMorphism (f : X ⤏ Y) : Prop :=
  f.domain = ⊤ ∧ ∃! φ : X ⟶ Y, φ.toRationalMap = f

/-- A rational application `f` of `X` to `Y` is *proper* (p. 139): there is an algebraic subscheme `T` of the product
`X × Y` over the base `S` and a morphism `g : X | U → Y` belonging to the class `f` (`U` open dense) such that the two
projections induce proper morphisms of `T`, the first projection induces an isomorphism of `T | p₁⁻¹(U)` to `X | U`,
and the second projection induces the composition of this isomorphism and `g`.

> We say that a rational application `f` of `X` to `Y` is *proper*, if there exists an algebraic subscheme (or analytic
> subspace) `T` of the product `X × Y` (either in `Al/B` or in `An/K`) and also a morphism `f : X | U → Y` belonging to
> the class `f` such that the projections `p₁` and `p₂` of `X × Y` to `X` and `Y` induce proper morphisms of `T`, and
> that `p₁` induces an isomorphism of `T | p₁⁻¹(U)` to `X | U` while `p₂` induces the composition of this isomorphism and
> the morphism `f : X | U → Y`.  (pp. 138–139)

Encoding: the subscheme `T` is a closed subscheme of the fibre product `X ×_S Y` (`Subscheme`); the restriction of `p₁`
to the open set `p₁⁻¹(U)` of `T` is `(T.ι ≫ p₁) ∣_ U`; the representative is a partial map `g` with dense domain `U`. -/
@[blueprint "def:0.5-proper-application"
  (statement := /-- A rational application $f$ of $X$ to $Y$ is \emph{proper} if there exists an algebraic subscheme
    $T$ of the product $X\times Y$ and a morphism $X|U\to Y$ belonging to the class $f$ such that the projections
    $p_1,p_2$ induce proper morphisms of $T$, $p_1$ induces an isomorphism of $T|p_1^{-1}(U)$ to $X|U$ and $p_2$ induces
    the composition of this isomorphism and the morphism $X|U\to Y$. (pp.~138--139.) Formalization note (encoding): $T$
    is a closed subscheme of the fibre product over the base. -/)
  (latexEnv := "definition")]
def IsProperApplication {S : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⤏ Y) : Prop :=
  ∃ (g : X.PartialMap Y) (T : Hironaka.Subscheme (pullback pX pY)),
    g.toRationalMap = f ∧
    IsProper (T.ι ≫ pullback.fst pX pY) ∧ IsProper (T.ι ≫ pullback.snd pX pY) ∧
    IsIso ((T.ι ≫ pullback.fst pX pY) ∣_ g.domain) ∧
    ((T.ι ≫ pullback.fst pX pY) ∣_ g.domain) ≫ g.hom =
      ((T.ι ≫ pullback.fst pX pY) ⁻¹ᵁ g.domain).ι ≫ T.ι ≫ pullback.snd pX pY

end
end AlgebraicGeometry.Scheme.RationalMap
namespace Hironaka
/-- The cited result `Hironaka.IsRegularLocalRing.uniqueFactorizationMonoid` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResultsCh0`. -/
class _root_.Hironaka.Cited.IsRegularLocalRingUniqueFactorizationMonoid : Prop where
  /-- The statement of `Hironaka.IsRegularLocalRing.uniqueFactorizationMonoid`. -/
  uniqueFactorizationMonoid : ∀ (R : Type u) [CommRing R]
      [IsRegularLocalRing R] [IsDomain R],
      UniqueFactorizationMonoid R

end Hironaka
namespace Hironaka.Scheme.Modules
section
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}}
/-- `c` is a frame of the `X`-module `M` over the open `U`: for every open `V ≤ U` the map
`Γ(X, V)^ι → Γ(M, V)`, `a ↦ ∑ aᵢ • cᵢ|_V` is bijective. -/
structure IsFrame (M : X.Modules) (U : X.Opens) {ι : Type u} [Fintype ι] (c : ι → Γ(M, U)) :
    Prop where
  bijective : ∀ (V : X.Opens) (h : V ≤ U),
    Function.Bijective fun a : ι → Γ(X, V) => ∑ i, a i • M.presheaf.map (homOfLE h).op (c i)

end
end Hironaka.Scheme.Modules
namespace Hironaka
section
variable {X : Scheme.{u}}
/-- A sheaf of ideals `K` is *not divisible by any invertible sheaf of ideals (except `O_X`)* (p. 141).

Encoding: "`K` is divisible by `Q`" (`K = Q · K''`) is encoded as the containment `K ⊆ Q` of the stalks.  For an invertible
`Q`, whose stalk at each point is generated by a non-zero-divisor, the two agree (cancel the generator); `Q = O_X` is
`∀ x, Q.stalkIdeal x = ⊤`. -/
@[blueprint "def:0.5-primitive-ideal"
  (statement := /-- A sheaf of ideals $K$ on $X$ is \emph{not divisible by any invertible sheaf of ideals (except
    $\mathcal O_X$)} if every invertible sheaf of ideals $Q$ with $K\subseteq Q$ is $\mathcal O_X$. (p.~141.)
    Formalization note (encoding): divisibility $K=QK''$ is encoded as the containment $K\subseteq Q$ on stalks; they agree
    because the stalks of an invertible sheaf of ideals are generated by non-zero-divisors. -/)
  (latexEnv := "definition")]
def Subscheme.IsPrimitive (K : Subscheme X) : Prop :=
  ∀ Q : Subscheme X, Q.IsInvertibleIdeal → (∀ x, K.stalkIdeal x ≤ Q.stalkIdeal x) →
    ∀ x, Q.stalkIdeal x = ⊤

end
end Hironaka
namespace Hironaka.RationalApplication
/-- The cited result `Hironaka.RationalApplication.exists_finite_system_domain_precomp_eq` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResultsCh0`. -/
class _root_.Hironaka.Cited.RationalApplicationExistsFiniteSystemDomainPrecompEq : Prop where
  /-- The statement of `Hironaka.RationalApplication.exists_finite_system_domain_precomp_eq`. -/
  exists_finite_system_domain_precomp_eq : ∀ {B : Type u} [Field B] [CharZero B] {X Y : Scheme.{u}}
      (pX : X ⟶ Spec (CommRingCat.of B)) (pY : Y ⟶ Spec (CommRingCat.of B))
      [LocallyOfFiniteType pX] [QuasiCompact pX] [IsSeparated pX]
      [LocallyOfFiniteType pY] [QuasiCompact pY] [IsSeparated pY]
      (hX : X.IsNonsingular) (f : X ⤏ Y) (hf : f.IsProperApplication pX pY),
      ∃ (d : ℕ) (J : Fin d → Subscheme X), (∀ i x, (J i).stalkIdeal x ≠ ⊥) ∧
        ∀ (X' : Scheme.{u}) (pX' : X' ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType pX'] [QuasiCompact pX']
          [IsSeparated pX'] (_ : X'.IsNonsingular) (h : X' ⟶ X) (_ : h ≫ pX = pX') (hh : h.PreimageDense)
          (P J' : Fin d → Subscheme X'),
          (∀ i, (P i).IsInvertibleIdeal ∧ (∀ x, (J' i).stalkIdeal x ≠ ⊥) ∧ Subscheme.IsPrimitive (J' i) ∧
            ∀ x, (Subscheme.totalTransform h (J i)).stalkIdeal x = (P i).stalkIdeal x * (J' i).stalkIdeal x) →
          ((f.precomp h hh).domain : Set X') = {x | ∃ i, (J' i).stalkIdeal x = ⊤}

end Hironaka.RationalApplication
namespace Hironaka.MonoidalSuccession
section
variable {X Y Z : Scheme.{u}}
/-- All centers of the succession are non-singular. -/
def HasNonsingularCenters : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, _, nil _ => True
  | _, _, cons B _ rest => B.IsNonsingular ∧ rest.HasNonsingularCenters

end
/-- Every center of the succession is nowhere dense in its stage (the hypothesis of p. 144 under which the
function field isomorphism `θ'` exists).

> If `(X, θ)` is as above, and if `f : X' → X` is a monoidal transformation with center nowhere dense in `X`, we have a
> unique `B`-isomorphism `θ'` of `L` to the function field of `X'` such that `θ ∘ θ'⁻¹` is induced by `f`.  (p. 144)

Encoding: "center nowhere dense in `X`" is `interior D.pts = ∅`, at each stage of the succession; for an integral stage
it is equivalent to the center missing the generic point (`Subscheme.interior_pts_eq_empty_iff`). -/
@[blueprint "def:0.5-nowhere-dense-centers"
  (statement := /-- A finite succession of monoidal transformations has \emph{nowhere dense centers} if the center of
    each monoidal transformation is nowhere dense in its source scheme. (Hypothesis under which the isomorphism
    $\theta'$ of $\mathbf L$ to the function field of $X'$ exists, p.~144.) Formalization note (encoding): the
    interior of the set of points of each center is empty. -/)
  (latexEnv := "definition")]
def NowhereDenseCenters : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, _, nil _ => True
  | _, _, cons D _ rest => interior D.pts = ∅ ∧ rest.NowhereDenseCenters

end Hironaka.MonoidalSuccession
namespace Hironaka
section
open Scheme
variable {X Y : Scheme.{u}}
/-- The canonical morphism `Spec 𝒪_{X,x} ⟶ X` followed by a morphism to `Spec B` is `Spec` of the structure map of the
stalk. -/
theorem fromSpecStalk_comp_eq_specMap {B : Type u} [CommRing B] (x : X) (p : X ⟶ Spec (CommRingCat.of B)) :
    X.fromSpecStalk x ≫ p = Spec.map (CommRingCat.ofHom
      ((X.presheaf.germ ⊤ x trivial).hom.comp
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom))) := by
  have key : X.fromSpecStalk x ≫ p ≫ (Spec (CommRingCat.of B)).toSpecΓ =
      Spec.map (p.appTop ≫ X.presheaf.germ ⊤ x trivial) := by
    rw [Scheme.toSpecΓ_naturality, Scheme.fromSpecStalk_toSpecΓ_assoc, ← Spec.map_comp]
  rw [← cancel_mono (Spec (CommRingCat.of B)).toSpecΓ, Category.assoc, key, ← SpecMap_ΓSpecIso_hom,
    ← Spec.map_comp]
  congr 1
  ext
  simp

end
section
open Scheme
/-- A pair `(X, θ)` of a reduced and irreducible algebraic `B`-scheme `X` and a `B`-isomorphism `θ` of `L` to the function
field of `X` (p. 144).

Encoding: "algebraic `B`-scheme" is, as for the Corollary of p. 132, a scheme `X` with a morphism `p : X ⟶ Spec B` that is
locally of finite type, quasi-compact and separated (p. 118–119: a scheme is separated); "reduced and irreducible" is
`IsIntegral X`; "`B`-isomorphism" is a ring isomorphism `θ : L ≃+* K(X)` with `θ(b) = functionFieldAlgebraMap p b`.  That `L`
is finitely generated over `B` is not assumed (it follows from the existence of a pair, and no proof uses it). -/
@[blueprint "def:0.5-pair"
  (statement := /-- Let $\mathbf B$ be a field of characteristic zero and $\mathbf L$ a field containing $\mathbf B$ and
    finitely generated over $\mathbf B$. A \emph{pair} $(X,\theta)$ consists of a reduced and irreducible algebraic
    $\mathbf B$-scheme $X$ and a $\mathbf B$-isomorphism $\theta$ of $\mathbf L$ to the function field of $X$. (p.~144.)
    Formalization note (encoding): an algebraic $\mathbf B$-scheme is a scheme with a morphism to
    $\operatorname{Spec}\mathbf B$ that is locally of finite type, quasi-compact and separated; finite generation of
    $\mathbf L$ is not assumed. -/)
  (latexEnv := "definition")]
structure FunctionFieldPair (B L : Type u) [Field B] [Field L] [Algebra B L] where
  /-- The scheme `X`. -/
  X : Scheme.{u}
  /-- The structure morphism `X ⟶ Spec B`. -/
  p : X ⟶ Spec (CommRingCat.of B)
  [isIntegral : IsIntegral X]
  [locallyOfFiniteType : LocallyOfFiniteType p]
  [quasiCompact : QuasiCompact p]
  [isSeparated : IsSeparated p]
  /-- The `B`-isomorphism `θ` of `L` to the function field of `X`. -/
  θ : L ≃+* X.functionField
  θ_algebraMap : ∀ b : B, θ (algebraMap B L b) = functionFieldAlgebraMap p b

end
end Hironaka
namespace Hironaka.FunctionFieldPair
section
open Scheme
variable {B L : Type u} [Field B] [Field L] [Algebra B L]
attribute [instance] isIntegral locallyOfFiniteType quasiCompact isSeparated

/-- The isomorphism `θ₁∘θ₂⁻¹ : K(X₂) → K(X₁)` of the function fields of two pairs, as a morphism of commutative rings. -/
noncomputable def thetaHom (P Q : FunctionFieldPair B L) : Q.X.functionField ⟶ P.X.functionField :=
  CommRingCat.ofHom (Q.θ.symm.trans P.θ).toRingHom

theorem thetaHom_apply (P Q : FunctionFieldPair B L) (x : Q.X.functionField) :
    P.thetaHom Q x = P.θ (Q.θ.symm x) := rfl

/-- The morphism `Spec K(X₁) ⟶ X₂` of the rational application of `(X₁, θ₁)` to `(X₂, θ₂)`: `Spec` of the isomorphism
`θ₁∘θ₂⁻¹ : K(X₂) → K(X₁)` followed by `Spec K(X₂) ⟶ X₂`. -/
noncomputable def ratFn (P Q : FunctionFieldPair B L) : Spec P.X.functionField ⟶ Q.X :=
  Spec.map (P.thetaHom Q) ≫ Q.X.fromSpecStalk (genericPoint Q.X)

/-- `ratFn` is a morphism over `Spec B`. -/
theorem ratFn_comp (P Q : FunctionFieldPair B L) :
    P.ratFn Q ≫ Q.p = P.X.fromSpecStalk (genericPoint P.X) ≫ P.p := by
  rw [ratFn, Category.assoc, fromSpecStalk_comp_eq_specMap, fromSpecStalk_comp_eq_specMap, ← Spec.map_comp]
  congr 1
  ext b
  have h1 := P.θ_algebraMap b
  have h2 := Q.θ_algebraMap b
  simp only [functionFieldAlgebraMap] at h1 h2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  rw [thetaHom_apply]
  have h2' := (RingEquiv.symm_apply_eq Q.θ).mpr h2.symm
  exact (congrArg P.θ h2').trans h1

/-- The rational application of `(X₁, θ₁)` to `(X₂, θ₂)` (p. 144): the rational map `X₁ ⤏ X₂` which induces the
isomorphism `θ₁∘θ₂⁻¹` of the function field of `X₂` to that of `X₁`. -/
@[blueprint "def:0.5-rational-application-of-pairs"
  (statement := /-- If $(X_1,\theta_1)$ and $(X_2,\theta_2)$ are two pairs, then there exists a unique rational
    application $f$ of $X_1$ to $X_2$ which induces the isomorphism $\theta_1\circ\theta_2^{-1}$ of the function field of
    $X_2$ to that of $X_1$. We call $f$ the rational application of $(X_1,\theta_1)$ to $(X_2,\theta_2)$. (p.~144.)
    Formalization note (encoding): Mathlib's rational maps; the rational application is constructed from the morphism
    $\operatorname{Spec}K(X_1)\to X_2$ induced by $\theta_1\circ\theta_2^{-1}$, and unique among the rational maps
    inducing it. -/)
  (latexEnv := "definition")]
noncomputable def ratApp (P Q : FunctionFieldPair B L) : P.X ⤏ Q.X :=
  RationalMap.ofFunctionField P.p Q.p (P.ratFn Q) (P.ratFn_comp Q)

/-- `(X₁, θ₁)` *dominates* `(X₂, θ₂)` if the rational application of `(X₁, θ₁)` to `(X₂, θ₂)` is a morphism (p. 144). -/
@[blueprint "def:0.5-dominates"
  (statement := /-- If the rational application $f$ of $(X_1,\theta_1)$ to $(X_2,\theta_2)$ is a morphism, then we say
    that $(X_1,\theta_1)$ \emph{dominates} $(X_2,\theta_2)$. (p.~144.) -/)
  (latexEnv := "definition")]
def Dominates (P Q : FunctionFieldPair B L) : Prop := (P.ratApp Q).IsMorphism

/-- The class `𝔐(L/B)` (p. 144): the pairs `(X, θ)` with `X` proper, i.e. the structure morphism `X ⟶ Spec B` is proper. -/
@[blueprint "def:0.5-class-U"
  (statement := /-- Let $\mathfrak M(\mathbf L/\mathbf B)$ denote the class of those pairs $(X,\theta)$ with proper $X$
    (i.e., the structural morphisms of $X$ to $\operatorname{Spec}(\mathbf B)$ are proper). (p.~144.) -/)
  (latexEnv := "definition")]
def IsProper (P : FunctionFieldPair B L) : Prop := AlgebraicGeometry.IsProper P.p

/-- `(X', θ')` is obtained from `(X, θ)` by the succession `s` of monoidal transformations with non-singular, nowhere dense
centers (p. 144, (1): "obtain `(X'₁, θ'₁)` from `(X₁, θ₁)` by means of a finite succession of monoidal transformations with
non-singular centers"): the centers are nowhere dense (so that `θ'` exists), non-singular, the structure morphism of `X'` is
the composite, and the rational application of `(X', θ')` to `(X, θ)` is the composite morphism ("`θ∘θ'⁻¹` is induced by
`f`"). -/
@[blueprint "def:0.5-obtained-by"
  (statement := /-- A pair $(X',\theta')$ is \emph{obtained from} $(X,\theta)$ by a finite succession of monoidal
    transformations with non-singular centers if the centers are nowhere dense, non-singular, and the rational
    application of $(X',\theta')$ to $(X,\theta)$ is the morphism composed of the monoidal transformations
    (i.e.\ $\theta\circ\theta'^{-1}$ is induced by it; p.~144). Formalization note (encoding): the structure morphism
    of $X'$ is the composite with that of $X$. -/)
  (latexEnv := "definition")]
def IsObtainedBy (P Q : FunctionFieldPair B L) (s : MonoidalSuccession P.X Q.X) : Prop :=
  s.NowhereDenseCenters ∧ s.HasNonsingularCenters ∧ Q.p = s.composite ≫ P.p ∧
    Q.ratApp P = s.composite.toRationalMap

end
section
variable {B L : Type u} [Field B] [Field L] [Algebra B L]
/-- The cited result `Hironaka.FunctionFieldPair.exists_projective_dominating` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResultsCh0`. -/
class _root_.Hironaka.Cited.FunctionFieldPairExistsProjectiveDominating : Prop where
  /-- The statement of `Hironaka.FunctionFieldPair.exists_projective_dominating`. -/
  exists_projective_dominating : ∀ {B L : Type u} [Field B] [Field L] [Algebra B L],
      ∀ (P₁ : FunctionFieldPair B L) (_hP₁ : P₁.IsProper)
      (_hns : P₁.X.IsNonsingular),
      ∃ P₂ : FunctionFieldPair B L, P₂.IsProper ∧ IsProjectiveOver P₂.X P₂.p ∧ P₂.Dominates P₁

/-- The cited result `Hironaka.FunctionFieldPair.isProjectiveOver_of_isObtainedBy_dominates` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResultsCh0`. -/
class _root_.Hironaka.Cited.FunctionFieldPairIsProjectiveOverOfIsObtainedByDominates : Prop where
  /-- The statement of `Hironaka.FunctionFieldPair.isProjectiveOver_of_isObtainedBy_dominates`. -/
  isProjectiveOver_of_isObtainedBy_dominates : ∀ {B L : Type u} [Field B] [Field L] [Algebra B L],
      ∀ {P₁ P₂ P' : FunctionFieldPair B L}
      {s : MonoidalSuccession P₁.X P'.X} (_hP₁ : P₁.IsProper) (_hns : P₁.X.IsNonsingular)
      (_hs : P₁.IsObtainedBy P' s) (_hP₂ : IsProjectiveOver P₂.X P₂.p) (_h₂₁ : P₂.Dominates P₁)
      (_h'₂ : P'.Dominates P₂),
      IsProjectiveOver P'.X P'.p

end
end Hironaka.FunctionFieldPair
namespace AlgebraicGeometry.Scheme
section
variable {X Y Z : Scheme.{u}}
/-- The structure sheaf `O_X` as an object of the category of `O_X`-modules. -/
noncomputable abbrev structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The comorphism `O_Y → f_*O_X` of a morphism of schemes `f : X ⟶ Y`. -/
noncomputable def Hom.structureUnit (f : X ⟶ Y) :
    Y.structureModule ⟶ (Modules.pushforward f).obj X.structureModule :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

end
end AlgebraicGeometry.Scheme
namespace Hironaka
section
variable {X Y Z : Scheme.{u}}
/-- The higher direct image `Rⁱf_*(O_X)` (p. 145), as the `i`-th right derived functor of the direct image functor
`f_* : X.Modules ⥤ Y.Modules`, evaluated at `O_X`. -/
noncomputable def higherDirectImageStructure (f : X ⟶ Y) (i : ℕ) : Y.Modules :=
  ((Scheme.Modules.pushforward f).rightDerived i).obj X.structureModule

end
section
variable {X : Scheme.{u}}
/-- The cited result `Hironaka.MonoidalTransformation.higherDirectImage_structureSheaf` as a hypothesis (its docstring gives the source). It is a field of
`Hironaka.HironakaCitedResultsCh0`. -/
class _root_.Hironaka.Cited.MonoidalTransformationHigherDirectImageStructureSheaf : Prop where
  /-- The statement of `Hironaka.MonoidalTransformation.higherDirectImage_structureSheaf`. -/
  higherDirectImage_structureSheaf : ∀ {X : Scheme.{u}},
      ∀ {B : Type u} [Field B] [CharZero B]
      (p : X ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType p] [QuasiCompact p] (hX : X.IsNonsingular) {D : Subscheme X} (hD : D.IsNonsingular) (hnd : interior D.pts = ∅)
      (t : MonoidalTransformation X D),
      (∀ i, 0 < i → IsZero (higherDirectImageStructure t.f i)) ∧ IsIso t.f.structureUnit

end
section
variable {X Y : Scheme.{u}}
/-- The comorphism followed by the canonical map `f_*O_X → R⁰f_*O_X`: `O_Y → R⁰f_*O_X`. -/
noncomputable def structureUnitR0 (f : X ⟶ Y) :
    Y.structureModule ⟶ higherDirectImageStructure f 0 :=
  f.structureUnit ≫ (Scheme.Modules.pushforward f).toRightDerivedZero.app X.structureModule

end
/-- The hypotheses used by Ch. 0 §5: those of `HironakaCitedResults`, the cited unique factorization of regular
local rings, and the four statements that the paper uses without proof or citation. -/
class HironakaCitedResultsCh0 : Prop extends
    Hironaka.HironakaCitedResults.{u},
    Hironaka.Cited.IsRegularLocalRingUniqueFactorizationMonoid.{u},
    Hironaka.Cited.RationalApplicationExistsFiniteSystemDomainPrecompEq.{u},
    Hironaka.Cited.MonoidalTransformationHigherDirectImageStructureSheaf.{u},
    Hironaka.Cited.FunctionFieldPairExistsProjectiveDominating.{u},
    Hironaka.Cited.FunctionFieldPairIsProjectiveOverOfIsObtainedByDominates.{u}

end Hironaka
namespace Hironaka.RationalApplication
section
variable {X Y : Scheme.{u}}
/-- The conclusions (i), (ii), (iii) of Question (E) (p. 140) for a succession of monoidal transformations
`X₀ ← X₁ ← ⋯` (`MonoidalSuccession X₀ X_r`) and the rational application `f ∘ a`, where `a : X₀ ⟶ X` is the composite of the
transformations done so far (`a = h_0 ∘ ⋯ ∘ h_{i-1}`, so `f ∘ a = f_i`), `S` is the set `S_i`.

The constructor `cons` is one step `h_i` with center `D_i`: `D_i` is irreducible (or empty, the agreement of p. 163) and
has no multiple points in a neighborhood of `S_i` (`hirr`, `hsimple`); every point of `D_i` is a point of indeterminacy of
`f_i` (`hind`); `a` and `t.f ≫ a` have dense preimages, so that `f_i` and `f_{i+1} = f_i ∘ h_i` are defined (p. 139;
`ha'`); the rest of the succession starts from `S_{i+1} = h_i⁻¹(S_i)`.  The constructor `nil` is (iii): the domain of
definition of `f_r` contains `S_r`.

Encoding: "no multiple points within a neighborhood of `S_i`" is "`D_i` has a simple point at every point of `D_i` in an open
set containing `S_i`" (`Subscheme.IsSimpleAt`, p. 163: a point is simple iff the local ring is regular). -/
@[blueprint "def:0.5-eliminates-indeterminacy"
  (statement := /-- Let $f\colon X\dashrightarrow Y$ be a rational application. A succession of monoidal transformations
    $h_i\colon X_{i+1}\to X_i$ with centers $D_i$ ($0\le i<r$, $X_0=X$) \emph{eliminates the points of indeterminacy of
    $f$ on $S_0$} if, with $S_{i+1}=h_i^{-1}(S_i)$: (i) $D_i$ is irreducible and has no multiple points within a
    neighbourhood of $S_i$ in $X_i$; (ii) if $f_i$ denotes the composition of $f$ and those $h_j$ with $j<i$, every point
    of $D_i$ is a point of indeterminacy of $f_i$; and (iii) the domain of the definition of $f_r$ contains $S_r$.
    (p.~140.) Formalization note (encoding): the empty subscheme counts as irreducible (the agreement of p.~163); the
    compositions $f_i$ exist because the morphisms $h_0\circ\dots\circ h_{i-1}$ have dense preimages (p.~139). -/)
  (latexEnv := "definition")]
inductive EliminatesIndeterminacy (f : X ⤏ Y) :
    ∀ {X₀ X₁ : Scheme.{u}}, (a : X₀ ⟶ X) → a.PreimageDense → Set X₀ → MonoidalSuccession X₀ X₁ → Prop
  | nil {X₀ : Scheme.{u}} (a : X₀ ⟶ X) (ha : a.PreimageDense) (S : Set X₀)
      (hS : ∀ x ∈ S, x ∈ (f.precomp a ha).domain) :
      EliminatesIndeterminacy f a ha S (.nil X₀)
  | cons {X₀ X₁ : Scheme.{u}} (a : X₀ ⟶ X) (ha : a.PreimageDense) (S : Set X₀) (D : Subscheme X₀)
      (t : MonoidalTransformation X₀ D) (rest : MonoidalSuccession t.X' X₁)
      (hirr : D = Subscheme.empty ∨ D.IsIrreducible)
      (hsimple : ∃ W : X₀.Opens, S ⊆ W ∧ ∀ y ∈ D.pts, y ∈ W → D.IsSimpleAt y)
      (hind : ∀ y ∈ D.pts, y ∉ (f.precomp a ha).domain)
      (ha' : (t.f ≫ a).PreimageDense)
      (hrest : EliminatesIndeterminacy f (t.f ≫ a) ha' (t.f ⁻¹' S) rest) :
      EliminatesIndeterminacy f a ha S (.cons D t rest)

end
end Hironaka.RationalApplication
namespace Hironaka.Scheme.Modules
section
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}}
/-- `L` is an *invertible* sheaf of `𝒪_X`-modules: it is locally free of rank one, i.e. every point has an
open neighbourhood `U` with a one-element frame `d` of `L` over `U`. -/
def IsInvertible (L : X.Modules) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (d : Γ(L, U)), IsFrame L U (fun _ : PUnit.{u + 1} => d)

end
end Hironaka.Scheme.Modules
namespace Hironaka.MonoidalSuccession
/-- The centers of the succession are non-singular (`IsCenter`, possibly empty) and nowhere dense in the scheme
they live in ("with non-singular and nowhere dense centers", Corollary 2 of Main Theorem II, p. 145). -/
def IsNowhereDense : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, _, nil _ => True
  | _, _, cons B _ rest => B.IsCenter ∧ _root_.IsNowhereDense B.pts ∧ rest.IsNowhereDense

end Hironaka.MonoidalSuccession

end
