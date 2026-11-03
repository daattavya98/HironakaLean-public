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

/-!
# Challenge: Ch. 0 §5 of Hironaka (1964)

Corollary 2 of Main Theorem II, Question (E) and the consequences (1)–(3) of Corollary 1 (the theorems of
`comparator-ch0.json`), with `sorry` proofs, and every declaration their statements need, restated from
`Hironaka.Statements` (whose docstrings are longer and quote the paper). The hypotheses are the class
`HironakaCitedResultsCh0`.
-/

@[expose] public section

noncomputable section

universe v₁ u₁ u
open IsLocalRing CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct
namespace Hironaka
section
variable {O : Type u} [CommRing O]
/-- The `O`-module `Pᵖ/Pᵖ⁺¹`: the submodule `Pᵖ ⊆ O` modulo the preimage of `Pᵖ⁺¹`. -/
abbrev GrPiece (P : Ideal O) (p : ℕ) : Type u :=
  ↥(P ^ p) ⧸ (Submodule.comap (P ^ p).subtype (P ^ (p + 1)))
theorem grPiece_isTorsionBySet (P : Ideal O) (p : ℕ) :
    Module.IsTorsionBySet O (GrPiece P p) (P : Set O) := by
  intro m a
  induction m using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_smul, smul_eq_mul, pow_succ']
    exact Ideal.mul_mem_mul a.2 x.2
/-- The `O/P`-module structure on `GrPiece P p` (it is killed by `P`). -/
noncomputable instance GrPiece.module (P : Ideal O) (p : ℕ) : Module (O ⧸ P) (GrPiece P p) :=
  (grPiece_isTorsionBySet P p).module
end
/-- The regular locus of `Spec A`: the primes `p` of `A` with `A_p` a regular local ring. -/
def regularLocus (A : Type u) [CommRing A] : Set (PrimeSpectrum A) :=
  {p | IsRegularLocalRing (Localization.AtPrime p.asIdeal)}
/-- Cited (fn. 3, p. 116): if `R → R'` is a flat local homomorphism, `R` Noetherian local and
  `R'` regular local, then `R` is regular. -/
class _root_.Hironaka.Cited.IsRegularLocalRingOfFlatOfIsRegularLocalRing : Prop where
  isRegularLocalRing_of_flat_of_isRegularLocalRing : ∀ {R R' : Type u} [CommRing R]
      [CommRing R'] [IsLocalRing R] [IsNoetherianRing R] [Algebra R R'] [Module.Flat R R']
      [IsRegularLocalRing R'] [IsLocalHom (algebraMap R R')],
      IsRegularLocalRing R
/-- Cited (fn. 3, p. 116): a flat local homomorphism `R → R'` of Noetherian local rings induces a
  flat local homomorphism `R̂ → R̂'` compatible with it. -/
class _root_.Hironaka.Cited.ExistsFlatIsLocalHomAdicCompletionOfFlat : Prop where
  exists_flat_isLocalHom_adicCompletion_of_flat : ∀ {R R' : Type u} [CommRing R] [CommRing R']
      [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing R'] [IsNoetherianRing R'] [Algebra R R']
      [Module.Flat R R'] [IsLocalHom (algebraMap R R')],
      ∃ φ : AdicCompletion (maximalIdeal R) R →+* AdicCompletion (maximalIdeal R') R',
        (∀ x : R, φ (algebraMap R (AdicCompletion (maximalIdeal R) R) x) =
          algebraMap R' (AdicCompletion (maximalIdeal R') R') (algebraMap R R' x)) ∧
        φ.Flat ∧ IsLocalHom φ
/-- Coefficientwise application of an additive map `d : R → R` to a polynomial in `R[σ]`. -/
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
/-- The `k`-derivation of `R[σ]` applying a `k`-derivation `d` of `R` to each coefficient. -/
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
/-- The ring `k⟦t₁,…,t_n⟧[x₁,…,x_m]` (footnote 30), i.e. `MvPolynomial (Fin m) (MvPowerSeries
  (Fin n) k)`, kept as a separate `def`. -/
def PowerSeriesPolynomialRing (k : Type u) [Field k] (n m : ℕ) : Type u :=
  MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)
end Hironaka
namespace Hironaka.PowerSeriesPolynomialRing
section
variable (k : Type u) [Field k] (n m : ℕ)
/-- The `CommRing` structure of `k⟦t⟧[x]`, that of the underlying `MvPolynomial` ring. -/
instance : CommRing (PowerSeriesPolynomialRing k n m) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))
/-- The `k`-algebra structure of `k⟦t⟧[x]`, that of the underlying `MvPolynomial` ring. -/
instance : Algebra k (PowerSeriesPolynomialRing k n m) :=
  inferInstanceAs (Algebra k (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))
/-- `∂/∂t_j` on `k⟦t⟧[x]`: differentiate each power-series coefficient in `t_j`. -/
def pderivT (j : Fin n) :
    Derivation k (PowerSeriesPolynomialRing k n m) (PowerSeriesPolynomialRing k n m) :=
  mapCoeffsDerivation k (Fin m)
    (MvPowerSeries.pderiv j : Derivation k (MvPowerSeries (Fin n) k) (MvPowerSeries (Fin n) k))
/-- `∂/∂x_l` on `k⟦t⟧[x]`: the formal derivative in the polynomial variable `x_l`. -/
def pderivX (l : Fin m) :
    Derivation k (PowerSeriesPolynomialRing k n m) (PowerSeriesPolynomialRing k n m) :=
  (MvPolynomial.pderiv l : Derivation (MvPowerSeries (Fin n) k)
    (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))
    (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))).restrictScalars k
/-- The derivations `∂/∂t₁,…,∂/∂t_n, ∂/∂x₁,…,∂/∂x_m` of `k⟦t⟧[x]`, indexed by `Fin (n + m)`. -/
def pderiv (j : Fin (n + m)) :
    Derivation k (PowerSeriesPolynomialRing k n m) (PowerSeriesPolynomialRing k n m) :=
  Fin.addCases (motive := fun _ => Derivation k (PowerSeriesPolynomialRing k n m)
    (PowerSeriesPolynomialRing k n m)) (pderivT k n m) (pderivX k n m) j
end
section
variable (k : Type u) [Field k] (n m : ℕ)
variable {k n m}
/-- The jacobian matrix `(∂f_i/∂u_j)` of `f₁,…,f_r ∈ k⟦t⟧[x]` in the variables `u = (t, x)`
  (Nagata [14], p. 428). -/
def jacobian {r : ℕ} (f : Fin r → PowerSeriesPolynomialRing k n m) :
    Matrix (Fin r) (Fin (n + m)) (PowerSeriesPolynomialRing k n m) :=
  Matrix.of fun i j => pderiv k n m j (f i)
/-- Reduction modulo a prime `𝔮` of `T = k⟦t⟧[x]`: the map `T → Frac(T/𝔮)` (quotient map, then
  inclusion). -/
def residueMap (𝔮 : Ideal (PowerSeriesPolynomialRing k n m)) [𝔮.IsPrime] :
    PowerSeriesPolynomialRing k n m →+* FractionRing (PowerSeriesPolynomialRing k n m ⧸ 𝔮) :=
  (algebraMap _ _).comp (Ideal.Quotient.mk 𝔮)
end
end Hironaka.PowerSeriesPolynomialRing
namespace Hironaka
/-- Cited (Cohen; fn. 30, p. 161): a complete Noetherian local ring with residue field of
  characteristic 0 is a quotient of `k⟦t₁,…,t_n⟧`, `k` a field of characteristic 0. -/
class _root_.Hironaka.Cited.ExistsSurjectiveMvPowerSeriesOfIsAdicComplete : Prop where
  exists_surjective_mvPowerSeries_of_isAdicComplete : ∀ (S : Type u) [CommRing S]
      [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
      [CharZero (ResidueField S)],
      ∃ (n : ℕ) (k : Type u) (_ : Field k) (_ : CharZero k) (f : MvPowerSeries (Fin n) k →+* S),
        Function.Surjective f
open PowerSeriesPolynomialRing in
/-- Cited (Nagata [14]; fn. 30, p. 161): for `T = k⟦t⟧[x]`, `char k = 0`, a prime `𝔭 =
  (f₁,…,f_r)` and `𝔮'` in `T/𝔭` over `𝔮`: `(T/𝔭)_𝔮'` is regular iff `rank (jacobian f mod 𝔮) = ht
  𝔭`. -/
class _root_.Hironaka.Cited.IsRegularLocalRingLocalizationIffRankJacobianEqHeight : Prop where
  isRegularLocalRing_localization_iff_rank_jacobian_eq_height : ∀ (k : Type u) [Field k]
      [CharZero k] (n m : ℕ) (𝔭 : Ideal (PowerSeriesPolynomialRing k n m)) [𝔭.IsPrime]
      (𝔮' : Ideal (PowerSeriesPolynomialRing k n m ⧸ 𝔭)) [𝔮'.IsPrime] {r : ℕ}
      (f : Fin r → PowerSeriesPolynomialRing k n m) (hf : Ideal.span (Set.range f) = 𝔭),
      IsRegularLocalRing (Localization.AtPrime 𝔮') ↔
        (((jacobian f).map (residueMap (𝔮'.comap (Ideal.Quotient.mk 𝔭)))).rank : ℕ∞) =
          𝔭.height
/-- Cited (Serre; fn. 9, p. 243): a localization of a regular local ring at a prime ideal is
  regular. -/
class _root_.Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing : Prop where
  isRegularLocalRing_localization_of_isRegularLocalRing : ∀ (R : Type u) [CommRing R]
      [IsRegularLocalRing R] (P : Ideal R) [P.IsPrime],
      IsRegularLocalRing (Localization.AtPrime P)
/-- Hironaka's class 𝔅 (p. 161): Noetherian local `S`, residue characteristic 0, and for each
  finite-type `S`-algebra `A`, a prime of `A ⊗ Ŝ` is regular iff its contraction to `A` is. -/
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
/-- Cited ((iii), p. 161; Nagata): for `S` in the class 𝔅 and `A` of finite type over `S`, the
  non-regular locus of `Spec A` is closed. -/
class _root_.Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus : Prop where
  isClosed_singularLocus : ∀ (S : Type u) [CommRing S] [IsLocalRing S]
      [IsHironakaBase S] (A : Type u) [CommRing A] [Algebra S A] [Algebra.FiniteType S A],
      IsClosed (regularLocus A)ᶜ
end Hironaka
namespace AlgebraicGeometry.Scheme
section
variable (X : Scheme.{u})
/-- `X` is simple (regular) at `x`: the local ring `O_{X,x}` is regular (footnote 29). -/
def IsSimpleAt (x : X) : Prop := IsRegularLocalRing (X.presheaf.stalk x)
/-- `X` is non-singular: simple at every point. -/
def IsNonsingular : Prop := ∀ x : X, X.IsSimpleAt x
end
end AlgebraicGeometry.Scheme
namespace Hironaka
/-- Subschemes of `X`: (closed) subschemes, i.e. ideal sheaves, `X.IdealSheafData`. -/
abbrev Subscheme (X : Scheme.{u}) := X.IdealSheafData
end Hironaka
namespace Hironaka.Subscheme
section
variable {X : Scheme.{u}}
/-- The underlying set of points of a subscheme: the support of its ideal sheaf. -/
def pts (D : Subscheme X) : Set X := (D.support : Set X)
/-- The scheme defined by the subscheme `D` (the closed subscheme cut out by its ideal sheaf). -/
abbrev toScheme (D : Subscheme X) : Scheme.{u} := D.subscheme
/-- The closed immersion `D.toScheme ⟶ X`. -/
abbrev ι (D : Subscheme X) : D.toScheme ⟶ X := D.subschemeι
/-- The stalk of the ideal sheaf of `D` at `x`: the ideal of `O_{X,x}` generated by germs at `x`
  of sections of `D.ideal U`, `U` affine open ∋ `x`. -/
def stalkIdeal (D : Subscheme X) (x : X) : Ideal (X.presheaf.stalk x) :=
  Ideal.span {a | ∃ (U : X.affineOpens) (hx : x ∈ (U : Opens X)) (s : Γ(X, U)),
    s ∈ D.ideal U ∧ X.presheaf.germ (U : Opens X) x hx s = a}
/-- The empty subscheme: the unit ideal sheaf `O_X` (`⊤`). -/
def empty : Subscheme X := ⊤
/-- `D` is irreducible: the space of `D.toScheme` is irreducible (so nonempty). -/
def IsIrreducible (D : Subscheme X) : Prop := IrreducibleSpace D.toScheme
/-- `D` is non-singular: the scheme `D.toScheme` is non-singular. -/
def IsNonsingular (D : Subscheme X) : Prop := D.toScheme.IsNonsingular
/-- `x` is a simple point of `D`: `x ∈ D` and `O_{X,x}` modulo the stalk of the ideal of `D` is a
  regular local ring. -/
def IsSimpleAt (D : Subscheme X) (x : X) : Prop :=
  x ∈ D.pts ∧ IsRegularLocalRing ((X.presheaf.stalk x) ⧸ D.stalkIdeal x)
/-- The ideal sheaf of `D` is invertible: each point has an affine open `U` with `D.ideal U`
  generated by a non-zero-divisor of `Γ(X,U)`. -/
def IsInvertibleIdeal (D : Subscheme X) : Prop :=
  ∀ x : X, ∃ (U : X.affineOpens) (_ : x ∈ (U : Opens X)) (a : Γ(X, U)),
    D.ideal U = Ideal.span {a} ∧ a ∈ nonZeroDivisors Γ(X, U)
end
/-- Total transform `f⁻¹(D)` (footnote 35): the kernel of the base change of the closed immersion
  `D ↪ X` along `f : X' ⟶ X`, a subscheme of `X'`. -/
noncomputable def totalTransform {X X' : Scheme.{u}} (f : X' ⟶ X) (D : Subscheme X) :
    Subscheme X' :=
  (pullback.fst f D.ι).ker
end Hironaka.Subscheme
namespace Hironaka
/-- Monoidal transformation of `X` with center `B`: `f : X' ⟶ X` whose total transform of `B` is
  invertible, universal for this property. -/
structure MonoidalTransformation (X : Scheme.{u}) (B : Subscheme X) where
  X' : Scheme.{u}
  f : X' ⟶ X
  invertible : (Subscheme.totalTransform f B).IsInvertibleIdeal
  universal : ∀ (X'' : Scheme.{u}) (f' : X'' ⟶ X),
    (Subscheme.totalTransform f' B).IsInvertibleIdeal → ∃! h : X'' ⟶ X', h ≫ f = f'
end Hironaka
namespace Hironaka.MonoidalTransformation
section
variable {X : Scheme.{u}} {B : Subscheme X}
/-- Cited (EGA II §3): for every scheme `X` and subscheme `B` a monoidal transformation of `X`
  with center `B` exists, and its `f` is proper if `X` is locally Noetherian. -/
class _root_.Hironaka.Cited.MonoidalTransformationExistsIsProper : Prop where
  exists_isProper : ∀ (X : Scheme.{u}) (B : Subscheme X),
      ∃ t : MonoidalTransformation X B, IsLocallyNoetherian X → IsProper t.f
end
end Hironaka.MonoidalTransformation
namespace Hironaka
/-- A succession of monoidal transformations `X₀ → … → Y` with specified centers (Def. 8, p.
  169): `nil` is trivial, `cons` adds one step `X' → X`. -/
inductive MonoidalSuccession : Scheme.{u} → Scheme.{u} → Type (u + 1)
  | nil (X : Scheme.{u}) : MonoidalSuccession X X
  | cons {X : Scheme.{u}} (B : Subscheme X) (t : MonoidalTransformation X B) {Y : Scheme.{u}}
      (rest : MonoidalSuccession t.X' Y) : MonoidalSuccession X Y
end Hironaka
namespace Hironaka.MonoidalSuccession
/-- The composite morphism `Y ⟶ X` of a succession: `𝟙` for `nil`, and `rest.composite ≫ t.f` for
  `cons`. -/
def composite : {X Y : Scheme.{u}} → MonoidalSuccession X Y → (Y ⟶ X)
  | _, _, nil X => 𝟙 X
  | _, _, cons _ t rest => rest.composite ≫ t.f
end Hironaka.MonoidalSuccession
namespace Hironaka
section
open Polynomial Filter
/-- `H_R(n) = Σ_{i≤n} dim_{R/𝔪}(𝔪ⁱ/𝔪ⁱ⁺¹)` (p. 133), the Samuel characteristic function, with
  `finrank` as dimension. -/
noncomputable def hilbertSamuel (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), Module.finrank (R ⧸ maximalIdeal R) (GrPiece (maximalIdeal R) i)
/-- Krull dimension of `R` as a natural number (`0` if it is `⊥` or `∞`). -/
noncomputable def dimNat (R : Type u) [CommRing R] : ℕ := WithBot.recBotCoe (0 : ℕ) ENat.toNat (ringKrullDim R)
/-- Cited (p. 133; fn. 3): for Noetherian local `R`, `hilbertSamuel R` is eventually a rational
  polynomial of degree `dim R`, with `(dim R)! · leading coefficient` a positive integer. -/
class _root_.Hironaka.Cited.ExistsHilbertSamuelPoly : Prop where
  exists_hilbertSamuelPoly : ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      ∃ p : ℚ[X], (∀ᶠ n : ℕ in atTop, p.eval (n : ℚ) = (hilbertSamuel R n : ℚ)) ∧
        p.natDegree = dimNat R ∧
        ∃ e : ℕ, 0 < e ∧ ((dimNat R).factorial : ℚ) * p.leadingCoeff = e
end
section
open Polynomial
/-- Cited (p. 218; fn. 10, p. 243): for a complete Noetherian local domain `S`, the integral
  closure of `S` in its fraction field is a finite `S`-module. -/
class _root_.Hironaka.Cited.CurveFiniteIntegralClosure : Prop where
  curve_finite_integralClosure : ∀ (S : Type u) [CommRing S] [IsDomain S] [IsLocalRing S]
      [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S],
      Module.Finite S (integralClosure S (FractionRing S))
end
section
open Classical
/-- A center (p. 168): `B` is empty, or non-singular and irreducible. -/
def Subscheme.IsCenter {X : Scheme.{u}} (B : Subscheme X) : Prop :=
  B = Subscheme.empty ∨ (B.IsNonsingular ∧ B.IsIrreducible)
end
/-- `k'/k` is separable (pp. 211–212): for every purely inseparable extension `k''` of `k`, `k'
  ⊗_k k''` is reduced. -/
def IsSeparableFieldExtension (k k' : Type u) [Field k] [Field k'] [Algebra k k'] : Prop :=
  ∀ (k'' : Type u) [Field k''] [Algebra k k''], IsPurelyInseparable k k'' →
    IsReduced (TensorProduct k k' k'')
/-- Cited (MacLane, p. 223, fn. 4): `K'/K` is separable iff each finitely generated subextension
  has a transcendence basis over which it is separable algebraic. -/
class _root_.Hironaka.Cited.IsSeparableFieldExtensionIff : Prop where
  isSeparableFieldExtension_iff : ∀ (K K' : Type u) [Field K] [Field K'] [Algebra K K'],
      IsSeparableFieldExtension K K' ↔
        ∀ L : IntermediateField K K',
          (∃ s : Finset K', L = IntermediateField.adjoin K (s : Set K')) →
          ∃ (ι : Type u) (x : ι → L), AlgebraicIndependent K x ∧
            Algebra.IsSeparable (IntermediateField.adjoin K (Set.range x)) L
section
open TensorProduct
/-- Cited (Cohen, p. 200): every complete Noetherian local ring is a quotient of a complete
  regular local ring. -/
class _root_.Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete : Prop where
  exists_surjective_of_isRegularLocalRing_of_isAdicComplete : ∀ (O : Type u) [CommRing O]
      [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O],
      ∃ (R : Type u) (_ : CommRing R) (_ : IsRegularLocalRing R)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (f : R →+* O),
        Function.Surjective f
end
/-- Cited (Cohen, pp. 258, 297): a complete Noetherian local ring whose characteristic equals
  that of its residue field has a coefficient field (a section of the residue map). -/
class _root_.Hironaka.Cited.ExistsResidueCompEqIdOfIsAdicCompleteOfRingCharEq : Prop where
  exists_residue_comp_eq_id_of_isAdicComplete_of_ringChar_eq : ∀ (R : Type u) [CommRing R]
      [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
      (hchar : ringChar R = ringChar (ResidueField R)),
      ∃ σ : ResidueField R →+* R, (IsLocalRing.residue R).comp σ = RingHom.id _
/-- Cited (fn. 10, p. 243): for a complete Noetherian local ring `S` and a domain `A` essentially
  of finite type over `S`, the integral closure of `A` in `Frac A` is finite over `A`. -/
class _root_.Hironaka.Cited.FiniteIntegralClosureOfEssFiniteType : Prop where
  finite_integralClosure_of_essFiniteType : ∀ {S A : Type u} [CommRing S] [IsLocalRing S]
      [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S] [CommRing A] [IsDomain A]
      [Algebra S A] [Algebra.EssFiniteType S A],
      Module.Finite A (integralClosure A (FractionRing A))
/-- Cited (fn. 12, p. 260; Zariski): for a perfect field `k` and a finite-type `k`-algebra `B`,
  the non-regular locus of `Spec B` is closed. -/
class _root_.Hironaka.Cited.IsClosedComplRegularLocusOfFiniteType : Prop where
  isClosed_compl_regularLocus_of_finiteType : ∀ (k : Type u) [Field k] [PerfectField k]
      (B : Type u) [CommRing B] [Algebra k B] [Algebra.FiniteType k B],
      IsClosed (regularLocus B)ᶜ
/-- Cited (p. 261; fn. 3): for `R` Noetherian local and `Q` an ideal, `R̂/QR̂` and `R/Q` have the
  same Krull dimension. -/
class _root_.Hironaka.Cited.RingKrullDimAdicCompletionQuotientEq : Prop where
  ringKrullDim_adicCompletion_quotient_eq : ∀ (R : Type u) [CommRing R] [IsLocalRing R]
      [IsNoetherianRing R] (Q : Ideal R),
      ringKrullDim (AdicCompletion (maximalIdeal R) R ⧸
        Q.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) = ringKrullDim (R ⧸ Q)
/-- The 15 results that the paper cites without proof and the fundamental and main theorems use,
  as hypotheses: one parent class `Hironaka.Cited.*` for each. -/
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
/-- The grading of `B[T₀,…,T_{n-1}]/𝔞` for homogeneous `𝔞` (p. 132): degree `d` is the `B`-span
  of the images of forms of degree `d`. -/
noncomputable def quotientGrading (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B)) :
    ℕ → Submodule B (MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal) :=
  fun d => (homogeneousSubmodule (Fin n) B d).map (Ideal.Quotient.mkₐ B 𝔞.toIdeal).toLinearMap
/-- The `B`-linear map from the forms of degree `d` to `quotientGrading 𝔞 d`, the restriction of
  the quotient map. -/
noncomputable def quotientRestrict (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B)) (d : ℕ) :
    homogeneousSubmodule (Fin n) B d →ₗ[B] quotientGrading 𝔞 d :=
  ((Ideal.Quotient.mkₐ B 𝔞.toIdeal).toLinearMap.restrict (p := homogeneousSubmodule (Fin n) B d)
    (q := quotientGrading 𝔞 d) fun x hx => ⟨x, hx, rfl⟩)
/-- The `B`-linear map `B[T] → ⨁_d quotientGrading 𝔞 d`, `a ↦ (class of a_d)_d`, where `a_d` is
  the degree-`d` component of `a`. -/
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
/-- The additive map `B[T]/𝔞 → ⨁_d quotientGrading 𝔞 d` induced by `quotientDecomposeAux`. -/
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
/-- The `DirectSum.Decomposition` of `B[T]/𝔞` into the pieces `quotientGrading 𝔞 d`, built from
  `quotientDecomposeHom`. -/
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
/-- The `SetLike.GradedMonoid` structure of `quotientGrading 𝔞`: `1` has degree 0 and degrees add
  under products. -/
instance quotientGradedMonoid (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B)) :
    SetLike.GradedMonoid (quotientGrading 𝔞) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, rfl⟩
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.GradedMul.mul_mem ha hb, rfl⟩
/-- The `GradedRing` structure of `B[T]/𝔞` for `quotientGrading 𝔞`, assembled from the
  decomposition and graded-monoid instances. -/
noncomputable instance quotientGradedRing (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B)) :
    GradedRing (quotientGrading 𝔞) :=
  { quotientGradedMonoid 𝔞, quotientDecomposition 𝔞 with }
end
section
open MvPolynomial DirectSum
attribute [local instance] MvPolynomial.gradedAlgebra
variable {B : Type u} [Field B] {n : ℕ} (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))
/-- The structure morphism `Proj H ⟶ Spec H₀ ⟶ Spec B` of `Proj(H)`, `H = B[T]/𝔞` (p. 132). -/
noncomputable def projStructure : Proj (quotientGrading 𝔞) ⟶ Spec (CommRingCat.of B) :=
  Proj.toSpecZero (quotientGrading 𝔞) ≫
    Spec.map (CommRingCat.ofHom (algebraMap B (quotientGrading 𝔞 0)))
/-- `X` is projective over the field `B` (p. 132): `X ≅ Proj(B[T₀,…,T_{n-1}]/𝔞)` for some
  homogeneous `𝔞`, compatibly with `p : X ⟶ Spec B`. -/
def IsProjectiveOver (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of B)) : Prop :=
  ∃ (n : ℕ) (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))
    (e : X ≅ Proj (quotientGrading 𝔞)), e.hom ≫ projStructure 𝔞 = p
end
section
variable {B : Type u} [CommRing B]
/-- The ring map `B → K(X)` for irreducible `p : X ⟶ Spec B` (p. 130): `B ≅ Γ(Spec B) → Γ(X, O_X)
  → K(X)`. -/
noncomputable def functionFieldAlgebraMap {X : Scheme.{u}} [IrreducibleSpace X]
    (p : X ⟶ Spec (CommRingCat.of B)) : B →+* X.functionField :=
  have : Nonempty (⊤ : X.Opens) := ⟨⟨(inferInstance : Nonempty X).some, trivial⟩⟩
  (X.germToFunctionField ⊤).hom.comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
end
end Hironaka
namespace AlgebraicGeometry.Scheme
section
variable {X X' X'' Y Z : Scheme.{u}}
/-- The hypothesis on `a : X' ⟶ X` for composition (p. 139): the inverse image of every open
  dense subset of `X` is dense in `X'`. -/
def Hom.PreimageDense (a : X' ⟶ X) : Prop :=
  ∀ V : X.Opens, Dense (V : Set X) → Dense ((a ⁻¹ᵁ V : X'.Opens) : Set X')
end
end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.Hom.PreimageDense
section
variable {X X' X'' Y Z : Scheme.{u}}
theorem id (X : Scheme.{u}) : (𝟙 X : X ⟶ X).PreimageDense := fun V hV => by simpa using hV
end
end AlgebraicGeometry.Scheme.Hom.PreimageDense
namespace AlgebraicGeometry.Scheme.PartialMap
section
variable {X X' X'' Y Z : Scheme.{u}}
/-- The composite `g ∘ a` of a partial map `g : X ⤏ Y` with `a : X' ⟶ X` with dense preimages:
  domain `a⁻¹(g.domain)`, map `a|_{a⁻¹(g.domain)} ≫ g.hom`. -/
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
theorem precomp_restrict (g : X.PartialMap Y) (a : X' ⟶ X) (ha : a.PreimageDense) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ g.domain) :
    (g.restrict U hU hU').precomp a ha =
      (g.precomp a ha).restrict (a ⁻¹ᵁ U) (ha U hU) (a.preimage_mono hU') := by
  refine PartialMap.ext _ _ rfl ?_
  simp [morphismRestrict_homOfLE_assoc]
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
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
/-- The composite `f ∘ a` of a rational map `f : X ⤏ Y` with `a : X' ⟶ X` with dense preimages
  (p. 139): the class of `g ∘ a`, `g` a representative of `f`. -/
noncomputable def RationalMap.precomp (f : X ⤏ Y) (a : X' ⟶ X) (ha : a.PreimageDense) : X' ⤏ Y :=
  Quotient.liftOn f (fun g => (g.precomp a ha).toRationalMap) fun _ _ h =>
    PartialMap.toRationalMap_eq_iff.mpr (PartialMap.precomp_equiv h a ha)
end
end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.RationalMap
section
variable {X Y : Scheme.{u}}
/-- `f` is a morphism (p. 139): its domain of definition is all of `X` and exactly one morphism
  `φ : X ⟶ Y` has class `f`. -/
def IsMorphism (f : X ⤏ Y) : Prop :=
  f.domain = ⊤ ∧ ∃! φ : X ⟶ Y, φ.toRationalMap = f
/-- `f : X ⤏ Y` is proper (p. 139): there are a representative `g` (dense domain `U`) and a
  closed `T ⊆ X ×_S Y` with both projections proper, `p₁` an iso over `U`, and `p₂ = g ∘ p₁`
  there. -/
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
/-- Cited (fn. 3, p. 116; Auslander–Buchsbaum): a regular local ring that is a domain is a unique
  factorization domain. -/
class _root_.Hironaka.Cited.IsRegularLocalRingUniqueFactorizationMonoid : Prop where
  uniqueFactorizationMonoid : ∀ (R : Type u) [CommRing R]
      [IsRegularLocalRing R] [IsDomain R],
      UniqueFactorizationMonoid R
end Hironaka
namespace Hironaka.Scheme.Modules
section
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}}
/-- `c` is a frame of the `X`-module `M` over `U`: for each open `V ≤ U`, `a ↦ ∑ aᵢ • cᵢ|_V` is a
  bijection `Γ(X, V)^ι → Γ(M, V)`. -/
structure IsFrame (M : X.Modules) (U : X.Opens) {ι : Type u} [Fintype ι] (c : ι → Γ(M, U)) :
    Prop where
  bijective : ∀ (V : X.Opens) (h : V ≤ U),
    Function.Bijective fun a : ι → Γ(X, V) => ∑ i, a i • M.presheaf.map (homOfLE h).op (c i)
end
end Hironaka.Scheme.Modules
namespace Hironaka
section
variable {X : Scheme.{u}}
/-- Ideal sheaf `K` is not divisible by any invertible ideal sheaf except `O_X` (p. 141): `K ⊆ Q`
  stalkwise with `Q` invertible forces `Q = O_X`. -/
def Subscheme.IsPrimitive (K : Subscheme X) : Prop :=
  ∀ Q : Subscheme X, Q.IsInvertibleIdeal → (∀ x, K.stalkIdeal x ≤ Q.stalkIdeal x) →
    ∀ x, Q.stalkIdeal x = ⊤
end
end Hironaka
namespace Hironaka.RationalApplication
/-- Assumed ((*), p. 141): for proper `f : X ⤏ Y`, `X` non-singular, finitely many `J_i ≠ 0`
  with: if `h⁻¹J_i = P_i J'_i`, `P_i` invertible, `J'_i` primitive, dom(`f∘h`) = {some `J'_i =
  O`}. -/
class _root_.Hironaka.Cited.RationalApplicationExistsFiniteSystemDomainPrecompEq : Prop where
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
/-- Every center of the succession is a non-singular subscheme. -/
def HasNonsingularCenters : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, _, nil _ => True
  | _, _, cons B _ rest => B.IsNonsingular ∧ rest.HasNonsingularCenters
end
/-- Every center `D_i` is nowhere dense in its stage `X_i` (p. 144): `interior D_i.pts = ∅`. -/
def NowhereDenseCenters : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, _, nil _ => True
  | _, _, cons D _ rest => interior D.pts = ∅ ∧ rest.NowhereDenseCenters
end Hironaka.MonoidalSuccession
namespace Hironaka
section
open Scheme
variable {X Y : Scheme.{u}}
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
/-- Pair `(X, θ)` (p. 144): integral `X` with a quasi-compact separated locally finite type `p :
  X ⟶ Spec B`, and `θ : L ≃+* K(X)` with `θ(b) =` the image of `b` in `K(X)`. -/
structure FunctionFieldPair (B L : Type u) [Field B] [Field L] [Algebra B L] where
  X : Scheme.{u}
  p : X ⟶ Spec (CommRingCat.of B)
  [isIntegral : IsIntegral X]
  [locallyOfFiniteType : LocallyOfFiniteType p]
  [quasiCompact : QuasiCompact p]
  [isSeparated : IsSeparated p]
  θ : L ≃+* X.functionField
  θ_algebraMap : ∀ b : B, θ (algebraMap B L b) = functionFieldAlgebraMap p b
end
end Hironaka
namespace Hironaka.FunctionFieldPair
section
open Scheme
variable {B L : Type u} [Field B] [Field L] [Algebra B L]
attribute [instance] isIntegral locallyOfFiniteType quasiCompact isSeparated
/-- The isomorphism `θ₁∘θ₂⁻¹ : K(X₂) → K(X₁)` of function fields of the pairs `P = (X₁, θ₁)`, `Q
  = (X₂, θ₂)`, as a morphism of commutative rings. -/
noncomputable def thetaHom (P Q : FunctionFieldPair B L) : Q.X.functionField ⟶ P.X.functionField :=
  CommRingCat.ofHom (Q.θ.symm.trans P.θ).toRingHom
theorem thetaHom_apply (P Q : FunctionFieldPair B L) (x : Q.X.functionField) :
    P.thetaHom Q x = P.θ (Q.θ.symm x) := rfl
/-- The morphism `Spec K(X₁) ⟶ X₂`: `Spec` of `θ₁∘θ₂⁻¹ : K(X₂) → K(X₁)` followed by `Spec K(X₂) ⟶
  X₂` at the generic point. -/
noncomputable def ratFn (P Q : FunctionFieldPair B L) : Spec P.X.functionField ⟶ Q.X :=
  Spec.map (P.thetaHom Q) ≫ Q.X.fromSpecStalk (genericPoint Q.X)
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
/-- The rational application `X₁ ⤏ X₂` of `(X₁, θ₁)` to `(X₂, θ₂)` (p. 144), built from `ratFn`;
  it induces the isomorphism `θ₁∘θ₂⁻¹` of function fields. -/
noncomputable def ratApp (P Q : FunctionFieldPair B L) : P.X ⤏ Q.X :=
  RationalMap.ofFunctionField P.p Q.p (P.ratFn Q) (P.ratFn_comp Q)
/-- `(X₁, θ₁)` dominates `(X₂, θ₂)` (p. 144): the rational application of `(X₁, θ₁)` to `(X₂,
  θ₂)` is a morphism. -/
def Dominates (P Q : FunctionFieldPair B L) : Prop := (P.ratApp Q).IsMorphism
/-- The pair `(X, θ)` lies in the class `𝔐(L/B)` (p. 144): the structure morphism `X ⟶ Spec B` is
  proper. -/
def IsProper (P : FunctionFieldPair B L) : Prop := AlgebraicGeometry.IsProper P.p
/-- `(X', θ')` is obtained from `(X, θ)` by `s` (p. 144): centers nowhere dense and non-singular,
  `p' = composite ≫ p`, and the rational application `(X', θ') ⤏ (X, θ)` is the composite. -/
def IsObtainedBy (P Q : FunctionFieldPair B L) (s : MonoidalSuccession P.X Q.X) : Prop :=
  s.NowhereDenseCenters ∧ s.HasNonsingularCenters ∧ Q.p = s.composite ≫ P.p ∧
    Q.ratApp P = s.composite.toRationalMap
end
section
variable {B L : Type u} [Field B] [Field L] [Algebra B L]
/-- Assumed (p. 145, "obvious"): a proper pair with non-singular `X₁` is dominated by a proper
  pair whose scheme is projective over `B`. -/
class _root_.Hironaka.Cited.FunctionFieldPairExistsProjectiveDominating : Prop where
  exists_projective_dominating : ∀ {B L : Type u} [Field B] [Field L] [Algebra B L],
      ∀ (P₁ : FunctionFieldPair B L) (_hP₁ : P₁.IsProper)
      (_hns : P₁.X.IsNonsingular),
      ∃ P₂ : FunctionFieldPair B L, P₂.IsProper ∧ IsProjectiveOver P₂.X P₂.p ∧ P₂.Dominates P₁
/-- Assumed (p. 145, "necessarily projective"): if `P'` is obtained from a proper non-singular
  `P₁` by a succession and dominates a projective `P₂` dominating `P₁`, then `P'` is projective. -/
class _root_.Hironaka.Cited.FunctionFieldPairIsProjectiveOverOfIsObtainedByDominates : Prop where
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
/-- The structure sheaf `O_X` as an object of the category of `O_X`-modules (the unit module). -/
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
/-- The higher direct image `Rⁱf_*(O_X)` (p. 145): the `i`-th right derived functor of `f_*` on
  `X.Modules`, evaluated at `O_X`. -/
noncomputable def higherDirectImageStructure (f : X ⟶ Y) (i : ℕ) : Y.Modules :=
  ((Scheme.Modules.pushforward f).rightDerived i).obj X.structureModule
end
section
variable {X : Scheme.{u}}
/-- Assumed (p. 145, single blow-up case of (2)): for a monoidal transformation `f` of a
  non-singular `X` with non-singular nowhere dense center, `Rⁱf_*O = 0` (`i > 0`) and `O_X ≅
  f_*O`. -/
class _root_.Hironaka.Cited.MonoidalTransformationHigherDirectImageStructureSheaf : Prop where
  higherDirectImage_structureSheaf : ∀ {X : Scheme.{u}},
      ∀ {B : Type u} [Field B] [CharZero B]
      (p : X ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType p] [QuasiCompact p] (hX : X.IsNonsingular) {D : Subscheme X} (hD : D.IsNonsingular) (hnd : interior D.pts = ∅)
      (t : MonoidalTransformation X D),
      (∀ i, 0 < i → IsZero (higherDirectImageStructure t.f i)) ∧ IsIso t.f.structureUnit
end
section
variable {X Y : Scheme.{u}}
/-- The map `O_Y → R⁰f_*O_X`: the comorphism `O_Y → f_*O_X` followed by the canonical map `f_*O_X
  → R⁰f_*O_X`. -/
noncomputable def structureUnitR0 (f : X ⟶ Y) :
    Y.structureModule ⟶ higherDirectImageStructure f 0 :=
  f.structureUnit ≫ (Scheme.Modules.pushforward f).toRightDerivedZero.app X.structureModule
end
/-- The 15 of `HironakaCitedResults` and the five that Ch. 0 §5 uses: regular local rings are
  UFDs, (*) of p. 141, and three statements of p. 145 that the paper uses without proof. -/
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
/-- (E) (p. 140) for `f∘a`, `a : X₀ ⟶ X`, `S ⊆ X₀`: `nil` if `S ⊆ dom(f∘a)`; `cons`: center `D`
  irreducible/empty, simple near `S`, inside the indeterminacy of `f∘a`, rest for `h⁻¹(S)`. -/
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
/-- `L` is an invertible sheaf of `𝒪_X`-modules: every point has an open neighbourhood `U` over
  which `L` has a one-element frame. -/
def IsInvertible (L : X.Modules) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (d : Γ(L, U)), IsFrame L U (fun _ : PUnit.{u + 1} => d)
end
end Hironaka.Scheme.Modules
namespace Hironaka.MonoidalSuccession
/-- Corollary 2 (p. 145): each center is a (possibly empty) non-singular irreducible subscheme,
  nowhere dense in its stage. -/
def IsNowhereDense : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, _, nil _ => True
  | _, _, cons B _ rest => B.IsCenter ∧ _root_.IsNowhereDense B.pts ∧ rest.IsNowhereDense
end Hironaka.MonoidalSuccession

/-! ## The compared theorems -/
namespace Hironaka.MainTheorem.Ch0
section
open AlgebraicGeometry.Scheme
open Hironaka.Scheme.Modules AlgebraicGeometry.Scheme.Modules
theorem exists_isInvertible_subsheaf_pullback [Hironaka.HironakaCitedResultsCh0.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType p] [QuasiCompact p] [IrreducibleSpace X]
    (hX : X.IsNonsingular) (F : X.Modules) [F.IsLocallyFree] [F.IsFiniteType] (hF : ¬ IsZero F) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsNowhereDense ∧
      ∃ (L : Y.Modules) (i : L ⟶ (Scheme.Modules.pullback s.composite).obj F),
        Mono i ∧ IsInvertible L ∧ (cokernel i).IsLocallyFree ∧ (cokernel i).IsFiniteType :=
  sorry
end
end Hironaka.MainTheorem.Ch0
namespace Hironaka.RationalApplication
section
variable {X Y : Scheme.{u}}
theorem question_E [Hironaka.HironakaCitedResultsCh0.{u}] {B : Type u} [Field B] [CharZero B] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (CommRingCat.of B)) (pY : Y ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType pX] [QuasiCompact pX] [IsSeparated pX]
    [LocallyOfFiniteType pY] [QuasiCompact pY] [IsSeparated pY]
    (hX : X.IsNonsingular) (f : X ⤏ Y) (hf : f.IsProperApplication pX pY) (S₀ : Set X) :
    ∃ (Xr : Scheme.{u}) (s : MonoidalSuccession X Xr),
      EliminatesIndeterminacy f (𝟙 X) (Scheme.Hom.PreimageDense.id X) S₀ s :=
  sorry
end
end Hironaka.RationalApplication
namespace Hironaka.FunctionFieldPair
section
variable {B L : Type u} [Field B] [Field L] [Algebra B L]
theorem exists_isObtainedBy_dominates [Hironaka.HironakaCitedResultsCh0.{u}] [CharZero B] (P₁ P₂ : FunctionFieldPair B L) (h₁ : P₁.IsProper)
    (h₂ : P₂.IsProper) :
    ∃ (P' : FunctionFieldPair B L) (s : MonoidalSuccession P₁.X P'.X),
      P₁.IsObtainedBy P' s ∧ P'.IsProper ∧ P'.Dominates P₂ ∧ (P₁.X.IsNonsingular → P'.X.IsNonsingular) :=
  sorry
theorem exists_higherDirectImage_structureSheaf [Hironaka.HironakaCitedResultsCh0.{u}] [CharZero B] (P₁ P₂ : FunctionFieldPair B L)
    (hP₁ : P₁.IsProper) (hP₂ : P₂.IsProper) (_hdom : P₁.Dominates P₂)
    (hn₁ : P₁.X.IsNonsingular) (hn₂ : P₂.X.IsNonsingular) (f : P₁.X ⟶ P₂.X)
    (hf : f.toRationalMap = P₁.ratApp P₂) :
    (∀ i, 0 < i → IsZero (higherDirectImageStructure f i)) ∧ IsIso f.structureUnit ∧
      IsIso (structureUnitR0 f) :=
  sorry
theorem exists_isObtainedBy_nonsingular_projective [Hironaka.HironakaCitedResultsCh0.{u}] [CharZero B] (P₁ : FunctionFieldPair B L) (h₁ : P₁.IsProper) :
    ∃ (P' : FunctionFieldPair B L) (s : MonoidalSuccession P₁.X P'.X),
      P₁.IsObtainedBy P' s ∧ P'.X.IsNonsingular ∧ IsProjectiveOver P'.X P'.p :=
  sorry
end
end Hironaka.FunctionFieldPair

end
