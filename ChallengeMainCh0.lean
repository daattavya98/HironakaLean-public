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
# Challenge: the main theorems of Hironaka (1964) as stated in Ch. 0

Main Theorem I in its four forms, the non-singular projective model, Main Theorem I*, Main Theorem II, (B*) and
Corollaries 1 and 3 of Main Theorem II (the theorems of `comparator-main-ch0.json`), with `sorry` proofs, and every
declaration their statements need, restated from `Hironaka.Statements` (whose docstrings are longer and quote the
paper). The cited results are hypotheses: the class `HironakaCitedResults`.
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
section
variable (R : Type u) [CommRing R] [IsLocalRing R]
/-- `s` is a regular system of parameters of the local ring `R`: `s` generates the maximal ideal
  and `|s| = dim R`. -/
def IsRegularSystemOfParameters (s : Finset R) : Prop :=
  Ideal.span (s : Set R) = maximalIdeal R ∧ (s.card : WithBot ℕ∞) = ringKrullDim R
end
section
variable {S : Type u} [CommRing S]
/-- The order `ν_M(J)` (p. 165): the supremum in `ℕ∞` of the `ν` with `J ⊆ M^ν`, so `∞` if `J ⊆
  M^ν` for all `ν`. -/
noncomputable def Ideal.ord (M J : Ideal S) : ℕ∞ :=
  ⨆ (ν : ℕ) (_ : J ≤ M ^ ν), (ν : ℕ∞)
/-- `ν(J)` for an ideal `J` of a local ring: its order `ν_𝔪(J)` with respect to the maximal ideal
  𝔪. -/
noncomputable abbrev Ideal.nu [IsLocalRing S] (J : Ideal S) : ℕ∞ :=
  Ideal.ord (maximalIdeal S) J
end
end Hironaka
namespace Hironaka.Subscheme
section
variable {X : Scheme.{u}}
/-- `D ⊆ D'` (p. 165): the ideal sheaf of `D'` is contained in that of `D` on every affine open. -/
def IsContainedIn (D D' : Subscheme X) : Prop := ∀ U : X.affineOpens, D'.ideal U ≤ D.ideal U
/-- Union of subschemes (p. 165): the subscheme whose ideal sheaf is the intersection of the two
  ideal sheaves. -/
def union (D D' : Subscheme X) : Subscheme X := D ⊓ D'
/-- The reduced subscheme structure on a closed subset `Z` of `X` (vanishing ideal sheaf of `Z`). -/
def ofClosed (Z : Closeds X) : Subscheme X := Scheme.IdealSheafData.vanishingIdeal Z
/-- The subscheme `D`, viewed as a scheme, is reduced. -/
def IsReduced (D : Subscheme X) : Prop := AlgebraicGeometry.IsReduced D.toScheme
/-- Codimension of `W` in `X` at `x` (p. 163): the height of the stalk ideal of `W` in `O_{X,x}`,
  in `ℕ∞`. -/
noncomputable def codimAt (W : Subscheme X) (x : X) : ℕ∞ := (W.stalkIdeal x).height
/-- `W` is everywhere of codimension `s` (p. 163): `codimAt W x = s` at every point `x` of `W`. -/
def IsEverywhereOfCodim (W : Subscheme X) (s : ℕ) : Prop := ∀ x ∈ W.pts, W.codimAt x = s
/-- The irreducible components of `D` (Ch. 0 §5): reduced structures on closed subsets maximal
  among irreducible closed subsets of `D`. -/
def irreducibleComponents (D : Subscheme X) : Set (Subscheme X) :=
  {C | ∃ Z : Closeds X,
    Maximal (fun Z : Closeds X => _root_.IsIrreducible (Z : Set X) ∧ (Z : Set X) ⊆ D.pts) Z ∧
    C = ofClosed Z}
/-- `E` is everywhere of codimension one (Def. 3 (I)(i), p. 164); vacuously true for the empty
  subscheme. -/
def IsEverywhereCodimOne (E : Subscheme X) : Prop := E.IsEverywhereOfCodim 1
end
end Hironaka.Subscheme
namespace Hironaka.MonoidalTransformation
section
variable {X : Scheme.{u}} {B : Subscheme X}
/-- The exceptional subscheme `f⁻¹(B)` of `t`, the total transform of the center `B` (`E_{α+1}`
  in Def. 7). -/
noncomputable def exceptional (t : MonoidalTransformation X B) : Subscheme t.X' :=
  Subscheme.totalTransform t.f B
end
end Hironaka.MonoidalTransformation
namespace Hironaka.Subscheme
/-- Strict transform of `V` by `t` (p. 167): the largest ideal sheaf on `X'` agreeing stalkwise
  with that of `f⁻¹(V)` off `f⁻¹(B)`. -/
noncomputable def strictTransform {X : Scheme.{u}} {B : Subscheme X}
    (t : MonoidalTransformation X B) (V : Subscheme X) : Subscheme t.X' :=
  sSup {V' : Subscheme t.X' |
    ∀ x' : t.X', x' ∉ t.exceptional.pts →
      V'.stalkIdeal x' = (totalTransform t.f V).stalkIdeal x'}
/-- `I·P⁻ᵛ` (Ch. 0 §5, p. 142): the largest `K` with `K·Pᵛ ⊆ I` on all stalks; it is the quotient
  `I/Pᵛ` when `Pᵛ` divides `I`. -/
noncomputable def divPow {X : Scheme.{u}} (I P : Subscheme X) (ν : ℕ) : Subscheme X :=
  sSup {K : Subscheme X | ∀ x : X, K.stalkIdeal x * (P.stalkIdeal x) ^ ν ≤ I.stalkIdeal x}
end Hironaka.Subscheme
namespace Hironaka.MonoidalSuccession
/-- Strict transform of a subscheme along a succession of monoidal transformations, one step at a
  time (p. 167). -/
noncomputable def strictTransform : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    Subscheme X → Subscheme Y
  | _, _, nil _, V => V
  | _, _, cons _ t rest, V => rest.strictTransform (Subscheme.strictTransform t V)
/-- Total transform of `V` by a succession `s`: the total transform by the composite morphism
  `s.composite`. -/
noncomputable def totalTransform {X Y : Scheme.{u}} (s : MonoidalSuccession X Y)
    (V : Subscheme X) : Subscheme Y :=
  Subscheme.totalTransform s.composite V
end Hironaka.MonoidalSuccession
namespace Hironaka.Subscheme
section
variable {X : Scheme.{u}}
/-- Def. 2: `O_{X,x}` has a regular system of parameters `z` such that each component of `E`
  through `x` is cut out by one element of `z` and `D` by a subset of `z`. -/
def HasOnlyNormalCrossingsWithAt (E D : Subscheme X) (x : X) : Prop :=
  ∃ z : Finset (X.presheaf.stalk x),
    IsRegularSystemOfParameters (X.presheaf.stalk x) z ∧
    (∀ C ∈ E.irreducibleComponents, x ∈ C.pts →
      ∃ a ∈ z, C.stalkIdeal x = Ideal.span {a}) ∧
    (∃ t : Finset (X.presheaf.stalk x), t ⊆ z ∧
      D.stalkIdeal x = Ideal.span (t : Set (X.presheaf.stalk x)))
/-- `E` has only normal crossings at `x` (Def. 2): the case of `D = X`, i.e. the zero ideal sheaf
  `⊥`. -/
def HasOnlyNormalCrossingsAt (E : Subscheme X) (x : X) : Prop :=
  E.HasOnlyNormalCrossingsWithAt ⊥ x
/-- `E` has only normal crossings: it does so at every point of `X`. -/
def HasOnlyNormalCrossings (E : Subscheme X) : Prop :=
  ∀ x : X, E.HasOnlyNormalCrossingsAt x
/-- `E` has only normal crossings with `D` (Def. 2): `E` does so with `D` at every point of `D`. -/
def HasOnlyNormalCrossingsWith (E D : Subscheme X) : Prop :=
  ∀ x ∈ D.pts, E.HasOnlyNormalCrossingsWithAt D x
end
end Hironaka.Subscheme
namespace Hironaka
section
variable {O : Type u} [CommRing O]
/-- Def. 1, stalk form: every graded piece `Pᵖ/Pᵖ⁺¹` (p ≥ 0) is a free module over `O/P`. -/
def IsNormallyFlatAlongIdeal (P : Ideal O) : Prop :=
  ∀ p : ℕ, Module.Free (O ⧸ P) (GrPiece P p)
end
end Hironaka
namespace Hironaka.Subscheme
section
variable {X : Scheme.{u}}
/-- Def. 1: `x` lies in `D` and the stalk `O_{X,x}` is normally flat along the stalk ideal of
  `D`. -/
def IsNormallyFlatAlongAt (D : Subscheme X) (x : X) : Prop :=
  x ∈ D.pts ∧ IsNormallyFlatAlongIdeal (D.stalkIdeal x)
/-- `V` is normally flat along `W` at `x` (Def. 4 (I)(ii)): some point `x'` of `V` over `x` is
  normally flat along `ι⁻¹(W)`. -/
def IsNormallyFlatAlongAt' (V W : Subscheme X) (x : X) : Prop :=
  ∃ x' : V.toScheme, V.ι.base x' = x ∧
    (totalTransform V.ι W).IsNormallyFlatAlongAt x'
end
section
variable {X : Scheme.{u}} {B : Subscheme X}
open Classical in
/-- Weak transform (Ch. III Remark 2, p. 214): sum over `ν ≤ ν(J_ξ)` of `f⁻¹(J)·P⁻ᵛ`, `ξ` a
  generic point of `B`; `f⁻¹(J)` if none. -/
noncomputable def weakTransform (t : MonoidalTransformation X B) (J : Subscheme X) :
    Subscheme t.X' :=
  if h : ∃ ξ : X, IsGenericPoint ξ B.pts then
    ⨆ (ν : ℕ) (_ : (ν : ℕ∞) ≤ Ideal.nu (J.stalkIdeal h.choose)),
      divPow (totalTransform t.f J) t.exceptional ν
  else totalTransform t.f J
end
end Hironaka.Subscheme
namespace Hironaka.MonoidalSuccession
/-- Main Theorem II(N) (p. 176): final `E` normal crossings, `J = O_X`; centers `B` non-singular
  irreducible, `max ν(J) = d > 0` attained on `B`, `E` crosses `B` normally; data transformed. -/
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
namespace Hironaka.MonoidalTransformation
section
variable {X : Scheme.{u}} {B : Subscheme X}
/-- The open subscheme `X − B`: the complement of the support of `B`, as an open of `X`. -/
def complOpens (B : Subscheme X) : X.Opens := ⟨B.ptsᶜ, B.support.isClosed.isOpen_compl⟩
end
end Hironaka.MonoidalTransformation
namespace Hironaka.Subscheme
section
variable {X : Scheme.{u}}
/-- `red(D)`: the associated reduced subscheme of `D` (p. 143), i.e. with the radical ideal
  sheaf. -/
abbrev red (D : Subscheme X) : Subscheme X := Scheme.IdealSheafData.radical D
end
end Hironaka.Subscheme
namespace Hironaka.MonoidalSuccession
/-- Main Theorem II (p. 142), integer `d`: final `E` normal crossings, `ν(J_y) < d`; centers
  non-singular irreducible, `ν(J) ≥ d` on them, `E` crossing them normally; data transformed. -/
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
/-- The weak transforms `J_j(i)` of a system `(J_j)` carried along the succession; the value is
  the system `J_j(r)` on the end scheme. -/
noncomputable def weakTransformFamily : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    (Fin e → Subscheme X) → Fin e → Subscheme Y
  | _, _, nil _, J => J
  | _, _, cons _ t rest, J => rest.weakTransformFamily fun j => Subscheme.weakTransform t (J j)
/-- Property (1) of Corollary 1 (p. 143): each center is a (possibly empty) non-singular
  irreducible `D(i)` and each `ν(J_j(i))` is a positive constant on it. -/
def IsTrivializingSteps : {X Y : Scheme.{u}} → MonoidalSuccession X Y → (Fin e → Subscheme X) → Prop
  | _, _, nil _, _ => True
  | _, _, cons B t rest, J =>
      B.IsCenter ∧ (∀ j, ∃ c : ℕ, 0 < c ∧ ∀ y ∈ B.pts, Ideal.nu ((J j).stalkIdeal y) = c) ∧
      rest.IsTrivializingSteps fun j => Subscheme.weakTransform t (J j)
end
section
variable {X Y : Scheme.{u}} {e : ℕ}
/-- Properties (1), (2) of Corollary 1 (p. 143): `IsTrivializingSteps`, and at each point of the
  end scheme some `J_j(r)` has stalk `O`. -/
def IsTrivializing (s : MonoidalSuccession X Y) (J : Fin e → Subscheme X) : Prop :=
  s.IsTrivializingSteps J ∧ ∀ x : Y, ∃ j, (s.weakTransformFamily J j).stalkIdeal x = ⊤
end
/-- Strong Main Theorem I (pp. 132–133): each `D_i` non-singular, with no simple point of `X_i`,
  `X_i` normally flat along it; `X_r` non-singular. -/
def IsStrongResolution : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, _, nil X => X.IsNonsingular
  | _, _, @cons X B _ _ rest =>
      B.IsNonsingular ∧ (∀ x ∈ B.pts, ¬ X.IsSimpleAt x) ∧
        (∀ x ∈ B.pts, Subscheme.IsNormallyFlatAlongAt' (⊥ : Subscheme X) B x) ∧ rest.IsStrongResolution
/-- Theorem I* (p. 138): `D_i` non-singular, `X_i` normally flat along it, `D_i` multiple on
  `red(X_i)` or `X_i` not normally flat along `red(X_i)`; `X_r` normally flat along a regular
  `red(X_r)`. -/
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
/-- Cor. 3 (p. 146), (ii) with non-singularity: each `D_i` is non-singular and contained in
  `f̄_i⁻¹(W)`, with `W_{i+1} = f_i⁻¹(W_i)` carried along. -/
def HasNonsingularCentersIn : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Subscheme X → Prop
  | _, _, nil _, _ => True
  | _, _, cons B t rest, W => B.IsNonsingular ∧ B.IsContainedIn W ∧
      rest.HasNonsingularCentersIn (Subscheme.totalTransform t.f W)
/-- Cor. 3 (p. 146) without (i): `HasNonsingularCentersIn W`, and `red` of the total transform of
  `W` is invertible and has only normal crossings. -/
def IsBoundarySimplification (s : MonoidalSuccession X Y) (W : Subscheme X) : Prop :=
  s.HasNonsingularCentersIn W ∧ (Subscheme.red (s.totalTransform W)).IsInvertibleIdeal ∧
    (Subscheme.red (s.totalTransform W)).HasOnlyNormalCrossings
end
end Hironaka.MonoidalSuccession

/-! ## The compared theorems -/
namespace Hironaka.MainTheorem.Ch0
theorem I [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p] [QuasiCompact p] [AlgebraicGeometry.IsReduced X] [IrreducibleSpace X] :
    ∃ D : Subscheme X, D.pts = {x | ¬ X.IsSimpleAt x} ∧ ∀ t : MonoidalTransformation X D, t.X'.IsNonsingular :=
  sorry
theorem I_weak [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p] [QuasiCompact p] [AlgebraicGeometry.IsReduced X] [IrreducibleSpace X] :
    ∃ D : Subscheme X, Dense D.ptsᶜ ∧ ∀ t : MonoidalTransformation X D,
      t.X'.IsNonsingular ∧ IsIso (t.f ∣_ MonoidalTransformation.complOpens D) :=
  sorry
theorem I_strong [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p] [QuasiCompact p] [AlgebraicGeometry.IsReduced X] [IrreducibleSpace X] :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsStrongResolution :=
  sorry
theorem I_strong_eq [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p] [QuasiCompact p] [AlgebraicGeometry.IsReduced X] [IrreducibleSpace X] :
    ∃ (D : Subscheme X) (Y : Scheme.{u}) (s : MonoidalSuccession X Y) (t : MonoidalTransformation X D)
      (e : Y ≅ t.X'), s.IsStrongResolution ∧ D.pts = {x | ¬ X.IsSimpleAt x} ∧ e.hom ≫ t.f = s.composite :=
  sorry
section
attribute [local instance] MvPolynomial.gradedAlgebra
theorem exists_projective_model [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] (L : Type u) [Field L] [Algebra B L]
    (hL : (⊤ : IntermediateField B L).FG) :
    ∃ (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of B)) (_ : IrreducibleSpace X),
      LocallyOfFiniteType p ∧ QuasiCompact p ∧ IsSeparated p ∧ X.IsNonsingular ∧ IsProjectiveOver X p ∧
      ∃ e : X.functionField ≃+* L, ∀ b : B, e (functionFieldAlgebraMap p b) = algebraMap B L b :=
  sorry
end
theorem IStar [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p] [QuasiCompact p] :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainIStar :=
  sorry
theorem II_full [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p] [QuasiCompact p] (hX : X.IsNonsingular) (J : Subscheme X)
    (hJ : ∀ x, J.stalkIdeal x ≠ ⊥) (d : ℕ)
    (hd : IsGreatest (Set.range fun x => Ideal.nu (J.stalkIdeal x)) (d : ℕ∞))
    (E : Subscheme X) (hE : E.IsReduced) (hE1 : E.IsEverywhereCodimOne)
    (hEnc : E.HasOnlyNormalCrossings) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainIIZero d J E :=
  sorry
theorem B_star [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p] [QuasiCompact p] (hX : X.IsNonsingular) (J : Subscheme X)
    (hJ : ∀ x, J.stalkIdeal x ≠ ⊥) {D : Subscheme X} (hD : D.IsCenter) (t : MonoidalTransformation X D)
    (hconst : ∀ x ∈ D.pts, ∀ x' ∈ D.pts, Ideal.nu (J.stalkIdeal x) = Ideal.nu (J.stalkIdeal x'))
    (y : t.X') :
    Ideal.nu ((Subscheme.weakTransform t J).stalkIdeal y) ≤ Ideal.nu (J.stalkIdeal (t.f y)) :=
  sorry
theorem exists_isTrivializing [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType p] [QuasiCompact p] (hX : X.IsNonsingular)
    {e : ℕ} (he : 1 ≤ e) (J : Fin e → Subscheme X) (hJ : ∀ j x, (J j).stalkIdeal x ≠ ⊥) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsTrivializing J :=
  sorry
theorem exists_isBoundarySimplification [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType p] [QuasiCompact p] (hX : X.IsNonsingular)
    (W : Subscheme X) (hW : IsNowhereDense W.pts) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), Y.IsNonsingular ∧ s.IsBoundarySimplification W :=
  sorry
theorem exists_isBoundarySimplification_of_singularLocus_subset_of_field [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType p] [QuasiCompact p]
    [AlgebraicGeometry.IsReduced X] (W : Subscheme X) (hW : IsNowhereDense W.pts)
    (hsing : {x | ¬ X.IsSimpleAt x} ⊆ W.pts) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), Y.IsNonsingular ∧ s.IsBoundarySimplification W :=
  sorry
end Hironaka.MainTheorem.Ch0

end
