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
# Challenge: the fundamental theorems and the main theorems I(n), II(N) of Hironaka (1964)

The theorems of `comparator.json`, with `sorry` proofs, and every declaration their statements need, restated from
`Hironaka.Statements` (whose docstrings are longer and quote the paper). The hypotheses are the class
`HironakaCitedResults`, one field per cited result, each a parent class `Hironaka.Cited.*`
stating it.
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
/-- Algebraic scheme (p. 162): has a quasi-compact, locally finite type morphism to `Spec S`, `S`
  a local ring in 𝔅 (`IsHironakaBase`). Not assumed separated (the paper's schemes are, p. 118). -/
class IsAlgebraicScheme (X : Scheme.{u}) : Prop where
  exists_base : ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : IsHironakaBase S)
    (p : X ⟶ Spec (CommRingCat.of S)), LocallyOfFiniteType p ∧ QuasiCompact p
end Hironaka
namespace AlgebraicGeometry.Scheme
section
variable (X : Scheme.{u})
/-- Dimension of `X` at `x` (p. 163): the Krull dimension of the stalk `O_{X,x}`, in `WithBot
  ℕ∞`. -/
noncomputable def dimAt (x : X) : WithBot ℕ∞ := ringKrullDim (X.presheaf.stalk x)
/-- Dimension of `X` (p. 163): the supremum over points of `dimAt`; the empty scheme gets `⊥`,
  which plays −1. -/
noncomputable def dim : WithBot ℕ∞ := ⨆ x : X, X.dimAt x
end
end AlgebraicGeometry.Scheme
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
/-- Dimension of the subscheme `D` (p. 163): the dimension of the scheme `D`, in `WithBot ℕ∞`. -/
noncomputable def dim (D : Subscheme X) : WithBot ℕ∞ := D.toScheme.dim
/-- Codimension of `W` in `X` at `x` (p. 163): the height of the stalk ideal of `W` in `O_{X,x}`,
  in `ℕ∞`. -/
noncomputable def codimAt (W : Subscheme X) (x : X) : ℕ∞ := (W.stalkIdeal x).height
/-- Codimension of `W` (p. 163): the infimum of `codimAt W x` over points `x` of `W`; `⊤` if `W`
  is empty. -/
noncomputable def codim (W : Subscheme X) : ℕ∞ := ⨅ x ∈ W.pts, W.codimAt x
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
/-- `F` is empty, or non-singular, irreducible and of codimension 1 (Defs. 3 (II), 5; pp.
  165–166); empty allowed (p. 163). -/
def IsNonsingularIrreducibleCodimOne (F : Subscheme X) : Prop :=
  F = empty ∨ (F.IsNonsingular ∧ F.IsIrreducible ∧ F.codim = 1)
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
namespace Hironaka.DatumI
section
open Classical
/-- Raw type I datum `(E; V₁, …, V_β; W)` on `X`: subschemes `E`, `V_j` (`j < β`) and `W`, with
  no conditions. -/
structure Raw (X : Scheme.{u}) where
  E : Subscheme X
  β : ℕ
  V : Fin β → Subscheme X
  W : Subscheme X
end
section
open Classical
variable {X : Scheme.{u}}
/-- Def. 3 (I): `E` is reduced, everywhere of codimension one, with only normal crossings; `W` is
  reduced and contained in every `V_j`. -/
def Raw.IsDatum (ℜ : Raw X) : Prop :=
  ℜ.E.IsReduced ∧ ℜ.E.IsEverywhereCodimOne ∧ ℜ.E.HasOnlyNormalCrossings ∧
  ℜ.W.IsReduced ∧ ∀ j, ℜ.W.IsContainedIn (ℜ.V j)
/-- `n = dim W` (Def. 3 (I)(iv)), in `WithBot ℕ∞`. -/
noncomputable def Raw.n (ℜ : Raw X) : WithBot ℕ∞ := ℜ.W.dim
/-- The principal subscheme of the datum (p. 170): its `W`. -/
abbrev Raw.principal (ℜ : Raw X) : Subscheme X := ℜ.W
/-- Def. 4 (I): `W` is simple at `x`, every `V_j` is normally flat along `W` at `x`, and `E` has
  only normal crossings with `W` at `x`. -/
def Raw.ResolvedAt (ℜ : Raw X) (x : X) : Prop :=
  ℜ.W.IsSimpleAt x ∧
  (∀ j, Subscheme.IsNormallyFlatAlongAt' (ℜ.V j) ℜ.W x) ∧
  ℜ.E.HasOnlyNormalCrossingsWithAt ℜ.W x
/-- Resolved at every point `x` of the principal subscheme `W` (p. 170). -/
def Raw.ResolvedEverywhere (ℜ : Raw X) : Prop := ∀ x ∈ ℜ.W.pts, ℜ.ResolvedAt x
/-- The tuple `(E; V₁, …, V_β, W; B)`: append `W` to the `V`'s and make `B` the principal
  subscheme (Def. 6). -/
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
/-- Resolution datum of type I on `X`: a raw datum `(E; V; W)` satisfying `IsDatum` (Def. 3 (I)). -/
abbrev DatumI (X : Scheme.{u}) := {ℜ : DatumI.Raw X // ℜ.IsDatum}
end
end Hironaka
namespace Hironaka.DatumII
section
open Classical
/-- Raw type II datum `(E₁, …, E_α; J; b; a₁, …, a_α)`: subschemes `E_i`, `J`, and natural
  numbers `b`, `a_i`, with no conditions. -/
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
/-- The union `E₁ ∪ ⋯ ∪ E_α`: the subscheme with the intersection of the ideal sheaves of the
  `E_i`. -/
def Raw.eUnion (ℜ : Raw X) : Subscheme X := ⨅ i, ℜ.E i
/-- Def. 3 (II): `b > 0`; each `E_i` non-singular irreducible of codimension one (or empty);
  `⋃E_i` has normal crossings; each stalk `J_x ≠ 0`. -/
def Raw.IsDatum (ℜ : Raw X) : Prop :=
  0 < ℜ.b ∧
  (∀ i, (ℜ.E i).IsNonsingularIrreducibleCodimOne) ∧
  ℜ.eUnion.HasOnlyNormalCrossings ∧
  ∀ x : X, ℜ.J.stalkIdeal x ≠ ⊥
/-- The weighted count `∑_{x ∈ E_i} a_i` at `x`: the sum of `a_i` over those `i` with `x ∈ E_i`. -/
noncomputable def Raw.weight (ℜ : Raw X) (x : X) : ℕ :=
  ∑ i ∈ (Finset.univ.filter fun i => x ∈ (ℜ.E i).pts), ℜ.a i
/-- `ν(J_x)`: the order of the stalk ideal `J_x` with respect to the maximal ideal of `O_{X,x}`,
  in `ℕ∞`. -/
noncomputable def Raw.nuAt (ℜ : Raw X) (x : X) : ℕ∞ :=
  Ideal.nu (ℜ.J.stalkIdeal x)
/-- Def. 4 (II): resolved at `x` when `∑_{x ∈ E_i} a_i + ν(J_x) < b` (in `ℕ∞`). -/
def Raw.ResolvedAt (ℜ : Raw X) (x : X) : Prop :=
  (ℜ.weight x : ℕ∞) + ℜ.nuAt x < ℜ.b
/-- Resolved at every point `x` of `X`. -/
def Raw.ResolvedEverywhere (ℜ : Raw X) : Prop := ∀ x : X, ℜ.ResolvedAt x
/-- `S(ℜ) = {x ∈ X | ∑_{x ∈ E_i} a_i + ν(J_x) ≥ b}` (p. 165). -/
def Raw.S (ℜ : Raw X) : Set X := {x | (ℜ.b : ℕ∞) ≤ (ℜ.weight x : ℕ∞) + ℜ.nuAt x}
/-- `ν(ℜ)` (p. 165): the supremum in `ℕ∞` of `ν(J_x)` over `x ∈ S(ℜ)`, which is `0` if `S(ℜ)` is
  empty. -/
noncomputable def Raw.nu (ℜ : Raw X) : ℕ∞ := ⨆ x ∈ ℜ.S, ℜ.nuAt x
/-- `S_ν(ℜ) = {x ∈ S(ℜ) | ν(J_x) ≥ ν}`. -/
def Raw.sNu (ℜ : Raw X) (ν : ℕ∞) : Set X := {x ∈ ℜ.S | ν ≤ ℜ.nuAt x}
/-- `S*(ℜ) = S_{ν(ℜ)}(ℜ)` (p. 165). -/
def Raw.sStar (ℜ : Raw X) : Set X := ℜ.sNu ℜ.nu
end
end Hironaka.DatumII
namespace Hironaka
section
open Classical
/-- Resolution datum of type II on `X`: a raw datum satisfying `IsDatum` (Def. 3 (II)). -/
abbrev DatumII (X : Scheme.{u}) := {ℜ : DatumII.Raw X // ℜ.IsDatum}
end
end Hironaka
namespace Hironaka.DatumI.Raw
section
open Classical
variable {X : Scheme.{u}}
/-- Def. 5 (I.1): `F` is non-singular irreducible of codimension one (or empty), `E ∪ F` has
  normal crossings, and `W` lies in the closure of `W − F`. -/
def IsClosedRestriction (ℜ : Raw X) (F : Subscheme X) : Prop :=
  F.IsNonsingularIrreducibleCodimOne ∧
  (ℜ.E.union F).HasOnlyNormalCrossings ∧
  ℜ.W.pts ⊆ closure (ℜ.W.pts \ F.pts)
/-- Def. 5 (I.2): `U = U₀ ∩ W` with `U₀` open in `X`, `U` is dense in `W`, and `ℜ` is resolved at
  every point of `U`. -/
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
/-- Def. 5 (II.1): `F` is non-singular irreducible of codimension one (or empty), and `E₁ ∪ ⋯ ∪
  E_α ∪ F` has only normal crossings. -/
def IsClosedRestriction (ℜ : Raw X) (F : Subscheme X) : Prop :=
  F.IsNonsingularIrreducibleCodimOne ∧ (ℜ.eUnion.union F).HasOnlyNormalCrossings
end
end Hironaka.DatumII.Raw
namespace Hironaka.DatumI.Raw
section
open Classical
variable {X : Scheme.{u}}
/-- Def. 6 (type I): `B` is a center, and `(E; V₁, …, V_β, W; B)` is a datum resolved at every
  point of `B`. -/
def IsPermissible (ℜ : Raw X) (B : Subscheme X) : Prop :=
  B.IsCenter ∧ (ℜ.extendBy B).IsDatum ∧ (ℜ.extendBy B).ResolvedEverywhere
/-- Permissible for `(ℜ, F)`: `B` is permissible for `ℜ` and `B ⊆ W ∩ F`. -/
def IsPermissibleClosed (ℜ : Raw X) (F B : Subscheme X) : Prop :=
  ℜ.IsPermissible B ∧ B.pts ⊆ ℜ.W.pts ∩ F.pts
/-- Permissible for `(ℜ, U)`: `B` is permissible for `ℜ` and `B ⊆ W − U`. -/
def IsPermissibleOpen (ℜ : Raw X) (U : Set X) (B : Subscheme X) : Prop :=
  ℜ.IsPermissible B ∧ B.pts ⊆ ℜ.W.pts \ U
end
end Hironaka.DatumI.Raw
namespace Hironaka.DatumII.Raw
section
open Classical
variable {X : Scheme.{u}}
/-- Def. 6 (type II): `B` is a center, `B ⊆ S*(ℜ)`, and `E₁ ∪ ⋯ ∪ E_α` has only normal crossings
  with `B`. -/
def IsPermissible (ℜ : Raw X) (B : Subscheme X) : Prop :=
  B.IsCenter ∧ B.pts ⊆ ℜ.sStar ∧ ℜ.eUnion.HasOnlyNormalCrossingsWith B
/-- Permissible for `(ℜ, F)`: `B` is permissible for `ℜ` and `B ⊆ F`. -/
def IsPermissibleClosed (ℜ : Raw X) (F B : Subscheme X) : Prop :=
  ℜ.IsPermissible B ∧ B.pts ⊆ F.pts
end
end Hironaka.DatumII.Raw
namespace Hironaka.DatumI.Raw
section
open Classical
variable {X : Scheme.{u}}
/-- Def. 7 (type I): `(E' ∪ f⁻¹(B); V'; W')`, primes being strict transforms, same `β`; defined
  for every center, permissible or not. -/
noncomputable def transform (ℜ : Raw X) {B : Subscheme X} (t : MonoidalTransformation X B) :
    Raw t.X' where
  E := (Subscheme.strictTransform t ℜ.E).union t.exceptional
  β := ℜ.β
  V := fun j => Subscheme.strictTransform t (ℜ.V j)
  W := Subscheme.strictTransform t ℜ.W
/-- Transform of an open restriction: the preimage `U' = f⁻¹(U)` under `f`. -/
def transformOpen {B : Subscheme X} (t : MonoidalTransformation X B) (U : Set X) : Set t.X' :=
  t.f.base ⁻¹' U
end
end Hironaka.DatumI.Raw
namespace Hironaka.DatumII.Raw
section
open Classical
variable {X : Scheme.{u}}
/-- Def. 7 (II): `E_i'` strict transforms, `E_{α+1} = f⁻¹(B)`, `J' = (f⁻¹J : P^ν)` with `P` its
  ideal and `ν = ν(ℜ)`, same `b`, `a_{α+1} = (∑_{B ⊆ E_i} a_i) + ν − b` in ℕ (truncated). -/
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
/-- Transform of a type I raw datum along a succession: apply the Def. 7 transform step by step. -/
noncomputable def transformI : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    DatumI.Raw X → DatumI.Raw Y
  | _, _, nil _, ℜ => ℜ
  | _, _, cons _ t rest, ℜ => rest.transformI (ℜ.transform t)
/-- Transform of a type II raw datum along a succession: apply the Def. 7 transform step by step. -/
noncomputable def transformII : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    DatumII.Raw X → DatumII.Raw Y
  | _, _, nil _, ℜ => ℜ
  | _, _, cons _ t rest, ℜ => rest.transformII (ℜ.transform t)
/-- Def. 8 for `(ℜ, F)`, type I: each center is permissible for the current datum and strict
  transform of `F`, transformed step by step. -/
def IsPermissibleIClosed : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    DatumI.Raw X → Subscheme X → Prop
  | _, _, nil _, _, _ => True
  | _, _, cons B t rest, ℜ, F =>
      ℜ.IsPermissibleClosed F B ∧
      rest.IsPermissibleIClosed (ℜ.transform t) (Subscheme.strictTransform t F)
/-- Def. 8, type I, `(ℜ, U)`: each center `B_i` is permissible for `ℜ_i` with `B_i ⊆ W_i − U_i`;
  `ℜ_{i+1} = f_i*ℜ_i`, `U_{i+1} = f_i⁻¹(U_i)`. -/
def IsPermissibleIOpen : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    DatumI.Raw X → Set X → Prop
  | _, _, nil _, _, _ => True
  | _, _, cons B t rest, ℜ, U =>
      ℜ.IsPermissibleOpen U B ∧
      rest.IsPermissibleIOpen (ℜ.transform t) (DatumI.Raw.transformOpen t U)
/-- Def. 8, type II, no restriction: each center `B_i` is permissible for `ℜ_i`, where `ℜ_{i+1} =
  f_i*ℜ_i`. -/
def IsPermissibleII : {X Y : Scheme.{u}} → MonoidalSuccession X Y → DatumII.Raw X → Prop
  | _, _, nil _, _ => True
  | _, _, cons B t rest, ℜ => ℜ.IsPermissible B ∧ rest.IsPermissibleII (ℜ.transform t)
/-- Def. 8, type II, `(ℜ, F)`: each center `B_i` is permissible for `(ℜ_i, F_i)`; `ℜ_{i+1} =
  f_i*ℜ_i`, `F_{i+1}` the strict transform of `F_i`. -/
def IsPermissibleIIClosed : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    DatumII.Raw X → Subscheme X → Prop
  | _, _, nil _, _, _ => True
  | _, _, cons B t rest, ℜ, F =>
      ℜ.IsPermissibleClosed F B ∧
      rest.IsPermissibleIIClosed (ℜ.transform t) (Subscheme.strictTransform t F)
end
end Hironaka.MonoidalSuccession
namespace Hironaka
/-- Standing hypothesis of §2 (p. 170): `X` is a non-singular irreducible algebraic scheme of
  dimension `N ≥ 0`. -/
def IsAmbient (X : Scheme.{u}) (N : ℕ) : Prop :=
  IsAlgebraicScheme X ∧ X.IsNonsingular ∧ IrreducibleSpace X ∧ X.dim = (N : WithBot ℕ∞)
/-- Theorem I₁^{N,n} (`n : ℕ`): for `(ℜ, F)` on an ambient `X` with `dim W = n`, some permissible
  succession makes the strict transform of `F` miss the principal subscheme of `f*ℜ`. -/
def FundamentalTheorem.I₁ (N n : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAmbient X N →
  ∀ (ℜ : DatumI X) (F : Subscheme X), (ℜ : DatumI.Raw X).IsClosedRestriction F →
    (ℜ : DatumI.Raw X).n = (n : WithBot ℕ∞) →
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
    s.IsPermissibleIClosed ℜ F ∧
    (s.transformI ℜ).principal.pts ∩ (s.strictTransform F).pts = ∅
/-- Theorem I₂^{N,n} (`n : ℕ`): for `(ℜ, U)` on an ambient `X` with `dim W = n`, some succession
  permissible for `(ℜ, U)` makes `f*ℜ` resolved everywhere. -/
def FundamentalTheorem.I₂ (N n : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAmbient X N →
  ∀ (ℜ : DatumI X) (U : Set X), (ℜ : DatumI.Raw X).IsOpenRestriction U →
    (ℜ : DatumI.Raw X).n = (n : WithBot ℕ∞) →
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
    s.IsPermissibleIOpen ℜ U ∧ (s.transformI ℜ).ResolvedEverywhere
/-- Theorem II₁^N: for type II `ℜ` with `ν(ℜ) > 0` and closed restriction `F` on an ambient `X`,
  a permissible succession makes the strict transform of `F` miss `S_ν(f*ℜ)`, `ν = ν(ℜ)`. -/
def FundamentalTheorem.II₁ (N : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAmbient X N →
  ∀ (ℜ : DatumII X) (F : Subscheme X), (ℜ : DatumII.Raw X).IsClosedRestriction F →
    0 < (ℜ : DatumII.Raw X).nu →
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
    s.IsPermissibleIIClosed ℜ F ∧
    (s.strictTransform F).pts ∩ (s.transformII ℜ).sNu (ℜ : DatumII.Raw X).nu = ∅
/-- Theorem II₂^N: for any type II datum `ℜ` on an ambient `X`, some succession permissible for
  `ℜ` makes `f*ℜ` resolved everywhere. -/
def FundamentalTheorem.II₂ (N : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAmbient X N →
  ∀ (ℜ : DatumII X),
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
    s.IsPermissibleII ℜ ∧ (s.transformII ℜ).ResolvedEverywhere
/-- Theorem I₁^{N,-1} (p. 171): the statement of `I₁` with `dim W = ⊥` (`⊥` plays −1, i.e. `W`
  empty) in place of `dim W = n`. -/
def FundamentalTheorem.I₁Bot (N : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAmbient X N →
  ∀ (ℜ : DatumI X) (F : Subscheme X), (ℜ : DatumI.Raw X).IsClosedRestriction F →
    (ℜ : DatumI.Raw X).n = ⊥ →
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
    s.IsPermissibleIClosed ℜ F ∧
    (s.transformI ℜ).principal.pts ∩ (s.strictTransform F).pts = ∅
/-- Theorem I₂^{N,-1} (p. 171): the statement of `I₂` with `dim W = ⊥` (`⊥` plays −1, i.e. `W`
  empty) in place of `dim W = n`. -/
def FundamentalTheorem.I₂Bot (N : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAmbient X N →
  ∀ (ℜ : DatumI X) (U : Set X), (ℜ : DatumI.Raw X).IsOpenRestriction U →
    (ℜ : DatumI.Raw X).n = ⊥ →
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
    s.IsPermissibleIOpen ℜ U ∧ (s.transformI ℜ).ResolvedEverywhere
/-- Theorem I₁^{N,n} for `n : WithBot ℕ` (`⊥` plays −1): `I₁Bot` at `⊥`, `I₁` at `n ≥ 0`. -/
def FundamentalTheorem.I₁WithBot (N : ℕ) : WithBot ℕ → Prop :=
  WithBot.recBotCoe (FundamentalTheorem.I₁Bot.{u} N) (FundamentalTheorem.I₁.{u} N)
/-- Theorem I₂^{N,n} for `n : WithBot ℕ` (`⊥` plays −1): `I₂Bot` at `⊥`, `I₂` at `n ≥ 0`. -/
def FundamentalTheorem.I₂WithBot (N : ℕ) : WithBot ℕ → Prop :=
  WithBot.recBotCoe (FundamentalTheorem.I₂Bot.{u} N) (FundamentalTheorem.I₂.{u} N)
end Hironaka
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
namespace Hironaka
/-- Main Theorem II(N) (p. 176): for non-singular algebraic `X` of dim `N`, `J` with nonzero
  stalks, `E` reduced, codim one, normal crossings, some succession has `IsMainSuccession J E`. -/
def MainTheorem.II (N : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAlgebraicScheme X → X.IsNonsingular → X.dim = (N : WithBot ℕ∞) →
  ∀ (J : Subscheme X), (∀ x, J.stalkIdeal x ≠ ⊥) →
  ∀ (E : Subscheme X), E.IsReduced → E.IsEverywhereCodimOne → E.HasOnlyNormalCrossings →
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainSuccession J E
section
variable {X : Scheme.{u}} {β : ℕ}
/-- The systems `V_0, V_1, …, V_β` (p. 174): `V_0 = ⊥` (the scheme `X` itself) followed by `V_1,
  …, V_β`. -/
def mainSystem (V : Fin β → Subscheme X) : Fin (β + 1) → Subscheme X :=
  Fin.cons ⊥ V
/-- (pp. 173–174) `x` is a simple point of `W` and every `V_j`, `0 ≤ j ≤ β`, is normally flat
  along `W` at `x`. -/
def Subscheme.IsMainResolvedAt (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) (x : X) : Prop :=
  W.IsSimpleAt x ∧ ∀ j, Subscheme.IsNormallyFlatAlongAt' (V j) W x
/-- Conditions (1)–(3) of Main Theorem I(n) for `B` (pp. 173–174): `Cen B`, `B ⊆ W`; no point of
  `B` is resolved for `(V; W)`; on `B`, all `V_j` and `W` are normally flat along `B`. -/
def Subscheme.IsMainStepWith (Cen : Subscheme X → Prop) (V : Fin (β + 1) → Subscheme X)
    (W B : Subscheme X) : Prop :=
  (Cen B ∧ B.IsContainedIn W) ∧
  (∀ x ∈ B.pts, ¬ Subscheme.IsMainResolvedAt V W x) ∧
  (∀ x ∈ B.pts, (∀ j, Subscheme.IsNormallyFlatAlongAt' (V j) B x) ∧
    Subscheme.IsNormallyFlatAlongAt' W B x)
/-- Condition (4) of Main Theorem I(n): `W` is non-singular and each `V_j` is normally flat along
  `W` at every point of `W`. -/
def Subscheme.IsMain4Data (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) : Prop :=
  W.IsNonsingular ∧ ∀ j, ∀ x ∈ W.pts, Subscheme.IsNormallyFlatAlongAt' (V j) W x
end
end Hironaka
namespace Hironaka.MonoidalSuccession
/-- Conditions (1)–(3) of Main Theorem I(n) for all `i` (p. 174): `IsMainStepWith` (centers of
  shape `Cen`) at each stage, `V_j`, `W` replaced by strict transforms. -/
def IsMain123With (Cen : ∀ {X : Scheme.{u}}, Subscheme X → Prop) :
    {X Y : Scheme.{u}} → MonoidalSuccession X Y → {β : ℕ} → (Fin (β + 1) → Subscheme X) →
      Subscheme X → Prop
  | _, _, nil _, _, _, _ => True
  | _, _, cons B t rest, _, V, W =>
      Subscheme.IsMainStepWith (fun D => Cen D) V W B ∧
      rest.IsMain123With Cen (fun j => Subscheme.strictTransform t (V j)) (Subscheme.strictTransform t W)
/-- Conditions (1), (2), (3) for all `i`, as printed: `IsMain123With` with centers non-singular
  irreducible (`IsCenter`). -/
abbrev IsMain123 {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {β : ℕ}
    (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) : Prop :=
  s.IsMain123With (fun {_} D => Subscheme.IsCenter D) V W
/-- Condition (4): the strict transforms of `V_j` and `W` at the end of the succession satisfy
  `IsMain4Data`. -/
def IsMain4 {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {β : ℕ}
    (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) : Prop :=
  Subscheme.IsMain4Data (fun j => s.strictTransform (V j)) (s.strictTransform W)
/-- Conclusion of Main Theorem I(n): `IsMain123` at every step and `IsMain4` at the end. -/
def IsMainI {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {β : ℕ}
    (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) : Prop :=
  s.IsMain123 V W ∧ s.IsMain4 V W
end Hironaka.MonoidalSuccession
namespace Hironaka.MainTheorem
/-- Main Theorem I(n) (p. 174): for algebraic `V₀`, reduced `W` of dimension `n` in each `V_j`
  (`1 ≤ j ≤ β`), some succession satisfies `IsMainI` for `V_0 = V₀`, `V_1, …, V_β`, `W`. -/
def I (n : ℕ) : Prop :=
  ∀ (V₀ : Scheme.{u}) [IsAlgebraicScheme V₀] (β : ℕ) (V : Fin β → Subscheme V₀) (W : Subscheme V₀),
    W.IsReduced → W.dim = (n : WithBot ℕ∞) → (∀ j, W.IsContainedIn (V j)) →
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession V₀ Y), s.IsMainI (mainSystem V) W
end Hironaka.MainTheorem

/-! ## The compared theorems -/
namespace Hironaka
theorem allFundamentalTheorems_printedRange [Hironaka.HironakaCitedResults.{u}] :
    (∀ (N : ℕ) (n : WithBot ℕ), n < (N : WithBot ℕ) →
      FundamentalTheorem.I₁WithBot.{u} N n ∧ FundamentalTheorem.I₂WithBot.{u} N n) ∧
    (∀ N : ℕ, FundamentalTheorem.II₁.{u} N ∧ FundamentalTheorem.II₂.{u} N) :=
  sorry
end Hironaka
namespace Hironaka.MainTheorem
theorem I_all [Hironaka.HironakaCitedResults.{u}] (n : ℕ) : MainTheorem.I.{u} n :=
  sorry
end Hironaka.MainTheorem
namespace Hironaka
theorem mainTheorem_II [Hironaka.HironakaCitedResults.{u}] (N : ℕ) : MainTheorem.II.{u} N :=
  sorry
end Hironaka

end
