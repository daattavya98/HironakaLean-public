/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Hironaka.Ch0.BlowingUpModules
public import Hironaka.Compat.SymmetricAlgebraGrading
public import Hironaka.Compat.ReesAlgebraGrading

/-!
# The sheaf of homogeneous elements of degree one on `Proj`

For a graded ring `𝒜` the paper (Ch. 0 §2, p. 124) uses the sheaf of modules `J₁` on `Proj` of the
symmetric algebra, "obtained as the subsheaf of modules of `O_{X'} | X` which consists of homogeneous
elements of degree one", where `X' = Spec`.  Mathlib has `Proj` and its structure sheaf (locally the
fractions `a / s` with `a`, `s` of the same degree) but no sheaf of fractions of degree one.  This file
builds it for every graded ring: on an open `U` the sections are the dependent functions
`x ↦ a / s ∈ Localization x`, locally given by a fraction with `a` of degree `i + 1` and `s` of
degree `i`, a module over the sections of the structure sheaf, in the way Mathlib builds the
structure sheaf of `Proj` and the sheaf `M~` on `Spec`.  The result is an `OModules` object on the
locally ringed space `Proj 𝒜`.  It is infrastructure for Grothendieck's observation and its
analogue for the Rees algebra (pp. 124, 128).
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry

open scoped DirectSum Pointwise

open DirectSum SetLike Localization TopCat TopologicalSpace CategoryTheory Opposite Hironaka

universe u

namespace ProjectiveSpectrum

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

local notation3 "at " x =>
  HomogeneousLocalization.AtPrime 𝒜
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x))

namespace DegreeOne

/-- The fibre at a point `x` of the sheaf of homogeneous elements of degree one: the elements
`a / s` of the localization of `A` at the prime `x` with `a` of degree `i + 1` and `s ∈ 𝒜 i` outside
`x`, a module over the homogeneous localization at `x`. -/
def stalk (x : ProjectiveSpectrum 𝒜) :
    Submodule (HomogeneousLocalization.AtPrime 𝒜 (HomogeneousIdeal.toIdeal x.asHomogeneousIdeal))
      (Localization.AtPrime (HomogeneousIdeal.toIdeal x.asHomogeneousIdeal)) where
  carrier := {y | ∃ (i : ℕ) (a : 𝒜 (i + 1)) (s : 𝒜 i)
    (hs : (s : A) ∈ (HomogeneousIdeal.toIdeal x.asHomogeneousIdeal).primeCompl),
      y = Localization.mk (a : A) ⟨s, hs⟩}
  add_mem' := by
    rintro _ _ ⟨i, a, s, hs, rfl⟩ ⟨j, b, t, ht, rfl⟩
    refine ⟨i + j, ⟨s * b + t * a, ?_⟩, ⟨s * t, ?_⟩,
      (HomogeneousIdeal.toIdeal x.asHomogeneousIdeal).primeCompl.mul_mem hs ht, ?_⟩
    · refine add_mem ?_ ?_
      · have := SetLike.mul_mem_graded s.2 b.2
        rwa [show i + (j + 1) = i + j + 1 by omega] at this
      · have := SetLike.mul_mem_graded t.2 a.2
        rwa [show j + (i + 1) = i + j + 1 by omega] at this
    · have := SetLike.mul_mem_graded s.2 t.2
      exact this
    · rw [Localization.add_mk]
      rfl
  zero_mem' := ⟨0, 0, 1, (HomogeneousIdeal.toIdeal x.asHomogeneousIdeal).primeCompl.one_mem,
    (Localization.mk_zero _).symm⟩
  smul_mem' := by
    rintro r _ ⟨i, a, s, hs, rfl⟩
    obtain ⟨⟨j, n, d, hd⟩, rfl⟩ := HomogeneousLocalization.mk_surjective r
    refine ⟨j + i, ⟨n * a, ?_⟩, ⟨d * s, ?_⟩,
      (HomogeneousIdeal.toIdeal x.asHomogeneousIdeal).primeCompl.mul_mem hd hs, ?_⟩
    · have := SetLike.mul_mem_graded n.2 a.2
      rwa [show j + (i + 1) = j + i + 1 by omega] at this
    · exact SetLike.mul_mem_graded d.2 s.2
    · change (HomogeneousLocalization.val _) * _ = _
      rw [HomogeneousLocalization.val_mk, Localization.mk_mul]
      rfl

open ProjectiveSpectrum.StructureSheaf

/-- The multiplicative set of the homogeneous elements-or-not outside the prime `x`
(a form of `primeCompl` stated for a point of `ProjectiveSpectrum 𝒜`, so that the primality instance
is found for points of the underlying space). -/
abbrev den (x : ProjectiveSpectrum 𝒜) : Submonoid A :=
  (HomogeneousIdeal.toIdeal x.asHomogeneousIdeal).primeCompl

/-- The homogeneous localization at a point (the degree-zero fibre of the structure sheaf). -/
abbrev loc (x : ProjectiveSpectrum 𝒜) : Type _ :=
  HomogeneousLocalization.AtPrime 𝒜 (HomogeneousIdeal.toIdeal x.asHomogeneousIdeal)

theorem mulMemGraded {i j k : ℕ} (h : i + j = k) {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) :
    a * b ∈ 𝒜 k :=
  h ▸ SetLike.mul_mem_graded ha hb

/-- The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` with `r` of degree `i + 1` and `s` of degree `i` in each of the stalks. -/
def IsFraction {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : ∀ x : U, stalk 𝒜 x.1) : Prop :=
  ∃ (i : ℕ) (r : 𝒜 (i + 1)) (s : 𝒜 i) (s_nin : ∀ x : U, (s : A) ∈ den 𝒜 x.1),
    ∀ x : U, (f x).1 = Localization.mk (r : A) ⟨s, s_nin x⟩

/-- `IsFraction` is prelocal. -/
def isFractionPrelocal : PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => stalk 𝒜 x where
  pred f := IsFraction 𝒜 f
  res := by rintro V U i f ⟨j, r, s, h, w⟩; exact ⟨j, r, s, (h <| i ·), (w <| i ·)⟩

/-- The sections of the sheaf of degree-one elements are the dependent functions that are locally
given by a fraction of degree `i + 1` over degree `i`. -/
def isLocallyFraction : LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => stalk 𝒜 x :=
  (isFractionPrelocal 𝒜).sheafify

variable {𝒜}

theorem zero_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜).pred (0 : ∀ x : U.unop, stalk 𝒜 x.1) := fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, 0, ⟨1, one_mem_graded _⟩, fun y => (den 𝒜 y.1).one_mem,
    fun _ => (Localization.mk_zero _).symm⟩⟩

theorem add_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : ∀ x : U.unop, stalk 𝒜 x.1)
    (ha : (isLocallyFraction 𝒜).pred a) (hb : (isLocallyFraction 𝒜).pred b) :
    (isLocallyFraction 𝒜).pred (a + b) := fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, hwa, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, hwb, wb⟩
  refine
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨sa * rb + sb * ra, add_mem (mulMemGraded 𝒜 (by omega) sa_mem rb_mem)
        (mulMemGraded 𝒜 (by omega) sb_mem ra_mem)⟩,
      ⟨sa * sb, mulMemGraded 𝒜 rfl sa_mem sb_mem⟩, fun y ↦
        (den 𝒜 y.1).mul_mem (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  change (a (ia ⟨y, hy.1⟩)).1 + (b (ib ⟨y, hy.2⟩)).1 = _
  rw [wa ⟨y, hy.1⟩, wb ⟨y, hy.2⟩, Localization.add_mk]
  rfl

theorem smul_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a : ∀ x : U.unop, loc 𝒜 x.1)
    (b : ∀ x : U.unop, stalk 𝒜 x.1)
    (ha : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜).pred a)
    (hb : (isLocallyFraction 𝒜).pred b) :
    (isLocallyFraction 𝒜).pred (a • b) := fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, hwa, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, hwb, wb⟩
  refine
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨ra * rb, mulMemGraded 𝒜 (by omega) ra_mem rb_mem⟩,
      ⟨sa * sb, mulMemGraded 𝒜 rfl sa_mem sb_mem⟩, fun y ↦
        (den 𝒜 y.1).mul_mem (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  change (HomogeneousLocalization.val (a (ia ⟨y, hy.1⟩))) * (b (ib ⟨y, hy.2⟩)).1 = _
  have ea := wa ⟨y, hy.1⟩
  have eb := wb ⟨y, hy.2⟩
  simp only at ea eb
  rw [ea, eb, HomogeneousLocalization.val_mk, Localization.mk_mul]
  rfl

variable (𝒜)

/-- The sections over `U` of the sheaf of degree-one elements, as a module over the sections of the
structure sheaf. -/
def sections (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Submodule (ProjectiveSpectrum.StructureSheaf.sectionsSubring U)
      (∀ x : U.unop, stalk 𝒜 x.1) where
  carrier := {f | (isLocallyFraction 𝒜).pred f}
  add_mem' ha hb := add_mem' U _ _ ha hb
  zero_mem' := zero_mem' U
  smul_mem' r f hf := smul_mem' U r.1 f r.2 hf

/-- The `Type`-valued sheaf of sections of the sheaf of degree-one elements. -/
def inType : Sheaf (Type u) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜)

instance (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) : AddCommGroup ((inType 𝒜).1.obj U) :=
  inferInstanceAs (AddCommGroup (sections 𝒜 U))

/-- The presheaf of degree-one elements, valued in abelian groups. -/
def inAb : Presheaf Ab.{u} (ProjectiveSpectrum.top 𝒜) where
  obj U := AddCommGrpCat.of ((inType 𝒜).1.obj U)
  map i := AddCommGrpCat.ofHom
    { toFun := (inType 𝒜).1.map i
      map_add' _ _ := Subtype.ext rfl
      map_zero' := Subtype.ext rfl }

instance (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((ProjectiveSpectrum.StructureSheaf.structureSheafInType 𝒜).obj.obj U)
      ((inType 𝒜).obj.obj U) :=
  inferInstanceAs (Module (ProjectiveSpectrum.StructureSheaf.sectionsSubring U) (sections 𝒜 U))

/-- The presheaf of degree-one elements as a presheaf of modules over the structure sheaf of `Proj`. -/
def presheafOfModules :
    PresheafOfModules ((Proj.structureSheaf 𝒜).1 ⋙ forget₂ CommRingCat RingCat.{u}) :=
  letI (X : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
      Module (((Proj.structureSheaf 𝒜).1 ⋙ forget₂ CommRingCat RingCat.{u}).obj X)
        ((inAb 𝒜).obj X) := by
    exact inferInstanceAs (Module ((ProjectiveSpectrum.StructureSheaf.structureSheafInType 𝒜).obj.obj X)
      ((inType 𝒜).obj.obj X))
  .ofPresheaf (inAb 𝒜) fun X Y f r m ↦ Subtype.ext rfl

/-- The isomorphism between the underlying `Type`-valued presheaf of `inAb` and `inType`. -/
def inAbCompForget : inAb 𝒜 ⋙ forget Ab.{u} ≅ (inType 𝒜).1 :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

end DegreeOne

open DegreeOne in
/-- The sheaf of `O_{Proj 𝒜}`-modules of homogeneous elements of degree one: the paper's `J₁` for
`Proj(S_A(J))` (Ch. 0 §2, p. 124) and `I₁*` for `Proj(S*_A(J))` (p. 128), for any graded ring. -/
def Proj.degreeOne : OModules.{u} (Proj.toLocallyRingedSpace 𝒜) where
  val := presheafOfModules 𝒜
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget Ab.{u}) _).mpr
    (TopCat.Presheaf.isSheaf_of_iso (inAbCompForget 𝒜).symm (inType 𝒜).property)

end ProjectiveSpectrum

namespace ProjDegreeOne

variable {R : CommRingCat.{u}} {A : Type u} [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [GradedAlgebra 𝒜]

/-- The ring homomorphism `R → 𝒜 0` (the base ring maps into the degree-zero part). -/
def zeroHom : R →+* 𝒜 0 where
  toFun r := ⟨algebraMap R A r, SetLike.algebraMap_mem_graded 𝒜 r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The ring homomorphism from `R` to the global sections of the structure sheaf of `Proj 𝒜`
sending `r` to the section `x ↦ r / 1`. -/
def structureRingHom : R →+* Γ(Proj 𝒜, ⊤) where
  toFun r := ⟨fun x => HomogeneousLocalization.fromZeroRingHom 𝒜 _ (zeroHom 𝒜 r),
    fun _ => ⟨⊤, trivial, 𝟙 _, 0, zeroHom 𝒜 r, ⟨1, one_mem_graded _⟩,
      fun _ => (ProjectiveSpectrum.DegreeOne.den 𝒜 _).one_mem, fun _ => rfl⟩⟩
  map_one' := Subtype.ext (funext fun x => by simp; rfl)
  map_mul' _ _ := Subtype.ext (funext fun x => by simp only [map_mul]; rfl)
  map_zero' := Subtype.ext (funext fun x => by simp; rfl)
  map_add' _ _ := Subtype.ext (funext fun x => by simp only [map_add]; rfl)

/-- `structureRingHom` as a morphism of commutative rings. -/
def structureHom : R ⟶ Γ(Proj 𝒜, ⊤) :=
  CommRingCat.ofHom (S := ↑(Γ(Proj 𝒜, ⊤))) (structureRingHom 𝒜)

/-- The structure morphism `Proj 𝒜 ⟶ Spec R` of a graded `R`-algebra: the morphism corresponding, under
the adjunction `Γ ⊣ Spec`, to the ring homomorphism `R → Γ(Proj 𝒜, O)` sending `r` to `r / 1`
(Mathlib has `Proj.toSpecZero` to `Spec (𝒜 0)`; this is its composite with `Spec` of `R → 𝒜 0`,
not proved here; it is used because it makes the module structures computable). -/
def structureMorphism : Proj 𝒜 ⟶ Spec R :=
  ΓSpec.adjunction.homEquiv (Proj 𝒜) (op R) (structureHom 𝒜).op

/-- On global sections, the structure morphism is the ring homomorphism `r ↦ r / 1`. -/
theorem appTop_inv_eq (r : R) :
    (structureMorphism 𝒜).appTop ((Scheme.ΓSpecIso R).inv r) = structureRingHom 𝒜 r := by
  have h0 := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (X := Proj 𝒜) (B := R) (structureHom 𝒜)
  have h1 := congrArg (fun g => CommRingCat.Hom.hom g r) h0
  unfold structureMorphism
  exact h1

/-- The structure morphism as a morphism of locally ringed spaces. -/
abbrev structureLRS : (Proj 𝒜).toLocallyRingedSpace ⟶ (Spec R).toLocallyRingedSpace :=
  (structureMorphism 𝒜).toLRSHom

/-- The scheme `Proj 𝒜` has the structure sheaf of modules `Proj.degreeOne 𝒜` over its locally ringed
space (the two descriptions agree by definition). -/
abbrev degreeOneSheaf : OModules.{u} (Proj 𝒜).toLocallyRingedSpace :=
  ProjectiveSpectrum.Proj.degreeOne 𝒜

/-- The section `x ↦ a / 1` of the sheaf of degree-one elements over the whole space, for `a` of
degree one. -/
def degreeOneSection (a : A) (ha : a ∈ 𝒜 1) :
    (ProjectiveSpectrum.DegreeOne.inType 𝒜).1.obj (op ⊤) :=
  ⟨fun _ => ⟨Localization.mk a 1, 0, ⟨a, ha⟩, ⟨1, one_mem_graded _⟩,
      (ProjectiveSpectrum.DegreeOne.den 𝒜 _).one_mem, rfl⟩,
    fun _ => ⟨⊤, trivial, 𝟙 _, 0, ⟨a, ha⟩, ⟨1, one_mem_graded _⟩,
      fun _ => (ProjectiveSpectrum.DegreeOne.den 𝒜 _).one_mem, fun _ => rfl⟩⟩

variable (N : Type u) [AddCommGroup N] [Module R N]

/-- `Ñ`, as an object of `OModules` on `Spec R`. -/
abbrev tildeOM : OModules.{u} ((Spec R).toLocallyRingedSpace) := tilde (ModuleCat.of R N)

/-- The direct image of the sheaf of degree-one elements under the structure morphism, as a sheaf of
modules on `Spec R` in Mathlib's sense. -/
abbrev directImage : (Spec R).Modules :=
  (OModules.pushforward (structureLRS 𝒜)).obj (degreeOneSheaf 𝒜)

/-- The `R`-linear map from `N` to the global sections of the direct image of `Proj.degreeOne 𝒜`, given
by `n ↦ u n / 1`. -/
def sectionsLinear (u : N →ₗ[R] A) (hu : ∀ n, u n ∈ 𝒜 1) :
    N →ₗ[R] Γ(directImage 𝒜, ⊤) where
  toFun n := (degreeOneSection 𝒜 (u n) (hu n) : ((directImage 𝒜).val.obj (op ⊤)))
  map_add' a b := by
    refine Subtype.ext (funext fun x => Subtype.ext ?_)
    change Localization.mk (u (a + b)) 1 = Localization.mk (u a) 1 + Localization.mk (u b) 1
    rw [map_add, Localization.add_mk]
    simp [add_comm]
  map_smul' r n := by
    have h := appTop_inv_eq 𝒜 r
    refine Subtype.ext (funext fun x => Subtype.ext ?_)
    change Localization.mk (u (r • n)) 1 =
      HomogeneousLocalization.val (((structureMorphism 𝒜).appTop
        ((Scheme.ΓSpecIso R).inv r)).1 x) * Localization.mk (u n) 1
    rw [h]
    change Localization.mk (u (r • n)) 1 = Localization.mk (algebraMap R A r) 1 * Localization.mk (u n) 1
    rw [Localization.mk_mul, map_smul, Algebra.smul_def]
    simp

variable {N}

/-- The morphism `Ñ → f_*(Proj.degreeOne 𝒜)` of sheaves of modules on `Spec R` corresponding, under the
adjunction `tilde ⊣ Γ`, to the module homomorphism `n ↦ u n / 1`. -/
def tildeToDirectImage (u : N →ₗ[R] A) (hu : ∀ n, u n ∈ 𝒜 1) : tildeOM N ⟶ directImage 𝒜 :=
  (tilde.adjunction.homEquiv (ModuleCat.of R N) (directImage 𝒜)).symm
    (show ModuleCat.of R N ⟶ moduleSpecΓFunctor.obj (directImage 𝒜) from
      ModuleCat.ofHom (Y := ModuleCat.of R Γ(directImage 𝒜, ⊤)) (sectionsLinear 𝒜 N u hu))

/-- The canonical homomorphism `f^*(Ñ) ⟶ Proj.degreeOne 𝒜` of sheaves of modules on `Proj 𝒜`,
adjoint to `tildeToDirectImage`.  On `N = 𝒜 ₁` it is the paper's "canonical homomorphism of the module
`S_A(J)₁` into `Γ(X, J₁)`" extended to the sheaf `J~` (p. 124). -/
def canonicalMap (u : N →ₗ[R] A) (hu : ∀ n, u n ∈ 𝒜 1) :
    (OModules.pullback (structureLRS 𝒜)).obj (tildeOM N) ⟶ degreeOneSheaf 𝒜 :=
  ((OModules.pullbackPushforwardAdjunction (structureLRS 𝒜)).homEquiv _ _).symm
    (tildeToDirectImage 𝒜 u hu)

end ProjDegreeOne

namespace ProjDegreeOne

section Symmetric

variable (R : CommRingCat.{u}) (J : Type u) [AddCommGroup J] [Module R J]

/-- The grading of the symmetric algebra `S_R(J)` by the symmetric powers (Ch. 0 §2, p. 124). -/
abbrev symmetricGrading : ℕ → Submodule R (SymmetricAlgebra R J) :=
  (LinearMap.range (SymmetricAlgebra.ι R J : J →ₗ[R] SymmetricAlgebra R J) ^ ·)

theorem symmetric_ι_mem (j : J) : SymmetricAlgebra.ι R J j ∈ symmetricGrading R J 1 := by
  simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R J) j

/-- The canonical homomorphism `f^*(J~) ⟶ J₁` for the symmetric algebra (p. 124, the morphism `Φ`
of `𝓡`-modules from `(Proj(S_A(J)), J₁)` to `(Spec(A), J~)`). -/
def symmetricCanonical :
    (OModules.pullback (structureLRS (symmetricGrading R J))).obj (tildeOM J) ⟶
      degreeOneSheaf (symmetricGrading R J) :=
  canonicalMap (symmetricGrading R J) (SymmetricAlgebra.ι R J) (symmetric_ι_mem R J)

end Symmetric

section Rees

variable (R : CommRingCat.{u}) (J : Ideal R)

/-- The grading of the Rees algebra `S*_R(J) = ⊕ₙ Jⁿ` (Ch. 0 §2, p. 128). -/
abbrev reesGrading : ℕ → Submodule R (reesAlgebra J) := Rees.reesPiece J

/-- The canonical homomorphism `f^*(J~) ⟶ I₁*` for the Rees algebra (p. 128). -/
def reesCanonical :
    (OModules.pullback (structureLRS (reesGrading R J))).obj (tildeOM J) ⟶
      degreeOneSheaf (reesGrading R J) :=
  canonicalMap (reesGrading R J) (Rees.toDegreeOne J) (Rees.toDegreeOne_mem J)

end Rees

end ProjDegreeOne

end AlgebraicGeometry
