/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Compat.ProjDegreeOne
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.FiniteType

/-!
# The structure morphism of `Proj` of a graded algebra

Infrastructure used in the derivation of assertions (a) and (b) of p. 124 of the paper; it proves no
claim of the paper.

The structure morphism `structureMorphism 𝒜 : Proj 𝒜 ⟶ Spec R` of a graded `R`-algebra (defined in
`Hironaka.Compat.ProjDegreeOne` through the adjunction `Γ ⊣ Spec`, because that description makes the
module structures computable) is compared here with Mathlib's `Proj.toSpecZero`, which is defined chart
by chart.  We prove

* `structureMorphism_eq`: `structureMorphism 𝒜` is `Proj.toSpecZero 𝒜` followed by `Spec` of
  `R ⟶ 𝒜 0`;
* `isSeparated_structureMorphism`: it is separated;
* for the symmetric algebra of a finitely generated `R`-module `J`: `SymmetricAlgebra R J` is of finite
  type over `R`, and the structure morphism is locally of finite type and quasi-compact.  (The map
  `R ⟶ 𝒜 0` is surjective for the symmetric grading, `zeroHom_symmetric_surjective`.)

These facts let separatedness, local finite type and quasi-compactness of the structure morphisms of
`Proj` of symmetric algebras be read off from Mathlib's results on `Proj.toSpecZero`.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjDegreeOne

universe u

namespace Hironaka

section ProjStructure

variable {R : CommRingCat.{u}} {A : Type u} [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [GradedAlgebra 𝒜]

/-- On global sections, Mathlib's `Proj.toSpecZero` sends the image of `zeroHom 𝒜 r` in `Γ(Spec 𝒜₀, ⊤)`
to the section `x ↦ r / 1` of the structure sheaf of `Proj 𝒜` (the one used to define
`structureMorphism`). -/
theorem toSpecZero_appTop_apply (r : R) :
    (Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv (zeroHom 𝒜 r)) =
      structureRingHom 𝒜 r := by
  rw [Proj.toSpecZero]
  simp only [Scheme.Hom.comp_appTop]
  rw [← CommRingCat.comp_apply, ← Category.assoc, ← Category.assoc, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Category.assoc]
  have h : (Proj.basicOpenToSpec 𝒜 1).appTop = (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection 𝒜 1 ≫
      (Proj.basicOpen 𝒜 1).topIso.inv := Proj.basicOpenToSpec_app_top 𝒜 1
  rw [h]
  simp only [Iso.inv_hom_id_assoc, Category.assoc]
  -- `Q` is the inverse of the open immersion `D₊(1) ⟶ Proj 𝒜`, `D₊(1)` being all of `Proj 𝒜`.
  set Q : Proj 𝒜 ⟶ (Proj.basicOpen 𝒜 1).toScheme :=
    (Proj 𝒜).topIso.inv ≫ ((Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv with hQdef
  have hQ : Q ≫ (Proj.basicOpen 𝒜 1).ι = 𝟙 _ := by simp [hQdef]
  have hQ' : ∀ t, Q.appTop ((Proj.basicOpen 𝒜 1).ι.appTop t) = t := fun t => by
    have e : (Proj.basicOpen 𝒜 1).ι.appTop ≫ Q.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, hQ, Scheme.Hom.id_appTop]
    exact congrArg (fun f => CommRingCat.Hom.hom f t) e
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  change Q.appTop _ = _
  rw [← hQ' (structureRingHom 𝒜 r)]
  congr 1

/-- `structureMorphism` is Mathlib's `Proj.toSpecZero` followed by `Spec` of `R ⟶ 𝒜₀`. -/
theorem structureMorphism_eq :
    structureMorphism 𝒜 = Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (zeroHom 𝒜)) := by
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso R).inv]
  ext r
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, appTop_inv_eq, Scheme.Hom.comp_appTop,
    ← CommRingCat.comp_apply, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]
  exact (toSpecZero_appTop_apply 𝒜 r).symm

/-- `Proj` of any graded algebra is separated over `Spec R`: `Proj.toSpecZero` is separated (Mathlib)
and so is `Spec` of any ring homomorphism. -/
theorem isSeparated_structureMorphism : IsSeparated (structureMorphism 𝒜) := by
  rw [structureMorphism_eq]
  infer_instance

/-- If `A` is of finite type over `R`, it is of finite type over `𝒜₀`: the `R`-algebra structure of `A`
factors through `R ⟶ 𝒜₀`, so generators over `R` also generate over `𝒜₀`. -/
theorem finiteType_zero [Algebra.FiniteType R A] : Algebra.FiniteType (𝒜 0) A := by
  have h := ‹Algebra.FiniteType R A›
  rw [← RingHom.finiteType_algebraMap] at h ⊢
  refine RingHom.FiniteType.of_comp_finiteType (f := zeroHom 𝒜) ?_
  exact h

end ProjStructure

section Symmetric

variable (R : CommRingCat.{u}) (J : Type u) [AddCommGroup J] [Module R J]

/-- For the symmetric grading, `R ⟶ 𝒜₀` is surjective (the degree-zero part `(range ι)⁰` is the image of
`R`), so `Spec` of it is a closed immersion. -/
theorem zeroHom_symmetric_surjective : Function.Surjective (zeroHom (symmetricGrading R J)) := by
  rintro ⟨x, hx⟩
  have : x ∈ (1 : Submodule R (SymmetricAlgebra R J)) := by simpa [pow_zero] using hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 this
  exact ⟨r, rfl⟩

/-- The symmetric algebra of a finitely generated `R`-module is of finite type over `R`: it is generated
as an algebra by the image of a finite set of module generators. -/
theorem finiteType_symmetricAlgebra [Module.Finite R J] :
    Algebra.FiniteType R (SymmetricAlgebra R J) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := J)
  refine ⟨⟨s.image (SymmetricAlgebra.ι R J), ?_⟩⟩
  refine eq_top_iff.2 fun a _ => ?_
  clear ‹a ∈ ⊤›
  induction a using SymmetricAlgebra.induction with
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | ι x =>
    have hx : x ∈ Submodule.span R (s : Set J) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hy))
    | zero => simp
    | add y z _ _ hy hz => simpa using Subalgebra.add_mem _ hy hz
    | smul c y _ hy => simpa using Subalgebra.smul_mem _ hy c
  | mul a b ha hb => exact Subalgebra.mul_mem _ ha hb
  | add a b ha hb => exact Subalgebra.add_mem _ ha hb

/-- The structure morphism of `Proj` of the symmetric algebra of a finitely generated module is locally
of finite type. -/
theorem locallyOfFiniteType_structureMorphism_symmetric [Module.Finite R J] :
    LocallyOfFiniteType (structureMorphism (symmetricGrading R J)) := by
  rw [structureMorphism_eq]
  have := finiteType_symmetricAlgebra R J
  have := finiteType_zero (symmetricGrading R J)
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (zeroHom (symmetricGrading R J)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_surjective _ (zeroHom_symmetric_surjective R J)
  infer_instance

/-- The structure morphism of `Proj` of the symmetric algebra of a finitely generated module is
quasi-compact. -/
theorem quasiCompact_structureMorphism_symmetric [Module.Finite R J] :
    QuasiCompact (structureMorphism (symmetricGrading R J)) := by
  rw [structureMorphism_eq]
  have := finiteType_symmetricAlgebra R J
  have := finiteType_zero (symmetricGrading R J)
  infer_instance

end Symmetric

end Hironaka

end
