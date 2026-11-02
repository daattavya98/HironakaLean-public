/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Hironaka.Compat.ProjectiveVocabulary

/-!
# A projective `B`-scheme is proper over `B` (vocabulary of the Corollary of Main Theorem I, p. 132)

The second half of the vocabulary of `Hironaka/Compat/ProjectiveVocabulary.lean`: for `H = B[T₀, …, T_{n-1}] ⧸ 𝔞`
with its natural grading,
* `H` is a finitely generated algebra over `B` and over its degree-zero part `H₀`;
* the structure morphism `projStructure 𝔞 : Proj H → Spec H₀ → Spec B` is proper (Mathlib's properness of `Proj` over
  `Spec H₀`, and `Spec H₀ → Spec B` is a closed immersion since `B → H₀` is surjective);
* hence a projective `B`-scheme (`IsProjectiveOver X p`) is locally of finite type, quasi-compact and separated over
  `B`, i.e. an algebraic `B`-scheme in the sense of pp. 118–119.

Nothing here is printed: it is the dictionary between the p. 132 definition of "projective" and the p. 118–119 words
"algebraic `B`-scheme".
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {B : Type u} [Field B] {n : ℕ} (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))

/-- `H = B[T] ⧸ 𝔞` is a finitely generated `B`-algebra. -/
instance finiteType_quotient : Algebra.FiniteType B (MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal) :=
  inferInstance

/-- The scalar tower `B → H₀ → H`. -/
instance isScalarTower_quotientGrading_zero :
    IsScalarTower B (quotientGrading 𝔞 0) (MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal) :=
  IsScalarTower.of_algebraMap_eq (R := B) (S := quotientGrading 𝔞 0)
    (A := MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal) fun _ => rfl

/-- `H` is a finitely generated algebra over its degree-zero part `H₀`. -/
instance finiteType_quotientGrading_zero :
    Algebra.FiniteType (quotientGrading 𝔞 0) (MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal) :=
  Algebra.FiniteType.of_restrictScalars_finiteType B (quotientGrading 𝔞 0) _

/-- `Spec H₀ → Spec B` is a closed immersion (`B → H₀` is surjective). -/
instance isClosedImmersion_specMap_quotientGrading_zero :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap B (quotientGrading 𝔞 0)))) :=
  IsClosedImmersion.spec_of_surjective _ (algebraMap_quotientGrading_zero_surjective 𝔞)

/-- The structure morphism `Proj H → Spec B` is proper. -/
instance isProper_projStructure : IsProper (projStructure 𝔞) := by
  unfold projStructure
  infer_instance

namespace IsProjectiveOver

variable {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of B)}

/-- A projective `B`-scheme is proper over `B`. -/
theorem isProper (hp : IsProjectiveOver X p) : IsProper p := by
  obtain ⟨n, 𝔞, e, rfl⟩ := hp
  infer_instance

/-- A projective `B`-scheme is locally of finite type over `B`. -/
theorem locallyOfFiniteType (hp : IsProjectiveOver X p) : LocallyOfFiniteType p := by
  have := hp.isProper
  infer_instance

/-- A projective `B`-scheme is quasi-compact over `B`. -/
theorem quasiCompact (hp : IsProjectiveOver X p) : QuasiCompact p := by
  have := hp.isProper
  infer_instance

/-- A projective `B`-scheme is separated over `B`. -/
theorem isSeparated (hp : IsProjectiveOver X p) : IsSeparated p := by
  have := hp.isProper
  infer_instance

/-- Projectivity is invariant under isomorphisms of `B`-schemes. -/
theorem of_iso {X' : Scheme.{u}} (e : X' ≅ X) (hp : IsProjectiveOver X p) :
    IsProjectiveOver X' (e.hom ≫ p) := by
  obtain ⟨n, 𝔞, e', rfl⟩ := hp
  exact ⟨n, 𝔞, e ≪≫ e', by simp⟩

/-- `Proj H` itself, with its structure morphism, is projective. -/
theorem projStructure : IsProjectiveOver (Proj (quotientGrading 𝔞)) (Hironaka.projStructure 𝔞) :=
  ⟨n, 𝔞, Iso.refl _, by simp⟩

end IsProjectiveOver

end Hironaka
