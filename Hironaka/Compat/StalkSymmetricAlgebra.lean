/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch0.BlowingUpProj
public import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# The symmetric algebra of the sections and of the stalk of a sheaf of modules

For a locally ringed space `X` and a sheaf of modules `J` on `X` (Ch. 0 §2, p. 125) the paper writes
`A(U) = Γ(U, O_X)`, `J(U) = Γ(U, J)`, `S(U) = S_{A(U)}(J(U))`, and for `x ∈ U` "a canonical homomorphism of
`S(U)` to `S_{O_x}(J_x)`".  This file gives these objects and the canonical homomorphism, which maps the
homogeneous elements of degree `n` to homogeneous elements of degree `n`.  None of this is a claim of the paper.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace Hironaka

universe u

variable {X : LocallyRingedSpace.{u}} (J : OModules.{u} X)

/-- `A(U) = Γ(U, O_X)`, as a commutative ring. -/
abbrev sectionsRing (U : Opens X) : CommRingCat.{u} := X.presheaf.obj (op U)

/-- `J(U) = Γ(U, J)`, as a module over `A(U)`. -/
abbrev sectionsMod (U : Opens X) : Type u := J.val.obj (op U)

instance (U : Opens X) : AddCommGroup (sectionsMod J U) := inferInstanceAs (AddCommGroup (J.val.obj (op U)))

instance (U : Opens X) : Module (sectionsRing U) (sectionsMod J U) :=
  inferInstanceAs (Module ((ringCatSheaf X).val.obj (op U)) (J.val.obj (op U)))

/-- `S(U) = S_{A(U)}(J(U))`, the symmetric algebra of the sections over `U`. -/
abbrev symSections (U : Opens X) : Type u := SymmetricAlgebra (sectionsRing U) (sectionsMod J U)

/-- `O_x`, the stalk of the structure sheaf at `x`. -/
abbrev stalkRing (x : X.toTopCat) : CommRingCat.{u} := X.presheaf.stalk x

/-- `J_x`, the stalk of the sheaf of modules at `x`. -/
abbrev stalkMod (x : X.toTopCat) : Type u :=
  ↑(TopCat.Presheaf.stalk (C := Ab.{u}) J.val.presheaf x)

instance (x : X.toTopCat) : AddCommGroup (stalkMod J x) :=
  inferInstanceAs (AddCommGroup (TopCat.Presheaf.stalk (C := Ab.{u}) J.val.presheaf x))

instance (x : X.toTopCat) : Module (stalkRing x) (stalkMod J x) :=
  let M' : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat.{u}) := J.val
  (inferInstance : Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk (C := Ab.{u}) M'.presheaf x))

/-- `S_{O_x}(J_x)`. -/
abbrev symStalk (x : X.toTopCat) : Type u := SymmetricAlgebra (stalkRing x) (stalkMod J x)

variable {J}

/-- The germ map `A(U) → O_x`. -/
def germRing {U : Opens X} {x : X.toTopCat} (hx : x ∈ U) : sectionsRing U →+* stalkRing x :=
  (X.presheaf.germ U x hx).hom

/-- The germ map `J(U) → J_x`. -/
def germMod {U : Opens X} {x : X.toTopCat} (hx : x ∈ U) : sectionsMod J U →+ stalkMod J x :=
  (TopCat.Presheaf.germ (C := Ab.{u}) J.val.presheaf U x hx).hom

theorem germMod_smul {U : Opens X} {x : X.toTopCat} (hx : x ∈ U) (r : sectionsRing U)
    (m : sectionsMod J U) : germMod hx (r • m) = germRing hx r • germMod hx m := by
  let M' : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat.{u}) := J.val
  exact PresheafOfModules.germ_smul (R := X.presheaf) M' x U hx r m

/-- The algebra structure of `S_{O_x}(J_x)` over `A(U)` through the germ map (a local instance, used to state
the canonical homomorphism `S(U) → S_{O_x}(J_x)`). -/
@[instance_reducible]
def germAlgebra {U : Opens X} {x : X.toTopCat} (hx : x ∈ U) : Algebra (sectionsRing U) (symStalk J x) :=
  ((algebraMap (stalkRing x) (symStalk J x)).comp (germRing hx)).toAlgebra

/-- The canonical homomorphism `S(U) → S_{O_x}(J_x)` (p. 125: "for every `x ∈ U`, we have a canonical homomorphism of
`S(U)` to `S_{O_x}(J_x)`"), induced by the germ maps `A(U) → O_x` and `J(U) → J_x`. -/
def germSym {U : Opens X} {x : X.toTopCat} (hx : x ∈ U) : symSections J U →+* symStalk J x :=
  letI := germAlgebra (J := J) hx
  (SymmetricAlgebra.lift
    { toFun := fun m => SymmetricAlgebra.ι (stalkRing x) (stalkMod J x) (germMod hx m)
      map_add' := fun a b => by simp
      map_smul' := fun r m => by
        simp only [germMod_smul, map_smul, RingHom.id_apply]
        exact (Algebra.smul_def (germRing hx r) _) }).toRingHom

theorem germSym_ι {U : Opens X} {x : X.toTopCat} (hx : x ∈ U) (m : sectionsMod J U) :
    germSym hx (SymmetricAlgebra.ι (sectionsRing U) (sectionsMod J U) m) =
      SymmetricAlgebra.ι (stalkRing x) (stalkMod J x) (germMod hx m) := by
  let _ := germAlgebra (J := J) hx
  exact SymmetricAlgebra.lift_ι_apply _ m

theorem germSym_algebraMap {U : Opens X} {x : X.toTopCat} (hx : x ∈ U) (r : sectionsRing U) :
    germSym hx (algebraMap (sectionsRing U) (symSections J U) r) =
      algebraMap (stalkRing x) (symStalk J x) (germRing hx r) := by
  let _ := germAlgebra (J := J) hx
  exact (SymmetricAlgebra.lift _).commutes r

/-- The canonical homomorphism maps homogeneous elements of degree `n` to homogeneous elements of degree `n`. -/
theorem germSym_mem_grading {U : Opens X} {x : X.toTopCat} (hx : x ∈ U) (n : ℕ)
    {ξ : symSections J U} (hξ : ξ ∈ ProjDegreeOne.symmetricGrading (sectionsRing U) (sectionsMod J U) n) :
    germSym hx ξ ∈ ProjDegreeOne.symmetricGrading (stalkRing x) (stalkMod J x) n := by
  induction n generalizing ξ with
  | zero =>
    simp only [ProjDegreeOne.symmetricGrading, pow_zero, Submodule.mem_one] at hξ ⊢
    obtain ⟨r, rfl⟩ := hξ
    exact ⟨germRing hx r, (germSym_algebraMap hx r).symm⟩
  | succ n ih =>
    simp only [ProjDegreeOne.symmetricGrading, pow_succ] at hξ ⊢
    refine Submodule.mul_induction_on hξ (fun m hm k hk => ?_) (fun a b ha hb => ?_)
    · rw [map_mul]
      refine Submodule.mul_mem_mul (ih hm) ?_
      obtain ⟨j, rfl⟩ := hk
      rw [germSym_ι]
      exact ⟨_, rfl⟩
    · rw [map_add]; exact add_mem ha hb

end Hironaka

end
