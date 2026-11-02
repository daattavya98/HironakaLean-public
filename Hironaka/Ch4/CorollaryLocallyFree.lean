/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch4.MainTheoremIICorollaries
public import Hironaka.Compat.CoordinateIdeal
public import Hironaka.Statements

/-!
# Corollary 1 of Main Theorem II with `e = 1`, in the proof of Corollary 2 (p. 145)

"To this sheaf of ideals `J` on `X`, we apply Corollary 1 of main theorem II in which `e = 1`": for a locally
free sheaf `F` with local frames and an invertible subsheaf `M ⊆ F`, a succession of monoidal transformations
with non-singular nowhere dense centers which trivializes the sheaf of ideals `J = coordSubscheme`
(`exists_isTrivializing_coordSubscheme`), with the facts on nowhere dense centers and generic points it uses.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

namespace MonoidalSuccession


end MonoidalSuccession

/-- On a non-singular irreducible scheme the local ring at the generic point is a field (the local rings are
domains, and `Spec` of the local ring at the generic point is a point). -/
theorem isField_stalk_genericPoint {Z : Scheme.{u}} [IrreducibleSpace Z] (hZ : Z.IsNonsingular) :
    IsField (Z.presheaf.stalk (genericPoint Z)) := by
  have hred : ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x) := fun x => by
    have : IsRegularLocalRing (Z.presheaf.stalk x) := hZ x
    have := isDomain_of_isRegularLocalRing (Z.presheaf.stalk x)
    infer_instance
  have : IsReduced Z := isReduced_of_isReduced_stalk Z
  exact isField_stalk_of_closure_mem_irreducibleComponents Z (genericPoint Z)
    (by rw [irreducibleComponents_eq_singleton, (genericPoint_spec Z).def]; rfl)

/-- On a non-singular irreducible scheme, a sheaf of non-zero ideals has a proper stalk ideal nowhere at the
generic point: `J_η = O_η`. -/
theorem stalkIdeal_genericPoint_eq_top {Z : Scheme.{u}} [IrreducibleSpace Z] (hZ : Z.IsNonsingular)
    {K : Subscheme Z} (hK : ∀ z, K.stalkIdeal z ≠ ⊥) : K.stalkIdeal (genericPoint Z) = ⊤ := by
  have hfield := isField_stalk_genericPoint hZ
  by_contra hne
  apply hK (genericPoint Z)
  by_contra hI
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨b, hb⟩ := hfield.mul_inv_cancel ha
  exact hne (Ideal.eq_top_of_isUnit_mem _ haI (IsUnit.of_mul_eq_one b hb))

/-- **The centers are nowhere dense.**  Along a succession with property (1) of Corollary 1 for a (non-empty)
system of sheaves of non-zero ideals on a non-singular irreducible algebraic scheme, every center is nowhere
dense: `ν(K(i)_y) > 0` on the center `D(i)` while the generic point has `K(i)_η = O_η`, so the closed
set `D(i)` misses the generic point of the irreducible scheme `X(i)`, which stays non-singular and
irreducible (`MonoidalTransformation.transform_isAmbient`). -/
theorem MonoidalSuccession.isNowhereDense_of_isTrivializingSteps [Hironaka.HironakaCitedResults.{u}] {e : ℕ} (he : 1 ≤ e) {Z Z' : Scheme.{u}}
    (s : MonoidalSuccession Z Z') :
    ∀ (_ : IsAlgebraicScheme Z) (_ : IrreducibleSpace Z) (_ : Z.IsNonsingular) (K : Fin e → Subscheme Z),
      (∀ k z, (K k).stalkIdeal z ≠ ⊥) → s.IsTrivializingSteps K → s.IsNowhereDense := by
  induction s with
  | nil _ => intro _ _ _ _ _ _; trivial
  | @cons Z₀ B t _ rest ih =>
    intro hZa hZi hZ K hK hs
    obtain ⟨hB, hc, hrest⟩ := hs
    have k0 : Fin e := ⟨0, he⟩
    have hηB : genericPoint Z₀ ∉ B.pts := by
      intro hη
      obtain ⟨c, hc0, hcy⟩ := hc k0
      have hnu := hcy _ hη
      have htop := stalkIdeal_genericPoint_eq_top hZ (hK k0)
      have : Ideal.nu ((K k0).stalkIdeal (genericPoint Z₀)) = 0 :=
        (Subscheme.stalkIdeal_eq_top_iff_nu_eq_zero _ _).mp htop
      rw [this] at hnu
      exact hc0.ne (by exact_mod_cast hnu)
    have hBX : B.pts ≠ Set.univ := fun h => hηB (h ▸ Set.mem_univ _)
    refine ⟨hB, ?_, ?_⟩
    · have hcl : IsClosed B.pts := B.support.isClosed
      rw [hcl.isNowhereDense_iff]
      by_contra hne
      obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.mpr hne
      have hmem : genericPoint Z₀ ∈ interior B.pts :=
        ((genericPoint_spec Z₀).mem_open_set_iff isOpen_interior).mpr ⟨u, Set.mem_univ _, hu⟩
      exact hηB (interior_subset hmem)
    · obtain ⟨hZa', hZ', hZi', -⟩ := MonoidalTransformation.transform_isAmbient hZ hB hBX t
      exact ih hZa' hZi' hZ' _ (fun k z => Subscheme.stalkIdeal_weakTransform_ne_bot hZ t (hK k) z) hrest

open AlgebraicGeometry.Scheme.Modules Hironaka.Scheme.Modules in
/-- **Corollary 1 applied to the sheaf of ideals `J`** (proof of Corollary 2, p. 145: "To this sheaf of ideals
`J` on `X`, we apply Corollary 1 of main theorem II in which `e = 1`.  We let `f : X' → X` be the composition of
a succession of monoidal transformations which we find according to Corollary 1"): for a locally free sheaf `F`
with local frames and an invertible subsheaf `M ⊆ F` there is a succession with non-singular nowhere dense
centers which trivializes `J = coordSubscheme`. -/
theorem exists_isTrivializing_coordSubscheme [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X] [IsLocallyNoetherian X] [IrreducibleSpace X]
    (hX : X.IsNonsingular) {M F : X.Modules} (i : M ⟶ F) [Mono i] (hF : HasLocalFrames F)
    (hM : IsInvertible M) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsNowhereDense ∧
      s.IsTrivializing (fun _ : Fin 1 => coordSubscheme i hF hM) := by
  have hJ : ∀ (_ : Fin 1) (x : X), (coordSubscheme i hF hM).stalkIdeal x ≠ ⊥ := fun _ x => by
    rw [stalkIdeal_coordSubscheme]
    exact coordStalkIdeal_ne_bot i hF hM x
  obtain ⟨Y, s, hs⟩ := MainTheorem.Ch0.exists_isTrivializing_of_isAlgebraicScheme X hX (le_refl 1)
    (fun _ : Fin 1 => coordSubscheme i hF hM) hJ
  exact ⟨Y, s, s.isNowhereDense_of_isTrivializingSteps (le_refl 1) inferInstance inferInstance hX _
    (fun _ x => hJ 0 x) hs.1, hs⟩


end Hironaka
