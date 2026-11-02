/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch4.CorollaryLocallyFree
public import Hironaka.Statements

/-!
# The total transform along a trivializing succession is invertible (Ch. 0, proof of Corollary 2, p. 145)

Hironaka, Ch. 0 §5, proof of Corollary 2 (p. 145): "We then obtain an invertible subsheaf `L` of `f*(F)` such
that `f*(M) = f^{-1}(J)L`".  The sheaf of ideals `f⁻¹(J)·O_{X'}` is invertible: this is the content of the
phrase "we find according to Corollary 1" (it is not argued in the paper).  By the definition of the
weak transform (Remark 2, p. 214) `f_i⁻¹(J(i)) = J(i+1)·P_i^{d_i}` with `P_i` the invertible exceptional ideal
of `f_i`; iterating, and using `J(r) = O_{X(r)}`, the total transform of `J` by the composite is a product of
total transforms of exceptional ideals, hence invertible.

* `Hironaka.Subscheme.IsInvertibleIdeal.totalTransform_composite`: pull-backs of invertible sheaves of ideals
  along a succession are invertible;
* `Hironaka.MonoidalSuccession.isInvertibleIdeal_totalTransform_composite`: if the weak transform of `K` by a
  succession with property (1) of Corollary 1 is the unit ideal, then `f⁻¹(K)` is invertible;
* `Hironaka.MonoidalSuccession.isAmbient_of_isTrivializingSteps`: the schemes of the succession stay
  non-singular, irreducible and algebraic.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

namespace MonoidalSuccession

/-- The total transform of an invertible sheaf of ideals along the composite of a succession is invertible. -/
theorem isInvertibleIdeal_totalTransform_composite_of_isInvertibleIdeal {Z Z' : Scheme.{u}}
    (s : MonoidalSuccession Z Z') :
    ∀ {E : Subscheme Z}, E.IsInvertibleIdeal →
      (Subscheme.totalTransform s.composite E).IsInvertibleIdeal := by
  induction s with
  | nil _ =>
    intro E hE
    simpa [composite] using hE
  | cons B t rest ih =>
    intro E hE
    simp only [composite, Subscheme.totalTransform_comp]
    exact ih (t.isInvertibleIdeal_totalTransform hE)

/-- The schemes along a succession with property (1) of Corollary 1 stay algebraic, non-singular and
irreducible. -/
theorem isAmbient_of_isTrivializingSteps [Hironaka.HironakaCitedResults.{u}] {e : ℕ} (he : 1 ≤ e) {Z Z' : Scheme.{u}}
    (s : MonoidalSuccession Z Z') :
    ∀ (_ : IsAlgebraicScheme Z) (_ : IrreducibleSpace Z) (_ : Z.IsNonsingular) (K : Fin e → Subscheme Z),
      (∀ k z, (K k).stalkIdeal z ≠ ⊥) → s.IsTrivializingSteps K →
        IsAlgebraicScheme Z' ∧ IrreducibleSpace Z' ∧ Z'.IsNonsingular := by
  induction s with
  | nil _ => intro hZa hZi hZ _ _ _; exact ⟨hZa, hZi, hZ⟩
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
    obtain ⟨hZa', hZ', hZi', -⟩ := MonoidalTransformation.transform_isAmbient hZ hB hBX t
    exact ih hZa' hZi' hZ' _ (fun k z => Subscheme.stalkIdeal_weakTransform_ne_bot hZ t (hK k) z) hrest

/-- **The total transform `f⁻¹(K)` is invertible** along a succession with property (1) of Corollary 1 for the
single sheaf of non-zero ideals `K` whose weak transform at the end is the unit ideal. -/
theorem isInvertibleIdeal_totalTransform_composite [Hironaka.HironakaCitedResults.{u}] {Z Z' : Scheme.{u}} (s : MonoidalSuccession Z Z') :
    ∀ (_ : IsAlgebraicScheme Z) (_ : Z.IsNonsingular) (K : Subscheme Z),
      (∀ z, K.stalkIdeal z ≠ ⊥) → s.IsTrivializingSteps (fun _ : Fin 1 => K) →
      (∀ z, (s.weakTransformFamily (fun _ : Fin 1 => K) 0).stalkIdeal z = ⊤) →
        (Subscheme.totalTransform s.composite K).IsInvertibleIdeal := by
  induction s with
  | nil _ =>
    intro _ _ K _ _ htop
    have : K = ⊤ := Subscheme.ext_stalkIdeal fun z => by
      rw [Subscheme.stalkIdeal_top_eq]; exact htop z
    simp only [composite, Subscheme.totalTransform_id]
    rw [this]
    exact Subscheme.isInvertibleIdeal_top
  | @cons Z₀ B t _ rest ih =>
    intro hZa hZ K hK hs htop
    obtain ⟨hB, -, hrest⟩ := hs
    have hX' := MonoidalTransformation.isNonsingular_and_isNonsingular_exceptional t hZ hB.isNonsingular
    have hmul : ∃ m : ℕ, Subscheme.totalTransform t.f K = Subscheme.weakTransform t K * t.exceptional ^ m := by
      by_cases h : ∃ ξ : Z₀, IsGenericPoint ξ B.pts
      · obtain ⟨ξ, hξ⟩ := h
        have : IsRegularLocalRing (Z₀.presheaf.stalk ξ) := hZ ξ
        obtain ⟨m, hm⟩ := Ideal.exists_nu_eq_natCast (hK ξ)
        exact ⟨m, Subscheme.totalTransform_eq_weakTransform_mul_pow hZ
          (hB.isNonsingular_of_isGenericPoint hξ) t K hξ hm⟩
      · exact ⟨0, by
          rw [pow_zero, mul_one]
          exact (Subscheme.weakTransform_eq_totalTransform_of_not_exists t K h).symm⟩
    obtain ⟨m, hm⟩ := hmul
    simp only [composite, Subscheme.totalTransform_comp]
    rw [hm, Subscheme.totalTransform_mul, Subscheme.totalTransform_pow]
    have hZa' := t.isAlgebraicScheme
    refine Subscheme.IsInvertibleIdeal.mul ?_ (Subscheme.IsInvertibleIdeal.pow ?_ m)
    · exact ih hZa' hX'.1 _ (fun z => Subscheme.stalkIdeal_weakTransform_ne_bot hZ t (hK) z) hrest htop
    · exact isInvertibleIdeal_totalTransform_composite_of_isInvertibleIdeal rest t.invertible

end MonoidalSuccession

end Hironaka
