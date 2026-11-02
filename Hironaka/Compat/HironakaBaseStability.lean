/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Compat.RegularLocalRing
public import Hironaka.Compat.AdicCompletionRegular
public import Hironaka.Statements

/-!
# Compatibility layer: ring-theoretic helpers for the stability of the class 𝔅 (p. 161)

Hironaka (Ch. I, p. 161) states, without proof, that the class 𝔅 contains every field of
characteristic zero (a), is stable under completion (b), and under passage to the local rings of
finite-type algebras (c).  For (a) and (b) the only non-formal ingredient is that the canonical
map from a *complete* local ring `S` to its completion `Ŝ` is an isomorphism, so that
`A ⊗_S Ŝ ≅ A` and condition (ii) holds trivially.  This file collects the helpers that do not
mention the class 𝔅:

* `regularLocus` (the regular locus of `Spec A`, used by the helpers below);
* `mem_regularLocus_iff_comap_ringEquiv`: the regular locus is transported along ring
  isomorphisms;
* `mem_regularLocus_tensor_iff_of_bijective`: if `S → T` is bijective, the regular locus of
  `A ⊗_S T` is the preimage of that of `A`;
* `isAdicComplete_maximalIdeal_of_field`: a field is complete for its (zero) maximal ideal;
* `HasCompletionRegularLocus`: condition (ii) of p. 161 written without the class 𝔅, so that the
  proof of property (c) (`Hironaka/Compat/ClassBLocalization.lean`) can be imported by
  `Hironaka/Ch0/AlgebraicScheme.lean`;
* `hasCompletionRegularLocus_of_isAdicComplete`: (ii) holds for a complete local ring.
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

noncomputable section

universe u

namespace Hironaka


/-- The regular locus is transported along ring isomorphisms: a prime `q` of `T'` is regular iff
its contraction along an isomorphism `e : T ≃+* T'` is. -/
theorem mem_regularLocus_iff_comap_ringEquiv {T T' : Type u} [CommRing T] [CommRing T']
    (e : T ≃+* T') (q : PrimeSpectrum T') :
    q ∈ regularLocus T' ↔ PrimeSpectrum.comap (e : T →+* T') q ∈ regularLocus T := by
  have H : (PrimeSpectrum.comap (e : T →+* T') q).asIdeal.primeCompl.map e.toMonoidHom =
      q.asIdeal.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, PrimeSpectrum.comap_asIdeal,
      Ideal.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e.symm x, by simpa using hx, by simp⟩
  let E := IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime (PrimeSpectrum.comap (e : T →+* T') q).asIdeal)
    (Localization.AtPrime q.asIdeal) e H
  constructor
  · intro h
    have h' : IsRegularLocalRing (Localization.AtPrime q.asIdeal) := h
    exact IsRegularLocalRing.of_ringEquiv E.symm
  · intro h
    have h' : IsRegularLocalRing
        (Localization.AtPrime (PrimeSpectrum.comap (e : T →+* T') q).asIdeal) := h
    exact IsRegularLocalRing.of_ringEquiv E

/-- If `S → T` is bijective, then `A → A ⊗_S T` is an isomorphism, so the regular locus of
`A ⊗_S T` is the preimage of that of `A` under the canonical map. -/
theorem mem_regularLocus_tensor_iff_of_bijective {S A T : Type u} [CommRing S] [CommRing A]
    [CommRing T] [Algebra S A] [Algebra S T] (h : Function.Bijective (algebraMap S T))
    (q : PrimeSpectrum (A ⊗[S] T)) :
    q ∈ regularLocus (A ⊗[S] T) ↔
      PrimeSpectrum.comap (algebraMap A (A ⊗[S] T)) q ∈ regularLocus A := by
  have hb : Function.Bijective (algebraMap A (A ⊗[S] T)) := by
    have := Algebra.TensorProduct.includeLeft_bijective (R := S) (S := S) (A := A) (B := T) h
    exact this
  exact mem_regularLocus_iff_comap_ringEquiv
    (RingEquiv.ofBijective (algebraMap A (A ⊗[S] T)) hb) q

/-- Condition (ii) of p. 161 (the singular locus of `Spec (A ⊗_S Ŝ)` is the preimage of that of
`Spec A`, stated through the regular loci), for a local ring `S`, without the class 𝔅.  The class
`IsHironakaBase` (in `Hironaka/Ch0/AlgebraicScheme.lean`) is: noetherian, residue characteristic
zero, and this condition. -/
def HasCompletionRegularLocus (S : Type u) [CommRing S] [IsLocalRing S] : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra S A] [Algebra.FiniteType S A]
    (q : PrimeSpectrum (TensorProduct S A (AdicCompletion (maximalIdeal S) S))),
    q ∈ regularLocus _ ↔
      PrimeSpectrum.comap
        (algebraMap A (TensorProduct S A (AdicCompletion (maximalIdeal S) S))) q ∈
          regularLocus A

/-- Condition (ii) holds for a local ring that is complete for its maximal ideal (the canonical
map to the completion is bijective). -/
theorem hasCompletionRegularLocus_of_isAdicComplete (S : Type u) [CommRing S] [IsLocalRing S]
    [IsAdicComplete (maximalIdeal S) S] : HasCompletionRegularLocus S := fun _ _ _ _ q =>
  mem_regularLocus_tensor_iff_of_bijective (AdicCompletion.of_bijective (maximalIdeal S) S) q

/-- A field is complete for its maximal ideal `(0)`. -/
theorem isAdicComplete_maximalIdeal_of_field (k : Type u) [Field k] :
    IsAdicComplete (maximalIdeal k) k := by
  have hbot : maximalIdeal k = ⊥ := maximalIdeal_eq_bot
  rw [hbot]
  refine { toIsHausdorff := ⟨fun x hx => ?_⟩,
           toIsPrecomplete := ⟨fun f hf => ⟨f 1, fun n => ?_⟩⟩ }
  · have := hx 1
    simpa [SModEq.zero] using this
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact SModEq.sub_mem.mpr (by simp)
    · have h1 : f 1 = f n := by
        have := SModEq.sub_mem.mp (hf (m := 1) (n := n) hn)
        simpa [sub_eq_zero] using this
      rw [h1]
      exact SModEq.refl _
