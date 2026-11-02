/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.LocalRing.Defs
public import Architect
public import Hironaka.Ch3.Transforms

/-!
# A monoidal transform as a ring of fractions of `R[z_v/z_t]` (Ch. I §1, p. 169; Ch. III §2, p. 209)

> If (x₁, …, x_r) is a minimal base of the prime ideal P and if R' is a monoidal transform of R
> with center P, then there exist an index i (1 ≤ i ≤ r) and a prime ideal M' in
> R[x₁/x_i, x₂/x_i, …, x_r/x_i] such that R' = R[x₁/x_i, …, x_r/x_i]_{M'} and
> M' ⊇ M R'[x₁/x_i, …, x_r/x_i] where M = the maximal ideal of R.  (p. 209)

> Then the local ring O_{x'} of X' at x' is a ring of fractions of
> A = O_x[z_{r+1}z_t^{-1}, …, z_s z_t^{-1}] for some t (r + 1 ≤ t ≤ s) with respect to a prime
> ideal M in A.  (p. 169)

The sentence of p. 209 is `MonoidalTransform.exists_index_subring_eq_localization`
(`Hironaka/Ch3/Transforms.lean`, blueprint node `lem:III.2-monoidal-transform-index`), in the
encoding of a monoidal transform as the subring `t.subring` of `Frac(R)`.

In the encoding of this project a monoidal transform is the datum `s = (x, M')` and
`R' = R[x⁻¹P]_{M'}` (`MonoidalTransform`), where `x ∈ P` is *any* non-zero element (the stalk of a
monoidal transformation produces some `x`).  This file turns the sentence of p. 209 into the form
needed for the chart of Remark 1 (p. 169): the element `x` of the datum may be replaced by any
`z_t ∈ P` with `P R' = z_t R'`, compatibly with `R → R'` and through an isomorphism of rings
(`MonoidalTransform.exists_equiv_of_span_eq`, from `MonoidalTransform.exists_subring_eq_of_isUnit`),
and `R[z_t⁻¹P] = R[z_v/z_t : z_v ∈ T]` when `P = (T)`
(`MonoidalTransform.blowupAlgebra_span_eq_adjoin`, from `blowupAlgebra_eq_adjoinDiv`).  Both are
used in `Hironaka/Ch1/ResolutionData.lean`.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

namespace MonoidalTransform

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

/-- `R[z⁻¹P]` for `P = (T)` is the ring `R[t/z : t ∈ T]` (p. 169: `A = O_x[z_{r+1}z_t^{-1}, …,
z_s z_t^{-1}]`, with `P = (z_{r+1}, …, z_s)`); `blowupAlgebra_eq_adjoinDiv` for a finite set `T`. -/
theorem blowupAlgebra_span_eq_adjoin (T : Finset R) (z : R) :
    blowupAlgebra R (Ideal.span (T : Set R)) z =
      Algebra.adjoin R ((fun t => algebraMap R (FractionRing R) t /
        algebraMap R (FractionRing R) z) '' (T : Set R)) := by
  have hrange : Set.range (fun i : Fin T.card => ((T.equivFin.symm i : T) : R)) = (T : Set R) := by
    ext t
    refine ⟨?_, fun ht => ⟨T.equivFin ⟨t, ht⟩, by simp⟩⟩
    rintro ⟨i, rfl⟩
    exact (T.equivFin.symm i).2
  rw [blowupAlgebra_eq_adjoinDiv (z := fun i : Fin T.card => ((T.equivFin.symm i : T) : R))
    (by rw [hrange]) z, adjoinDiv, ← hrange]
  congr 1
  ext y
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-- p. 209 and p. 169 ("for some `t`", "with respect to a prime ideal `M` in `A`"): if `P R' = z_t R'`
for a `z_t ∈ P`, then `R'` is, compatibly with `R → R'` and through an isomorphism of rings, the
localization at a prime ideal of `R[z_t⁻¹P]` (`s'.x = z_t`); i.e. in the data `(x, M')` of the monoidal
transform `R'`, `x` can be taken to be `z_t`.

Proof: `z_t R' = x R'` gives `x u = z_t` with `u` a unit of `R'`; then the monoidal transform with data
`(z_t, M'')` has the same subring of `Frac(R)` as `s` (`exists_subring_eq_of_isUnit`, the second half of
the claim of p. 209), hence is isomorphic to `s` over `R`. -/
theorem exists_equiv_of_span_eq (s : MonoidalTransform R P) {zt : R} (hzt : zt ∈ P)
    (hspan : Ideal.span {s.toRing zt} = P.map s.toRing) :
    ∃ (s' : MonoidalTransform R P) (e : s.ring ≃+* s'.ring),
      s'.x = zt ∧ e.toRingHom.comp s.toRing = s'.toRing := by
  obtain ⟨u, hu⟩ : Associated s.xR (s.toRing zt) :=
    Ideal.span_singleton_eq_span_singleton.mp (s.span_xR_eq_map.trans hspan.symm)
  obtain ⟨h0, M'', hM, hle, hsub⟩ := s.exists_subring_eq_of_isUnit hzt u.isUnit hu
  set s' : MonoidalTransform R P := ⟨zt, hzt, h0, M'', hM, hle⟩ with hs'
  refine ⟨s', s.ringEquivOfSubringEq s' hsub.symm, rfl, ?_⟩
  ext r
  apply s'.injective_toFractionRing
  show s'.toFractionRing (s.ringEquivOfSubringEq s' hsub.symm (s.toRing r)) =
    s'.toFractionRing (s'.toRing r)
  rw [toFractionRing_ringEquivOfSubringEq, s.toFractionRing_toRing, s'.toFractionRing_toRing]

end MonoidalTransform

end Hironaka
