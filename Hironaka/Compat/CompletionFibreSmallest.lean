/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Architect
public import Hironaka.Compat.MainISystem
public import Hironaka.Ch4.ImplicationsAB
public import Hironaka.Ch4.CompletionFibre

/-!
# Main Theorem I(n), p. 175: the smallest subscheme `C` of `V₀(r)` with `Ĉ = c_r⁻¹(C)`

> Therefore, we can find a reduced irreducible subscheme `C` of `V₀(r)` such that `Ĉ = c_r⁻¹(C)`.  In fact, we take
> the smallest subscheme `C` of `V₀(r)` such that `Ĉ = c_r⁻¹(C)`.  (p. 175)

The Corollary of Lemma (AB.3) (p. 296) and its variant for non-reduced `B̂` (p. 316) are proved in Ch. IV
(`Ch4/ImplicationsAB.lean`: `Completion.exists_unique_isReduced_totalTransform`; `Ch4/CompletionFibre.lean`:
`Completion.exists_unique_totalTransform`) for a NON-SINGULAR scheme `X`, a SIMPLE point `x₀` that is closed, and a subscheme
`B̂` whose image is the closed point `x̂₀`.  Here `Y` is the singular scheme `V₀(r)` of an arbitrary algebraic scheme and the
point `x` is an arbitrary (not necessarily closed) point of an arbitrary algebraic scheme, so the image `c(Ĉ)` is only a
subset of the fibre `g⁻¹(x)` and the scheme `C` is its scheme-theoretic closure.

Contents.
* `AB.completionClosedPoint`, `AB.c0_apply_completionClosedPoint`, `AB.eq_completionClosedPoint_of_c0_apply_eq`,
  `AB.isIso_residueFieldMap_c0_completionClosedPoint`, `AB.fiberIdeal_c0_completionClosedPoint`: the facts about
  `c₀ : X̂₀ → X` at the closed point `x̂` of `Spec(Ŝ)` that Ch. IV proves for a simple point (`c0_apply_xhat0`,
  `eq_xhat0_of_c0_apply_eq`, `isIso_residueFieldMap_c0_xhat0`, `fiberIdeal_c0_xhat0`), for an arbitrary noetherian local ring
  `S = O_{X,x}` (`c₀⁻¹(x) = {x̂}`, `κ(x) ≅ κ(x̂)`, `m_x Ŝ = m̂`), from Mathlib's `AdicCompletion` API.
* `exists_sub_mem_ker_stalkMap_fiberι`, `ker_stalkMap_fiberι_le_fiberIdeal`,
  `exists_sub_mem_fiberIdeal_of_isPullback_completion`: `O_{Ŷ,ŷ} = c^#(O_{Y,y}) + m̂ O_{Ŷ,ŷ}` at a point `ŷ` of `ĝ⁻¹(x̂)`,
  i.e. `Ŝ_s = S_s + M̂ Ŝ_s` of the Corollary of (AB.3), here from the isomorphism of the scheme-theoretic fibres
  `ĝ⁻¹(x̂) ≅ g⁻¹(x)` (a base change of `κ(x) ≅ κ(x̂)`) and the surjectivity of `O_{Y,y}` onto the local ring of the fibre.
* `fiberIdeal_eq_map_of_isPullback_completion`: `m̂ O_{Ŷ,ŷ} = (m_x O_{Y,y}) O_{Ŷ,ŷ}`.
* `mem_pts_of_apply_mem_closure_image`: `c⁻¹(closure c(Ĉ)) = Ĉ` as sets (`c` is a homeomorphism `ĝ⁻¹(x̂) → g⁻¹(x)`,
  `AB.exists_homeomorph_preimage_of_isPullback`).
* `mem_stalkIdeal_map_of_stalkMap_mem`: for the integral scheme `Ĉ`, a function whose pull-back vanishes on `Ĉ` near `ŷ`
  vanishes on the scheme-theoretic image of `Ĉ` near `c(ŷ)` (germs on an integral scheme are injective).
* `exists_reduced_irreducible_totalTransform_eq`: `C` is the scheme-theoretic image `c(Ĉ)` (the reduced subscheme on the
  closure of `c(Ĉ)`), `c⁻¹(C) ⊆ Ĉ` is the statement `I_ŷ ⊆ (I_ŷ ∩ O_{Y,y}) O_{Ŷ,ŷ}` proved by the Corollary's argument
  (`I ⊇ M̂`, `O_{Ŷ,ŷ} = O_{Y,y} + M̂`), and minimality is the adjunction `c⁻¹ ⊣ c_*` of ideal sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

/-! ### The completion at an arbitrary point of an algebraic scheme

The facts about `c₀ : X̂₀ → X` at the closed point of `Spec Ŝ` that Ch. IV proves for a simple point
`x₀` (`c0_apply_xhat0`, `isIso_residueFieldMap_c0_xhat0`, `fiberIdeal_c0_xhat0`,
`eq_xhat0_of_c0_apply_eq`) use regularity only to know that `S = O_{X,x₀}` is a noetherian local
ring; here they are restated for an arbitrary noetherian local ring `S`, which is all that is needed
when `X` is an arbitrary algebraic scheme (p. 175). -/

namespace AB

section GeneralCompletion

variable {X : Scheme.{u}} (x : X) [IsNoetherianRing (X.presheaf.stalk x)]

/-- The closed point of `X̂₀ = Spec(Ŝ)`, for an arbitrary noetherian local ring `S = O_{X,x}`. -/
noncomputable def completionClosedPoint : xHat0 X x :=
  IsLocalRing.closedPoint (Shat X x)

theorem c0_apply_completionClosedPoint : (c0 X x).base (completionClosedPoint x) = x := by
  show X.fromSpecStalk x (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
    (Shat X x))) (IsLocalRing.closedPoint (Shat X x))) = x
  have hloc : IsLocalHom (algebraMap (X.presheaf.stalk x) (Shat X x)) := inferInstance
  have : IsLocalHom (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (Shat X x))).hom := hloc
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

theorem stalkMap_c0_completionClosedPoint :
    (c0 X x).stalkMap (completionClosedPoint x) ≫
        (stalkClosedPointIso (CommRingCat.of (Shat X x))).hom =
      (X.presheaf.stalkCongr (Inseparable.of_eq (c0_apply_completionClosedPoint x))).hom ≫
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (Shat X x)) := by
  have hloc : IsLocalHom (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) (Shat X x))).hom :=
    (inferInstance : IsLocalHom (algebraMap (X.presheaf.stalk x) (Shat X x)))
  have := (SpecToEquivOfLocalRing X (CommRingCat.of (Shat X x))).apply_symm_apply ⟨x, _, hloc⟩
  obtain ⟨h1, h'⟩ := SpecToEquivOfLocalRing_eq_iff.mp this
  exact h'

/-- `c_0⁻¹(x) = {x̂}`: the only point of `Spec(Ŝ)` over `x` is the closed point (`m_x Ŝ` is the
maximal ideal of `Ŝ`). -/
theorem eq_completionClosedPoint_of_c0_apply_eq (p : xHat0 X x) (hp : (c0 X x).base p = x) :
    p = completionClosedPoint x := by
  let φ := CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (Shat X x))
  have hq : (Spec.map φ).base p = closedPoint (X.presheaf.stalk x) := by
    apply (X.fromSpecStalk x).isEmbedding.injective
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hp
  have hcomap : (p : PrimeSpectrum (Shat X x)).asIdeal.comap
      (algebraMap (X.presheaf.stalk x) (Shat X x)) = maximalIdeal (X.presheaf.stalk x) :=
    congrArg PrimeSpectrum.asIdeal hq
  have hle : maximalIdeal (Shat X x) ≤ (p : PrimeSpectrum (Shat X x)).asIdeal := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap, hcomap]
  exact PrimeSpectrum.ext (le_antisymm
    (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum (Shat X x)).isPrime.ne_top) hle)

/-- The local homomorphism induced by `c_0` at the closed point is, up to isomorphisms, `S → Ŝ`:
so it induces an isomorphism of residue fields and `m_x` generates the maximal ideal. -/
theorem bijective_residueField_map_stalkMap_c0_completionClosedPoint :
    Function.Bijective (ResidueField.map ((c0 X x).stalkMap (completionClosedPoint x)).hom) := by
  let ι := X.presheaf.stalkCongr (Inseparable.of_eq (c0_apply_completionClosedPoint x))
  let κ : (xHat0 X x).presheaf.stalk (completionClosedPoint x) ≅ CommRingCat.of (Shat X x) :=
    stalkClosedPointIso (CommRingCat.of (Shat X x))
  have hκ : IsLocalHom κ.inv.hom := isLocalHom_of_isIso _
  have hι : IsLocalHom ι.hom.hom := isLocalHom_of_isIso _
  have hφ0 : IsLocalHom (algebraMap (X.presheaf.stalk x) (Shat X x)) := inferInstance
  have h1 : IsLocalHom ((algebraMap (X.presheaf.stalk x) (Shat X x)).comp ι.hom.hom) :=
    RingHom.isLocalHom_comp _ _
  have h2 : IsLocalHom (κ.inv.hom.comp
      ((algebraMap (X.presheaf.stalk x) (Shat X x)).comp ι.hom.hom)) :=
    RingHom.isLocalHom_comp _ _
  have e1 : (c0 X x).stalkMap (completionClosedPoint x) =
      (ι.hom ≫ CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (Shat X x))) ≫ κ.inv :=
    (Iso.eq_comp_inv _).mpr (stalkMap_c0_completionClosedPoint x)
  have e2 : ((c0 X x).stalkMap (completionClosedPoint x)).hom = κ.inv.hom.comp
      ((algebraMap (X.presheaf.stalk x) (Shat X x)).comp ι.hom.hom) := by
    rw [e1]; rfl
  have hφ : IsLocalHom (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) (Shat X x))).hom :=
    (inferInstance : IsLocalHom (algebraMap (X.presheaf.stalk x) (Shat X x)))
  rw [residueField_map_congr e2, ResidueField.map_comp, ResidueField.map_comp]
  exact (bijective_residueField_map_of_isIso κ.inv).comp
    ((AdicCompletion.residueField_map_bijective _).comp
      (bijective_residueField_map_of_isIso ι.hom))

/-- `m_x Ŝ` is the maximal ideal of `Ŝ`: the ideal `m_x O_{X̂₀,x̂}` of the fibre of `c₀` over `x̂`
is the maximal ideal of `O_{X̂₀,x̂}`. -/
theorem fiberIdeal_c0_completionClosedPoint :
    fiberIdeal (c0 X x) (completionClosedPoint x) =
      maximalIdeal ((xHat0 X x).presheaf.stalk (completionClosedPoint x)) := by
  let ι := X.presheaf.stalkCongr (Inseparable.of_eq (c0_apply_completionClosedPoint x))
  let κ : (xHat0 X x).presheaf.stalk (completionClosedPoint x) ≅ CommRingCat.of (Shat X x) :=
    stalkClosedPointIso (CommRingCat.of (Shat X x))
  have e1 : (c0 X x).stalkMap (completionClosedPoint x) =
      (ι.hom ≫ CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (Shat X x))) ≫ κ.inv :=
    (Iso.eq_comp_inv _).mpr (stalkMap_c0_completionClosedPoint x)
  have h1 : (maximalIdeal (X.presheaf.stalk ((c0 X x).base (completionClosedPoint x)))).map
      ι.hom.hom = maximalIdeal (X.presheaf.stalk x) := by
    have := Ideal.map_isMaximal_of_equiv (p := maximalIdeal
      (X.presheaf.stalk ((c0 X x).base (completionClosedPoint x))))
      ι.commRingCatIsoToRingEquiv
    exact IsLocalRing.eq_maximalIdeal this
  have h2 : (maximalIdeal (Shat X x)).map κ.inv.hom =
      maximalIdeal ((xHat0 X x).presheaf.stalk (completionClosedPoint x)) := by
    have := Ideal.map_isMaximal_of_equiv (p := maximalIdeal (Shat X x))
      κ.symm.commRingCatIsoToRingEquiv
    exact IsLocalRing.eq_maximalIdeal this
  have e2 : ((c0 X x).stalkMap (completionClosedPoint x)).hom = κ.inv.hom.comp
      ((algebraMap (X.presheaf.stalk x) (Shat X x)).comp ι.hom.hom) := by
    rw [e1]; rfl
  unfold fiberIdeal
  rw [e2, ← Ideal.map_map, ← Ideal.map_map, h1, ← AdicCompletion.maximalIdeal_eq_map, h2]

theorem isClosed_singleton_completionClosedPoint :
    IsClosed ({completionClosedPoint x} : Set (xHat0 X x)) := by
  show IsClosed ({IsLocalRing.closedPoint (Shat X x)} : Set (PrimeSpectrum (Shat X x)))
  rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  exact maximalIdeal.isMaximal _

/-- `κ(x) → κ(x̂)`, induced by `c_0`, is an isomorphism. -/
theorem isIso_residueFieldMap_c0_completionClosedPoint :
    IsIso ((c0 X x).residueFieldMap (completionClosedPoint x)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_residueField_map_stalkMap_c0_completionClosedPoint x

end GeneralCompletion

end AB

/-! ### The fibre of a morphism at a point -/

section Fibre

variable {P X Y Z : Scheme.{u}}

/-- In a pull-back square `P = X ×_Z Y` in which `g : Y → Z` induces an isomorphism of residue
fields at `y`, the local ring map `O_{X,fst p} → O_{P,p}` is onto modulo the kernel of the stalk map
of the fibre `P_y ↪ P`: the fibre `snd⁻¹(y)` is the fibre `f⁻¹(g y)` (as in
`exists_homeomorph_preimage_of_isPullback`, here with the structure sheaves), and `O_{X,x}` maps
onto the local ring of the fibre `f⁻¹(g y)` at `x`. -/
theorem exists_sub_mem_ker_stalkMap_fiberι {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (y : Y) [IsIso (g.residueFieldMap y)]
    (q : snd.fiber y) (b : P.presheaf.stalk (snd.fiberι y q)) :
    ∃ a : X.presheaf.stalk (fst (snd.fiberι y q)),
      (fst.stalkMap (snd.fiberι y q)).hom a - b ∈
        RingHom.ker ((snd.fiberι y).stalkMap q).hom := by
  have hp := isPullback_fiberToSpecResidueField_of_isPullback h y
  have : IsIso (Spec.map (g.residueFieldMap y)) := inferInstance
  obtain ⟨θ, hθ, hcomp⟩ : ∃ θ : snd.fiber y ⟶ f.fiber (g y), IsIso θ ∧
      θ ≫ f.fiberι (g y) = snd.fiberι y ≫ fst :=
    ⟨_, hp.isIso_fst_of_isIso, by
      simp only [Scheme.Hom.fiberι, pullback.map]
      exact pullback.lift_fst _ _ _⟩
  have hs : Function.Surjective (Scheme.Hom.stalkMap (snd.fiberι y ≫ fst) q).hom := by
    have h1 : Function.Surjective (Scheme.Hom.stalkMap (θ ≫ f.fiberι (g y)) q).hom := by
      rw [Scheme.Hom.stalkMap_comp]
      exact ((Scheme.Hom.stalkMap_surjective θ q).comp
        (Scheme.Hom.stalkMap_surjective (f.fiberι (g y)) (θ q)))
    rw [Scheme.Hom.stalkMap_congr_hom _ _ hcomp q] at h1
    exact Function.Surjective.of_comp h1
  rw [Scheme.Hom.stalkMap_comp] at hs
  obtain ⟨a, ha⟩ := hs (((snd.fiberι y).stalkMap q).hom b)
  refine ⟨a, ?_⟩
  rw [RingHom.mem_ker, map_sub]
  exact sub_eq_zero.2 ha

/-- The kernel of the stalk map of the fibre `P_s ↪ P` of `f : P → S` over a closed point `s` lies in
the ideal `m_s O_{P,p}` of the fibre. -/
theorem ker_stalkMap_fiberι_le_fiberIdeal {S : Scheme.{u}} (f : P ⟶ S) {s : S}
    (hs : IsClosed ({s} : Set S)) (q : f.fiber s) :
    RingHom.ker ((f.fiberι s).stalkMap q).hom ≤ AB.fiberIdeal f (f.fiberι s q) := by
  have hi : IsClosedImmersion (S.fromSpecResidueField s) :=
    isClosed_singleton_iff_isClosedImmersion.mp hs
  have hj : IsClosedImmersion (f.fiberι s) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst f (S.fromSpecResidueField s)))
  set j := f.fiberι s with hjdef
  obtain ⟨hker, -⟩ := Subscheme.ker_stalkMap_eq_and_surjective_of_eq_iso_comp j j.ker
    (asIso j.toImage) (Scheme.Hom.toImage_imageι j).symm q
  rw [hker]
  have hker' : j.ker = (S.fromSpecResidueField s).ker.comap f :=
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _
  have hfs : f.base (j.base q) = s := by
    have : j.base q ∈ Set.range j.base := ⟨q, rfl⟩
    have h2 := Scheme.Hom.range_fiberι f s
    rw [← hjdef] at h2
    rw [h2] at this
    exact this
  have hmem : f.base (j.base q) ∈ Subscheme.pts (S.fromSpecResidueField s).ker := by
    rw [hfs]
    show s ∈ (((S.fromSpecResidueField s).ker.support : Closeds S) : Set S)
    rw [Scheme.Hom.support_ker]
    refine subset_closure ?_
    rw [Scheme.range_fromSpecResidueField]
    rfl
  rw [hker', Subscheme.stalkIdeal_comap]
  exact Ideal.map_mono (Subscheme.stalkIdeal_le_maximalIdeal _ hmem)

end Fibre

/-! ### The pull-back along the completion at a point of the fibre -/

section Smallest

variable {X Y Ŷ : Scheme.{u}} {x : X} [IsNoetherianRing (X.presheaf.stalk x)] {g : Y ⟶ X}
  {c : Ŷ ⟶ Y} {ĝ : Ŷ ⟶ AB.xHat0 X x}

/-- `ĝ(ŷ) = x̂` as soon as `g(c(ŷ)) = x`: the only point of `Spec(Ŝ)` over `x` is the closed point. -/
theorem eq_completionClosedPoint_of_apply_eq (H : IsPullback c ĝ g (AB.c0 X x)) {ŷ : Ŷ}
    (h : g.base (c.base ŷ) = x) : ĝ.base ŷ = AB.completionClosedPoint x := by
  apply AB.eq_completionClosedPoint_of_c0_apply_eq
  refine Eq.trans ?_ h
  rw [← Scheme.Hom.comp_apply, ← H.w, Scheme.Hom.comp_apply]

/-- If `g(c(ŷ))` is a specialization of `x`, then `ĝ(ŷ) = x̂`: `c₀` maps `Spec(Ŝ)` onto the
generizations of `x`. -/
theorem eq_completionClosedPoint_of_specializes (H : IsPullback c ĝ g (AB.c0 X x)) {ŷ : Ŷ}
    (h : x ⤳ g.base (c.base ŷ)) : ĝ.base ŷ = AB.completionClosedPoint x := by
  apply eq_completionClosedPoint_of_apply_eq H
  have hw : g.base (c.base ŷ) = (AB.c0 X x).base (ĝ.base ŷ) := by
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
  have h1 : (ĝ.base ŷ) ⤳ AB.completionClosedPoint x :=
    (PrimeSpectrum.le_iff_specializes (ĝ.base ŷ) (IsLocalRing.closedPoint (AB.Shat X x))).mp
      (IsLocalRing.le_maximalIdeal ((ĝ.base ŷ : PrimeSpectrum (AB.Shat X x)).isPrime.ne_top))
  have h2 : (AB.c0 X x).base (ĝ.base ŷ) ⤳ x := by
    have := h1.map (AB.c0 X x).continuous
    rwa [AB.c0_apply_completionClosedPoint] at this
  rw [← hw] at h2
  exact (h2.antisymm h).eq

/-- **`O_{Y,y} → O_{Ŷ,ŷ}` is onto modulo the ideal of the fibre** (the Corollary of Lemma (AB.3),
p. 296, for an arbitrary algebraic scheme): at a point `ŷ` of `ĝ⁻¹(x̂)` every element of `O_{Ŷ,ŷ}`
is congruent modulo `m̂ O_{Ŷ,ŷ}` to the image of an element of `O_{Y,c(ŷ)}`.  Proof: the fibres
`ĝ⁻¹(x̂)` and `g⁻¹(x)` are isomorphic (the residue fields of `x` and `x̂` agree) and `O_{Y,y}` maps
onto the local ring of the fibre `g⁻¹(x)` at `y`. -/
theorem exists_sub_mem_fiberIdeal_of_isPullback_completion (H : IsPullback c ĝ g (AB.c0 X x))
    {ŷ : Ŷ} (hŷ : ĝ.base ŷ = AB.completionClosedPoint x) (b : Ŷ.presheaf.stalk ŷ) :
    ∃ a : Y.presheaf.stalk (c.base ŷ),
      (c.stalkMap ŷ).hom a - b ∈ AB.fiberIdeal ĝ ŷ := by
  have := AB.isIso_residueFieldMap_c0_completionClosedPoint x
  obtain ⟨q, hq⟩ : ŷ ∈ Set.range (ĝ.fiberι (AB.completionClosedPoint x)) := by
    rw [Scheme.Hom.range_fiberι]; exact hŷ
  subst hq
  obtain ⟨a, ha⟩ := exists_sub_mem_ker_stalkMap_fiberι H (AB.completionClosedPoint x) q b
  exact ⟨a, ker_stalkMap_fiberι_le_fiberIdeal ĝ (AB.isClosed_singleton_completionClosedPoint x) q ha⟩

/-- `m̂ O_{Ŷ,ŷ} = (m_x O_{Y,y}) O_{Ŷ,ŷ}` at a point over `x̂` (`m_x Ŝ` is the maximal ideal of `Ŝ`). -/
theorem fiberIdeal_eq_map_of_isPullback_completion (H : IsPullback c ĝ g (AB.c0 X x)) {ŷ : Ŷ}
    (hŷ : ĝ.base ŷ = AB.completionClosedPoint x) :
    AB.fiberIdeal ĝ ŷ = (AB.fiberIdeal g (c.base ŷ)).map (c.stalkMap ŷ).hom := by
  have h1 : AB.fiberIdeal (c ≫ g) ŷ = (AB.fiberIdeal g (c.base ŷ)).map (c.stalkMap ŷ).hom :=
    AB.fiberIdeal_comp c g ŷ
  have h2 : AB.fiberIdeal (ĝ ≫ AB.c0 X x) ŷ =
      (AB.fiberIdeal (AB.c0 X x) (ĝ.base ŷ)).map (ĝ.stalkMap ŷ).hom := AB.fiberIdeal_comp ĝ _ ŷ
  have h3 : AB.fiberIdeal (c ≫ g) ŷ = AB.fiberIdeal (ĝ ≫ AB.c0 X x) ŷ :=
    AB.fiberIdeal_congr H.w ŷ
  have h4 : AB.fiberIdeal (AB.c0 X x) (ĝ.base ŷ) =
      maximalIdeal ((AB.xHat0 X x).presheaf.stalk (ĝ.base ŷ)) := by
    rw [hŷ]
    exact AB.fiberIdeal_c0_completionClosedPoint x
  rw [← h1, h3, h2, h4]
  rfl

/-- The points of `Ŷ` over the closure of `c(Ĉ)` for a subscheme `Ĉ` lying over `x̂` are those
of `Ĉ`: `c⁻¹(closure c(Ĉ)) = Ĉ` as sets (`c` is a homeomorphism of `ĝ⁻¹(x̂)` onto `g⁻¹(x)`). -/
theorem mem_pts_of_apply_mem_closure_image (H : IsPullback c ĝ g (AB.c0 X x)) (Ĉ : Subscheme Ŷ)
    (hfib : ∀ ŷ ∈ Ĉ.pts, g.base (c.base ŷ) = x) {ŷ : Ŷ}
    (hŷ : c.base ŷ ∈ closure (c.base '' Ĉ.pts)) : ŷ ∈ Ĉ.pts := by
  have hx : x ⤳ g.base (c.base ŷ) := by
    rw [specializes_iff_mem_closure]
    exact map_mem_closure g.continuous hŷ (by
      rintro _ ⟨ŷ', hŷ', rfl⟩
      exact hfib ŷ' hŷ')
  have hŷĝ := eq_completionClosedPoint_of_specializes H hx
  have := AB.isIso_residueFieldMap_c0_completionClosedPoint x
  obtain ⟨Hh, hH⟩ := AB.exists_homeomorph_preimage_of_isPullback H (AB.completionClosedPoint x)
    inferInstance
  have hŷF : ŷ ∈ ĝ.base ⁻¹' {AB.completionClosedPoint x} := hŷĝ
  let A : Set (g.base ⁻¹' {(AB.c0 X x).base (AB.completionClosedPoint x)}) :=
    Hh '' (Subtype.val ⁻¹' Ĉ.pts)
  have hA : IsClosed A := Hh.isClosedMap _ (Ĉ.support.isClosed.preimage continuous_subtype_val)
  have hyF : c.base ŷ ∈ g.base ⁻¹' {(AB.c0 X x).base (AB.completionClosedPoint x)} := by
    rw [← hH ⟨ŷ, hŷF⟩]
    exact (Hh ⟨ŷ, hŷF⟩).2
  have hval : Subtype.val '' A = c.base '' Ĉ.pts := by
    ext z
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p.1, hp, (hH p).symm⟩
    · rintro ⟨ĉ, hĉ, rfl⟩
      have hĉF : ĉ ∈ ĝ.base ⁻¹' {AB.completionClosedPoint x} :=
        eq_completionClosedPoint_of_apply_eq H (hfib ĉ hĉ)
      exact ⟨Hh ⟨ĉ, hĉF⟩, ⟨⟨ĉ, hĉF⟩, hĉ, rfl⟩, hH _⟩
  have hyA : (⟨c.base ŷ, hyF⟩ : g.base ⁻¹' {(AB.c0 X x).base (AB.completionClosedPoint x)}) ∈ A := by
    rw [← hA.closure_eq, Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, hval]
    exact hŷ
  obtain ⟨p, hp, hpe⟩ := hyA
  have hpe' : Hh p = Hh ⟨ŷ, hŷF⟩ := by
    refine hpe.trans (Subtype.ext ?_)
    exact (hH ⟨ŷ, hŷF⟩).symm
  have := Hh.injective hpe'
  rw [this] at hp
  exact hp

/-- A function on `Y` near `y = c(ŷ)` whose pull-back vanishes near `ŷ ∈ Ĉ` on the integral
subscheme `Ĉ` vanishes on `Ĉ` near `ŷ`, hence lies in the ideal of the scheme-theoretic image
`C = c(Ĉ)`: if `a ∈ O_{Y,y}` and `c^#(a) ∈ Ĉ_ŷ`, then `a ∈ C_y`. -/
theorem mem_stalkIdeal_map_of_stalkMap_mem (c : Ŷ ⟶ Y) (Ĉ : Subscheme Ŷ)
    [QuasiCompact (Ĉ.ι ≫ c)] [IsIntegral Ĉ.toScheme] {ŷ : Ŷ} (hŷ : ŷ ∈ Ĉ.pts)
    {a : Y.presheaf.stalk (c.base ŷ)} (ha : (c.stalkMap ŷ).hom a ∈ Ĉ.stalkIdeal ŷ) :
    a ∈ Subscheme.stalkIdeal (Scheme.IdealSheafData.map Ĉ c) (c.base ŷ) := by
  obtain ⟨p, rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts Ĉ hŷ
  obtain ⟨U₁, hyU₁, s₁, rfl⟩ := Y.presheaf.exists_germ_eq a
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUU₁⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU₁ U₁.isOpen
  let s : Γ(Y, U) := Y.presheaf.map (homOfLE hUU₁).op s₁
  have hs : Y.presheaf.germ U (c.base (Ĉ.ι.base p)) hyU s =
      Y.presheaf.germ U₁ (c.base (Ĉ.ι.base p)) hyU₁ s₁ := Y.presheaf.germ_res_apply _ _ _ _
  rw [← hs] at ha ⊢
  have hker := stalkIdeal_eq_ker_stalkMap Ĉ p
  rw [hker, RingHom.mem_ker] at ha
  have h0 : ((Ĉ.ι ≫ c).app U).hom s = 0 := by
    refine germ_injective_of_isIntegral (X := Ĉ.toScheme) (U := (Ĉ.ι ≫ c) ⁻¹ᵁ U) p hyU ?_
    rw [map_zero, ← Scheme.Hom.germ_stalkMap_apply (Ĉ.ι ≫ c) U p hyU s,
      Scheme.Hom.stalkMap_comp]
    exact ha
  have h1 : s ∈ RingHom.ker ((Ĉ.ι ≫ c).app ((⟨U, hU⟩ : Y.affineOpens) : Y.Opens)).hom := h0
  rw [← Scheme.Hom.ker_apply (f := Ĉ.ι ≫ c) (⟨U, hU⟩ : Y.affineOpens)] at h1
  rw [Subscheme.stalkIdeal_eq_map_germ_affine (Scheme.IdealSheafData.map Ĉ c) ⟨U, hU⟩ hyU]
  exact Ideal.mem_map_of_mem _ h1

/-- The scheme-theoretic image of a reduced subscheme `Ĉ` under `c` is the reduced subscheme on the
closure of `c(Ĉ)`. -/
theorem map_eq_ofClosed_closure_image (c : Ŷ ⟶ Y) (Ĉ : Subscheme Ŷ) (hred : Ĉ.IsReduced) :
    Scheme.IdealSheafData.map Ĉ c =
      Subscheme.ofClosed ⟨closure (c.base '' Ĉ.pts), isClosed_closure⟩ := by
  conv_lhs => rw [Subscheme.eq_ofClosed_support Ĉ hred]
  unfold Subscheme.ofClosed
  rw [Scheme.IdealSheafData.map_vanishingIdeal]
  rfl

end Smallest

/-- p. 175: "we can find a reduced irreducible subscheme `C` of `V₀(r)` such that `Ĉ = c_r⁻¹(C)`.  In fact, we take
the smallest subscheme `C` of `V₀(r)` such that `Ĉ = c_r⁻¹(C)`."  `Y → X` of finite type, `Ŷ = Y ×_X Spec(Ô_{X,x})`,
`Ĉ` a reduced irreducible subscheme of `Ŷ` all of whose points lie over `x`: the scheme-theoretic image `C` of `Ĉ → Y`
is reduced irreducible with `c⁻¹(C) = Ĉ`, its set of points is the closure of `c(Ĉ)`, and it is contained in every `C'` with
`c⁻¹(C') = Ĉ`.

Proof (the argument of the Corollary of (AB.3), p. 296): at a point `ŷ` of `Ĉ` (over `x̂`) the ideal `I = Ĉ_ŷ` contains the
ideal `m̂ O_{Ŷ,ŷ} = (m_x O_{Y,y}) O_{Ŷ,ŷ}` of the fibre (`Ĉ` is reduced and lies in the fibre), and
`O_{Ŷ,ŷ} = O_{Y,y} + m̂ O_{Ŷ,ŷ}` (`exists_sub_mem_fiberIdeal_of_isPullback_completion`); hence `I = (I ∩ O_{Y,y}) O_{Ŷ,ŷ}`.
Since `Ĉ` is integral, `I ∩ O_{Y,y}` lies in the stalk at `y` of the scheme-theoretic image `C` of `Ĉ` (`mem_stalkIdeal_map_of_stalkMap_mem`),
so `c⁻¹(C) ⊆ Ĉ`; the other inclusion `Ĉ ⊆ c⁻¹(C)` and the minimality of `C` are the adjunction `c⁻¹ ⊣ c_*` of ideal
sheaves; the points of `Ŷ` off `Ĉ` are not mapped into `C` by `mem_pts_of_apply_mem_closure_image`.

Deviation from the paper (gap filled): the paper states this at the place of use (p. 175, "Therefore, we can find … In fact,
we take the smallest") as the Corollary of (AB.3).  That corollary is proved in Ch. IV (p. 296, and p. 316 for non-reduced `B̂`)
only for a non-singular `X`, a simple closed point `x₀` and a subscheme `B̂` mapping to `x̂₀`; p. 175 uses it on the singular
scheme `V₀(r)` and for an arbitrary point `x` (generic point of `S̄(r)`), so `c(Ĉ)` need not be closed and `C` is the closure
of the image.  The facts about the completion `c₀` at `x̂` used in Ch. IV for a simple point hold for any noetherian local
ring `S` (`AB.completionClosedPoint` …), and the argument of the Corollary of (AB.3) goes through with
`O_{Ŷ,ŷ} = O_{Y,y} + m̂ O_{Ŷ,ŷ}` obtained from the isomorphism of the fibres; neither regularity of `Ŝ_s` nor the flatness of
`O_{Y,y} → O_{Ŷ,ŷ}` is needed here (flatness would only give the uniqueness of `C` among the subschemes of `g⁻¹(x)`,
which the paper does not assert). -/
theorem exists_reduced_irreducible_totalTransform_eq {X Y Ŷ : Scheme.{u}} [IsAlgebraicScheme X] (x : X)
    (g : Y ⟶ X) [LocallyOfFiniteType g] (c : Ŷ ⟶ Y) (ĝ : Ŷ ⟶ AB.xHat0 X x)
    (H : IsPullback c ĝ g (AB.c0 X x)) (Ĉ : Subscheme Ŷ) (hred : Ĉ.IsReduced) (hirr : Ĉ.IsIrreducible)
    (hfib : ∀ ŷ ∈ Ĉ.pts, g.base (c.base ŷ) = x) :
    ∃ C : Subscheme Y, C.IsReduced ∧ C.IsIrreducible ∧ Subscheme.totalTransform c C = Ĉ ∧
      C.pts = closure (c.base '' Ĉ.pts) ∧
      ∀ C' : Subscheme Y, Subscheme.totalTransform c C' = Ĉ → C.IsContainedIn C' := by
  have := IsAlgebraicScheme.isNoetherian X
  have : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
  have : IsNoetherianRing (AB.Shat X x) := isNoetherianRing_adicCompletion_of_isNoetherianRing _
  have : NoetherianSpace (AB.xHat0 X x) := by
    unfold AB.xHat0
    infer_instance
  have : QuasiCompact (AB.c0 X x) := inferInstance
  have : QuasiCompact c := MorphismProperty.of_isPullback H.flip this
  have : QuasiCompact (Ĉ.ι ≫ c) := inferInstance
  have : AlgebraicGeometry.IsReduced Ĉ.toScheme := hred
  have : IrreducibleSpace Ĉ.toScheme := hirr
  have : IsIntegral Ĉ.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hCeq := map_eq_ofClosed_closure_image c Ĉ hred
  have hCpts : Subscheme.pts (Scheme.IdealSheafData.map Ĉ c) = closure (c.base '' Ĉ.pts) := by
    rw [hCeq, Subscheme.pts_ofClosed]
    rfl
  refine ⟨Scheme.IdealSheafData.map Ĉ c, ?_, ?_, ?_, hCpts, ?_⟩
  · rw [hCeq]
    exact Subscheme.ofClosed_isReduced _
  · refine Subscheme.isIrreducible_of_pts _ ?_
    rw [hCpts]
    exact ((Subscheme.isIrreducible_pts Ĉ hirr).image _ c.continuous.continuousOn).closure
  · refine le_antisymm (Scheme.IdealSheafData.comap_map_le (I := Ĉ) (f := c)) ?_
    refine Subscheme.le_iff_stalkIdeal_le.mpr fun ŷ => ?_
    rw [stalkIdeal_totalTransform]
    by_cases hŷ : ŷ ∈ Ĉ.pts
    · have hĝ : ĝ.base ŷ = AB.completionClosedPoint x :=
        eq_completionClosedPoint_of_apply_eq H (hfib ŷ hŷ)
      have hM : AB.fiberIdeal ĝ ŷ ≤ Ĉ.stalkIdeal ŷ := by
        have h1 := AB.fiberIdeal_le_stalkIdeal_ofClosed ĝ Ĉ.support
          (fun ĉ hĉ => eq_completionClosedPoint_of_apply_eq H (hfib ĉ hĉ)) ŷ hĝ
        rwa [← Subscheme.eq_ofClosed_support Ĉ hred] at h1
      have hN : (AB.fiberIdeal g (c.base ŷ)).map (c.stalkMap ŷ).hom ≤ Ĉ.stalkIdeal ŷ := by
        rw [← fiberIdeal_eq_map_of_isPullback_completion H hĝ]
        exact hM
      have hNC : AB.fiberIdeal g (c.base ŷ) ≤
          Subscheme.stalkIdeal (Scheme.IdealSheafData.map Ĉ c) (c.base ŷ) := fun n hn =>
        mem_stalkIdeal_map_of_stalkMap_mem c Ĉ hŷ (hN (Ideal.mem_map_of_mem _ hn))
      intro z hz
      obtain ⟨a, ha⟩ := exists_sub_mem_fiberIdeal_of_isPullback_completion H hĝ z
      have ha1 : (c.stalkMap ŷ).hom a ∈ Ĉ.stalkIdeal ŷ := by
        have := add_mem (hM ha) hz
        simpa using this
      have ha2 : a ∈ Subscheme.stalkIdeal (Scheme.IdealSheafData.map Ĉ c) (c.base ŷ) :=
        mem_stalkIdeal_map_of_stalkMap_mem c Ĉ hŷ ha1
      have ha3 : (c.stalkMap ŷ).hom a - z ∈
          (Subscheme.stalkIdeal (Scheme.IdealSheafData.map Ĉ c) (c.base ŷ)).map
            (c.stalkMap ŷ).hom := by
        rw [fiberIdeal_eq_map_of_isPullback_completion H hĝ] at ha
        exact Ideal.map_mono hNC ha
      have : z = (c.stalkMap ŷ).hom a - ((c.stalkMap ŷ).hom a - z) := by ring
      rw [this]
      exact sub_mem (Ideal.mem_map_of_mem _ ha2) ha3
    · have hnot : c.base ŷ ∉ Subscheme.pts (Scheme.IdealSheafData.map Ĉ c) := fun h => by
        rw [hCpts] at h
        exact hŷ (mem_pts_of_apply_mem_closure_image H Ĉ hfib h)
      rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hŷ,
        Subscheme.stalkIdeal_eq_top_of_notMem_pts hnot, Ideal.map_top]
  · intro C' hC'
    have : C' ≤ Scheme.IdealSheafData.map Ĉ c :=
      Scheme.IdealSheafData.le_map_iff_comap_le.mpr hC'.le
    exact fun U => Scheme.IdealSheafData.le_def.mp this U

end Hironaka
