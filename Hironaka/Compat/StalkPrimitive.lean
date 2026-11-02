/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Hironaka.Ch0.AlgebraicScheme
public import Hironaka.Compat.FrameCoordinates
public import Hironaka.Compat.PrimitiveLocus
public import Hironaka.Compat.RegularLocalRingUFD

/-!
# Sections of an integral scheme inside its function field (Compat API for Corollary 2 of Main Theorem II)

For an integral scheme `X` with function field `K`, every stalk `𝒪_{X,x}` is a subring of `K`
(`Scheme.stalkRange`), and the ring of sections `Γ(X, V)` of a non-empty open set embeds into `K`
(`Scheme.germToFunctionField`).  This module collects the two facts used in the proof that a locally free
sheaf contains an invertible subsheaf (`Hironaka/Compat/InvertibleSubsheaf.lean`, the remark of p. 145 of
Hironaka, Ch. 0, asserted without proof):

* `Hironaka.Scheme.exists_section_of_forall_mem_stalkRange`: an element of `K` which lies in every stalk
  `𝒪_{X,y}`, `y ∈ V`, is the image of a section over `V` (sections are the intersection of the stalks);
* `Hironaka.Scheme.exists_forall_isPrimitive_stalkRange`: if `X` is non-singular and locally noetherian, the
  primitive locus of a vector of sections is open (`Hironaka/Compat/PrimitiveLocus.lean`; the local rings are
  unique factorization domains by the cited fact of `Hironaka/Compat/RegularLocalRingUFD.lean`).

This is infrastructure (no statement of the paper); it is not a deviation.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The stalk `𝒪_{X,x}` as a subring of the function field. -/
noncomputable def stalkRange (x : X) : Set X.functionField :=
  Set.range (algebraMap (X.presheaf.stalk x) X.functionField)

variable {X}

/-- The function field image commutes with restriction of sections. -/
theorem germToFunctionField_resO {V W : X.Opens} [Nonempty V] [Nonempty W] (h : V ≤ W)
    (a : Γ(X, W)) : X.germToFunctionField V (resO X h a) = X.germToFunctionField W a := by
  unfold resO Scheme.germToFunctionField
  exact X.presheaf.germ_res_apply (homOfLE h) _ _ a

/-- The image of a section over `V` in the function field lies in the stalk at each point of `V`. -/
theorem germToFunctionField_mem_stalkRange {V : X.Opens} [Nonempty V] (a : Γ(X, V)) {y : X}
    (hy : y ∈ V) : X.germToFunctionField V a ∈ stalkRange X y :=
  ⟨X.presheaf.germ V y hy a, Scheme.algebraMap_germ_eq_germToFunctionField X hy a⟩

omit [IsIntegral X] in
/-- Over an open set without points the ring of sections is trivial. -/
theorem subsingleton_sections_of_not_nonempty (W : X.Opens) (h : ¬ Nonempty W) :
    Subsingleton Γ(X, W) := by
  have : W = ⊥ := le_antisymm (fun x hx => (h ⟨⟨x, hx⟩⟩).elim) bot_le
  subst this
  infer_instance

/-- **Sections are the intersection of the stalks.** On an integral scheme, an element of the function
field which lies in the stalk `𝒪_{X,y}` for every point `y` of a non-empty open set `V` is the image of a
section over `V`. -/
theorem exists_section_of_forall_mem_stalkRange {V : X.Opens} [Nonempty V] (l : X.functionField)
    (hl : ∀ y ∈ V, l ∈ stalkRange X y) : ∃ a : Γ(X, V), X.germToFunctionField V a = l := by
  have hex : ∀ y : V, ∃ (W : X.Opens) (hW : (y : X) ∈ W) (t : Γ(X, W)),
      algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ W y hW t) = l := by
    intro y
    obtain ⟨s, hs⟩ := hl y y.2
    obtain ⟨W, hW, t, ht⟩ := X.presheaf.exists_germ_eq s
    exact ⟨W, hW, t, by rw [ht]; exact hs⟩
  choose W hW t ht using hex
  let U : V → X.Opens := fun y => W y ⊓ V
  have hUW : ∀ y, U y ≤ W y := fun y => inf_le_left
  have hUV : ∀ y, U y ≤ V := fun y => inf_le_right
  have hUne : ∀ y : V, Nonempty (U y) := fun y => ⟨⟨y, hW y, y.2⟩⟩
  have hWne : ∀ y : V, Nonempty (W y) := fun y => ⟨⟨y, hW y⟩⟩
  let t' : ∀ y : V, Γ(X, U y) := fun y => resO X (hUW y) (t y)
  have ht' : ∀ y : V, X.germToFunctionField (U y) (t' y) = l := fun y => by
    have := hWne y
    have := hUne y
    have e := germToFunctionField_resO (hUW y) (t y)
    refine e.trans ?_
    rw [← ht y, Scheme.algebraMap_germ_eq_germToFunctionField X (hW y)]
  have hcomp : ∀ i j, resO X (inf_le_left : U i ⊓ U j ≤ U i) (t' i) =
      resO X (inf_le_right : U i ⊓ U j ≤ U j) (t' j) := by
    intro i j
    by_cases hne : Nonempty (U i ⊓ U j : X.Opens)
    · have := hUne i
      have := hUne j
      refine Scheme.germToFunctionField_injective X (U i ⊓ U j) ?_
      have e1 := germToFunctionField_resO (inf_le_left : U i ⊓ U j ≤ U i) (t' i)
      have e2 := germToFunctionField_resO (inf_le_right : U i ⊓ U j ≤ U j) (t' j)
      rw [e1, e2, ht', ht']
    · have := subsingleton_sections_of_not_nonempty _ hne
      exact Subsingleton.elim _ _
  obtain ⟨a, ha⟩ := exists_section_of_compatible X U hUV
    (fun y hy => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hW ⟨y, hy⟩, hy⟩) t' hcomp
  obtain ⟨y₀⟩ := ‹Nonempty V›
  let y : V := y₀
  have := hUne y
  refine ⟨a, ?_⟩
  have e := germToFunctionField_resO (hUV y) a
  rw [← e, ha y, ht']

section Locus

variable [IsLocallyNoetherian X] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
  [IsFractionRing Γ(X, U) X.functionField]

include hU

omit [IsLocallyNoetherian X] in
/-- The stalk at a point of an affine open set is the localization `A_q ⊆ K` of `A = Γ(X, U)`. -/
theorem stalkRange_eq_locAlg (y : U) :
    stalkRange X y = (Hironaka.locAlg X.functionField (hU.primeIdealOf y).asIdeal : Set X.functionField) := by
  have := hU.isLocalization_stalk y
  exact Hironaka.range_algebraMap_eq_locAlg X.functionField (hU.primeIdealOf y).asIdeal
    (X.presheaf.stalk y)

omit [IsLocallyNoetherian X] in
/-- On a non-singular scheme, the localizations of `Γ(X, U)` at primes (inside the function field) are UFDs
(the local rings are regular, hence UFDs: cited fact `IsRegularLocalRing.uniqueFactorizationMonoid`). -/
theorem uniqueFactorizationMonoid_locAlg [Hironaka.Cited.IsRegularLocalRingUniqueFactorizationMonoid.{u}] (hX : X.IsNonsingular) (q : Ideal Γ(X, U)) [hq : q.IsPrime] :
    UniqueFactorizationMonoid (Hironaka.locAlg X.functionField q) := by
  let y : PrimeSpectrum Γ(X, U) := ⟨q, hq⟩
  have hy : hU.fromSpec y ∈ U := by
    have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
    rwa [hU.range_fromSpec] at this
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) q :=
    hU.isLocalization_stalk' y hy
  have : IsRegularLocalRing (X.presheaf.stalk (hU.fromSpec y)) := hX _
  have : IsDomain (X.presheaf.stalk (hU.fromSpec y)) := inferInstance
  exact Hironaka.uniqueFactorizationMonoid_locAlg X.functionField q (X.presheaf.stalk (hU.fromSpec y))
    (Hironaka.IsRegularLocalRing.uniqueFactorizationMonoid _)

omit [IsIntegral X] [IsLocallyNoetherian X] [Nonempty U] [IsFractionRing Γ(X, U) X.functionField] in
/-- A function lies in the prime of a point of an affine open set iff the point is not in its basic open
set. -/
theorem mem_primeIdealOf_iff_notMem_basicOpen {z : X} (hz : z ∈ U) (f : Γ(X, U)) :
    f ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal ↔ z ∉ X.basicOpen f := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hz⟩ : U)
  have := hU.isLocalization_stalk ⟨z, hz⟩
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk z) _ f,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Scheme.mem_basicOpen _ _ _ hz]
  rfl

/-- **Openness of the primitive locus.** On a non-singular locally noetherian integral scheme, let `w` be a
vector of sections over an affine open set `U`, not zero.  If `w` is primitive for the stalk at `x ∈ U`
(a scalar `l` of the function field with all `l * wᵢ` in the stalk is in the stalk), it is primitive for the
stalks at all points of a neighbourhood `D(f)` of `x`. -/
theorem exists_forall_isPrimitive_stalkRange [Hironaka.Cited.IsRegularLocalRingUniqueFactorizationMonoid.{u}] (hX : X.IsNonsingular) {ι : Type*} [Finite ι]
    (w : ι → Γ(X, U)) (hw : ∃ i, w i ≠ 0) {x : X} (hx : x ∈ U)
    (hp : Hironaka.IsPrimitive (stalkRange X x) fun i => X.germToFunctionField U (w i)) :
    ∃ f : Γ(X, U), x ∈ X.basicOpen f ∧ ∀ y ∈ X.basicOpen f,
      Hironaka.IsPrimitive (stalkRange X y) fun i => X.germToFunctionField U (w i) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsDomain Γ(X, U) := inferInstance
  have hp' : Hironaka.IsPrimitive
      (Hironaka.locAlg X.functionField (hU.primeIdealOf ⟨x, hx⟩).asIdeal : Set X.functionField)
      fun i => algebraMap Γ(X, U) X.functionField (w i) := by
    rw [← stalkRange_eq_locAlg hU ⟨x, hx⟩]
    exact hp
  obtain ⟨f, hfp, hf⟩ := Hironaka.exists_forall_isPrimitive_of_isPrimitive
    (fun q _ => uniqueFactorizationMonoid_locAlg hU hX q) hw hp'
  refine ⟨f, ?_, fun y hy => ?_⟩
  · rw [← not_not (a := x ∈ X.basicOpen f), ← mem_primeIdealOf_iff_notMem_basicOpen hU hx]
    exact hfp
  · have hyU : y ∈ U := X.basicOpen_le f hy
    rw [stalkRange_eq_locAlg hU ⟨y, hyU⟩]
    refine hf _ ?_
    rw [mem_primeIdealOf_iff_notMem_basicOpen hU hyU]
    exact not_not.mpr hy

end Locus

end AlgebraicGeometry.Scheme
