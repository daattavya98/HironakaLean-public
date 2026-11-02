/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.ComponentStalk
public import Hironaka.Ch3.Transforms
public import Hironaka.Ch3.JStability
public import Hironaka.Ch1.ResolutionData

/-!
# Normal crossings along pull-backs and restrictions (Ch. IV §4, p. 321: the "we see" facts)

> For the case in which `ℜ = (ℜ^N_II, F)`, we see that `Ê_1(s) ∪ ⋯ ∪ Ê_{α+s}(s)` has only normal
> crossings with `X̃` in `X̂_s`. In the other case, we see that `Ê_{α+1}(s) ∪ ⋯ ∪ Ê_{α+s}(s)` has
> only normal crossings with `X̃` in `X̂_s`. … We see that, in both cases, `Ẽ_j` `(1 ≦ j ≦ α̃)` are
> non-singular irreducible subschemes of `X̃` of codimension 1, and `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only
> normal crossings on `X̃`. (p. 321)

General statements, independent of the construction of `X̃`:

* `hasOnlyNormalCrossingsWithAt_totalTransform_of_mapsRSOP`, `…With_totalTransform_of_mapsRSOP`:
  normal crossings are preserved by total transforms along a morphism whose stalk maps send a
  regular system of parameters to one (e.g. `c_s`, Lemma (CD.3) / (AB.2)): `Ê_j(s) = c_s⁻¹E_j(s)`.
* `exists_stalk_presentation_totalTransform_ι`, `hasOnlyNormalCrossingsAt_totalTransform_ι`:
  restriction of a reduced `E` with only normal crossings with `D` to `D`, when `D` is not
  locally contained in a component of `E` (transversality).
* `exists_stalk_presentation_iInf_totalTransform_ι` and its global consequences
  `hasOnlyNormalCrossings_iInf_totalTransform_ι` (`Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on `D`),
  `isNonsingular_and_isEverywhereOfCodim_totalTransform_ι` and
  `isNonsingularIrreducibleCodimOne_totalTransform_ι` (`Ẽ_j` non-singular of codimension one;
  irreducibility is the global input `hirr`): for a finite family `E_j` of divisors, non-singular
  and of codimension one, whose union has only normal crossings with `D`.

Deviation from the paper (gap filled): the paper writes "we see" for these facts. Lean proves the
local algebra: all the statements are read on stalks, where a reduced `E` with only normal
crossings with `D` is `(∏_J a)` with `D = (T)`, `J, T` parts of a regular system of parameters; a
ring map sending a regular system of parameters to one carries this presentation to the
corresponding one, and on `D = Spec(O/(T))` the images of `z \ T` form a regular system of
parameters. Left to the caller (specific to the construction): that `D` is transversal to the
`E_j`, that the `Ê_j` have the stated properties on `X̂_s`, and the irreducibility of `Ẽ_j`.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory TopologicalSpace

namespace Hironaka

universe u

namespace Subscheme

variable {Y' Y : Scheme.{u}}

/-- Normal crossings are preserved by total transforms along a morphism whose stalk map at the
point transforms a regular system of parameters into one. On p. 321 the paper only says "we see
that `Ê_1(s) ∪ ⋯ ∪ Ê_{α+s}(s)` has only normal crossings with `X̃` in `X̂_s`". The property of
`c_s` used here is the one the paper invokes in §3, Remark 4 (p. 309, there to pass from `X̂_s`
down to `X_s`): "the canonical homomorphism `S_s → Ŝ_s` transforms a regular system of parameters
of `S_s` into such a system of parameters of `Ŝ_s`. (See Lemma (AB.2).)"; in §4 it is Lemma (CD.3)
(p. 316). -/
theorem hasOnlyNormalCrossingsWithAt_totalTransform_of_mapsRSOP (g : Y' ⟶ Y) (y' : Y')
    [IsRegularLocalRing (Y.presheaf.stalk (g y'))] [IsRegularLocalRing (Y'.presheaf.stalk y')]
    [IsLocalHom (g.stalkMap y').hom] (hα : RingHom.MapsRSOP (g.stalkMap y').hom)
    {E D : Subscheme Y} (hE : E.IsReduced) (h : E.HasOnlyNormalCrossingsWithAt D (g y')) :
    (totalTransform g E).HasOnlyNormalCrossingsWithAt (totalTransform g D) y' := by
  classical
  obtain ⟨z, hz, ⟨J, hJz, hEJ⟩, ⟨T, hTz, hDT⟩⟩ :=
    (hasOnlyNormalCrossingsWithAt_iff hE (by exact ‹IsRegularLocalRing (Y.presheaf.stalk (g y'))›)).mp h
  set α := (g.stalkMap y').hom with hαdef
  obtain ⟨hz', -⟩ := hα.isRegularSystemOfParameters_image hz
  have hinj : Function.Injective α := RingHom.MapsRSOP.injective α hα
  have hJ' : ExtendsToRSOP (Y'.presheaf.stalk y') (J.image α) :=
    (ExtendsToRSOP.of_isRegularSystemOfParameters hz').mono (Finset.image_subset_image hJz)
  refine ⟨z.image α, hz', fun C hC hyC => ?_, T.image α, Finset.image_subset_image hTz, ?_⟩
  · have h1 := stalkIdeal_mem_minimalPrimes hC hyC
    rw [stalkIdeal_totalTransform, hEJ, Ideal.map_span, Set.image_singleton, map_prod,
      ← Finset.prod_image (f := fun a => a) (fun a _ b _ h => hinj h),
      hJ'.minimalPrimes_span_prod] at h1
    obtain ⟨a, haJ, ha⟩ := h1
    exact ⟨a, Finset.image_subset_image hJz (Finset.mem_coe.mp haJ), ha.symm⟩
  · rw [stalkIdeal_totalTransform, hDT, Ideal.map_span, Finset.coe_image]

/-- Normal crossings read off a stalk presentation `E_x = (∏_J a)`, `D_x = (T)` by a part of a
regular system of parameters (the converse half of `hasOnlyNormalCrossingsWithAt_iff`, which does
not need `E` to be reduced). -/
theorem hasOnlyNormalCrossingsWithAt_of_stalkIdeal_eq {E D : Subscheme Y} {x : Y}
    [IsRegularLocalRing (Y.presheaf.stalk x)] {z : Finset (Y.presheaf.stalk x)}
    (hz : IsRegularSystemOfParameters _ z) {J T : Finset (Y.presheaf.stalk x)} (hJz : J ⊆ z)
    (hTz : T ⊆ z) (hE : E.stalkIdeal x = Ideal.span {∏ a ∈ J, a})
    (hD : D.stalkIdeal x = Ideal.span (T : Set (Y.presheaf.stalk x))) :
    E.HasOnlyNormalCrossingsWithAt D x := by
  classical
  have hJext := (ExtendsToRSOP.of_isRegularSystemOfParameters hz).mono hJz
  refine ⟨z, hz, fun C hC hxC => ?_, ⟨T, hTz, hD⟩⟩
  have h1 := stalkIdeal_mem_minimalPrimes hC hxC
  rw [hE, hJext.minimalPrimes_span_prod] at h1
  obtain ⟨a, haJ, ha⟩ := h1
  exact ⟨a, hJz haJ, ha.symm⟩

open Classical in
/-- The quotient of the local ring of `Y` at `D.ι x'` by the stalk of the ideal sheaf of `D`,
generated by part `T` of a regular system of parameters `z`, is the local ring of `D` at `x'`: it is
regular, the images of `z \ T` form a regular system of parameters, and no two are identified. -/
theorem exists_quotient_rsop_data {D : Subscheme Y} (x' : D.toScheme)
    [IsRegularLocalRing (Y.presheaf.stalk (D.ι x'))] {z T : Finset (Y.presheaf.stalk (D.ι x'))}
    (hz : IsRegularSystemOfParameters _ z) (hTz : T ⊆ z)
    (hDT : D.stalkIdeal (D.ι x') = Ideal.span (T : Set (Y.presheaf.stalk (D.ι x')))) :
    ∃ (_ : IsRegularLocalRing (D.toScheme.presheaf.stalk x')),
      IsRegularSystemOfParameters _ ((z \ T).image (D.ι.stalkMap x').hom) ∧
      Set.InjOn (D.ι.stalkMap x').hom (z \ T : Finset _) := by
  classical
  set φ := (D.ι.stalkMap x').hom with hφ
  have hsurj : Function.Surjective φ := D.ι.stalkMap_surjective x'
  have hker : RingHom.ker φ = Ideal.span (T : Set (Y.presheaf.stalk (D.ι x'))) := by
    rw [← hDT]; exact (stalkIdeal_eq_ker_stalkMap D x').symm
  obtain ⟨hreg, hrs, hcard⟩ := rsop_quotient hz hTz
  let e : (Y.presheaf.stalk (D.ι x') ⧸ Ideal.span (T : Set (Y.presheaf.stalk (D.ι x')))) ≃+*
      D.toScheme.presheaf.stalk x' :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have heφ : ∀ a, e (Ideal.Quotient.mk _ a) = φ a := fun a => rfl
  have hregS : IsRegularLocalRing (D.toScheme.presheaf.stalk x') :=
    IsRegularLocalRing.of_ringEquiv e
  refine ⟨hregS, ?_, ?_⟩
  · have := isRegularSystemOfParameters_image_ringEquiv e hrs
    rw [Finset.image_image] at this
    exact this
  · intro a ha b hb hab
    have hcard' : (((z \ T).image (Ideal.Quotient.mk (Ideal.span (T : Set (Y.presheaf.stalk
        (D.ι x')))))).card) = (z \ T).card := hcard
    have := Finset.card_image_iff.mp hcard'
    exact this ha hb (e.injective (by simpa [heφ] using hab))

/-- **Restriction of normal crossings to a transversal subscheme** (p. 321: "`Ẽ_j = Ê_j(s) ∩ X̃`
… `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on `X̃`").  If a reduced `E` has only normal
crossings with `D` at `x = ι(x')`, no component of `E` through `x` contains `D` near `x` (stalkwise,
`C_x ⊄ D_x`), then the total transform of `E` to `D` has a stalk at `x'` presented by part of a
regular system of parameters of `O_{D,x'}`. -/
theorem exists_stalk_presentation_totalTransform_ι {E D : Subscheme Y} (hE : E.IsReduced)
    (x' : D.toScheme) [IsRegularLocalRing (Y.presheaf.stalk (D.ι x'))]
    (h : E.HasOnlyNormalCrossingsWithAt D (D.ι x'))
    (hT : ∀ C ∈ E.irreducibleComponents, D.ι x' ∈ C.pts →
      ¬ C.stalkIdeal (D.ι x') ≤ D.stalkIdeal (D.ι x')) :
    ∃ (_ : IsRegularLocalRing (D.toScheme.presheaf.stalk x'))
      (zb : Finset (D.toScheme.presheaf.stalk x')) (Jb : Finset (D.toScheme.presheaf.stalk x')),
      IsRegularSystemOfParameters _ zb ∧ Jb ⊆ zb ∧
      (totalTransform D.ι E).stalkIdeal x' = Ideal.span {∏ a ∈ Jb, a} := by
  classical
  obtain ⟨z, hz, ⟨J, hJz, hEJ⟩, ⟨T, hTz, hDT⟩⟩ :=
    (hasOnlyNormalCrossingsWithAt_iff hE
      (by exact ‹IsRegularLocalRing (Y.presheaf.stalk (D.ι x'))›)).mp h
  have hzext := ExtendsToRSOP.of_isRegularSystemOfParameters hz
  have hJT : ∀ a ∈ J, a ∉ T := by
    intro a haJ haT
    have hmin : Ideal.span {a} ∈ (E.stalkIdeal (D.ι x')).minimalPrimes := by
      rw [hEJ, (hzext.mono hJz).minimalPrimes_span_prod]
      exact ⟨a, haJ, rfl⟩
    obtain ⟨C, hC, hxC, hCa⟩ := exists_mem_irreducibleComponents_of_mem_minimalPrimes E _ hmin
    refine hT C hC hxC ?_
    rw [hCa, hDT, Ideal.span_singleton_le_iff_mem]
    exact Ideal.subset_span haT
  obtain ⟨hregS, hrsS, hinj⟩ := exists_quotient_rsop_data x' hz hTz hDT
  refine ⟨hregS, _, J.image (D.ι.stalkMap x').hom, hrsS, Finset.image_subset_image
    (fun a ha => Finset.mem_sdiff.mpr ⟨hJz ha, hJT a ha⟩), ?_⟩
  rw [stalkIdeal_totalTransform, hEJ, Ideal.map_span, Set.image_singleton, map_prod,
    Finset.prod_image (f := fun a => a) (fun a ha b hb h => hinj
      (Finset.mem_sdiff.mpr ⟨hJz ha, hJT a ha⟩) (Finset.mem_sdiff.mpr ⟨hJz hb, hJT b hb⟩) h)]

/-- Normal crossings of the restriction `E ∩ D` at the point `x'` of `D`. -/
theorem hasOnlyNormalCrossingsAt_totalTransform_ι {E D : Subscheme Y} (hE : E.IsReduced)
    (x' : D.toScheme) [IsRegularLocalRing (Y.presheaf.stalk (D.ι x'))]
    (h : E.HasOnlyNormalCrossingsWithAt D (D.ι x'))
    (hT : ∀ C ∈ E.irreducibleComponents, D.ι x' ∈ C.pts →
      ¬ C.stalkIdeal (D.ι x') ≤ D.stalkIdeal (D.ι x')) :
    (totalTransform D.ι E).HasOnlyNormalCrossingsAt x' := by
  obtain ⟨hreg, zb, Jb, hzb, hJb, hst⟩ := exists_stalk_presentation_totalTransform_ι hE x' h hT
  exact hasOnlyNormalCrossingsWithAt_of_stalkIdeal_eq (D := ⊥) hzb hJb (Finset.empty_subset _)
    hst (by rw [stalkIdeal_bot_eq]; simp)

/-- The intersection of the ideals `(∏ K_j)` is generated by the product over the union, for
families inside a regular system of parameters. -/
theorem iInf_span_prod_biUnion {R : Type u} [CommRing R] [IsRegularLocalRing R]
    {ι : Type*} [Fintype ι] [DecidableEq R] (K : ι → Finset R)
    (h : ExtendsToRSOP R (Finset.univ.biUnion K)) :
    ⨅ j, Ideal.span {∏ a ∈ K j, a} = Ideal.span {∏ a ∈ Finset.univ.biUnion K, a} := by
  have hK : ∀ j, ExtendsToRSOP R (K j) := fun j =>
    h.mono (Finset.subset_biUnion_of_mem K (Finset.mem_univ j))
  simp_rw [← (hK _).iInf_span_singleton, ← h.iInf_span_singleton]
  refine le_antisymm (le_iInf₂ fun a ha => ?_) (le_iInf fun j => le_iInf₂ fun a ha => ?_)
  · obtain ⟨j, -, haj⟩ := Finset.mem_biUnion.mp ha
    exact (iInf_le _ j).trans (iInf₂_le a haj)
  · exact iInf₂_le a (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩)

/-- A prime of height one containing `(∏ J)`, `J` part of a regular system of parameters, is
generated by a member of `J`. -/
theorem exists_eq_span_of_prod_mem {R : Type u} [CommRing R] [IsRegularLocalRing R]
    {J z : Finset R} (hz : IsRegularSystemOfParameters R z) (hJz : J ⊆ z) {P : Ideal R}
    [P.IsPrime] (hP : P.height = 1) (hle : Ideal.span {∏ a ∈ J, a} ≤ P) :
    ∃ a ∈ J, P = Ideal.span {a} := by
  have hzext := ExtendsToRSOP.of_isRegularSystemOfParameters hz
  have h1 : ∏ a ∈ J, a ∈ P := hle (Ideal.mem_span_singleton_self _)
  obtain ⟨a, haJ, haP⟩ := (Ideal.IsPrime.prod_mem_iff (x := fun k : R => k)).mp h1
  have hprime := hzext.isPrime_span_singleton (hJz haJ)
  have ha0 : Ideal.span {a} ≠ ⊥ := by
    intro h0
    have := rsop_notMem_span hz (Finset.empty_subset z) (hJz haJ) (Finset.notMem_empty a)
    apply this
    rw [Finset.coe_empty, Ideal.span_empty, ← h0]
    exact Ideal.mem_span_singleton_self a
  have hle' : Ideal.span {a} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr haP
  have : IsDomain R := Transforms.isDomain_of_isRegularLocalRing R
  exact ⟨a, haJ, (Hironaka.DatumTransform.eq_of_le_of_height_eq_one hle' ha0 hP).symm⟩

open Classical in
/-- **Family version** (p. 321): let `E_j` be non-singular of codimension one at the points of
`E_j` (their ideals are prime of height one there), such that `⨅ E_j` is reduced and has only normal
crossings with `D` at `x = ι(x')`, no `E_j` through `x` having stalk contained in that of `D`
(i.e. `D` is not locally contained in `E_j`).  Then the stalks of the total transforms `E_j ∩ D`
at `x'` are generated by single members `b_j` of one regular system of parameters of `O_{D,x'}`
(or are the unit ideal), and the stalk of `⨅ (E_j ∩ D)` by the product of the distinct `b_j`. -/
theorem exists_stalk_presentation_iInf_totalTransform_ι {ι : Type*} [Fintype ι]
    {E : ι → Subscheme Y} {D : Subscheme Y} (hE : (⨅ j, E j).IsReduced) (x' : D.toScheme)
    [IsRegularLocalRing (Y.presheaf.stalk (D.ι x'))]
    (h : (⨅ j, E j).HasOnlyNormalCrossingsWithAt D (D.ι x'))
    (hsimple : ∀ j, D.ι x' ∈ (E j).pts →
      (E j).IsSimpleAt (D.ι x') ∧ (E j).codimAt (D.ι x') = 1)
    (hT : ∀ j, D.ι x' ∈ (E j).pts → ¬ (E j).stalkIdeal (D.ι x') ≤ D.stalkIdeal (D.ι x')) :
    ∃ (_ : IsRegularLocalRing (D.toScheme.presheaf.stalk x'))
      (zb : Finset (D.toScheme.presheaf.stalk x')) (K : ι → Finset (D.toScheme.presheaf.stalk x')),
      IsRegularSystemOfParameters _ zb ∧ (∀ j, K j ⊆ zb) ∧
      (∀ j, D.ι x' ∈ (E j).pts → ∃ b ∈ zb, K j = {b}) ∧
      (∀ j, D.ι x' ∉ (E j).pts → K j = ∅) ∧
      (∀ j, (totalTransform D.ι (E j)).stalkIdeal x' = Ideal.span {∏ a ∈ K j, a}) ∧
      (⨅ j, totalTransform D.ι (E j)).stalkIdeal x' =
        Ideal.span {∏ a ∈ Finset.univ.biUnion K, a} ∧
      (∀ j j', K j = K j' → (E j).stalkIdeal (D.ι x') = (E j').stalkIdeal (D.ι x')) := by
  obtain ⟨z, hz, ⟨J, hJz, hEJ⟩, ⟨T, hTz, hDT⟩⟩ :=
    (hasOnlyNormalCrossingsWithAt_iff hE
      (by exact ‹IsRegularLocalRing (Y.presheaf.stalk (D.ι x'))›)).mp h
  have key : ∀ j, ∃ A : Finset (Y.presheaf.stalk (D.ι x')), A ⊆ J ∧ (∀ a ∈ A, a ∉ T) ∧
      (D.ι x' ∈ (E j).pts → ∃ a, A = {a} ∧ (E j).stalkIdeal (D.ι x') = Ideal.span {a}) ∧
      (D.ι x' ∉ (E j).pts → A = ∅ ∧ (E j).stalkIdeal (D.ι x') = ⊤) := by
    intro j
    by_cases hx : D.ι x' ∈ (E j).pts
    · obtain ⟨hs, hc⟩ := hsimple j hx
      have hreg : IsRegularLocalRing (Y.presheaf.stalk (D.ι x') ⧸ (E j).stalkIdeal (D.ι x')) :=
        hs.2
      have hPp : ((E j).stalkIdeal (D.ι x')).IsPrime :=
        (Ideal.Quotient.isDomain_iff_prime _).mp (Transforms.isDomain_of_isRegularLocalRing _)
      have hle : Ideal.span {∏ a ∈ J, a} ≤ (E j).stalkIdeal (D.ι x') := by
        rw [← hEJ, DatumTransform.stalkIdeal_iInf_fintype]
        exact iInf_le _ j
      obtain ⟨a, haJ, hPa⟩ := exists_eq_span_of_prod_mem hz hJz hc hle
      refine ⟨{a}, Finset.singleton_subset_iff.mpr haJ, ?_, fun _ => ⟨a, rfl, hPa⟩,
        fun hx' => absurd hx hx'⟩
      intro b hb haT
      rw [Finset.mem_singleton] at hb
      subst hb
      refine hT j hx ?_
      rw [hPa, hDT, Ideal.span_singleton_le_iff_mem]
      exact Ideal.subset_span haT
    · exact ⟨∅, Finset.empty_subset _, fun a ha => absurd ha (Finset.notMem_empty a),
        fun hx' => absurd hx' hx, fun _ => ⟨rfl, stalkIdeal_eq_top_of_notMem_pts hx⟩⟩
  choose A hAJ hAT hA1 hA0 using key
  obtain ⟨hregS, hrsS, hinj⟩ := exists_quotient_rsop_data x' hz hTz hDT
  set φ := (D.ι.stalkMap x').hom with hφ
  have hAzT : ∀ j, (A j : Set _) ⊆ (z \ T : Finset _) := fun j a ha =>
    Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨hJz (hAJ j ha), hAT j a ha⟩)
  refine ⟨hregS, _, fun j => (A j).image φ, hrsS,
    fun j => Finset.image_subset_image (fun a ha => Finset.mem_coe.mp (hAzT j ha)), ?_, ?_, ?_, ?_, ?_⟩
  · intro j hx
    obtain ⟨a, haA, -⟩ := hA1 j hx
    refine ⟨φ a, Finset.mem_image_of_mem φ (Finset.mem_coe.mp (hAzT j (by rw [haA]; simp))), ?_⟩
    beta_reduce
    rw [haA, Finset.image_singleton]
  · intro j hx
    beta_reduce
    rw [(hA0 j hx).1, Finset.image_empty]
  · intro j
    beta_reduce
    by_cases hx : D.ι x' ∈ (E j).pts
    · obtain ⟨a, haA, hEa⟩ := hA1 j hx
      rw [stalkIdeal_totalTransform, hEa, Ideal.map_span, Set.image_singleton, haA,
        Finset.image_singleton, Finset.prod_singleton]
    · obtain ⟨hA, hEt⟩ := hA0 j hx
      rw [stalkIdeal_totalTransform, hEt, Ideal.map_top, hA, Finset.image_empty,
        Finset.prod_empty, Ideal.span_singleton_one]
  · have hext : ExtendsToRSOP _ (Finset.univ.biUnion fun j => (A j).image φ) :=
      (ExtendsToRSOP.of_isRegularSystemOfParameters hrsS).mono (Finset.biUnion_subset.mpr
        fun j _ => Finset.image_subset_image (fun a ha => Finset.mem_coe.mp (hAzT j ha)))
    rw [DatumTransform.stalkIdeal_iInf_fintype, ← iInf_span_prod_biUnion _ hext]
    refine iInf_congr fun j => ?_
    beta_reduce
    by_cases hx : D.ι x' ∈ (E j).pts
    · obtain ⟨a, haA, hEa⟩ := hA1 j hx
      rw [stalkIdeal_totalTransform, hEa, Ideal.map_span, Set.image_singleton, haA,
        Finset.image_singleton, Finset.prod_singleton]
    · obtain ⟨hA, hEt⟩ := hA0 j hx
      rw [stalkIdeal_totalTransform, hEt, Ideal.map_top, hA, Finset.image_empty,
        Finset.prod_empty, Ideal.span_singleton_one]
  · intro j j' hjj'
    have hAA : A j = A j' := by
      have hmem : ∀ i i', (A i).image φ = (A i').image φ → ∀ a ∈ A i, a ∈ A i' := by
        intro i i' hii' a ha
        have : φ a ∈ (A i').image φ := by
          rw [← hii']; exact Finset.mem_image_of_mem φ ha
        obtain ⟨a', ha', hφa⟩ := Finset.mem_image.mp this
        have := hinj (hAzT i' ha') (hAzT i ha) hφa
        rwa [this] at ha'
      exact Finset.Subset.antisymm (hmem j j' hjj') (hmem j' j hjj'.symm)
    have hst : ∀ i, (E i).stalkIdeal (D.ι x') = Ideal.span {∏ a ∈ A i, a} := by
      intro i
      by_cases hx : D.ι x' ∈ (E i).pts
      · obtain ⟨a, haA, hEa⟩ := hA1 i hx
        rw [hEa, haA, Finset.prod_singleton]
      · obtain ⟨hA, hEt⟩ := hA0 i hx
        rw [hEt, hA, Finset.prod_empty, Ideal.span_singleton_one]
    rw [hst j, hst j', hAA]

/-- The points of the total transform to `D` of `E` are the points of `D` lying on `E`. -/
theorem mem_pts_totalTransform_subschemeι_iff {E D : Subscheme Y} (x' : D.toScheme) :
    x' ∈ (totalTransform D.ι E).pts ↔ D.ι x' ∈ E.pts := by
  change x' ∈ ((E.comap D.ι).support : Set D.toScheme) ↔ _
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- The hypotheses of the family theorems at every point of `D` (the global form). -/
def IsTransversalFamilyWith {ι : Type*} (E : ι → Subscheme Y) (D : Subscheme Y) : Prop :=
  (∀ j, ∀ x ∈ (E j).pts ∩ D.pts, (E j).IsSimpleAt x ∧ (E j).codimAt x = 1) ∧
  (∀ j, ∀ x ∈ (E j).pts ∩ D.pts, ¬ (E j).stalkIdeal x ≤ D.stalkIdeal x)

/-- **p. 321: `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on `X̃`.**  For a finite family of
non-singular divisors `E_j` of the non-singular scheme `Y` whose union is reduced and has only
normal crossings with `D`, and such that `D` is not locally contained in any `E_j`.

Deviation from the paper (gap filled): "we see that … `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on
`X̃`" (p. 321) is proved here from the local presentations by parts of one regular system of
parameters. -/
@[blueprint "lem:IV.4-tilde-facts-local"
  (statement := /-- Let $Y$ be a non-singular scheme, $D\subseteq Y$ a subscheme and $E_1,\dots,E_k$
    non-singular subschemes of $Y$ of codimension one such that $E_1\cup\dots\cup E_k$ is reduced
    and has only normal crossings with $D$ and no $E_j$ contains $D$ near a point of $D$. Then
    $\tilde E_1\cup\dots\cup\tilde E_k$, $\tilde E_j=E_j\cap D$, has only normal crossings on $D$,
    each $\tilde E_j$ is non-singular and everywhere of codimension one on $D$. (Used on p.~321.) -/)
  (proof := /-- At a point $x$ of $D$, $D_x=(T)$ and $(E_1\cup\dots\cup E_k)_x=(\prod_Ja)$ for parts
    $J,T$ of a regular system of parameters $z$ of $\mathcal O_{Y,x}$; each $E_{j,x}$ is a prime of
    height one containing $(\prod_Ja)$, hence equal to $(a_j)$ with $a_j\in J$, and $a_j\notin T$
    because $D$ is not contained in $E_j$. The images of $z\setminus T$ form a regular system of
    parameters of $\mathcal O_{D,x}=\mathcal O_{Y,x}/(T)$ and $\tilde E_{j,x}=(\bar a_j)$,
    $(\bigcup\tilde E_j)_x=(\prod\bar a_j)$.

    \textbf{Deviation from the paper (gap filled).} The paper writes ``we see that \dots\ has only
    normal crossings on $\tilde X$'' (p.~321). Lean proves it from the local presentations above. -/)
  (latexEnv := "lemma")]
theorem hasOnlyNormalCrossings_iInf_totalTransform_ι {ι : Type*} [Fintype ι]
    {E : ι → Subscheme Y} {D : Subscheme Y} (hY : Y.IsNonsingular) (hE : (⨅ j, E j).IsReduced)
    (hNC : (⨅ j, E j).HasOnlyNormalCrossingsWith D) (hF : IsTransversalFamilyWith E D) :
    (⨅ j, totalTransform D.ι (E j)).HasOnlyNormalCrossings := by
  intro x'
  have hx : D.ι x' ∈ D.pts := mem_pts_ι D x'
  have : IsRegularLocalRing (Y.presheaf.stalk (D.ι x')) := hY (D.ι x')
  obtain ⟨hreg, zb, K, hzb, hKz, -, -, -, hst, -⟩ := exists_stalk_presentation_iInf_totalTransform_ι
    hE x' (hNC _ hx) (fun j hj => hF.1 j _ ⟨hj, hx⟩) (fun j hj => hF.2 j _ ⟨hj, hx⟩)
  classical
  exact hasOnlyNormalCrossingsWithAt_of_stalkIdeal_eq (D := ⊥) hzb
    (Finset.biUnion_subset.mpr fun j _ => hKz j) (Finset.empty_subset _) hst
    (by rw [stalkIdeal_bot_eq]; simp)

/-- **p. 321: the `Ẽ_j` are non-singular and everywhere of codimension one on `X̃`** (the
irreducibility asserted there is not a local statement and is not covered). -/
theorem isNonsingular_and_isEverywhereOfCodim_totalTransform_ι {ι : Type*} [Fintype ι]
    {E : ι → Subscheme Y} {D : Subscheme Y} (hY : Y.IsNonsingular) (hE : (⨅ j, E j).IsReduced)
    (hNC : (⨅ j, E j).HasOnlyNormalCrossingsWith D) (hF : IsTransversalFamilyWith E D) (j : ι) :
    (totalTransform D.ι (E j)).IsNonsingular ∧ (totalTransform D.ι (E j)).IsEverywhereOfCodim 1 := by
  classical
  have key : ∀ x' : D.toScheme, x' ∈ (totalTransform D.ι (E j)).pts →
      IsRegularLocalRing (D.toScheme.presheaf.stalk x' ⧸
        (totalTransform D.ι (E j)).stalkIdeal x') ∧
      (totalTransform D.ι (E j)).codimAt x' = 1 := by
    intro x' hx'
    have hxE : D.ι x' ∈ (E j).pts := (mem_pts_totalTransform_subschemeι_iff x').mp hx'
    have hx : D.ι x' ∈ D.pts := mem_pts_ι D x'
    have : IsRegularLocalRing (Y.presheaf.stalk (D.ι x')) := hY (D.ι x')
    obtain ⟨hreg, zb, K, hzb, hKz, hK1, -, hstj, -, -⟩ := exists_stalk_presentation_iInf_totalTransform_ι
      hE x' (hNC _ hx) (fun j hj => hF.1 j _ ⟨hj, hx⟩) (fun j hj => hF.2 j _ ⟨hj, hx⟩)
    obtain ⟨b, hbz, hKb⟩ := hK1 j hxE
    have hext := ExtendsToRSOP.of_isRegularSystemOfParameters hzb
    have hid : (totalTransform D.ι (E j)).stalkIdeal x' = Ideal.span {b} := by
      rw [hstj j, hKb, Finset.prod_singleton]
    refine ⟨?_, ?_⟩
    · rw [hid]; exact hext.isRegularLocalRing_quotient_span_singleton hbz
    have hprime := hext.isPrime_span_singleton hbz
    have hb0 : Ideal.span {b} ≠ ⊥ := by
      intro h0
      have := rsop_notMem_span hzb (Finset.empty_subset zb) hbz (Finset.notMem_empty b)
      apply this
      rw [Finset.coe_empty, Ideal.span_empty, ← h0]
      exact Ideal.mem_span_singleton_self b
    have : IsDomain (D.toScheme.presheaf.stalk x') := Transforms.isDomain_of_isRegularLocalRing _
    show ((totalTransform D.ι (E j)).stalkIdeal x').height = 1
    rw [hid]
    refine le_antisymm ?_ ?_
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {b}) _
        ⟨⟨hprime, le_rfl⟩, fun Q hQ _ => hQ.2⟩
    · exact Order.one_le_iff_ne_zero.mpr fun h0 => hb0 (Ideal.height_eq_zero_iff_eq_bot.mp h0)
  refine ⟨fun y => ?_, fun x' hx' => (key x' hx').2⟩
  have hx' : (totalTransform D.ι (E j)).ι y ∈ (totalTransform D.ι (E j)).pts :=
    mem_pts_ι _ y
  obtain ⟨e⟩ := nonempty_stalk_quot_equiv (totalTransform D.ι (E j)) y
  have := (key _ hx').1
  exact IsRegularLocalRing.of_ringEquiv e

/-- **p. 321: `Ẽ_j` is non-singular irreducible of codimension one** from the local facts and the
irreducibility (if `Ẽ_j` has a point it must be irreducible; this is the global input). -/
theorem isNonsingularIrreducibleCodimOne_totalTransform_ι {ι : Type*} [Fintype ι]
    {E : ι → Subscheme Y} {D : Subscheme Y} (hY : Y.IsNonsingular) (hE : (⨅ j, E j).IsReduced)
    (hNC : (⨅ j, E j).HasOnlyNormalCrossingsWith D) (hF : IsTransversalFamilyWith E D) (j : ι)
    (hirr : (totalTransform D.ι (E j)).pts.Nonempty → (totalTransform D.ι (E j)).IsIrreducible) :
    (totalTransform D.ι (E j)).IsNonsingularIrreducibleCodimOne := by
  by_cases hne : (totalTransform D.ι (E j)).pts.Nonempty
  · obtain ⟨h1, h2⟩ := isNonsingular_and_isEverywhereOfCodim_totalTransform_ι hY hE hNC hF j
    refine Or.inr ⟨h1, hirr hne, ?_⟩
    obtain ⟨x, hx⟩ := hne
    refine le_antisymm (iInf₂_le x hx |>.trans (h2 x hx).le) (le_iInf₂ fun y hy => (h2 y hy).ge)
  · left
    exact eq_empty_of_pts_eq_empty (Set.not_nonempty_iff_eq_empty.mp hne)

/-- Replacing `D` by a subscheme with the same stalks at the points in question. -/
theorem hasOnlyNormalCrossingsWithAt_congr_right {E D D' : Subscheme Y} {x : Y}
    (h : E.HasOnlyNormalCrossingsWithAt D x) (hD : D.stalkIdeal x = D'.stalkIdeal x) :
    E.HasOnlyNormalCrossingsWithAt D' x := by
  obtain ⟨z, hz, hc, t, htz, ht⟩ := h
  exact ⟨z, hz, hc, t, htz, hD ▸ ht⟩

/-- Global form of the pull-back: if `g` induces on the local rings at the points of `g⁻¹D` maps
sending regular systems of parameters to such systems, then `g⁻¹E` has only normal crossings with
`g⁻¹D`. -/
theorem hasOnlyNormalCrossingsWith_totalTransform_of_mapsRSOP (g : Y' ⟶ Y)
    (hY : Y.IsNonsingular) (hY' : Y'.IsNonsingular) {E D : Subscheme Y} (hE : E.IsReduced)
    (hmaps : ∀ y' ∈ (totalTransform g D).pts, RingHom.MapsRSOP (g.stalkMap y').hom)
    (h : E.HasOnlyNormalCrossingsWith D) :
    (totalTransform g E).HasOnlyNormalCrossingsWith (totalTransform g D) := by
  intro y' hy'
  have : IsRegularLocalRing (Y.presheaf.stalk (g y')) := hY (g y')
  have : IsRegularLocalRing (Y'.presheaf.stalk y') := hY' y'
  refine hasOnlyNormalCrossingsWithAt_totalTransform_of_mapsRSOP g y' (hmaps y' hy') hE
    (h (g y') ?_)
  have : y' ∈ g ⁻¹' D.pts := by
    have h1 : y' ∈ (totalTransform g D).pts := hy'
    change y' ∈ ((D.comap g).support : Set Y') at h1
    rw [Scheme.IdealSheafData.support_comap] at h1
    exact h1
  exact this

end Subscheme

open Classical in
/-- A homomorphism of local rings transforms every regular system of parameters of `R` into a system
extendable to a regular system of parameters of `R'` (p. 320: "the local homomorphism
`S'_s → Ŝ'_s` transforms a regular system of parameters of `S'_s` into a system of elements of
`Ŝ'_s` which can be extended to a regular system of parameters of `Ŝ'_s`"), with distinct images.
Weaker than `RingHom.MapsRSOP`, which asks for a regular system of parameters of `R'`; this is what
holds at every point of `X̂_s` (class `𝔅`), not only over `x̂_0`. -/
def RingHom.MapsToPartRSOP {R R' : Type u} [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R']
    (α : R →+* R') : Prop :=
  ∀ z : Finset R, IsRegularSystemOfParameters R z →
    Set.InjOn α z ∧ ExtendsToRSOP R' (z.image α)

namespace Subscheme

variable {Y' Y : Scheme.{u}}

/-- Normal crossings are preserved by total transforms along a morphism whose stalk map at the
point transforms regular systems of parameters into systems extendable to regular systems of
parameters.

Deviation from the paper (gap filled): on p. 321 the paper only says "we see that `Ê_1(s) ∪ ⋯ ∪
Ê_{α+s}(s)` has only normal crossings with `X̃` in `X̂_s`"; the property of `c_s` it invokes is the
one of p. 320, "transforms a regular system of parameters of `S'_s` into a system of elements of
`Ŝ'_s` which can be extended to a regular system of parameters of `Ŝ'_s`", valid at every point of
`X̂_s`; `hasOnlyNormalCrossingsWithAt_totalTransform_of_mapsRSOP` is the case of a regular system
of parameters. -/
theorem hasOnlyNormalCrossingsWithAt_totalTransform_of_mapsToPartRSOP (g : Y' ⟶ Y) (y' : Y')
    [IsRegularLocalRing (Y.presheaf.stalk (g y'))] [IsRegularLocalRing (Y'.presheaf.stalk y')]
    (hα : RingHom.MapsToPartRSOP (g.stalkMap y').hom)
    {E D : Subscheme Y} (hE : E.IsReduced) (h : E.HasOnlyNormalCrossingsWithAt D (g y')) :
    (totalTransform g E).HasOnlyNormalCrossingsWithAt (totalTransform g D) y' := by
  classical
  obtain ⟨z, hz, ⟨J, hJz, hEJ⟩, ⟨T, hTz, hDT⟩⟩ :=
    (hasOnlyNormalCrossingsWithAt_iff hE (by exact ‹IsRegularLocalRing (Y.presheaf.stalk (g y'))›)).mp h
  set α := (g.stalkMap y').hom with hαdef
  obtain ⟨hinj, Z', hZ'sub, hZ'⟩ := hα z hz
  have hinjJ : Set.InjOn α (J : Set _) := hinj.mono (by exact_mod_cast hJz)
  have hJ' : ExtendsToRSOP (Y'.presheaf.stalk y') (J.image α) :=
    ⟨Z', (Finset.image_subset_image hJz).trans hZ'sub, hZ'⟩
  refine ⟨Z', hZ', fun C hC hyC => ?_, T.image α,
    (Finset.image_subset_image hTz).trans hZ'sub, ?_⟩
  · have h1 := stalkIdeal_mem_minimalPrimes hC hyC
    rw [stalkIdeal_totalTransform, hEJ, Ideal.map_span, Set.image_singleton, map_prod,
      ← Finset.prod_image (f := fun a => a) (fun a ha b hb h => hinjJ ha hb h),
      hJ'.minimalPrimes_span_prod] at h1
    obtain ⟨a, haJ, ha⟩ := h1
    exact ⟨a, (Finset.image_subset_image hJz).trans hZ'sub (Finset.mem_coe.mp haJ), ha.symm⟩
  · rw [stalkIdeal_totalTransform, hDT, Ideal.map_span, Finset.coe_image]

/-- Global form of the pull-back, for maps that transform regular systems of parameters into
extendable systems at the points of `g⁻¹D`. -/
theorem hasOnlyNormalCrossingsWith_totalTransform_of_mapsToPartRSOP (g : Y' ⟶ Y)
    (hY : Y.IsNonsingular) (hY' : Y'.IsNonsingular) {E D : Subscheme Y} (hE : E.IsReduced)
    (hmaps : ∀ y' ∈ (totalTransform g D).pts, RingHom.MapsToPartRSOP (g.stalkMap y').hom)
    (h : E.HasOnlyNormalCrossingsWith D) :
    (totalTransform g E).HasOnlyNormalCrossingsWith (totalTransform g D) := by
  intro y' hy'
  have : IsRegularLocalRing (Y.presheaf.stalk (g y')) := hY (g y')
  have : IsRegularLocalRing (Y'.presheaf.stalk y') := hY' y'
  refine hasOnlyNormalCrossingsWithAt_totalTransform_of_mapsToPartRSOP g y' (hmaps y' hy') hE
    (h (g y') ?_)
  have : y' ∈ g ⁻¹' D.pts := by
    have h1 : y' ∈ (totalTransform g D).pts := hy'
    change y' ∈ ((D.comap g).support : Set Y') at h1
    rw [Scheme.IdealSheafData.support_comap] at h1
    exact h1
  exact this

end Subscheme

namespace Subscheme

variable {Y : Scheme.{u}}

/-- **Pointwise form** of `hasOnlyNormalCrossings_iInf_totalTransform_ι` (p. 321, p. 308): the
hypotheses are only needed at the point `ι(x')`. -/
theorem hasOnlyNormalCrossingsAt_iInf_totalTransform_ι {ι : Type*} [Fintype ι]
    {E : ι → Subscheme Y} {D : Subscheme Y} (hE : (⨅ j, E j).IsReduced) (x' : D.toScheme)
    [IsRegularLocalRing (Y.presheaf.stalk (D.ι x'))]
    (hNC : (⨅ j, E j).HasOnlyNormalCrossingsWithAt D (D.ι x'))
    (hsimple : ∀ j, D.ι x' ∈ (E j).pts →
      (E j).IsSimpleAt (D.ι x') ∧ (E j).codimAt (D.ι x') = 1)
    (hT : ∀ j, D.ι x' ∈ (E j).pts → ¬ (E j).stalkIdeal (D.ι x') ≤ D.stalkIdeal (D.ι x')) :
    (⨅ j, totalTransform D.ι (E j)).HasOnlyNormalCrossingsAt x' := by
  classical
  obtain ⟨hreg, zb, K, hzb, hKz, -, -, -, hst, -⟩ := exists_stalk_presentation_iInf_totalTransform_ι
    hE x' hNC hsimple hT
  exact hasOnlyNormalCrossingsWithAt_of_stalkIdeal_eq (D := ⊥) hzb
    (Finset.biUnion_subset.mpr fun j _ => hKz j) (Finset.empty_subset _) hst
    (by rw [stalkIdeal_bot_eq]; simp)

/-- **Pointwise form** of `isNonsingular_and_isEverywhereOfCodim_totalTransform_ι`: `E_j ∩ D` is
simple of codimension one at the point `x'` of `D` lying on it. -/
theorem isSimpleAt_and_codimAt_eq_one_totalTransform_ι {ι : Type*} [Fintype ι]
    {E : ι → Subscheme Y} {D : Subscheme Y} (hE : (⨅ j, E j).IsReduced) (x' : D.toScheme)
    [IsRegularLocalRing (Y.presheaf.stalk (D.ι x'))]
    (hNC : (⨅ j, E j).HasOnlyNormalCrossingsWithAt D (D.ι x'))
    (hsimple : ∀ j, D.ι x' ∈ (E j).pts →
      (E j).IsSimpleAt (D.ι x') ∧ (E j).codimAt (D.ι x') = 1)
    (hT : ∀ j, D.ι x' ∈ (E j).pts → ¬ (E j).stalkIdeal (D.ι x') ≤ D.stalkIdeal (D.ι x'))
    (j : ι) (hx' : x' ∈ (totalTransform D.ι (E j)).pts) :
    (totalTransform D.ι (E j)).IsSimpleAt x' ∧ (totalTransform D.ι (E j)).codimAt x' = 1 := by
  classical
  have hxE : D.ι x' ∈ (E j).pts := (mem_pts_totalTransform_subschemeι_iff x').mp hx'
  obtain ⟨hreg, zb, K, hzb, hKz, hK1, -, hstj, -, -⟩ :=
    exists_stalk_presentation_iInf_totalTransform_ι hE x' hNC hsimple hT
  obtain ⟨b, hbz, hKb⟩ := hK1 j hxE
  have hext := ExtendsToRSOP.of_isRegularSystemOfParameters hzb
  have hid : (totalTransform D.ι (E j)).stalkIdeal x' = Ideal.span {b} := by
    rw [hstj j, hKb, Finset.prod_singleton]
  refine ⟨⟨hx', ?_⟩, ?_⟩
  · rw [hid]; exact hext.isRegularLocalRing_quotient_span_singleton hbz
  have hprime := hext.isPrime_span_singleton hbz
  have hb0 : Ideal.span {b} ≠ ⊥ := by
    intro h0
    have := rsop_notMem_span hzb (Finset.empty_subset zb) hbz (Finset.notMem_empty b)
    apply this
    rw [Finset.coe_empty, Ideal.span_empty, ← h0]
    exact Ideal.mem_span_singleton_self b
  have : IsDomain (D.toScheme.presheaf.stalk x') := Transforms.isDomain_of_isRegularLocalRing _
  show ((totalTransform D.ι (E j)).stalkIdeal x').height = 1
  rw [hid]
  refine le_antisymm ?_ ?_
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {b}) _
      ⟨⟨hprime, le_rfl⟩, fun Q hQ _ => hQ.2⟩
  · exact Order.one_le_iff_ne_zero.mpr fun h0 => hb0 (Ideal.height_eq_zero_iff_eq_bot.mp h0)

end Subscheme

end Hironaka
