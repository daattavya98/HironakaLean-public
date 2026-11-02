/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Compat.StrictTransformExceptional
public import Hironaka.Ch3.Transforms

/-!
# Regularity of the strict transform along a regular center contained in it (Ch. IV, p. 298)

Pointwise, general form of the "we see" of p. 298 ("`f̄'_s` is the monoidal transformation with the
non-singular center `B̄'_s`"): for a monoidal transformation `t` with center `B` and a subscheme
`Z`, the strict transform `Z'` of `Z` is the blow-up of `Z` along `B ∩ Z`
(`Subscheme.nonempty_monoidalTransformation_strictTransform`), so at a point `q` of `Z'` over a
point
`p` at which `Z` is regular, and where `Z_p ⊆ B_p` with `O_p/B_p` regular if `p ∈ B`, the local ring
of `Z'` is regular and the exceptional divisor is regular of codimension one (Ch. III §2).
Irreducibility of `Z'` needs no regularity.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Hironaka

universe u

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X} (t : MonoidalTransformation X B)

/-- Pointwise form of `isRegularLocalRing_stalk`, `isRegularLocalRing_quotient_exceptional` and
`exceptional_isEverywhereOfCodim_one`: if `X` is regular at `f y` and, when `f y ∈ B`, the quotient
by the ideal of `B` is regular there, then `X'` is regular at `y`, and the exceptional divisor is
regular of codimension one at its points. -/
theorem isRegularLocalRing_stalk_and_exceptional_of_pointwise (y : t.X')
    [IsRegularLocalRing (X.presheaf.stalk (t.f y))]
    (hB : t.f y ∈ B.pts → IsRegularLocalRing (X.presheaf.stalk (t.f y) ⧸ B.stalkIdeal (t.f y))) :
    IsRegularLocalRing (t.X'.presheaf.stalk y) ∧
      (y ∈ t.exceptional.pts →
        IsRegularLocalRing (t.X'.presheaf.stalk y ⧸ t.exceptional.stalkIdeal y) ∧
          t.exceptional.codimAt y = 1) := by
  have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  by_cases hy : t.f y ∈ B.pts
  · have hS := hB hy
    have hP : (B.stalkIdeal (t.f y)).IsPrime := by
      have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y) ⧸
        B.stalkIdeal (t.f y))
      exact (Ideal.Quotient.isDomain_iff_prime _).mp this
    obtain ⟨s, e, -, hE⟩ := t.exists_monoidalTransform_stalk_exceptional y
    have hP0 : B.stalkIdeal (t.f y) ≠ ⊥ := fun h =>
      s.x_ne_zero ((Submodule.mem_bot _).mp (le_of_eq h s.x_mem))
    have hreg := (s.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map hP hP0 hS).1
    have hreg' : IsRegularLocalRing (t.X'.presheaf.stalk y) := IsRegularLocalRing.of_ringEquiv e
    refine ⟨hreg', fun hyE => ⟨?_, ?_⟩⟩
    · have := s.isRegularLocalRing_quotient_span_xR hP hS
      rw [hE]
      refine IsRegularLocalRing.of_ringEquiv
        (Ideal.quotientEquiv (Ideal.span {s.xR}) (Ideal.span {e s.xR}) e ?_)
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    · have := Transforms.isDomain_of_isRegularLocalRing (t.X'.presheaf.stalk y)
      have hg0 : e s.xR ≠ 0 := by
        rw [ne_eq, map_eq_zero_iff e e.injective]
        intro h
        exact s.x_ne_zero (s.toRing_injective (h.trans (map_zero _).symm))
      have hgu : ¬ IsUnit (e s.xR) := fun h =>
        Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hyE
          (by rw [hE]; exact Ideal.span_singleton_eq_top.mpr h)
      rw [Subscheme.codimAt, hE]
      exact_mod_cast Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hg0) hgu
  · refine ⟨IsRegularLocalRing.of_ringEquiv
      (RingEquiv.ofBijective (t.f.stalkMap y).hom (t.bijective_stalkMap_of_notMem y hy)),
      fun hyE => absurd (t.mem_pts_of_mem_exceptional hyE) hy⟩

end MonoidalTransformation

theorem map_ringEquiv_eq_top_iff {R S : Type*} [CommRing R] [CommRing S] (ε : R ≃+* S)
    (I : Ideal R) : I.map ε = ⊤ ↔ I = ⊤ := by
  refine ⟨fun h => ?_, fun h => by rw [h, Ideal.map_top]⟩
  have := Ideal.comap_map_of_bijective (f := ε.toRingHom) (by exact ε.bijective) (I := I)
  rw [show Ideal.map ε.toRingHom I = ⊤ from h, Ideal.comap_top] at this
  exact this.symm

namespace Subscheme

/-- Simplicity and codimension of a subscheme at a point are transported along an isomorphism of
schemes. -/
theorem isSimpleAt_and_codimAt_totalTransform_iso {W W' : Scheme.{u}} (e : W ⟶ W') [IsIso e]
    (D : Subscheme W') (y : W) :
    (D.IsSimpleAt (e y) ↔ (totalTransform e D).IsSimpleAt y) ∧
      D.codimAt (e y) = (totalTransform e D).codimAt y := by
  let ε : W'.presheaf.stalk (e y) ≃+* W.presheaf.stalk y :=
    (asIso (e.stalkMap y)).commRingCatIsoToRingEquiv
  have hI : (totalTransform e D).stalkIdeal y = (D.stalkIdeal (e y)).map ε := by
    rw [stalkIdeal_totalTransform]; rfl
  have hq : (W'.presheaf.stalk (e y) ⧸ D.stalkIdeal (e y)) ≃+*
      (W.presheaf.stalk y ⧸ (totalTransform e D).stalkIdeal y) :=
    Ideal.quotientEquiv _ _ ε hI
  have htop : (totalTransform e D).stalkIdeal y = ⊤ ↔ D.stalkIdeal (e y) = ⊤ := by
    rw [hI]; exact map_ringEquiv_eq_top_iff ε _
  refine ⟨?_, ?_⟩
  · unfold IsSimpleAt
    rw [mem_pts_iff_stalkIdeal_ne_top, mem_pts_iff_stalkIdeal_ne_top]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (htop.mp h), IsRegularLocalRing.of_ringEquiv hq⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (htop.mpr h), IsRegularLocalRing.of_ringEquiv hq.symm⟩
  · rw [codimAt, codimAt, hI, RingEquiv.height_map]

end Subscheme

namespace MonoidalTransformation

variable {Y : Scheme.{u}} {B : Subscheme Y}

/-- **The strict transform along a regular center contained in it is regular** (p. 298, "we see").
Let `t` be a monoidal transformation of `Y` with center `B`, `Z ⊆ Y` a subscheme, `Z'` its strict
transform and `fb : Z' → Z` the induced morphism.  Let `q` be a point of `Z'` with image `p` in
`Z`.  If `Z` is regular at `p` and, when `p ∈ B`, `Z_p ⊆ B_p` and `O_{Y,p}/B_p` is regular, then
`Z'` is regular at `q`, and the exceptional divisor of `Z' → Z` (the pull-back of `B ∩ Z`) is
regular of codimension one at `q` when it passes through `q`.

Deviation from the paper (gap filled), p. 298: "We see that `X̄'_{s+1}` is … non-singular" and
"`f̄'_s` is the monoidal transformation with the non-singular center `B̄'_s`" are asserted without
argument.  Lean identifies `Z'` with the blow-up of `Z` along `B ∩ Z`
(`nonempty_monoidalTransformation_strictTransform`) and applies the pointwise form of Ch. III §2
(`isRegularLocalRing_stalk_and_exceptional_of_pointwise`). -/
@[blueprint "lem:IV.3-strict-transform-regular"
  (statement := /-- Let $f\colon Y'\to Y$ be the monoidal transformation with center $B$, $Z$ a
    subscheme of $Y$, $Z'$ its strict transform, $\bar f\colon Z'\to Z$ the induced morphism and
    $q\in Z'$. Suppose that $Z$ is regular at $\bar f(q)$ and, if $\bar f(q)\in B$, that
    $Z_p\subseteq B_p$ and $\mathcal O_{Y,p}/B_p$ is regular. Then $Z'$ is regular at $q$, and the
    pull-back of $B\cap Z$ to $Z'$ is regular of codimension one at $q$ if it passes through $q$.
    (p.~298: ``We see that $\bar X'_{s+1}$ is \dots\ non-singular'' and ``$\bar f'_s$ is the
    monoidal transformation with the non-singular center $\bar B'_s$''.) -/)
  (proof := /-- The strict transform $Z'$ is the monoidal transformation of $Z$ with center
    $B\cap Z$ (\cref{lem:strict-transform-is-blowup}); at a point over $B$ the local ring of $Z$ is
    regular and $\mathcal O_{Z,p}/(B\cap Z)_p=\mathcal O_{Y,p}/B_p$ is regular, so the local ring of
    $Z'$ is a monoidal transform with regular center, regular with the exceptional divisor
    regular of codimension one by Ch.~III~\S2 (\cref{lem:III.2-monoidal-transform-regular},
    \cref{lem:monoidal-transformation-nonsingular}); off $B$ the map is a local isomorphism.
    \textbf{Deviation from the paper (gap filled).} The paper asserts this without argument. -/)
  (proofUses := ["lem:strict-transform-is-blowup", "lem:III.2-monoidal-transform-regular",
    "lem:monoidal-transformation-nonsingular"])
  (latexEnv := "lemma")]
theorem isRegularLocalRing_stalk_and_exceptional_strictTransform [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (t : MonoidalTransformation Y B)
    (Z : Subscheme Y) (fb : (Subscheme.strictTransform t Z).toScheme ⟶ Z.toScheme)
    (hfb : fb ≫ Z.ι = (Subscheme.strictTransform t Z).ι ≫ t.f)
    (q : (Subscheme.strictTransform t Z).toScheme)
    [IsRegularLocalRing (Z.toScheme.presheaf.stalk (fb q))]
    (hB : Z.ι (fb q) ∈ B.pts →
      Z.stalkIdeal (Z.ι (fb q)) ≤ B.stalkIdeal (Z.ι (fb q)) ∧
        IsRegularLocalRing (Y.presheaf.stalk (Z.ι (fb q)) ⧸ B.stalkIdeal (Z.ι (fb q)))) :
    IsRegularLocalRing ((Subscheme.strictTransform t Z).toScheme.presheaf.stalk q) ∧
      (q ∈ (Subscheme.totalTransform fb (Subscheme.totalTransform Z.ι B)).pts →
        (Subscheme.totalTransform fb (Subscheme.totalTransform Z.ι B)).IsSimpleAt q ∧
          (Subscheme.totalTransform fb (Subscheme.totalTransform Z.ι B)).codimAt q = 1) := by
  obtain ⟨⟨s⟩, hs⟩ := Subscheme.nonempty_monoidalTransformation_strictTransform t Z
  obtain ⟨e, he⟩ := hs s
  have hef : e.hom ≫ fb = s.f := by
    rw [← cancel_mono Z.ι, Category.assoc, hfb]; exact he
  obtain ⟨y, rfl⟩ : ∃ y, e.hom y = q := ⟨e.inv q, by rw [← Scheme.Hom.comp_apply]; simp⟩
  have hx : s.f y = fb (e.hom y) := by
    rw [← hef]; rfl
  have hCpts : s.f y ∈ (Subscheme.totalTransform Z.ι B).pts → Z.ι (s.f y) ∈ B.pts := by
    intro h
    rw [Subscheme.pts_totalTransform_eq_preimage] at h
    exact h
  have hC : s.f y ∈ (Subscheme.totalTransform Z.ι B).pts →
      IsRegularLocalRing (Z.toScheme.presheaf.stalk (s.f y) ⧸
        (Subscheme.totalTransform Z.ι B).stalkIdeal (s.f y)) := by
    intro h
    have hb := hB (by rw [← hx]; exact hCpts h)
    rw [← hx] at hb
    exact Subscheme.isRegularLocalRing_quotient_totalTransform_subschemeι _ hb.1 hb.2
  have hreg : IsRegularLocalRing (Z.toScheme.presheaf.stalk (s.f y)) :=
    IsRegularLocalRing.of_ringEquiv
      (Z.toScheme.presheaf.stalkCongr (.of_eq hx.symm)).commRingCatIsoToRingEquiv
  obtain ⟨h1, h2⟩ := s.isRegularLocalRing_stalk_and_exceptional_of_pointwise y hC
  let ε : s.X'.presheaf.stalk y ≃+* (Subscheme.strictTransform t Z).toScheme.presheaf.stalk
      (e.hom y) := (asIso (e.hom.stalkMap y)).commRingCatIsoToRingEquiv.symm
  refine ⟨IsRegularLocalRing.of_ringEquiv ε, fun hyE => ?_⟩
  set D := Subscheme.totalTransform fb (Subscheme.totalTransform Z.ι B) with hD
  have hexc : Subscheme.totalTransform e.hom D = s.exceptional := by
    rw [hD, ← Subscheme.totalTransform_comp, hef]; rfl
  have hyE' : y ∈ s.exceptional.pts := by
    rw [← hexc, Subscheme.pts_totalTransform_eq_preimage]; exact hyE
  obtain ⟨hs1, hs2⟩ := h2 hyE'
  obtain ⟨hiff, hcod⟩ := Subscheme.isSimpleAt_and_codimAt_totalTransform_iso e.hom D y
  rw [hexc] at hiff hcod
  exact ⟨hiff.mpr ⟨hyE', hs1⟩, hcod.trans hs2⟩

/-- **Irreducibility of the strict transform** (p. 298): the strict transform of an irreducible
subscheme `Z` is irreducible if it is non-empty (no regularity is needed).  If it is non-empty, a
point of it off the exceptional subscheme lies over a point of `Z` off `B`, so `Z ⊄ B`.  This is
the irreducibility part of "We see that `X̄'_{s+1}` is … non-singular" (p. 298), which the paper
asserts without argument. -/
@[blueprint "lem:IV.3-strict-transform-irreducible"
  (statement := /-- Let $f\colon Y'\to Y$ be a monoidal transformation with center $B$ and $Z$ an
    irreducible subscheme of $Y$ whose strict transform $Z'$ is non-empty. Then $Z'$ is
    irreducible. (The irreducibility of $\bar X'_{s+1}$ in the construction of p.~298.) -/)
  (proof := /-- A point of $Z'$ has a generization off the exceptional subscheme
    ($f$ is an isomorphism there), lying over a point of $Z$ off $B$, so $Z\not\subseteq B$; the
    strict transform of an irreducible $Z\not\subseteq B$ is the closure of its irreducible part
    off the exceptional subscheme.
    \textbf{Deviation from the paper (gap filled).} The paper asserts the irreducibility without
    argument. -/)
  (proofUses := ["compat:blowup-flat-base-change"])
  (latexEnv := "lemma")]
theorem isIrreducible_strictTransform_of_nonempty (t : MonoidalTransformation Y B)
    (Z : Subscheme Y) (hZ : Z.IsIrreducible) (hne : (Subscheme.strictTransform t Z).pts.Nonempty) :
    (Subscheme.strictTransform t Z).IsIrreducible := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨q, hq, hqE, -⟩ := t.exists_generization_notMem_exceptional Z hp
  refine t.strictTransform_isIrreducible Z hZ fun hsub => ?_
  have h1 := (mem_pts_strictTransform_iff_of_notMem t Z hqE).mp hq
  have h2 := hsub h1
  rw [pts_exceptional] at hqE
  exact hqE h2

/-- A non-empty strict transform lies over a non-empty subscheme. -/
theorem pts_nonempty_of_strictTransform (t : MonoidalTransformation Y B) (Z : Subscheme Y)
    (hne : (Subscheme.strictTransform t Z).pts.Nonempty) : Z.pts.Nonempty := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨q, hq, hqE, -⟩ := t.exists_generization_notMem_exceptional Z hp
  exact ⟨t.f q, (mem_pts_strictTransform_iff_of_notMem t Z hqE).mp hq⟩

end MonoidalTransformation

/-- A non-empty open subset of the space of an irreducible subscheme is irreducible. -/
theorem Subscheme.isIrreducible_of_isOpen {Y : Scheme.{u}} {Z : Subscheme Y}
    (hZ : Z.IsIrreducible) {O : Set Z.toScheme} (ho : IsOpen O) (hne : O.Nonempty) :
    _root_.IsIrreducible O := by
  have : IrreducibleSpace Z.toScheme := hZ
  exact ⟨hne, (IrreducibleSpace.isIrreducible_univ Z.toScheme).isPreirreducible.open_subset ho
    (Set.subset_univ O)⟩

end Hironaka
