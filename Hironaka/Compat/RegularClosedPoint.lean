/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Compat.HironakaBaseStability
public import Hironaka.Statements

/-!
# Compatibility layer: a closed regular point of a variety over a perfect field (footnote 12, p. 260)

In the proof of Corollary 1 of Proposition 2, Ch. III §8 (p. 260), Hironaka writes: "`N ∩ R = M`,
and therefore `Ā = A/N` is an algebra of finite type over the residue field of `R`. We then know
that the singular locus of `Spec(Ā)` is a nowhere dense closed subset (footnote 12: cf. Zariski
[29]). Therefore we can find a maximal ideal `N'` in `A` such that `N'` contains `N` and that
`A_{N'}/NA_{N'}` is regular."

This file contains the cited fact (as a leaf) and the deduction of the existence of a closed regular
point:

* `isClosed_compl_regularLocus_of_finiteType` (**cited leaf**): the singular locus of `Spec B` is
  closed for an algebra `B` of finite type over a perfect field `k` (Zariski [29]);
  `IsHironakaBase.isClosed_singularLocus` is not usable here because `IsHironakaBase.of_field`
  needs characteristic zero, while Corollary 1 is stated for perfect fields of any characteristic;
* `exists_isMaximal_isRegularLocalRing_localization`: a domain `B` of finite type over a perfect
  field has a maximal ideal `m` with `B_m` regular (the generic point of `Spec B` is regular, so
  the regular locus is an open set containing it; the closed points are dense, `B` being a
  Jacobson ring).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u


/-- **Cited** (p. 260, footnote 12, "cf. Zariski [29]"): "We then know that the singular locus of
`Spec(Ā)` is a nowhere dense closed subset" for an algebra `Ā` of finite type over a perfect field
`k` (and a domain; the closedness is stated here for every `k`-algebra of finite type, and the
nowhere density of the singular locus of a domain is derived in
`exists_isMaximal_isRegularLocalRing_localization`, the generic point being regular).

Not proved in the paper: O. Zariski, *The concept of a simple point of an abstract algebraic
variety*, Trans. Amer. Math. Soc. 62 (1947), 1–52; for the closedness of the singular locus of an
algebra of finite type over a field in general see Nagata, *Local Rings*, §46 and EGA IV, 6.12.5
(excellence of algebras of finite type over a field). -/
@[blueprint "lem:III.8-singular-locus-closed"
  (statement := /-- Let $k$ be a perfect field and $B$ an algebra of finite type over $k$. Then the
    singular locus of $\operatorname{Spec}B$ is a closed subset of $\operatorname{Spec}B$.
    (Cited: footnote~12, p.~260, ``cf.\ Zariski [29]''; the paper states that the singular locus
    is a nowhere dense closed subset.) -/)
  (proof := /-- Cited, not proved in the paper: footnote~12, p.~260 (``cf.\ Zariski [29]''):
    O.~Zariski, The concept of a simple point of an abstract algebraic variety, Trans.\ Amer.\
    Math.\ Soc.\ 62 (1947); Nagata, Local Rings, \S46; EGA~IV 6.12.5. -/)
  (latexEnv := "lemma")]
theorem isClosed_compl_regularLocus_of_finiteType [Hironaka.Cited.IsClosedComplRegularLocusOfFiniteType.{u}] :
    ∀ (k : Type u) [Field k] [PerfectField k]
    (B : Type u) [CommRing B] [Algebra k B] [Algebra.FiniteType k B],
    IsClosed (regularLocus B)ᶜ :=
  @Hironaka.Cited.IsClosedComplRegularLocusOfFiniteType.isClosed_compl_regularLocus_of_finiteType _

/-- The generic point of the spectrum of a domain is regular: the localization at `(0)` is a
field. -/
theorem bot_mem_regularLocus (B : Type u) [CommRing B] [IsDomain B] :
    (⊥ : PrimeSpectrum B) ∈ regularLocus B := by
  show IsRegularLocalRing (Localization.AtPrime (⊥ : Ideal B))
  have hmax : maximalIdeal (Localization.AtPrime (⊥ : Ideal B)) = ⊥ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_bot]
  have hfield : IsField (Localization.AtPrime (⊥ : Ideal B)) :=
    (IsLocalRing.isField_iff_maximalIdeal_eq).mpr hmax
  let _ := hfield.toField
  infer_instance

/-- A domain `B` of finite type over a perfect field has a maximal ideal `m` with `B_m` a regular
local ring (p. 260: "Therefore we can find a maximal ideal `N'` in `A` such that ... `A_{N'}/NA_{N'}`
is regular"), by the cited closedness of the singular locus. -/
theorem exists_isMaximal_isRegularLocalRing_localization [Hironaka.Cited.IsClosedComplRegularLocusOfFiniteType.{u}] (k : Type u) [Field k] [PerfectField k]
    (B : Type u) [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] :
    ∃ m : PrimeSpectrum B, m.asIdeal.IsMaximal ∧ m ∈ regularLocus B := by
  have hopen : IsOpen (regularLocus B) := by
    simpa [isOpen_compl_iff] using isClosed_compl_regularLocus_of_finiteType k B
  obtain ⟨_, ⟨f, rfl⟩, hbf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (bot_mem_regularLocus B) hopen
  have hf0 : f ∉ (⊥ : Ideal B) := hbf
  have : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k) (B := B)
  have hJac : (⊥ : Ideal B).jacobson = ⊥ := ((isJacobsonRing_iff.mp this) ⊥ Ideal.isRadical_bot)
  have hex : ∃ m : Ideal B, m.IsMaximal ∧ f ∉ m := by
    by_contra hcon
    push Not at hcon
    apply hf0
    rw [← hJac, Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    exact hcon m hm
  obtain ⟨m, hm, hfm⟩ := hex
  exact ⟨⟨m, hm.isPrime⟩, hm, hsub (show (⟨m, hm.isPrime⟩ : PrimeSpectrum B) ∈ _ from hfm)⟩

end Hironaka
