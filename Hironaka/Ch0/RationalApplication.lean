/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Architect
public import Hironaka.Ch0.AlgebraicScheme
public import Hironaka.Compat.RationalMapPrecomp
public import Hironaka.Statements

/-!
# Ch. 0 §5 (pp. 138–140): rational applications, domain of definition, points of indeterminacy, proper rational applications

> Let `X` and `Y` be `S`-local-ringed spaces, where `S` is a local-ringed space or a commutative ring with unity which
> is fixed.  Let `U` and `V` be open dense subsets of the underlying topological space of `X`, and let `f : X | U → Y`
> and `g : X | V → Y` be `S`-morphisms of the respective restrictions of `X` to `Y`.  We say that `f` and `g` are
> equivalent to each other if they induce the same morphism of `X | U ∩ V` to `Y`.  An equivalence class of
> `S`-morphisms of such restrictions of `X` to `Y` is called a rational `S`-application of `X` to `Y`, or simply
> rational application of `X` to `Y` whenever no confusion can arise.  (p. 138)

The rational applications of schemes are Mathlib's `Scheme.RationalMap` (`Birational/RationalMap.lean`): a partial map
is a morphism on a dense open subscheme, two are equivalent if they agree on a dense open subscheme (the intersection
`U ∩ V` of two dense open sets is dense open), and the rational map is the class.  The domain of definition of p. 139
is `RationalMap.domain` (`mem_domain`), a point of indeterminacy is a point outside it.  This file adds, for the schemes
of the paper, the vocabulary of pp. 139–140 that Mathlib lacks:

* `Scheme.RationalMap.IsIndeterminacyPoint` (p. 139);
* `Scheme.RationalMap.IsMorphism` ("the rational application `f` is a morphism", p. 139), with the existence and
  uniqueness of the morphism for a reduced source and a separated target;
* `Scheme.RationalMap.IsProperApplication` ("`f` is proper", p. 139).

The composition of a rational application with a morphism, the only composition used in Question (E), is
`Scheme.RationalMap.precomp` (`Hironaka/Compat/RationalMapPrecomp.lean`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.RationalMap

variable {X Y : Scheme.{u}}

/-- A rational application is *defined at `x`* iff `x` is in its domain of definition; a *point of indeterminacy* is a
point where it is not (p. 139: "a point of `X` is called a point of indeterminacy of a rational application `f` of `X`
to `Y`, if it is not contained in the domain of definition of `f`").

Encoding: the domain of definition is Mathlib's `RationalMap.domain`, `sSup` of the domains of the partial maps of the
class, which is the paper's "maximal open subset `W` … such that for every `x ∈ W` we can find a morphism … with
`x ∈ U ⊂ W` which belongs to the class" (`RationalMap.mem_domain`). -/
@[blueprint "def:0.5-point-of-indeterminacy"
  (statement := /-- Let $f$ be a rational application of $X$ to $Y$. The \emph{domain of definition} of $f$ is the
    maximal open subset $W$ of $X$ such that every $x\in W$ has an open neighbourhood $U\subset W$ and a morphism
    $X|U\to Y$ belonging to the class $f$. A point of $X$ is a \emph{point of indeterminacy} of $f$ if it is not
    contained in the domain of definition of $f$. (p.~139.) Formalization note (encoding): Mathlib's
    \texttt{RationalMap.domain}. -/)
  (latexEnv := "definition")]
def IsIndeterminacyPoint (f : X ⤏ Y) (x : X) : Prop := x ∉ f.domain


/-- Two morphisms from a reduced scheme to a separated scheme that define the same rational application are equal
(they agree on a dense open set).  This is the uniqueness of the morphism in "these [sic] exists a unique morphism
`f : X | W → Y`" (p. 139). -/
theorem eq_of_toRationalMap_eq [IsReduced X] [Y.IsSeparated] {φ φ' : X ⟶ Y}
    (h : φ.toRationalMap = φ'.toRationalMap) : φ = φ' := by
  have h1 : φ.toPartialMap.equiv φ'.toPartialMap := PartialMap.toRationalMap_eq_iff.mp h
  rw [PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)] at h1
  exact (cancel_epi X.topIso.hom).mp h1

/-- A rational application whose source is reduced and whose target is separated is a morphism as soon as its domain of
definition is everything: "these [sic] exists a unique morphism `f : X | W → Y`, with the domain of definition `W` of `f`,
which belongs to the class `f`" (p. 139).

Encoding: "scheme" is "separated": "If the diagonal of `X ×_S X` is a closed subscheme, then the `S`-prescheme `(X, p)`
is called an `S`-scheme." (p. 118); p. 139 asks `X` reduced pre-scheme and `Y` a scheme. -/
theorem isMorphism_iff_domain_eq_top [IsReduced X] [Y.IsSeparated] {f : X ⤏ Y} :
    f.IsMorphism ↔ f.domain = ⊤ := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  have hD : (⊤ : X.Opens) = f.toPartialMap.domain := h.symm
  let φ : X ⟶ Y := X.topIso.inv ≫ (X.isoOfEq hD).hom ≫ f.toPartialMap.hom
  have hφ : φ.toRationalMap = f := by
    have : f.toPartialMap.equiv φ.toPartialMap := by
      rw [PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
      have h1 : f.toPartialMap.domain.ι = (X.isoOfEq hD).inv ≫ Scheme.Opens.ι _ :=
        (Scheme.isoOfEq_inv_ι X hD).symm
      rw [h1]
      simp only [φ, Category.assoc, Scheme.ι_toIso_inv_assoc, Iso.inv_hom_id_assoc]
    rw [← f.toRationalMap_toPartialMap]
    exact (PartialMap.toRationalMap_eq_iff.mpr this).symm
  exact ⟨φ, hφ, fun φ' hφ' => eq_of_toRationalMap_eq (hφ'.trans hφ.symm)⟩

/-- The morphism of a rational application which is a morphism (p. 139: "we identify `f` with `f`"). -/
noncomputable def IsMorphism.toHom {f : X ⤏ Y} (h : f.IsMorphism) : X ⟶ Y := h.2.choose

theorem IsMorphism.toHom_toRationalMap {f : X ⤏ Y} (h : f.IsMorphism) : h.toHom.toRationalMap = f :=
  h.2.choose_spec.1

/-- The class of a morphism is a morphism, when `X` is reduced and `Y` separated. -/
theorem isMorphism_toRationalMap [IsReduced X] [Y.IsSeparated] (φ : X ⟶ Y) : φ.toRationalMap.IsMorphism :=
  isMorphism_iff_domain_eq_top.mpr (by
    refine top_le_iff.mp fun x _ => ?_
    exact RationalMap.mem_domain.mpr ⟨φ.toPartialMap, by simp, rfl⟩)


/-- A proper rational application over a base has a representative which is a morphism over the base (the second
projection `p₂` composed with the structure morphism of `Y` is the first one composed with that of `X`, and the
representative is `p₂ ∘ (p₁)⁻¹` on `X | U`). -/
theorem IsProperApplication.exists_over {S : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S} {f : X ⤏ Y}
    (hf : f.IsProperApplication pX pY) :
    ∃ g : X.PartialMap Y, g.toRationalMap = f ∧ g.hom ≫ pY = g.domain.ι ≫ pX := by
  obtain ⟨g, T, hg, -, -, hiso, hcomm⟩ := hf
  refine ⟨g, hg, ?_⟩
  set q₁ := T.ι ≫ pullback.fst pX pY with hq₁
  set q₂ := T.ι ≫ pullback.snd pX pY with hq₂
  have hq : q₁ ≫ pX = q₂ ≫ pY := by
    simp only [hq₁, hq₂, Category.assoc, pullback.condition]
  have hg' : g.hom = inv (q₁ ∣_ g.domain) ≫ (q₁ ⁻¹ᵁ g.domain).ι ≫ q₂ := by
    rw [← hcomm]
    exact (IsIso.inv_hom_id_assoc _ _).symm
  calc g.hom ≫ pY = (inv (q₁ ∣_ g.domain) ≫ (q₁ ⁻¹ᵁ g.domain).ι ≫ q₂) ≫ pY := by rw [← hg']
    _ = inv (q₁ ∣_ g.domain) ≫ (q₁ ⁻¹ᵁ g.domain).ι ≫ q₁ ≫ pX := by rw [hq]; simp only [Category.assoc]
    _ = g.domain.ι ≫ pX := by
      rw [← Category.assoc ((q₁ ⁻¹ᵁ g.domain).ι), ← morphismRestrict_ι q₁ g.domain]
      simp

/-- A proper rational application of a reduced scheme is over the base: composed with the structure morphism of `Y` it is
the class of the structure morphism of `X` (the two partial maps are equal on the domain of the representative). -/
theorem IsProperApplication.compHom_eq {S : Scheme.{u}} [S.IsSeparated] [IsReduced X] {pX : X ⟶ S}
    {pY : Y ⟶ S} {f : X ⤏ Y} (hf : f.IsProperApplication pX pY) : f.compHom pY = pX.toRationalMap := by
  obtain ⟨g, hg, hgo⟩ := hf.exists_over
  rw [← hg, ← compHom_toRationalMap]
  refine PartialMap.toRationalMap_eq_iff.mpr ?_
  rw [PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
  exact hgo

/-- The composition of the class of a morphism `φ : X ⟶ Z` (`X` reduced, `Z` separated) with a morphism `c` with dense
preimages is the class of `c ≫ φ`. -/
theorem precomp_toRationalMap_hom {X' Z : Scheme.{u}} [IsReduced X'] [Z.IsSeparated] (φ : X ⟶ Z)
    (c : X' ⟶ X) (hc : c.PreimageDense) : φ.toRationalMap.precomp c hc = (c ≫ φ).toRationalMap := by
  refine PartialMap.toRationalMap_eq_iff.mpr ?_
  rw [PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
  simp only [PartialMap.precomp_hom, Hom.toPartialMap_hom, PartialMap.precomp_domain]
  change c ∣_ (⊤ : X.Opens) ≫ (⊤ : X.Opens).ι ≫ φ = (c ⁻¹ᵁ (⊤ : X.Opens)).ι ≫ c ≫ φ
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]

end AlgebraicGeometry.Scheme.RationalMap
