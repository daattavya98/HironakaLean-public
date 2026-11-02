/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch1.FundamentalTheorems
public import Hironaka.Compat.ComponentStalk
public import Hironaka.Compat.SubschemeStalk
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Ch4.Localization

/-!
# Irreducible components of a subscheme and the presentation `(⋃ E_i; V_1, …, V_β; W)` of a datum

Ch. IV, p. 274 (introduction): "we shall often find it convenient to express a resolution datum of
type `ℜ^{N,n}_I` on a non-singular irreducible algebraic scheme `X` in the following form:
`ℜ^{N,n}_I = (⋃_{i=1}^α E_i; V_1, V_2, …, V_β; W)`.  We agree once for all that whenever this
expression is taken, all the `E_j` denote non-singular irreducible subschemes of `X` of
codimension one."

The paper uses the presentation without ever saying that every datum has one.  This file proves it
(`DatumI.Raw.isUnionOfDivisors_of_isDatum`, and `DatumI.Raw.isUnionOfDivisors_of_isNonsingular` without
the dimension): the irreducible components of the reduced subscheme `E`, which is everywhere of
codimension one and has only normal crossings, are non-singular irreducible subschemes of codimension
one, there are finitely many of them, and `E` is their union.

The file lies upstream of `Hironaka/Ch4/Preparation.lean`, so that the presentation is available to
Lemma 4 of Ch. IV §2 as it is used on pp. 290 and 294, 307 (`DatumI.Raw.resolvedAt_transform_of_resolvedAt`).
It contains the general facts on irreducible components needed for that and nothing else; the
remaining facts on components (non-singular subschemes of pure codimension one, closed restrictions)
are in `Hironaka/Compat/DatumPresentation.lean`.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

section GeneralTopology

variable {X : Scheme.{u}}

/-- The preimage under an inducing map of an irreducible subset of the range is irreducible. -/
theorem isIrreducible_preimage_of_isInducing {Y : Type*} {Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {f : Y → Z} (hf : Topology.IsInducing f) {s : Set Z}
    (hs : IsIrreducible s) (hsr : s ⊆ Set.range f) : IsIrreducible (f ⁻¹' s) := by
  obtain ⟨y₀, hy₀⟩ : (f ⁻¹' s).Nonempty := by
    obtain ⟨z, hz⟩ := hs.nonempty
    obtain ⟨y, rfl⟩ := hsr hz
    exact ⟨y, hz⟩
  refine ⟨⟨y₀, hy₀⟩, fun U V hU hV ⟨a, ha, haU⟩ ⟨b, hb, hbV⟩ => ?_⟩
  obtain ⟨U', hU', rfl⟩ := hf.isOpen_iff.mp hU
  obtain ⟨V', hV', rfl⟩ := hf.isOpen_iff.mp hV
  obtain ⟨c, hcs, hcU, hcV⟩ := hs.2 U' V' hU' hV' ⟨f a, ha, haU⟩ ⟨f b, hb, hbV⟩
  obtain ⟨y, rfl⟩ := hsr hcs
  exact ⟨y, hcs, hcU, hcV⟩

/-- Every point of a subscheme lies on an irreducible component of it (a minimal prime of the
stalk ideal is the stalk ideal of a component). -/
theorem Subscheme.exists_mem_irreducibleComponents_of_mem_pts (D : Subscheme X) {x : X}
    (hx : x ∈ D.pts) : ∃ G ∈ D.irreducibleComponents, x ∈ G.pts := by
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le (Subscheme.stalkIdeal_le_maximalIdeal D hx)
  obtain ⟨C, hC, hxC, -⟩ :=
    Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes D x hq
  exact ⟨C, hC, hxC⟩

/-- The irreducible components of a closed subset of a noetherian space form a finite set. -/
theorem finite_setOf_maximal_isIrreducible_subset [TopologicalSpace.NoetherianSpace X]
    {T : Set X} (hT : IsClosed T) :
    {Z : TopologicalSpace.Closeds X | Maximal (fun Z : TopologicalSpace.Closeds X =>
      _root_.IsIrreducible (Z : Set X) ∧ (Z : Set X) ⊆ T) Z}.Finite := by
  have hfin : (irreducibleComponents T).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  refine Set.Finite.of_injOn (f := fun Z : TopologicalSpace.Closeds X =>
    (Subtype.val ⁻¹' (Z : Set X) : Set T)) (fun Z hZ => ?_) (fun Z hZ Z' hZ' h => ?_) hfin
  · -- the preimage is an irreducible component of `T`
    obtain ⟨⟨hZirr, hZT⟩, hZmax⟩ := hZ
    refine ⟨isIrreducible_preimage_of_isInducing Topology.IsInducing.subtypeVal hZirr
      (by simpa using hZT), fun S hS hle => ?_⟩
    have hSirr : _root_.IsIrreducible (Subtype.val '' S) := hS.image _ continuous_subtype_val.continuousOn
    have hcl : closure (Subtype.val '' S) ⊆ T := closure_minimal (by
      rintro _ ⟨s, -, rfl⟩; exact s.2) hT
    have hZle : Z ≤ (⟨closure (Subtype.val '' S), isClosed_closure⟩ : TopologicalSpace.Closeds X) := by
      intro z hz
      exact subset_closure ⟨⟨z, hZT hz⟩, hle hz, rfl⟩
    have := hZmax (y := ⟨closure (Subtype.val '' S), isClosed_closure⟩) ⟨hSirr.closure, hcl⟩ hZle
    intro s hs
    exact this (subset_closure ⟨s, hs, rfl⟩)
  · have hsub : ∀ Z : TopologicalSpace.Closeds X, (Z : Set X) ⊆ T →
        (Z : Set X) = Subtype.val '' (Subtype.val ⁻¹' (Z : Set X) : Set T) := fun Z hZ => by
      ext z
      exact ⟨fun hz => ⟨⟨z, hZ hz⟩, hz, rfl⟩, by rintro ⟨s, hs, rfl⟩; exact hs⟩
    exact SetLike.coe_injective <| by
      rw [hsub Z hZ.1.2, hsub Z' hZ'.1.2]
      exact congrArg _ h

/-- The points of an irreducible component of a subscheme lie in it. -/
theorem Subscheme.pts_subset_of_mem_irreducibleComponents {D G : Subscheme X}
    (hG : G ∈ D.irreducibleComponents) : G.pts ⊆ D.pts := by
  obtain ⟨Z, hZ, rfl⟩ := hG
  have : (Subscheme.ofClosed Z).pts = Z := Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  rw [this]; exact hZ.1.2

end GeneralTopology

namespace Subscheme

variable {X : Scheme.{u}}

/-- A subscheme of a scheme with noetherian underlying space has finitely many irreducible
components. -/
theorem finite_irreducibleComponents_of_noetherianSpace [NoetherianSpace X] (D : Subscheme X) :
    D.irreducibleComponents.Finite := by
  have h := finite_setOf_maximal_isIrreducible_subset (X := X) (T := D.pts) D.support.isClosed
  refine (h.image ofClosed).subset ?_
  rintro C ⟨Z, hZ, rfl⟩
  exact ⟨Z, hZ, rfl⟩

/-- An irreducible component of a subscheme is an irreducible subscheme. -/
theorem isIrreducible_of_mem_irreducibleComponents {D C : Subscheme X}
    (hC : C ∈ D.irreducibleComponents) : C.IsIrreducible := by
  obtain ⟨Z, hZ, rfl⟩ := hC
  refine Subscheme.isIrreducible_of_pts _ ?_
  rw [pts_ofClosed]
  exact hZ.1.1

/-- An irreducible component of a subscheme is non-empty. -/
theorem nonempty_pts_of_mem_irreducibleComponents {D C : Subscheme X}
    (hC : C ∈ D.irreducibleComponents) : C.pts.Nonempty := by
  obtain ⟨Z, hZ, rfl⟩ := hC
  rw [pts_ofClosed]
  exact hZ.1.1.nonempty

/-- An irreducible component of a subscheme is a reduced subscheme. -/
theorem isReduced_of_mem_irreducibleComponents {D C : Subscheme X}
    (hC : C ∈ D.irreducibleComponents) : C.IsReduced := by
  obtain ⟨Z, -, rfl⟩ := hC
  exact ofClosed_isReduced Z

/-- The points of a subscheme are the union of the points of its irreducible components. -/
theorem pts_eq_iUnion_irreducibleComponents (D : Subscheme X) :
    D.pts = ⋃ C ∈ D.irreducibleComponents, C.pts := by
  refine Set.Subset.antisymm (fun x hx => ?_)
    (Set.iUnion₂_subset fun C hC => pts_subset_of_mem_irreducibleComponents hC)
  obtain ⟨C, hC, hxC⟩ := exists_mem_irreducibleComponents_of_mem_pts D hx
  exact Set.mem_iUnion₂.mpr ⟨C, hC, hxC⟩

/-- A finite intersection of ideal sheaves of reduced subschemes is reduced (any finite index
type). -/
theorem isReduced_iInf_of_forall_isReduced {ι : Type*} [Fintype ι] (E : ι → Subscheme X)
    (h : ∀ i, (E i).IsReduced) : (⨅ i, E i).IsReduced := by
  refine isReduced_of_isRadical_stalkIdeal fun z => ?_
  rw [DatumTransform.stalkIdeal_iInf_fintype]
  exact Ideal.isRadical_iInf _ fun i => isRadical_stalkIdeal_of_isReduced (h i) z

/-- Two reduced subschemes with the same points are equal. -/
theorem eq_of_pts_eq_of_isReduced {D D' : Subscheme X} (hD : D.IsReduced) (hD' : D'.IsReduced)
    (h : D.pts = D'.pts) : D = D' := by
  rw [eq_ofClosed_support D hD, eq_ofClosed_support D' hD']
  congr 1
  exact TopologicalSpace.Closeds.ext h

/-- An enumeration (without repetition) of the finitely many irreducible components of a
subscheme of a scheme with noetherian underlying space. -/
theorem exists_family_irreducibleComponents [NoetherianSpace X] (D : Subscheme X) :
    ∃ (α : ℕ) (C : Fin α → Subscheme X), (∀ i, C i ∈ D.irreducibleComponents) ∧
      Function.Injective C ∧ ∀ C' ∈ D.irreducibleComponents, ∃ i, C i = C' := by
  classical
  have hfin := finite_irreducibleComponents_of_noetherianSpace D
  let e := hfin.toFinset.equivFin
  refine ⟨hfin.toFinset.card, fun i => (e.symm i : Subscheme X),
    fun i => hfin.mem_toFinset.mp (e.symm i).2, fun i j hij => e.symm.injective (Subtype.ext hij),
    fun C' hC' => ⟨e ⟨C', hfin.mem_toFinset.mpr hC'⟩, by simp⟩⟩

/-- A reduced subscheme is the union of any family that lists its irreducible components. -/
theorem eq_iInf_of_isReduced {D : Subscheme X} (hD : D.IsReduced) {α : ℕ}
    (C : Fin α → Subscheme X) (hC : ∀ i, C i ∈ D.irreducibleComponents)
    (hcov : ∀ C' ∈ D.irreducibleComponents, ∃ i, C i = C') : D = ⨅ i, C i := by
  have hred : (⨅ i, C i).IsReduced :=
    isReduced_iInf_of_forall_isReduced _ fun i => isReduced_of_mem_irreducibleComponents (hC i)
  refine eq_of_pts_eq_of_isReduced hD hred ?_
  rw [pts_iInf, pts_eq_iUnion_irreducibleComponents D]
  refine Set.Subset.antisymm (Set.iUnion₂_subset fun C' hC' => ?_) (Set.iUnion_subset fun i => ?_)
  · obtain ⟨i, rfl⟩ := hcov C' hC'
    exact Set.subset_iUnion (fun i => (C i).pts) i
  · exact Set.subset_biUnion_of_mem (hC i)

/-- An irreducible component of a reduced subscheme `E` with only normal crossings on a
non-singular scheme is a non-singular irreducible subscheme of codimension one: at each of its
points its stalk ideal is generated by a member of a regular system of parameters (this is how the
definition of normal crossings, Ch. 0 §5 Def. 2, is phrased). -/
theorem isNonsingularIrreducibleCodimOne_of_mem_irreducibleComponents_of_hasOnlyNormalCrossings
    (hX : X.IsNonsingular) {E C : Subscheme X} (hE : E.HasOnlyNormalCrossings)
    (hC : C ∈ E.irreducibleComponents) : C.IsNonsingularIrreducibleCodimOne := by
  have hloc : ∀ z ∈ C.pts, ∃ (K : Finset (X.presheaf.stalk z)) (a : X.presheaf.stalk z),
      ExtendsToRSOP _ K ∧ a ∈ K ∧ C.stalkIdeal z = Ideal.span {a} := by
    intro z hz
    have : IsRegularLocalRing (X.presheaf.stalk z) := hX z
    obtain ⟨K, hK, hcomp, -⟩ := hE z
    obtain ⟨a, ha, hCa⟩ := hcomp C hC hz
    exact ⟨K, a, ExtendsToRSOP.of_isRegularSystemOfParameters hK, ha, hCa⟩
  refine Or.inr ⟨isNonsingular_of_stalk_quot C fun z hz => ?_,
    isIrreducible_of_mem_irreducibleComponents hC, ?_⟩
  · obtain ⟨K, a, hK, ha, hCa⟩ := hloc z hz
    exact (isSimpleAt_of_stalkIdeal_eq_span (hX z) hK ha hCa).2
  · obtain ⟨z₀, hz₀⟩ := nonempty_pts_of_mem_irreducibleComponents hC
    have hcodim : ∀ z ∈ C.pts, C.codimAt z = 1 := fun z hz => by
      obtain ⟨K, a, hK, ha, hCa⟩ := hloc z hz
      have : IsRegularLocalRing (X.presheaf.stalk z) := hX z
      have : IsDomain (X.presheaf.stalk z) := isDomain_of_isRegularLocalRing _
      have hz0 : a ≠ 0 := hK.ne_zero ha
      have hnu : ¬ IsUnit a := (IsLocalRing.mem_maximalIdeal _).mp (hK.mem_maximalIdeal ha)
      show (C.stalkIdeal z).height = 1
      rw [hCa]
      exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hz0) hnu
    exact le_antisymm ((iInf₂_le z₀ hz₀).trans (hcodim z₀ hz₀).le)
      (le_iInf₂ fun z hz => (hcodim z hz).ge)

end Subscheme

/-- `DatumI.Raw.isUnionOfDivisors_of_isDatum` for a non-singular algebraic scheme, without the
irreducibility and the dimension of the ambient scheme (only `IsAlgebraicScheme X` and
`X.IsNonsingular` are used). -/
theorem DatumI.Raw.isUnionOfDivisors_of_isNonsingular {X : Scheme.{u}} [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) (ℜ : DatumI.Raw X) (hℜ : ℜ.IsDatum) : ℜ.IsUnionOfDivisors := by
  have := IsAlgebraicScheme.noetherianSpace X
  obtain ⟨α, C, hC, -, hcov⟩ := Subscheme.exists_family_irreducibleComponents ℜ.E
  exact ⟨α, C, fun i =>
    Subscheme.isNonsingularIrreducibleCodimOne_of_mem_irreducibleComponents_of_hasOnlyNormalCrossings
      hX hℜ.2.2.1 (hC i),
    Subscheme.eq_iInf_of_isReduced hℜ.1 C hC hcov⟩

/-- **Every datum has a presentation** (the tacit assertion of p. 274): the boundary `E` of a
resolution datum of type `ℜ^{N,n}_I` on a non-singular irreducible algebraic scheme is the union
`⋃_{i=1}^α E_i` of its (finitely many) irreducible components, which are non-singular irreducible
subschemes of codimension one.

\textbf{Deviation from the paper (gap filled).} The paper writes "we shall often find it
convenient to express a resolution datum of type `ℜ^{N,n}_I` on a non-singular irreducible
algebraic scheme `X` in the following form: `ℜ^{N,n}_I = (⋃_{i=1}^α E_i; V_1, V_2, …, V_β; W)`.
We agree once for all that whenever this expression is taken, all the `E_j` denote non-singular
irreducible subschemes of `X` of codimension one" (p. 274) and never says that such an expression
exists.  In Lean the `E_i` are the irreducible components of `E`; at each of their points their
ideal is generated by a member of a regular system of parameters, by the normal crossings of `E`,
so they are non-singular of codimension one; they are finite in number by the noetherianity of
`X`, and `E` is reduced, so it is the union of its components. -/
@[blueprint "lem:IV.0-presentation-exists"
  (statement := /-- Let $\mathfrak R^{N,n}_{\mathrm I}=(E;V_1,\dots,V_\beta;W)$ be a resolution
    datum on a non-singular irreducible algebraic scheme $X$. Then there are $\alpha\ge0$ and
    non-singular irreducible subschemes $E_1,\dots,E_\alpha$ of $X$ of codimension one with
    $E=E_1\cup\dots\cup E_\alpha$, i.e.\ $\mathfrak R$ can be written in the form
    $(\bigcup_{i=1}^\alpha E_i;V_1,\dots,V_\beta;W)$. (The convention of p.~274.) -/)
  (proof := /-- Let $E_1,\dots,E_\alpha$ be the irreducible components of $E$; there are finitely
    many, as $X$ is noetherian, and $E$ is the union of them as $E$ is reduced. Let $x$ be a point
    of $E_i$. As $E$ has only normal crossings at $x$, the ideal of $E_i$ in $\mathcal O_{X,x}$ is
    generated by a member $z$ of a regular system of parameters of $\mathcal O_{X,x}$
    (\cref{def:0.2-normal-crossings-with-at}); hence $E_i$ is non-singular at $x$ and of
    codimension one there. Finally $E_i$ is irreducible, being the reduced structure on an
    irreducible closed set.

    \textbf{Deviation from the paper (gap filled).} The paper says only ``We agree once for all
    that whenever this expression is taken, all the $E_j$ denote non-singular irreducible
    subschemes of $X$ of codimension one'' (p.~274) and does not say that every datum has such an
    expression. -/)
  (latexEnv := "lemma")]
theorem DatumI.Raw.isUnionOfDivisors_of_isDatum {X : Scheme.{u}} {N : ℕ} (hX : IsAmbient X N)
    (ℜ : DatumI.Raw X) (hℜ : ℜ.IsDatum) : ℜ.IsUnionOfDivisors := by
  have := hX.1
  exact DatumI.Raw.isUnionOfDivisors_of_isNonsingular hX.2.1 ℜ hℜ

end Hironaka
