/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Architect
public import Hironaka.Compat.RestrictSubset
public import Hironaka.Statements

/-!
# Ch. 0 §3 (pp. 130–131): algebraic Ω-varieties attached to algebraic B-schemes

The scheme-level facts of pp. 130–131 for an algebraic scheme over a field `B`, a reduced and
irreducible algebraic `B`-scheme `X`, and an algebraically closed field `Ω ⊇ B`.

> Let us first consider the case in which X is an algebraic B-scheme where B is a field. Let us also assume that X is
> reduced and irreducible. Let Ω be an algebraically closed field, and suppose B is given as a subfield of Ω, so that
> we can view Spec(Ω) as a B-scheme in a fixed way. Let X_Ω denote the product of X and Spec(Ω) in the category of
> B-schemes. ... Let X(Ω) denote the set of Ω-morphisms from Spec(Ω) to X_Ω, which are called geometric points of X in
> Ω. ... Let f be the natural mapping of X(Ω) into the underlying topological space of X_Ω. Then f is injective and
> induces a structure of Ω-local-ringed space on X(Ω) which is isomorphic to the restriction of X_Ω to the image of
> f. An Ω-local-ringed space obtained in this manner is called an algebraic variety (or, more precisely, an algebraic
> Ω-variety) if X_Ω is also reduced and irreducible. (p. 130)

## What is formalized

The base change `X_Ω` (`baseChange`), the geometric points `X(Ω)` (`GeometricPoint`), the condition "`X_Ω` is also
reduced and irreducible" (`IsAlgebraicVariety`), Weil-regularity of `B(X)/B` (`IsRegularExtension`), and the claims
of pp. 130–131 about them (each a `def … : Prop` with its classification in its docstring).

The `Ω`-local-ringed space `X̄` itself is the restriction of `X_Ω` to the image of the set of geometric points
(`varietyOf`, using `LocallyRingedSpace.restrictSubset`, which restricts to an arbitrary subset), with its
structure morphism to `Spec Ω` (`varietyOver`, an object of `Over (specOmega Ω)`, the category of `Ω`-local-ringed
spaces) and its natural morphism to `X` (`varietyToScheme`).  On top of it: the claim that `f` induces the structure
on `X(Ω)` (`GeometricPointsInduceVariety`), "defined over `B`" and "algebraic `Ω`-variety" (`IsDefinedOver`,
`IsAlgebraicOmegaVariety`), the uniqueness of `X` (`SchemeDeterminedByVariety`), the canonical `Ω`-morphism induced
by `f × id` (`IsInducedBy`, `InducedVarietyMorphismExists`), morphisms of varieties obtained from `B`-morphisms
(`Presentation`, `MorphismFromBMorphism`, `MorphismDefinedOver`), properness (`IsProperMorphism`) and its independence
of `B` (`ProperIndependentOfField`).

## Formalization notes (encoding)

* Generic point, irreducible, function field: Mathlib's `IrreducibleSpace`, `IsReduced`, `Scheme.functionField` (a
  field for an integral scheme) and the project's `functionFieldAlgebraMap`; the algebraic `B`-scheme `X` is a Mathlib
  scheme with `p : X ⟶ Spec B` locally of finite type, quasi-compact and separated (`IsReducedIrreducibleAlgebraic`).
  The printed definition of a generic point ("the closure of `{x̄}` contains an open subset of `X`") must mean a
  *non-empty* open subset (the empty set is open); this slip is recorded and not formalized here, since it is not
  needed by the statements below.
* "Non-singular" for `X̄`: a point of `X̄ = X(Ω)` is simple iff its local ring is regular, and the local ring of the
  restriction of `X_Ω` at a geometric point is the local ring of `X_Ω` at its image (the stalk of an inverse image
  sheaf is the stalk), so `X̄` is non-singular iff `X_Ω` is regular at every point in the image of a geometric point
  (`GeometricPoint.IsSimple`); the singular locus of `X̄` is the set of geometric points failing this.
* The `Ω`-local-ringed space `X̄`: an `S`-local-ringed space is a local-ringed space over `S` (p. 117), so the category
  of `Ω`-local-ringed spaces is `Over (specOmega Ω)` and an `Ω`-morphism is a morphism there.  "The restriction of
  `X_Ω` to the image of `f`" is `LocallyRingedSpace.restrictSubset` (inverse image of the structure sheaf).  The
  underlying set of `X̄` is the image of `f`; the structure "induced on `X(Ω)`" is the transport along the injection
  `f`, which `GeometricPointsInduceVariety` states as an isomorphism, with the identification of the points.
* "`X̄` is obtained from `X` in this manner" and "`B` is a field of definition of `X̄`" are encoded existentially
  (`IsDefinedOver`): an `Ω`-local-ringed space `V` is defined over the subfield `B` of `Ω` if it is isomorphic, over
  `Ω`, to `X̄` for some algebraic `B`-scheme `X` (reduced, irreducible, with `X_Ω` reduced and irreducible).
* "The one induced by `f × (identity)`": the restriction of `f × id : X₁Ω → X₂Ω` to `X̄₁ → X̄₂` is encoded by the
  commutative square with the inclusions `X̄ᵢ → X_{iΩ}` (`IsInducedBy`); that exactly one `Ω`-morphism makes the
  square commute is the claim `InducedVarietyMorphismExists`.
* "Obtained as above from a `B`-morphism" is the structure `Presentation`: algebraic `B`-schemes `Xᵢ` with varieties
  `X̄ᵢ ≅ Vᵢ`, a `B`-morphism `f` and the `Ω`-isomorphisms identifying the given `Ω`-morphism with the one induced by `f`.
* "Regular in the sense of A. Weil": `K ⊇ k` is regular iff `K` and `k̄` are linearly disjoint over `k`, equivalently
  `K ⊗_k k̄` is a domain (`IsRegularExtension`), recorded as an encoding choice.

## Not formalized

The comparison with the definitions of Serre and Weil ("conicides [sic] with that of J-P. Serre (and essentially
with that of A. Weil)", p. 131) and the analytic sentences (complex numbers, analytic `ℂ`-covers) are not formalized.

## Misprints of the source

p. 131 "conicides" (kept, with [sic], in the quotation above).  p. 130: "generic point" is defined by "an open
subset of X", which must mean a non-empty one; not formalized.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace Hironaka

universe u

namespace AlgebraicVariety

variable (B Ω : Type u) [Field B] [Field Ω] [Algebra B Ω]

/-- The morphism `Spec Ω ⟶ Spec B` given by the inclusion of `B` in `Ω` (the fixed `B`-scheme structure of `Spec Ω`, p. 130). -/
abbrev specAlgebraMap : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B Ω))

variable {B Ω} {X : Scheme.{u}}

/-- The product `X_Ω = X ×_{Spec B} Spec Ω` in the category of `B`-schemes (p. 130).

> Let Ω be an algebraically closed field, and suppose B is given as a subfield of Ω, so that we can view Spec(Ω) as a
> B-scheme in a fixed way. Let X_Ω denote the product of X and Spec(Ω) in the category of B-schemes. Then X_Ω can be
> viewed as an algebraic Ω-scheme in a natural manner. (p. 130)

Definition (p. 130).  Formalization note (encoding): the fibre product `pullback p (specAlgebraMap B Ω)`; that
`X_Ω` is an algebraic `Ω`-scheme (the second sentence, stated without proof) is `BaseChangeIsAlgebraic`. -/
@[blueprint "def:0.3-base-change"
  (statement := /-- Let $\Omega$ be an algebraically closed field, and suppose $\mathbf B$ is given as a subfield of $\Omega$, so that we
    can view $\operatorname{Spec}(\Omega)$ as a $\mathbf B$-scheme in a fixed way. Let $X_\Omega$ denote the product of $X$
    and $\operatorname{Spec}(\Omega)$ in the category of $\mathbf B$-schemes. (p.~130.) -/)
  (latexEnv := "definition")]

abbrev baseChange (p : X ⟶ Spec (CommRingCat.of B)) : Scheme.{u} :=
  pullback p (specAlgebraMap B Ω)

variable (B Ω) in
/-- A geometric point of `X` in `Ω`: an `Ω`-morphism `Spec Ω ⟶ X_Ω`.

> Let X(Ω) denote the set of Ω-morphisms from Spec(Ω) to X_Ω, which are called geometric points of X in Ω. (p. 130)

Definition (p. 130).  Formalization note (encoding): an `Ω`-morphism is a section of the projection `X_Ω ⟶ Spec Ω`
(`s ≫ pullback.snd = 𝟙`). -/
@[blueprint "def:0.3-geometric-point"
  (statement := /-- Let $X(\Omega)$ denote the set of $\Omega$-morphisms from $\operatorname{Spec}(\Omega)$ to $X_\Omega$, which are
    called \emph{geometric points of $X$ in $\Omega$}. (p.~130.) Formalization note (encoding): an $\Omega$-morphism
    is a section of the projection $X_\Omega\to\operatorname{Spec}(\Omega)$. -/)
  (latexEnv := "definition")]

structure GeometricPoint (p : X ⟶ Spec (CommRingCat.of B)) where
  /-- The morphism `Spec Ω ⟶ X_Ω`. -/
  s : Spec (CommRingCat.of Ω) ⟶ baseChange (Ω := Ω) p
  /-- `s` is a morphism over `Ω`. -/
  over : s ≫ pullback.snd p (specAlgebraMap B Ω) = 𝟙 _

/-- The standing assumptions of p. 130: `p : X ⟶ Spec B` makes `X` an algebraic `B`-scheme (`B` a field, hence noetherian),
and `X` is reduced and irreducible.

> Let us first consider the case in which X is an algebraic B-scheme where B is a field. Let us also assume that X is
> reduced and irreducible. (p. 130)

Formalization note (encoding): the algebraic `B`-scheme is separated, locally of finite type and quasi-compact over
`Spec B` (p. 118), as in the other statements of Ch. 0. -/
def IsReducedIrreducibleAlgebraic (p : X ⟶ Spec (CommRingCat.of B)) : Prop :=
  LocallyOfFiniteType p ∧ QuasiCompact p ∧ IsSeparated p ∧ IsReduced X ∧ IrreducibleSpace X

/-- Geometric points correspond to `B`-morphisms `Spec Ω ⟶ X`.

> (In fact, this set is in a one to one correspondence with the set of B-morphisms of Spec(Ω) to X, where an
> Ω-morphism of Spec(Ω) to X_Ω followed by the projection of X_Ω gives rise to a B-morphism of Spec(Ω) to X.) (p. 130)

Stated without proof (p. 130, "In fact"); not proved here (it is the universal property of the fibre product).
Formalization note: stated under the standing hypotheses of p. 130 (`X` an algebraic `B`-scheme, reduced and irreducible,
`B` a field, `Ω ⊇ B` algebraically closed). -/
@[blueprint "prop:0.3-geometric-points-b-morphisms"
  (statement := /-- (In fact, this set is in a one to one correspondence with the set of $\mathbf B$-morphisms of
    $\operatorname{Spec}(\Omega)$ to $X$, where an $\Omega$-morphism of $\operatorname{Spec}(\Omega)$ to $X_\Omega$ followed by
    the projection of $X_\Omega$ gives rise to a $\mathbf B$-morphism of $\operatorname{Spec}(\Omega)$ to $X$.) (p.~130.)
    Formalization note: under the standing hypotheses of p.~130 ($X$ an algebraic $\mathbf B$-scheme, reduced and
    irreducible, $\Omega$ algebraically closed). Not proved here: stated without argument (it is the universal
    property of the product). -/)
  (latexEnv := "proposition")]
def GeometricPointsEquivBMorphisms : Prop :=
  ∀ (B Ω : Type u) [Field B] [Field Ω] [Algebra B Ω] [IsAlgClosed Ω] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of B)), IsReducedIrreducibleAlgebraic p →
    Function.Injective (fun s : GeometricPoint B Ω p => s.s ≫ pullback.fst p (specAlgebraMap B Ω)) ∧
    Set.range (fun s : GeometricPoint B Ω p => s.s ≫ pullback.fst p (specAlgebraMap B Ω)) =
      {t : Spec (CommRingCat.of Ω) ⟶ X | t ≫ p = specAlgebraMap B Ω}

/-- `X_Ω` is an algebraic `Ω`-scheme.

> Then X_Ω can be viewed as an algebraic Ω-scheme in a natural manner. (p. 130)

Stated without proof or citation (p. 130); not proved here.  Formalization note (encoding): "algebraic `Ω`-scheme" is
the projection `X_Ω ⟶ Spec Ω` being locally of finite type, quasi-compact and separated (`Ω` is a field, hence
noetherian). -/
@[blueprint "prop:0.3-base-change-algebraic"
  (statement := /-- Then $X_\Omega$ can be viewed as an algebraic $\Omega$-scheme in a natural manner. (p.~130.)
    Formalization note (encoding): the projection $X_\Omega\to\operatorname{Spec}(\Omega)$ is separated and of finite
    type. Not proved here: stated without argument or citation. -/)
  (latexEnv := "proposition")]
def BaseChangeIsAlgebraic : Prop :=
  ∀ (B Ω : Type u) [Field B] [Field Ω] [Algebra B Ω] [IsAlgClosed Ω] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of B)), IsReducedIrreducibleAlgebraic p →
    LocallyOfFiniteType (pullback.snd p (specAlgebraMap B Ω)) ∧
    QuasiCompact (pullback.snd p (specAlgebraMap B Ω)) ∧ IsSeparated (pullback.snd p (specAlgebraMap B Ω))

/-- The statement of `BaseChangePreschemeIsAlgebraic` for a given field `K`: for every subfield `k` of `K`, the base change
of an algebraic `k`-prescheme to `K` is of finite type over `Spec K`. -/
def BaseChangePreschemeIsAlgebraicOver (K : Type) [Field K] : Prop :=
  ∀ (k : Subfield K) (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of k)),
    LocallyOfFiniteType p → QuasiCompact p →
    LocallyOfFiniteType (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
    QuasiCompact (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k K))))

/-- For `k ⊆ K` with `K = ℂ` or `ℝ`, the base change of an algebraic `k`-prescheme to `K` is an algebraic `K`-prescheme.

> Let k and K be as above. Let X be an algebraic k-prescheme and let X_K denote the product X ×_{Spec(k)} Spec(K) in the
> category pre-𝔖/k, which can be viewed as an algebraic K-prescheme. (p. 122)

Stated without proof or citation (p. 122); not proved here.  Formalization note: only this algebraic assertion of the
sentence is stated; the rest of the paragraph (analytic K-covers) is analytic and not formalized.  "`k` and `K` as
above" is `k` a subfield of `K = ℂ` or `ℝ`. -/
@[blueprint "prop:0.3-base-change-prescheme-algebraic"
  (statement := /-- Let $\mathbf k$ and $\mathbf K$ be as above. Let $X$ be an algebraic $\mathbf k$-prescheme and let $X_{\mathbf K}$
    denote the product $X\times_{\operatorname{Spec}(\mathbf k)}\operatorname{Spec}(\mathbf K)$ in the category
    $\mathrm{pre}\text{-}\mathfrak S/\mathbf k$, which can be viewed as an algebraic $\mathbf K$-prescheme. (p.~122.)
    Formalization note: only the algebraic assertion is stated, for $\mathbf k$ a subfield of $\mathbb C$ or $\mathbb R$.
    Not proved here: stated without argument or citation. -/)
  (latexEnv := "proposition")]
def BaseChangePreschemeIsAlgebraic : Prop :=
  BaseChangePreschemeIsAlgebraicOver Complex ∧ BaseChangePreschemeIsAlgebraicOver Real

/-- The natural map of `X(Ω)` into the underlying topological space of `X_Ω` is injective.

> Let f be the natural mapping of X(Ω) into the underlying topological space of X_Ω. Then f is injective and induces
> a structure of Ω-local-ringed space on X(Ω) which is isomorphic to the restriction of X_Ω to the image of f. (p. 130)

Stated without proof (p. 130); not proved here.  Formalization note: only the injectivity is stated (a geometric
point is determined by the point of `X_Ω` it hits: two with the same image coincide); the second assertion (the
`Ω`-local-ringed space structure on `X(Ω)`) is the separate node `GeometricPointsInduceVariety`, on the space `varietyOf`. -/
@[blueprint "prop:0.3-geometric-points-injective"
  (statement := /-- Let $f$ be the natural mapping of $X(\Omega)$ into the underlying topological space of $X_\Omega$. Then $f$ is
    injective and induces a structure of $\Omega$-local-ringed space on $X(\Omega)$ which is isomorphic to the
    restriction of $X_\Omega$ to the image of $f$. (p.~130.) Formalization note: only the injectivity of $f$ is stated
    (the point of $X_\Omega$ hit by a geometric point is the image of the unique point of $\operatorname{Spec}\Omega$);
    the structure of local-ringed space on $X(\Omega)$ is the separate node \texttt{GeometricPointsInduceVariety}
    (the space \texttt{varietyOf}, a restriction to a non-open subset). Not proved here: stated without argument. -/)
  (latexEnv := "proposition")]

def GeometricPointsInjective : Prop :=
  ∀ (B Ω : Type u) [Field B] [Field Ω] [Algebra B Ω] [IsAlgClosed Ω]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of B)), IsReducedIrreducibleAlgebraic p →
    ∀ s t : GeometricPoint B Ω p, Set.range s.s.base = Set.range t.s.base → s.s = t.s

/-- `X_Ω` is also reduced and irreducible, i.e. the `Ω`-local-ringed space `X(Ω)` is an algebraic `Ω`-variety.

> An Ω-local-ringed space obtained in this manner is called an algebraic variety (or, more precisely, an algebraic
> Ω-variety) if X_Ω is also reduced and irreducible. This condition on X (which is assumed to be reduced and
> irreducible) is equivalent to saying that the field extension B(X)/B is regular in the sense of A. Weil ... (pp.
> 130–131)

Definition (p. 130).  Formalization note (encoding): the condition on `X` that makes `X(Ω)` an algebraic
`Ω`-variety; the `Ω`-local-ringed space itself is `varietyOf` (with `GeometricPointsInduceVariety` and
`IsAlgebraicOmegaVariety`). -/
@[blueprint "def:0.3-algebraic-variety"
  (statement := /-- An $\Omega$-local-ringed space obtained in this manner is called an \emph{algebraic variety} (or, more precisely, an
    \emph{algebraic $\Omega$-variety}) if $X_\Omega$ is also reduced and irreducible. (p.~130.) Formalization note
    (encoding): the condition on $X$ that $X_\Omega$ be reduced and irreducible; the local-ringed space $X(\Omega)$ is
    \texttt{varietyOf} (see \texttt{GeometricPointsInduceVariety}, \texttt{IsAlgebraicOmegaVariety}). -/)
  (latexEnv := "definition")]

def IsAlgebraicVariety (p : X ⟶ Spec (CommRingCat.of B)) : Prop :=
  IsReduced (baseChange (Ω := Ω) p) ∧ IrreducibleSpace (baseChange (Ω := Ω) p)

/-- The field extension `K/k` is regular in the sense of A. Weil.

Definition by name (p. 131: "regular in the sense of A. Weil"; Foundations of Algebraic Geometry).  Formalization
note (encoding): `K` is regular over `k` iff `K` and an algebraic closure `k̄` are linearly disjoint over `k`, which
is equivalent to `K ⊗_k k̄` being an integral domain (a domain embeds in its field of fractions, a common field
extension of `K` and `k̄`, in which linear disjointness is the injectivity of `K ⊗_k k̄ → K k̄`); recorded as an
encoding choice. -/
@[blueprint "def:0.3-regular-extension"
  (statement := /-- A field extension $K/k$ is \emph{regular in the sense of A.~Weil} (p.~131) if $K$ and an algebraic closure of $k$
    are linearly disjoint over $k$. Formalization note (encoding): equivalently, $K\otimes_k\bar k$ is an integral
    domain. -/)
  (latexEnv := "definition")]

def IsRegularExtension (k K : Type u) [Field k] [CommRing K] [Algebra k K] : Prop :=
  IsDomain (TensorProduct k K (AlgebraicClosure k))

/-- `X_Ω` is reduced and irreducible iff the function field extension `B(X)/B` is regular in the sense of Weil.

> This condition on X (which is assumed to be reduced and irreducible) is equivalent to saying that the field
> extension B(X)/B is regular in the sense of A. Weil, where B(X) denotes the function field of X. (p. 131)

Stated without proof (p. 131); not proved here. -/
@[blueprint "prop:0.3-variety-iff-regular"
  (statement := /-- This condition on $X$ (which is assumed to be reduced and irreducible) is equivalent to saying that the field extension
    $\mathbf B(X)/\mathbf B$ is \emph{regular} in the sense of A.~Weil, where $\mathbf B(X)$ denotes the function field of
    $X$. (p.~131.) Not proved here: stated without argument. -/)
  (latexEnv := "proposition")]

def VarietyIffRegularExtension : Prop :=
  ∀ (B Ω : Type u) [Field B] [Field Ω] [Algebra B Ω] [IsAlgClosed Ω]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of B)) (h : IsReducedIrreducibleAlgebraic p),
    haveI : IrreducibleSpace X := h.2.2.2.2
    IsAlgebraicVariety (Ω := Ω) p ↔
      @IsRegularExtension B X.functionField _ _ (functionFieldAlgebraMap p).toAlgebra

/-- The condition that `X_Ω` be reduced and irreducible does not depend on the algebraically closed field `Ω`.

> This regularity of the field extension is independent of Ω ... (p. 131)

Stated without proof (p. 131); not proved here.  Formalization note: the independence is of the condition that
`X_Ω` be reduced and irreducible, to which the regularity is equivalent. -/
@[blueprint "prop:0.3-regularity-independent-of-omega"
  (statement := /-- This regularity of the field extension is independent of $\Omega$ \dots{} (p.~131.) Formalization note: stated as the
    independence of the condition that $X_\Omega$ be reduced and irreducible. Not proved here: stated without
    argument. -/)
  (latexEnv := "proposition")]

def RegularityIndependentOfOmega : Prop :=
  ∀ (B Ω₁ Ω₂ : Type u) [Field B] [Field Ω₁] [Field Ω₂] [Algebra B Ω₁] [Algebra B Ω₂]
    [IsAlgClosed Ω₁] [IsAlgClosed Ω₂] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of B)),
    IsReducedIrreducibleAlgebraic p →
    (IsAlgebraicVariety (Ω := Ω₁) p ↔ IsAlgebraicVariety (Ω := Ω₂) p)

/-- In characteristic zero, `B(X)/B` is regular iff `B` is algebraically closed in `B(X)`.

> ... and if B has characteristic zero, it amounts to saying that B is algebraically closed in B(X). (p. 131)

Stated without proof (p. 131); not proved here. -/
@[blueprint "prop:0.3-regular-char-zero"
  (statement := /-- \dots{} and if $\mathbf B$ has characteristic zero, it amounts to saying that $\mathbf B$ is algebraically closed in
    $\mathbf B(X)$. (p.~131.) Not proved here: stated without argument. -/)
  (latexEnv := "proposition")]

def RegularExtensionCharZero : Prop :=
  ∀ (B : Type u) [Field B] [CharZero B] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of B))
    (h : IsReducedIrreducibleAlgebraic p),
    haveI : IrreducibleSpace X := h.2.2.2.2
    letI : Algebra B X.functionField := (functionFieldAlgebraMap p).toAlgebra
    IsRegularExtension B X.functionField ↔
      ∀ a : X.functionField, IsAlgebraic B a → a ∈ Set.range (algebraMap B X.functionField)

/-- The geometric point `s` of `X` is a simple point of the `Ω`-variety `X̄`: the local ring of `X_Ω` at (the image of) `s` is
regular.

Formalization note (encoding): the local ring of the restriction `X̄` of `X_Ω` at a geometric point is the local ring of `X_Ω` at its
image (stalks of an inverse image sheaf are stalks); "simple" is regularity of the local ring (p. 121, `Scheme.IsSimpleAt`). -/
def GeometricPoint.IsSimple (p : X ⟶ Spec (CommRingCat.of B)) (s : GeometricPoint B Ω p) : Prop :=
  ∀ y ∈ Set.range s.s.base, (baseChange (Ω := Ω) p).IsSimpleAt y

/-- If `X̄` is non-singular then `X` is non-singular.

> With X and X̄ related in this manner, if X̄ is non-singular, then X is necessarily non-singular. (p. 131)

Stated without proof (p. 131, "necessarily"); not proved here.  Formalization note (encoding): "`X̄` is non-singular"
is that all its points (geometric points) are simple, see `GeometricPoint.IsSimple`; `X` is non-singular is
`Scheme.IsNonsingular`. -/
@[blueprint "prop:0.3-variety-nonsingular-implies"
  (statement := /-- With $X$ and $\bar X$ related in this manner, if $\bar X$ is non-singular, then $X$ is necessarily non-singular.
    (p.~131.) Formalization note (encoding): $\bar X$ is non-singular if its local rings at all geometric points are
    regular. Not proved here: stated without argument. -/)
  (latexEnv := "proposition")]

def NonsingularOfNonsingularVariety : Prop :=
  ∀ (B Ω : Type u) [Field B] [Field Ω] [Algebra B Ω] [IsAlgClosed Ω]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of B)), IsReducedIrreducibleAlgebraic p →
    IsAlgebraicVariety (Ω := Ω) p → (∀ s : GeometricPoint B Ω p, s.IsSimple p) → X.IsNonsingular

/-- The converse holds in characteristic zero: if `X` is non-singular then `X̄` is non-singular.

> The converse is true if Ω (or, equivalently B) has characteristic zero ... (p. 131)

Stated without proof (p. 131); not proved here (see `SingularLocusIsPreimage` for the stronger statement). -/
@[blueprint "prop:0.3-variety-nonsingular-converse-char-zero"
  (statement := /-- The converse is true if $\Omega$ (or, equivalently $\mathbf B$) has characteristic zero \dots{} (p.~131.) Not proved
    here: stated without argument. -/)
  (latexEnv := "proposition")]

def NonsingularVarietyOfNonsingularCharZero : Prop :=
  ∀ (B Ω : Type u) [Field B] [Field Ω] [Algebra B Ω] [IsAlgClosed Ω] [CharZero B]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of B)), IsReducedIrreducibleAlgebraic p →
    IsAlgebraicVariety (Ω := Ω) p → X.IsNonsingular → ∀ s : GeometricPoint B Ω p, s.IsSimple p

/-- The converse fails in general (positive characteristic): there are `B`, `Ω`, `X` with `X` non-singular but `X̄`
singular.

> ... but not in general if otherwise. (p. 131)

Stated without proof or example (p. 131, "but not in general"); not proved here.  Formalization note: the
assertion is read as the existence of a counterexample to the converse (for instance `y² = x³ − t` over `𝔽₃(t)`); it
is not claimed to be unique, and the assumptions of the setting (`X` reduced and irreducible, `X̄` a variety) are kept. -/
@[blueprint "prop:0.3-variety-nonsingular-converse-fails"
  (statement := /-- The converse is true if $\Omega$ (or, equivalently $\mathbf B$) has characteristic zero, but not in general if
    otherwise. (p.~131.) Formalization note: ``but not in general'' is read as the existence of a counterexample to the
    converse. Not proved here: stated without argument or example. -/)
  (latexEnv := "proposition")]

def NonsingularConverseFailsInGeneral : Prop :=
  ∃ (B Ω : Type u) (_ : Field B) (_ : Field Ω) (_ : Algebra B Ω) (_ : IsAlgClosed Ω)
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of B)), IsReducedIrreducibleAlgebraic p ∧
    IsAlgebraicVariety (Ω := Ω) p ∧ X.IsNonsingular ∧ ∃ s : GeometricPoint B Ω p, ¬ s.IsSimple p

/-- In characteristic zero the singular locus of `X̄` is the preimage of that of `X`.

> In fact, if B (hence, Ω) has characteristic zero, the singular locus of X̄ (i.e., the set of multiple points of X̄)
> is equal to the preimage of the singular locus of X under the natural B-morphism of X̄ to X. (p. 131)

Stated without proof (p. 131, "In fact"); not proved here.  Formalization note (encoding): the natural
`B`-morphism `X̄ → X` is, on points, the first projection `X_Ω ⟶ X` applied to the image of the geometric point; a point
is multiple iff it is not simple (`Scheme.IsSimpleAt`). -/
@[blueprint "prop:0.3-singular-locus-preimage"
  (statement := /-- In fact, if $\mathbf B$ (hence, $\Omega$) has characteristic zero, the singular locus of $\bar X$ (i.e., the set of
    multiple points of $\bar X$) is equal to the preimage of the singular locus of $X$ under the natural
    $\mathbf B$-morphism of $\bar X$ to $X$. (p.~131.) Formalization note (encoding): on points, the natural morphism is the
    first projection of $X_\Omega\to X$. Not proved here: stated without argument. -/)
  (latexEnv := "proposition")]

def SingularLocusIsPreimage : Prop :=
  ∀ (B Ω : Type u) [Field B] [Field Ω] [Algebra B Ω] [IsAlgClosed Ω] [CharZero B]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of B)), IsReducedIrreducibleAlgebraic p →
    IsAlgebraicVariety (Ω := Ω) p → ∀ (s : GeometricPoint B Ω p), ∀ y ∈ Set.range s.s.base,
      (¬ (baseChange (Ω := Ω) p).IsSimpleAt y ↔
        ¬ X.IsSimpleAt ((pullback.fst p (specAlgebraMap B Ω)).base y))

/-- The `Ω`-local-ringed space `Spec Ω`, the base of the category of `Ω`-local-ringed spaces (the paper's "`S`-local-ringed
spaces" for `S = Spec Ω`, p. 117). -/
abbrev specOmega (Ω : Type u) [Field Ω] : LocallyRingedSpace.{u} :=
  (Spec (CommRingCat.of Ω)).toLocallyRingedSpace

/-- The image of the natural mapping `f` of `X(Ω)` into the underlying space of `X_Ω`: the points of `X_Ω` hit by a
geometric point.

> Let f be the natural mapping of X(Ω) into the underlying topological space of X_Ω. (p. 130)

Definition (p. 130). -/
def geometricPointImage (p : X ⟶ Spec (CommRingCat.of B)) :
    Set (baseChange (Ω := Ω) p).toLocallyRingedSpace :=
  {y | ∃ s : GeometricPoint B Ω p, y ∈ Set.range s.s.base}

/-- The `Ω`-local-ringed space `X̄`: the restriction of `X_Ω` to the image of `f`.

> Then f is injective and induces a structure of Ω-local-ringed space on X(Ω) which is isomorphic to the restriction of
> X_Ω to the image of f. (p. 130)

Definition (p. 130).  Formalization note (encoding): `X̄` is taken to be the restriction of `X_Ω` to the image of `f`
(`LocallyRingedSpace.restrictSubset`, the restriction to an arbitrary subset, here a non-open one), so that its
underlying set is the image of `f`; the structure induced on the set `X(Ω)` itself is the transport along the
injection `f` and is the content of `GeometricPointsInduceVariety`.  Its structure of `Ω`-local-ringed space is
`varietyToSpec`. -/
@[blueprint "def:0.3-variety"
  (statement := /-- Let $f$ be the natural mapping of $X(\Omega)$ into the underlying topological space of $X_\Omega$.
    Then \dots{} the restriction of $X_\Omega$ to the image of $f$ (p.~130), written $\bar X$. Formalization note
    (encoding): $\bar X$ is this restriction, to a non-open subset (\texttt{restrictSubset}), with its structure
    morphism to $\operatorname{Spec}(\Omega)$. -/)
  (latexEnv := "definition")]
def varietyOf (p : X ⟶ Spec (CommRingCat.of B)) : LocallyRingedSpace.{u} :=
  (baseChange (Ω := Ω) p).toLocallyRingedSpace.restrictSubset (geometricPointImage p)

/-- The canonical morphism `X̄ ⟶ X_Ω` (the inclusion of the restriction). -/
def varietyIncl (p : X ⟶ Spec (CommRingCat.of B)) :
    varietyOf (Ω := Ω) p ⟶ (baseChange (Ω := Ω) p).toLocallyRingedSpace :=
  LocallyRingedSpace.ofRestrictSubset _ _

/-- The structure morphism `X̄ ⟶ Spec Ω` of the `Ω`-local-ringed space `X̄`: the inclusion followed by the projection
`X_Ω ⟶ Spec Ω` (`X_Ω` is an `Ω`-scheme, p. 130). -/
def varietyToSpec (p : X ⟶ Spec (CommRingCat.of B)) : varietyOf (Ω := Ω) p ⟶ specOmega Ω :=
  varietyIncl p ≫ (pullback.snd p (specAlgebraMap B Ω)).toLRSHom

/-- `X̄` as an object of the category of `Ω`-local-ringed spaces (`Over (specOmega Ω)`). -/
def varietyOver (p : X ⟶ Spec (CommRingCat.of B)) : Over (specOmega Ω) :=
  Over.mk (varietyToSpec (Ω := Ω) p)

/-- The natural `B`-morphism `X̄ ⟶ X`: the inclusion into `X_Ω` followed by the first projection.

> ... the preimage of the singular locus of X under the natural B-morphism of X̄ to X. (p. 131)

Definition (p. 131; the statements of p. 131 above speak of it only on points, see `SingularLocusIsPreimage`). -/
def varietyToScheme (p : X ⟶ Spec (CommRingCat.of B)) :
    varietyOf (Ω := Ω) p ⟶ X.toLocallyRingedSpace :=
  varietyIncl p ≫ (pullback.fst p (specAlgebraMap B Ω)).toLRSHom

/-- The morphism `f × (identity) : X₁Ω ⟶ X₂Ω` induced by a `B`-morphism `f : X₁ ⟶ X₂`.

> ... the one induced by f × (identity) from X_{1Ω} to X_{2Ω}. (p. 131)

Definition (p. 131). -/
def baseChangeMap {X₁ X₂ : Scheme.{u}} {p₁ : X₁ ⟶ Spec (CommRingCat.of B)}
    {p₂ : X₂ ⟶ Spec (CommRingCat.of B)} (f : X₁ ⟶ X₂) (hf : f ≫ p₂ = p₁) :
    baseChange (Ω := Ω) p₁ ⟶ baseChange (Ω := Ω) p₂ :=
  pullback.map p₁ (specAlgebraMap B Ω) p₂ (specAlgebraMap B Ω) f (𝟙 _) (𝟙 _)
    (by simp [hf]) (by simp)

/-- The `Ω`-morphism `F : X̄₁ ⟶ X̄₂` is the one induced by `f × (identity)`: it is compatible with the inclusions into
`X₁Ω` and `X₂Ω` and `f × id`.

> ... f gives rise to a canonical Ω-morphism of X̄₁ to X̄₂, i.e., the one induced by f × (identity) from X_{1Ω} to
> X_{2Ω}. (p. 131)

Definition (p. 131).  Formalization note (encoding): "the one induced by `f × id`" is the restriction of `f × id` to
the images of the geometric points; it is encoded as the morphism making the square with the inclusions commute (the
inclusion of a restriction is a monomorphism, so there is at most one), and its existence is
`InducedVarietyMorphismExists`. -/
def IsInducedBy {X₁ X₂ : Scheme.{u}} {p₁ : X₁ ⟶ Spec (CommRingCat.of B)}
    {p₂ : X₂ ⟶ Spec (CommRingCat.of B)} (f : X₁ ⟶ X₂) (hf : f ≫ p₂ = p₁)
    (F : varietyOver (Ω := Ω) p₁ ⟶ varietyOver (Ω := Ω) p₂) : Prop :=
  F.left ≫ varietyIncl p₂ = varietyIncl p₁ ≫ (baseChangeMap (Ω := Ω) f hf).toLRSHom

/-- The map `f` of geometric points into `X_Ω` is injective and induces on `X(Ω)` a structure of `Ω`-local-ringed
space isomorphic to `X̄`.

> Let f be the natural mapping of X(Ω) into the underlying topological space of X_Ω. Then f is injective and induces
> a structure of Ω-local-ringed space on X(Ω) which is isomorphic to the restriction of X_Ω to the image of f. (p. 130)

Stated without proof (p. 130); not proved here.  Formalization note (encoding): the structure induced on the set
`X(Ω)` is stated existentially: there are an `Ω`-local-ringed space `V`, an `Ω`-isomorphism `V ≅ X̄` and a bijection
of the points of `V` with `X(Ω)` under which a geometric point corresponds to the point of `X̄` it hits (so the
bijection is `f`, and `f` is injective).  The injectivity alone is `GeometricPointsInjective`. -/
@[blueprint "prop:0.3-geometric-points-induce-variety"
  (statement := /-- Let $f$ be the natural mapping of $X(\Omega)$ into the underlying topological space of $X_\Omega$.
    Then $f$ is injective and induces a structure of $\Omega$-local-ringed space on $X(\Omega)$ which is isomorphic to
    the restriction of $X_\Omega$ to the image of $f$. (p.~130.) Formalization note (encoding): there is an
    $\Omega$-local-ringed space $V$ with an $\Omega$-isomorphism $V\cong\bar X$ and a bijection of its points with
    $X(\Omega)$ under which a geometric point corresponds to the point of $\bar X$ it hits. Not proved here: stated
    without argument. -/)
  (latexEnv := "proposition")]
def GeometricPointsInduceVariety : Prop :=
  ∀ (B Ω : Type u) [Field B] [Field Ω] [Algebra B Ω] [IsAlgClosed Ω] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of B)), IsReducedIrreducibleAlgebraic p →
    ∃ (V : Over (specOmega Ω)) (e : V ≅ varietyOver (Ω := Ω) p)
      (φ : V.left.carrier ≃ GeometricPoint B Ω p),
      ∀ v : V.left.carrier, Set.range (φ v).s.base =
        {(varietyIncl (Ω := Ω) p).base (e.hom.left.base v)}

/-- The `Ω`-local-ringed space `V` is defined over the subfield `B` of `Ω`: it is the `Ω`-variety `X̄` obtained from an
algebraic `B`-scheme `X` with `X_Ω` reduced and irreducible.

> When an algebraic Ω-variety X̄ is obtained from an algebraic B-scheme X (such that B(X)/B is a regular extension) in
> such a way as above, X is uniquely determined by X̄ and B (up to a B-isomorphism) and we say that X̄ is defined over
> B, or B is a field of definition of X̄. (p. 131)

Definition (p. 131).  Formalization note (encoding): "obtained from `X` in such a way as above" is
`V ≅ varietyOver p` over `Ω`; the algebraic `B`-scheme is `IsReducedIrreducibleAlgebraic p` and "`B(X)/B` is a
regular extension" is `IsAlgebraicVariety p` (the two are equivalent, `VarietyIffRegularExtension`). -/
@[blueprint "def:0.3-defined-over"
  (statement := /-- When an algebraic $\Omega$-variety $\bar X$ is obtained from an algebraic $\mathbf B$-scheme $X$ (such that
    $\mathbf B(X)/\mathbf B$ is a regular extension) in such a way as above, we say that $\bar X$ is \emph{defined over}
    $\mathbf B$, or $\mathbf B$ is a \emph{field of definition of} $\bar X$. (p.~131.) Formalization note (encoding):
    $V$ is $\Omega$-isomorphic to $\bar X$ for an algebraic $\mathbf B$-scheme $X$ with $X_\Omega$ reduced and
    irreducible. -/)
  (latexEnv := "definition")]
def IsDefinedOver (B : Subfield Ω) (V : Over (specOmega Ω)) : Prop :=
  ∃ (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of B)), IsReducedIrreducibleAlgebraic p ∧
    IsAlgebraicVariety (Ω := Ω) p ∧ Nonempty (V ≅ varietyOver (Ω := Ω) p)

/-- An algebraic `Ω`-variety: an `Ω`-local-ringed space obtained in the manner of p. 130 from an algebraic `B`-scheme
`X` for some subfield `B` of `Ω`, with `X_Ω` reduced and irreducible (the condition `IsAlgebraicVariety`).

> An Ω-local-ringed space obtained in this manner is called an algebraic variety (or, more precisely, an algebraic
> Ω-variety) if X_Ω is also reduced and irreducible. (p. 130)

Definition (p. 130).  Formalization note (encoding): "obtained in this manner" is existential in `B`, `X` and `p`
(`IsDefinedOver`); the condition on `X` is the existing `IsAlgebraicVariety`. -/
@[blueprint "def:0.3-algebraic-omega-variety"
  (statement := /-- An $\Omega$-local-ringed space obtained in this manner is called an \emph{algebraic variety} (or, more
    precisely, an \emph{algebraic $\Omega$-variety}) if $X_\Omega$ is also reduced and irreducible. (p.~130.)
    Formalization note (encoding): $V$ is an algebraic $\Omega$-variety if it is defined over some subfield
    $\mathbf B$ of $\Omega$. -/)
  (latexEnv := "definition")]
def IsAlgebraicOmegaVariety (Ω : Type u) [Field Ω] (V : Over (specOmega Ω)) : Prop :=
  ∃ B : Subfield Ω, IsDefinedOver B V

/-- `X` is uniquely determined by `X̄` and `B` up to a `B`-isomorphism, read literally: two algebraic `B`-schemes
whose `Ω`-varieties are `Ω`-isomorphic are `B`-isomorphic.

> ... X is uniquely determined by X̄ and B (up to a B-isomorphism) ... (p. 131)

Stated without argument or citation (p. 131); not proved here.  Statement as printed, read literally (false as
literally read): an abstract `Ω`-isomorphism `X̄₁ ≅ X̄₂` need not come from a `B`-isomorphism.  For `B = ℚ`,
`Ω = ℚ̄`, the projective line and the conic `x² + y² + z² = 0` have isomorphic varieties (the conic is `ℙ¹` over
`ℚ̄`) but are not `ℚ`-isomorphic (the conic has no rational point).  The paper presumably means that `X` is determined
by `X̄` together with the way `B` sits in it; no reading with this extra datum is formalized. -/
@[blueprint "prop:0.3-scheme-determined-by-variety"
  (statement := /-- When an algebraic $\Omega$-variety $\bar X$ is obtained from an algebraic $\mathbf B$-scheme $X$ (such that
    $\mathbf B(X)/\mathbf B$ is a regular extension) in such a way as above, $X$ is uniquely determined by $\bar X$
    and $\mathbf B$ (up to a $\mathbf B$-isomorphism). (p.~131.) \textbf{Statement as printed, read literally
    (false):} two algebraic $\mathbf B$-schemes with $\Omega$-isomorphic varieties are $\mathbf B$-isomorphic; the
    projective line and the conic $x^2+y^2+z^2=0$ over $\mathbb Q$ (with $\Omega=\overline{\mathbb Q}$) have isomorphic
    varieties but are not $\mathbb Q$-isomorphic. Not proved here: stated without argument or citation. -/)
  (latexEnv := "proposition")]
def SchemeDeterminedByVariety : Prop :=
  ∀ (B Ω : Type u) [Field B] [Field Ω] [Algebra B Ω] [IsAlgClosed Ω] (X₁ X₂ : Scheme.{u})
    (p₁ : X₁ ⟶ Spec (CommRingCat.of B)) (p₂ : X₂ ⟶ Spec (CommRingCat.of B)),
    IsReducedIrreducibleAlgebraic p₁ → IsReducedIrreducibleAlgebraic p₂ →
    IsAlgebraicVariety (Ω := Ω) p₁ → IsAlgebraicVariety (Ω := Ω) p₂ →
    Nonempty (varietyOver (Ω := Ω) p₁ ≅ varietyOver (Ω := Ω) p₂) →
    Nonempty (Over.mk p₁ ≅ Over.mk p₂)

/-- A `B`-morphism of algebraic `B`-schemes gives rise to a canonical `Ω`-morphism of the varieties.

> If f: X₁ → X₂ is a B-morphism of algebraic B-schemes, and if an algebraic Ω-variety X̄_i is obtained from X_i for each
> i = 1, 2, then f gives rise to a canonical Ω-morphism of X̄₁ to X̄₂, i.e., the one induced by f × (identity) from
> X_{1Ω} to X_{2Ω}. (p. 131)

Stated without proof (p. 131); not proved here.  Formalization note (encoding): "canonical" is read as: there is
exactly one `Ω`-morphism compatible with `f × id` (`IsInducedBy`). -/
@[blueprint "prop:0.3-induced-morphism-exists"
  (statement := /-- If $f\colon X_1\to X_2$ is a $\mathbf B$-morphism of algebraic $\mathbf B$-schemes, and if an algebraic
    $\Omega$-variety $\bar X_i$ is obtained from $X_i$ for each $i=1,2$, then $f$ gives rise to a canonical
    $\Omega$-morphism of $\bar X_1$ to $\bar X_2$, i.e., the one induced by $f\times(\mathrm{identity})$ from
    $X_{1\Omega}$ to $X_{2\Omega}$. (p.~131.) Formalization note (encoding): there is exactly one $\Omega$-morphism
    compatible with $f\times\mathrm{id}$ and the inclusions. Not proved here: stated without argument. -/)
  (latexEnv := "proposition")]
def InducedVarietyMorphismExists : Prop :=
  ∀ (B Ω : Type u) [Field B] [Field Ω] [Algebra B Ω] [IsAlgClosed Ω] (X₁ X₂ : Scheme.{u})
    (p₁ : X₁ ⟶ Spec (CommRingCat.of B)) (p₂ : X₂ ⟶ Spec (CommRingCat.of B)),
    IsReducedIrreducibleAlgebraic p₁ → IsReducedIrreducibleAlgebraic p₂ →
    IsAlgebraicVariety (Ω := Ω) p₁ → IsAlgebraicVariety (Ω := Ω) p₂ →
    ∀ (f : X₁ ⟶ X₂) (hf : f ≫ p₂ = p₁),
      ∃! F : varietyOver (Ω := Ω) p₁ ⟶ varietyOver (Ω := Ω) p₂, IsInducedBy f hf F

/-- An `Ω`-morphism `F : V₁ ⟶ V₂` of `Ω`-local-ringed spaces is obtained from a `B`-morphism of algebraic `B`-schemes:
the data of algebraic `B`-schemes `X₁`, `X₂` (with `X_{iΩ}` reduced and irreducible), a `B`-morphism `f`, and `Ω`-isomorphisms
`Vᵢ ≅ X̄ᵢ` under which `F` is the morphism induced by `f × id`.

> A morphism of algebraic Ω-varieties, X̄₁ → X̄₂, is by definition an Ω-morphism, and it is obtained as above from a
> B-morphism of algebraic B-schemes, where B is a suitable subfield of Ω over which X₁ and X₂ are defined. (p. 131)

Definition (p. 131).  Formalization note (encoding): "obtained as above from a `B`-morphism" is this structure for
the subfield `B`; "a morphism of algebraic `Ω`-varieties" is a morphism in `Over (specOmega Ω)` between algebraic
`Ω`-varieties (`IsAlgebraicOmegaVariety`). -/
@[blueprint "def:0.3-presentation"
  (statement := /-- A morphism of algebraic $\Omega$-varieties, $\bar X_1\to\bar X_2$, is by definition an $\Omega$-morphism,
    and it is obtained as above from a $\mathbf B$-morphism of algebraic $\mathbf B$-schemes, where $\mathbf B$ is a
    suitable subfield of $\Omega$ over which $X_1$ and $X_2$ are defined. (p.~131.) Formalization note (encoding): an
    $\Omega$-morphism $V_1\to V_2$ is obtained from the $\mathbf B$-morphism $f$ if, under $\Omega$-isomorphisms
    $V_i\cong\bar X_i$, it is the morphism induced by $f\times\mathrm{id}$. -/)
  (latexEnv := "definition")]
structure Presentation (B : Type u) [Field B] [Algebra B Ω] {V₁ V₂ : Over (specOmega Ω)}
    (F : V₁ ⟶ V₂) where
  /-- The source algebraic `B`-scheme. -/
  X₁ : Scheme.{u}
  /-- The target algebraic `B`-scheme. -/
  X₂ : Scheme.{u}
  /-- The structure morphism of `X₁`. -/
  p₁ : X₁ ⟶ Spec (CommRingCat.of B)
  /-- The structure morphism of `X₂`. -/
  p₂ : X₂ ⟶ Spec (CommRingCat.of B)
  /-- `X₁` is an algebraic `B`-scheme, reduced and irreducible. -/
  isAlgebraic₁ : IsReducedIrreducibleAlgebraic p₁
  /-- `X₂` is an algebraic `B`-scheme, reduced and irreducible. -/
  isAlgebraic₂ : IsReducedIrreducibleAlgebraic p₂
  /-- `X₁Ω` is reduced and irreducible. -/
  isVariety₁ : IsAlgebraicVariety (Ω := Ω) p₁
  /-- `X₂Ω` is reduced and irreducible. -/
  isVariety₂ : IsAlgebraicVariety (Ω := Ω) p₂
  /-- The `B`-morphism. -/
  f : X₁ ⟶ X₂
  /-- `f` is a `B`-morphism. -/
  hf : f ≫ p₂ = p₁
  /-- The identification of `V₁` with `X̄₁`. -/
  e₁ : V₁ ≅ varietyOver (Ω := Ω) p₁
  /-- The identification of `V₂` with `X̄₂`. -/
  e₂ : V₂ ≅ varietyOver (Ω := Ω) p₂
  /-- `F` is the morphism induced by `f × id`. -/
  induced : IsInducedBy f hf (e₁.inv ≫ F ≫ e₂.hom)

/-- Every `Ω`-morphism of algebraic `Ω`-varieties is obtained from a `B`-morphism of algebraic `B`-schemes, for a
suitable subfield `B` of `Ω`.

> A morphism of algebraic Ω-varieties, X̄₁ → X̄₂, is by definition an Ω-morphism, and it is obtained as above from a
> B-morphism of algebraic B-schemes, where B is a suitable subfield of Ω over which X₁ and X₂ are defined. (p. 131)

Stated without proof (p. 131); not proved here. -/
@[blueprint "prop:0.3-morphism-from-b-morphism"
  (statement := /-- A morphism of algebraic $\Omega$-varieties, $\bar X_1\to\bar X_2$, is by definition an $\Omega$-morphism,
    and it is obtained as above from a $\mathbf B$-morphism of algebraic $\mathbf B$-schemes, where $\mathbf B$ is a
    suitable subfield of $\Omega$ over which $X_1$ and $X_2$ are defined. (p.~131.) Not proved here: stated without
    argument. -/)
  (latexEnv := "proposition")]
def MorphismFromBMorphism : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (V₁ V₂ : Over (specOmega Ω)) (F : V₁ ⟶ V₂),
    IsAlgebraicOmegaVariety Ω V₁ → IsAlgebraicOmegaVariety Ω V₂ →
    ∃ B : Subfield Ω, Nonempty (Presentation (Ω := Ω) B F)

/-- The morphism of algebraic `Ω`-varieties `F` is defined over the subfield `B` of `Ω`.

> If B is so chosen, then we say that the morphism of algebraic Ω-varieties is defined over B. (p. 131)

Definition (p. 131). -/
@[blueprint "def:0.3-morphism-defined-over"
  (statement := /-- If $\mathbf B$ is so chosen, then we say that the morphism of algebraic $\Omega$-varieties is
    \emph{defined over} $\mathbf B$. (p.~131.) Formalization note (encoding): $F$ is obtained from a
    $\mathbf B$-morphism of algebraic $\mathbf B$-schemes in the sense of the structure \texttt{Presentation}. -/)
  (latexEnv := "definition")]
def MorphismDefinedOver (B : Subfield Ω) {V₁ V₂ : Over (specOmega Ω)} (F : V₁ ⟶ V₂) : Prop :=
  Nonempty (Presentation (Ω := Ω) B F)

/-- A morphism of algebraic `Ω`-varieties is proper if it is obtained from a proper `B`-morphism of algebraic
`B`-schemes.

> A morphism f̄: X̄₁ → X̄₂ is said to be proper, if it is obtained from a proper B-morphism (in the sense of A.
> Grothendieck) of algebraic B-schemes as above. (p. 131)

Definition (p. 131).  Formalization note (encoding): proper in the sense of Grothendieck is Mathlib's `IsProper`. -/
@[blueprint "def:0.3-proper-morphism"
  (statement := /-- A morphism $\bar f\colon\bar X_1\to\bar X_2$ is said to be \emph{proper}, if it is obtained from a proper
    $\mathbf B$-morphism (in the sense of A.~Grothendieck) of algebraic $\mathbf B$-schemes as above. (p.~131.)
    Formalization note (encoding): there are a subfield $\mathbf B$ and a presentation of $\bar f$ by a $\mathbf B$-morphism
    that is proper. -/)
  (latexEnv := "definition")]
def IsProperMorphism {V₁ V₂ : Over (specOmega Ω)} (F : V₁ ⟶ V₂) : Prop :=
  ∃ (B : Subfield Ω) (P : Presentation (Ω := Ω) B F), IsProper P.f

/-- Properness of the associated `B`-morphisms does not depend on the choice of `B`.

> This condition of being proper on the associated B-morphisms for a given f̄, is independent of the choice of B. (p. 131)

Stated without proof (p. 131); not proved here.  Formalization note (encoding): for two presentations of the same
`Ω`-morphism `F` over subfields `B₁`, `B₂`, the associated `B₁`- and `B₂`-morphisms are proper simultaneously. -/
@[blueprint "prop:0.3-proper-independent-of-field"
  (statement := /-- This condition of being proper on the associated $\mathbf B$-morphisms for a given $\bar f$, is independent
    of the choice of $\mathbf B$. (p.~131.) Formalization note (encoding): two presentations of the same
    $\Omega$-morphism over subfields $\mathbf B_1$, $\mathbf B_2$ have proper $\mathbf B_i$-morphisms simultaneously.
    Not proved here: stated without argument. -/)
  (latexEnv := "proposition")]
def ProperIndependentOfField : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (V₁ V₂ : Over (specOmega Ω)) (F : V₁ ⟶ V₂)
    (B₁ B₂ : Subfield Ω) (P₁ : Presentation (Ω := Ω) B₁ F) (P₂ : Presentation (Ω := Ω) B₂ F),
    IsProper P₁.f ↔ IsProper P₂.f

end AlgebraicVariety

end Hironaka

end
