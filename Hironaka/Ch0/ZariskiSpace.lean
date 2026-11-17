/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Architect
public import Hironaka.Ch0.RationalApplication
public import Hironaka.Ch0.Generalities
public import Hironaka.Compat.MonoidalSuccessionBaseChange
public import Hironaka.Statements

/-!
# Ch. 0 §6 (pp. 146-150): modifications, the Zariski space, complete morphisms, local uniformization (statements only)

> Let `f : X′ → X` be a rational application of reduced algebraic `B`-schemes (resp. reduced analytic `K`-spaces).  We
> say that `f` is a *modification* if `f` induces an isomorphism of the restrictions of `X′` and `X` to open dense
> subsets of their underlying topological spaces.  A modification is said to be *proper* if it is so as a rational
> application.  For a fixed reduced algebraic `B`-scheme (resp. a reduced analytic `K`-space) `X`, we consider the class
> `𝔐(X)` of all pairs `(X′, f)` of reduced algebraic `B`-schemes (resp. reduced analytic `K`-spaces) `X` [sic] and proper
> modifications `f` of `X′` to `X`.  (p. 146)

> We can prove that there exists a local-ringed space `ℨ(X)` with morphisms `h(X′, f) : ℨ(X) → X′` for `(X′, f) ∈ 𝔐(X)`,
> which has the following properties: (i) If `(X_i, f_i) ∈ 𝔐(X)`, for `i = 1, 2`, such that `f₁⁻¹ ∘ f₂` is a morphism,
> `h(X₁, f₁) = (f₁⁻¹ ∘ f₂) ∘ h(X₂, f₂)`, and (ii) if another `ℨ(X)′` with `h(X′, f)′ : ℨ(X) → X′` [sic] for
> `(X′, f) ∈ 𝔐(X)` has the property (i), then there exists a unique morphism `g : ℨ(X)′ → ℨ(X)` such that
> `h(X′, f)′ = h(X′, f) ∘ g` for all `(X′, f) ∈ 𝔐(X)`.  (pp. 146-147)

This file states, as `def … : Prop`, the claims of the algebraic case of §6; nothing is proved (every claim of the section
is either cited, deferred, stated without proof, or a question).  The analytic parts ("resp. analytic `K`-spaces",
"resp. `C`-space") are not formalized.

**Encodings (each stated in the docstring of the declaration concerned).**
* `B` is a noetherian commutative ring (p. 118: "We shall be particularly interested in `B`-schemes where `B` is a
  noetherian ring"), a *field of characteristic zero* where the paper says so; an *algebraic `B`-prescheme* is a scheme
  with a morphism of finite type (locally of finite type and quasi-compact) to `Spec B`, an *algebraic `B`-scheme* one
  which is moreover separated (pp. 118-119).
* A rational application is Mathlib's `Scheme.RationalMap`.  The composition of rational applications of p. 139 is
  stated as a relation (`Scheme.RationalMap.IsComposite`), since the project had only the composition with a morphism.
* The class `𝔐(X)` is the type `ModificationClass pX` of data `(X′, p′, f)` with `X′` in the universe of `X`
  (so a type in the next universe: the "class" of the paper); a point `(X′, f) ∈ 𝔐(X)` such as `(X, id_X)` or
  `(X_{ij}, f_{ij})` is recognised up to isomorphism of `X′` (`ZariskiSpaceData.IsCanonicalFor`).
* The Zariski space is a locally ringed space with the family `h`; "unique up to isomorphism" is the universal
  property (ii), quantified over the structures in the same universe.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

/-! ### Modifications (p. 146) -/

namespace AlgebraicGeometry.Scheme

variable {X' X Y Z : Scheme.{u}}

/-- The data witnessing that a rational application `f : X' ⤏ X` is a modification: a representative `g`, open dense
subsets `U ⊆ g.domain` of `X'` and `V` of `X`, and an isomorphism `U ≅ V` through which `g` restricted to `U` factors.

> We say that `f` is a *modification* if `f` induces an isomorphism of the restrictions of `X′` and `X` to open dense
> subsets of their underlying topological spaces.  (p. 146)

Formalization note (encoding): "`f` induces an isomorphism of the restrictions `X'|U → X|V`" is: some representative `g`
of `f` restricted to `U` is the composite of an isomorphism `U ≅ V` and the inclusion of `V`.  The witness is data so that
the inverse `f⁻¹` of p. 146 can be written down (`ModificationData.inverse`). -/
@[blueprint "def:0.6-modification-data"
  (statement := /-- A \emph{modification datum} from $X'$ to $X$ consists of a partial map $g\colon X'|W\to X$ ($W$ open
    dense), open dense subsets $U\subseteq W$ of $X'$ and $V$ of $X$, and an isomorphism $e\colon X'|U\to X|V$ such that
    $g|_U$ is $e$ followed by the inclusion of $V$. It records that the rational application of $g$ ``induces an
    isomorphism of the restrictions of $X'$ and $X$ to open dense subsets'' (p.~146). Formalization note (encoding).
    -/)
  (latexEnv := "definition")]
structure ModificationData (X' X : Scheme.{u}) where
  /-- A representative of the rational application. -/
  g : X'.PartialMap X
  /-- The open dense subset of the source. -/
  U : X'.Opens
  dense_U : Dense (U : Set X')
  le : U ≤ g.domain
  /-- The open dense subset of the target. -/
  V : X.Opens
  dense_V : Dense (V : Set X)
  /-- The isomorphism of the restrictions. -/
  e : U.toScheme ≅ V.toScheme
  comm : X'.homOfLE le ≫ g.hom = e.hom ≫ V.ι

/-- The inverse rational application of a modification datum: the class of the partial map `V ≅ U ⊆ X'` (p. 146: the
rational applications `f_i⁻¹ ∘ f₃`). -/
noncomputable def ModificationData.inverse (w : ModificationData X' X) : X ⤏ X' :=
  (PartialMap.mk w.V w.dense_V (w.e.inv ≫ w.U.ι)).toRationalMap

namespace RationalMap

/-- `f` is a *modification* (p. 146).

> We say that `f` is a *modification* if `f` induces an isomorphism of the restrictions of `X′` and `X` to open dense
> subsets of their underlying topological spaces.  (p. 146)

Formalization note (encoding): `ModificationData`.  The reducedness of `X'` and `X` of the paper's hypothesis is carried
by the places where the definition is used (`ModificationClass`). -/
@[blueprint "def:0.6-modification"
  (statement := /-- A rational application $f\colon X'\dashrightarrow X$ of reduced algebraic $\mathbf B$-schemes is a
    \emph{modification} if $f$ induces an isomorphism of the restrictions of $X'$ and $X$ to open dense subsets of their
    underlying topological spaces. (p.~146.) Formalization note (encoding): some modification datum represents $f$. -/)
  (latexEnv := "definition")]
def IsModification (f : X' ⤏ X) : Prop := ∃ w : ModificationData X' X, w.g.toRationalMap = f

/-- `f'` is the *inverse* `f⁻¹` of the modification `f` (notation of p. 146: "`f_i⁻¹ ∘ f₃`").

Formalization note (encoding): the paper uses `f⁻¹` without defining it; it is the class of the inverse isomorphism
`V ≅ U` between the open dense subsets on which `f` is an isomorphism.  For reduced `X'` and separated `X` it does not
depend on the choice of the modification datum; this independence is not proved here, and the relation is "some
datum representing `f` has inverse `f'`". -/
@[blueprint "def:0.6-modification-inverse"
  (statement := /-- For a modification $f\colon X'\dashrightarrow X$, the rational application $f^{-1}\colon
    X\dashrightarrow X'$ is the class of the inverse of the isomorphism of restrictions $X'|U\to X|V$ followed by the
    inclusion $X'|U\subseteq X'$ (notation of p.~146). Formalization note (encoding): a relation, defined through the
    modification datum. -/)
  (latexEnv := "definition")]
def IsInverseOf (f' : X ⤏ X') (f : X' ⤏ X) : Prop :=
  ∃ w : ModificationData X' X, w.g.toRationalMap = f ∧ w.inverse = f'

/-- A modification is *proper* if it is so as a rational application (p. 146), over the base `S`.

> A modification is said to be *proper* if it is so as a rational application.  (p. 146)

Formalization note (encoding): "proper as a rational application" is `IsProperApplication` (p. 139) for the structure
morphisms `pX'` of `X'` and `pX` of `X`. -/
@[blueprint "def:0.6-proper-modification"
  (statement := /-- A modification is \emph{proper} if it is so as a rational application (p.~146), i.e.\ in the sense of
    \cref{def:0.5-proper-application}. -/)
  (latexEnv := "definition")]
def IsProperModification {S : Scheme.{u}} (pX' : X' ⟶ S) (pX : X ⟶ S) (f : X' ⤏ X) : Prop :=
  f.IsModification ∧ f.IsProperApplication pX' pX

end RationalMap

/-! ### Composition of rational applications (p. 139) -/

/-- The composite `g ∘ f` of a partial map `f : X ⤏ Y` whose underlying morphism has dense preimages with a partial map
`g : Y ⤏ Z`: the domain is the image in `X` of `f⁻¹(g.domain)` (an open dense subset of `X`).  This is the construction of
Mathlib's `PartialMap.comp` for a source which need not be irreducible and the paper's hypothesis on `f` (p. 139: "`f⁻¹(V)`
is open and dense for every open dense subset `V`"). -/
@[blueprint "def:0.6-partial-composition"
  (statement := /-- Let $f\colon X|U\to Y$ be a morphism such that $f^{-1}(V)$ is open and dense for every open dense $V\subseteq
    Y$, and $g\colon Y|V_0\to Z$. The composite is the morphism $X|f^{-1}(V_0)\to Z$, on the open dense subset $f^{-1}(V_0)$.
    (Composition of morphisms, p.~139.) -/)
  (latexEnv := "definition")]
noncomputable def PartialMap.compOfPreimageDense (f : X.PartialMap Y) (hf : f.hom.PreimageDense) (g : Y.PartialMap Z) :
    X.PartialMap Z where
  domain := f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain
  dense_domain := by
    have h1 : Dense ((f.hom ⁻¹ᵁ g.domain : f.domain.toScheme.Opens) : Set f.domain.toScheme) :=
      hf _ g.dense_domain
    have h2 : DenseRange f.domain.ι := by
      rw [DenseRange, Scheme.Opens.range_ι]; exact f.dense_domain
    simpa using h2.dense_image f.domain.ι.continuous h1
  hom := (f.domain.ι.isoImage _).inv ≫ f.hom ∣_ g.domain ≫ g.hom

/-- `h` is the *composition* `g ∘ f` of the rational applications `f : X ⤏ Y` and `g : Y ⤏ Z` (p. 139).

> If `f` (resp. `g`) is a rational application of `X` to `Y` (resp. `Y` to `Z`), and if `f` contains a morphism
> `f : X | U → Y` such that `f⁻¹(V)` is open and dense for every open dense subset `V` of the underlying topological
> space of `Y`, then we get a unique rational application of `X` to `Z` as the class of composed morphisms of those in
> `f` and those in `g`.  This rational application of `X` to `Z` will be called the composition of `f` and `g`, or the composed application of them.  (p. 139)

Formalization note (encoding): a relation: `f` contains a representative with dense preimages, and the composite of every
such representative with every representative of `g` is a representative of `h`.  That the class is independent of the
choices ("a unique rational application") is part of the paper's sentence and is not proved here. -/
@[blueprint "def:0.6-composition"
  (statement := /-- The rational application $h\colon X\dashrightarrow Z$ is the \emph{composition} of $f\colon
    X\dashrightarrow Y$ and $g\colon Y\dashrightarrow Z$ if $f$ contains a morphism $X|U\to Y$ such that $f^{-1}(V)$ is
    open and dense for every open dense $V\subseteq Y$, and $h$ is the class of the composed morphisms of those in $f$
    (with this property) and those in $g$. (p.~139.) Formalization note (encoding): a relation; the independence of the
    choices is part of the paper's sentence and is not proved here. -/)
  (latexEnv := "definition")]
def RationalMap.IsComposite (f : X ⤏ Y) (g : Y ⤏ Z) (h : X ⤏ Z) : Prop :=
  (∃ f₀ : X.PartialMap Y, f₀.toRationalMap = f ∧ f₀.hom.PreimageDense) ∧
  ∀ (f₀ : X.PartialMap Y) (hf₀ : f₀.hom.PreimageDense) (g₀ : Y.PartialMap Z),
    f₀.toRationalMap = f → g₀.toRationalMap = g → (f₀.compOfPreimageDense hf₀ g₀).toRationalMap = h

end AlgebraicGeometry.Scheme

/-! ### Algebraic `B`-schemes and the class `𝔐(X)` (p. 146) -/

namespace Hironaka

variable {B : Type u} [CommRing B]

/- An algebraic `B`-prescheme and an algebraic `B`-scheme (pp. 118–119) are `IsAlgebraicPreschemeOver` and
`IsAlgebraicSchemeOver` of `Hironaka/Ch0/Generalities.lean` (with `B` noetherian, as on p. 118). -/

/-- A *reduced algebraic `B`-scheme* (p. 146): an algebraic `B`-scheme whose underlying scheme is reduced. -/
@[blueprint "def:0.6-reduced-algebraic-b-scheme"
  (statement := /-- A reduced algebraic $\mathbf B$-scheme is an algebraic $\mathbf B$-scheme $X$ which is a reduced scheme
    (p.~146). -/)
  (latexEnv := "definition")]
def IsReducedAlgebraicBScheme {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B)) : Prop :=
  IsAlgebraicSchemeOver p ∧ AlgebraicGeometry.IsReduced X

/-- The class `𝔐(X)` of pairs `(X′, f)` of a reduced algebraic `B`-scheme `X′` and a proper modification `f` of `X′` to `X`
(p. 146).

> For a fixed reduced algebraic `B`-scheme (resp. a reduced analytic `K`-space) `X`, we consider the class `𝔐(X)` of all
> pairs `(X′, f)` of reduced algebraic `B`-schemes (resp. reduced analytic `K`-spaces) `X` and proper modifications `f` of
> `X′` to `X`.  (p. 146)

The printed "schemes `X` and proper modifications" has `X` where `X′` is meant (misprint: the letter is unprimed in the printed text); read as `X′`.

Formalization note (encoding): the structure morphism `p` of `X′` is part of the datum; `X′` ranges over all schemes in
the universe of `X`, so the "class" is a type in the next universe.  The rational application `f` is over `B` by
`IsProperApplication` (p. 139), which uses the structure morphisms.  The class does not itself require `X` to be a reduced
algebraic `B`-scheme; the statements that use it assume this. -/
@[blueprint "def:0.6-class-modifications"
  (statement := /-- For a fixed reduced algebraic $\mathbf B$-scheme $X$, $\mathfrak M(X)$ is the class of all pairs $(X',f)$
    of reduced algebraic $\mathbf B$-schemes $X'$ and proper modifications $f$ of $X'$ to $X$. (p.~146; the printed text has
    $X$ for $X'$, a misprint.) Formalization note (encoding): $X'$ ranges over the schemes of one universe; the structure
    morphism of $X'$ is part of the datum. -/)
  (latexEnv := "definition")]
structure ModificationClass {X : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of B)) where
  /-- The scheme `X′`. -/
  X' : Scheme.{u}
  /-- The structure morphism of `X′`. -/
  p : X' ⟶ Spec (CommRingCat.of B)
  /-- The proper modification `f` of `X′` to `X`. -/
  f : X' ⤏ X
  isReducedAlgebraicBScheme : IsReducedAlgebraicBScheme p
  isProperModification : f.IsProperModification p pX

namespace ModificationClass

variable {X : Scheme.{u}} {pX : X ⟶ Spec (CommRingCat.of B)}

/-- `h` is the rational application `f₁⁻¹ ∘ f₃ : X₃ ⤏ X₁` for `(X₁, f₁), (X₃, f₃) ∈ 𝔐(X)` (p. 146): the composition of
`f₃` and the inverse `f₁⁻¹` of the modification `f₁`.

> there exists `(X₃, f₃) ∈ 𝔐(X)` such that the rational applications `f_i⁻¹ ∘ f₃` (`i = 1, 2`) are both *morphisms*.
> (p. 146)

Formalization note (encoding): `Scheme.RationalMap.IsInverseOf`, `Scheme.RationalMap.IsComposite`. -/
@[blueprint "def:0.6-inverse-composite"
  (statement := /-- For $(X_1,f_1),(X_3,f_3)\in\mathfrak M(X)$, $h\colon X_3\dashrightarrow X_1$ is the rational
    application $f_1^{-1}\circ f_3$: the composition of $f_3$ with the inverse of the modification $f_1$ (p.~146). -/)
  (latexEnv := "definition")]
def IsInvComp (m₁ m₃ : ModificationClass pX) (h : m₃.X' ⤏ m₁.X') : Prop :=
  ∃ f' : X ⤏ m₁.X', Scheme.RationalMap.IsInverseOf f' m₁.f ∧ Scheme.RationalMap.IsComposite m₃.f f' h

/-- "The rational application `f₁⁻¹ ∘ f₃` is a morphism" (p. 146), in the sense of p. 139 (`IsMorphism`). -/
@[blueprint "def:0.6-inverse-composite-morphism"
  (statement := /-- For $(X_1,f_1),(X_3,f_3)\in\mathfrak M(X)$: the rational application $f_1^{-1}\circ f_3$ is a morphism
    (in the sense of p.~139). (p.~146.) -/)
  (latexEnv := "definition")]
def InvCompIsMorphism (m₁ m₃ : ModificationClass pX) : Prop :=
  ∃ h : m₃.X' ⤏ m₁.X', m₁.IsInvComp m₃ h ∧ h.IsMorphism

end ModificationClass

/-- **Common refinement in `𝔐(X)`** (p. 146): for `(X₁, f₁), (X₂, f₂) ∈ 𝔐(X)` there is `(X₃, f₃) ∈ 𝔐(X)` such that the
rational applications `f_i⁻¹ ∘ f₃` (`i = 1, 2`) are both morphisms.

> For `(X₁, f₁) ∈ 𝔐(X)` and `(X₂, f₂) ∈ 𝔐(X)`, there exists `(X₃, f₃) ∈ 𝔐(X)` such that the rational applications
> `f_i⁻¹ ∘ f₃` (`i = 1, 2`) are both *morphisms*.  (p. 146)

Stated without proof or citation (p. 146); not proved here.  The base ring `B` is a noetherian ring (p. 118); the paper
does not restrict `B` in this section (the field of characteristic zero appears only in the local uniformization
theorem). -/
@[blueprint "thm:0.6-common-modification"
  (statement := /-- Let $X$ be a reduced algebraic $\mathbf B$-scheme. For $(X_1,f_1)\in\mathfrak M(X)$ and
    $(X_2,f_2)\in\mathfrak M(X)$, there exists $(X_3,f_3)\in\mathfrak M(X)$ such that the rational applications
    $f_i^{-1}\circ f_3$ ($i=1,2$) are both morphisms. (p.~146.) Not proved here: stated without proof. -/)
  (latexEnv := "theorem")]
def ExistsCommonModification : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (X : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of B)),
    IsReducedAlgebraicBScheme pX → ∀ m₁ m₂ : ModificationClass pX,
      ∃ m₃ : ModificationClass pX, m₁.InvCompIsMorphism m₃ ∧ m₂.InvCompIsMorphism m₃

/-! ### The Zariski space (pp. 146-147) -/

/-- A locally ringed space `ℨ(X)` with morphisms `h(X′, f) : ℨ(X) → X′` for `(X′, f) ∈ 𝔐(X)` having the property (i) of
p. 146.

> there exists a local-ringed space `ℨ(X)` with morphisms `h(X′, f) : ℨ(X) → X′` for `(X′, f) ∈ 𝔐(X)`, which has the
> following properties: (i) If `(X_i, f_i) ∈ 𝔐(X)`, for `i = 1, 2`, such that `f₁⁻¹ ∘ f₂` is a morphism,
> `h(X₁, f₁) = (f₁⁻¹ ∘ f₂) ∘ h(X₂, f₂)`, and … (p. 146)

Formalization note (encoding): `h_comp` is (i), for the morphism `φ` of schemes (`X₂ ⟶ X₁`) whose class is `f₁⁻¹ ∘ f₂`
(`toRationalMap`); the composite of the morphisms of locally ringed spaces is the equality of (i). -/
@[blueprint "def:0.6-zariski-space-data"
  (statement := /-- A locally ringed space $\mathfrak Z$ with morphisms $h(X',f)\colon\mathfrak Z\to X'$ for $(X',f)\in
    \mathfrak M(X)$ such that: if $(X_i,f_i)\in\mathfrak M(X)$, $i=1,2$, are such that $f_1^{-1}\circ f_2$ is a morphism,
    then $h(X_1,f_1)=(f_1^{-1}\circ f_2)\circ h(X_2,f_2)$. (Property (i), p.~146.) Formalization note (encoding): the
    index $(X',f)$ ranges over the type of \cref{def:0.6-class-modifications}. -/)
  (latexEnv := "definition")]
structure ZariskiSpaceData {X : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of B)) where
  /-- The locally ringed space. -/
  Z : LocallyRingedSpace.{u}
  /-- The morphisms `h(X′, f)`. -/
  h : ∀ m : ModificationClass pX, Z ⟶ m.X'.toLocallyRingedSpace
  /-- The property (i). -/
  h_comp : ∀ (m₁ m₂ : ModificationClass pX) (φ : m₂.X' ⟶ m₁.X'),
    m₁.IsInvComp m₂ φ.toRationalMap → h m₁ = h m₂ ≫ φ.toLRSHom

/-- The property (ii) of p. 147: the data `(ℨ(X), h)` is terminal among the data with property (i).

> (ii) if another `ℨ(X)′` with `h(X′, f)′ : ℨ(X) → X′` for `(X′, f) ∈ 𝔐(X)` has the property (i), then there exists a
> unique morphism `g : ℨ(X)′ → ℨ(X)` such that `h(X′, f)′ = h(X′, f) ∘ g` for all `(X′, f) ∈ 𝔐(X)`.  (pp. 146-147)

(The printed "`h(X′, f)′ : ℨ(X) → X′`" has `ℨ(X)` where `ℨ(X)′` is meant; read as `ℨ(X)′ → X′`.  This is the
only reading under which the next line `g : ℨ(X)′ → ℨ(X)` composes.  Misprint: the printed text has the unprimed `ℨ(X)`.)

Formalization note (encoding): "another" is any datum `ZariskiSpaceData pX` in the same universe. -/
@[blueprint "def:0.6-zariski-universal"
  (statement := /-- A datum $(\mathfrak Z,h)$ as in \cref{def:0.6-zariski-space-data} has the property (ii) if for every
    other such datum $(\mathfrak Z',h')$ there is a unique morphism $g\colon\mathfrak Z'\to\mathfrak Z$ with
    $h'(X',f)=h(X',f)\circ g$ for all $(X',f)\in\mathfrak M(X)$. (p.~147.) -/)
  (latexEnv := "definition")]
def ZariskiSpaceData.IsUniversal {X : Scheme.{u}} {pX : X ⟶ Spec (CommRingCat.of B)} (Z : ZariskiSpaceData pX) :
    Prop :=
  ∀ Z' : ZariskiSpaceData pX, ∃! g : Z'.Z ⟶ Z.Z, ∀ m, Z'.h m = g ≫ Z.h m

/-- `k` is the canonical morphism `h(W, f)` for the pair `(W, f)`, `f : W ⤏ X` a rational application and `pW` the
structure morphism of `W` (p. 147: "`h(X)` for `h(X, id_X)`").

Formalization note (encoding): the pair `(W, f)` is recognised in `𝔐(X)` up to isomorphism: some element `m` of the class
has an isomorphism `e : m.X' ≅ W` over `B` with `m.f = f ∘ e`, and `k = h(m) ∘ e`.  For `W = X`, `f = id` this is the
morphism `h(X) = h(X, id_X)`; for a morphism `c : W ⟶ X` it is `f = c.toRationalMap`. -/
@[blueprint "def:0.6-canonical-morphism"
  (statement := /-- The \emph{canonical morphism} of $\mathfrak Z(X)$ to $(X',f)\in\mathfrak M(X)$ is $h(X',f)$; we write
    $h(X)=h(X,\mathrm{id}_X)$. (p.~147.) Formalization note (encoding): the pair is recognised up to isomorphism of
    $X'$. -/)
  (latexEnv := "definition")]
def ZariskiSpaceData.IsCanonicalFor {X : Scheme.{u}} {pX : X ⟶ Spec (CommRingCat.of B)} (Z : ZariskiSpaceData pX)
    {W : Scheme.{u}} (pW : W ⟶ Spec (CommRingCat.of B)) (f : W ⤏ X) (k : Z.Z ⟶ W.toLocallyRingedSpace) : Prop :=
  ∃ (m : ModificationClass pX) (e : m.X' ≅ W), m.p = e.hom ≫ pW ∧
    m.f = f.precomp e.hom (Scheme.Hom.PreimageDense.of_isOpenImmersion _) ∧ k = Z.h m ≫ e.hom.toLRSHom

/-- `k : Z' → W` is the canonical morphism `h(W, f)` when the Zariski space `Z.Z` is identified with `Z'` by `ι`
(p. 148: "`ℨ = ℨ(X₁) = ℨ(X₂)`, the Zariski spaces canonically identified"). -/
@[blueprint "def:0.6-canonical-via"
  (statement := /-- If the Zariski space $\mathfrak Z(X)$ is identified with a locally ringed space $\mathfrak Z$ by an
    isomorphism $\iota$, the canonical morphism $\mathfrak Z\to X'$ is the composite of $\iota$ with $h(X',f)$.
    (p.~148.) -/)
  (latexEnv := "definition")]
def ZariskiSpaceData.IsCanonicalVia {X : Scheme.{u}} {pX : X ⟶ Spec (CommRingCat.of B)} (Z : ZariskiSpaceData pX)
    {Z' : LocallyRingedSpace.{u}} (ι : Z' ≅ Z.Z)
    {W : Scheme.{u}} (pW : W ⟶ Spec (CommRingCat.of B)) (f : W ⤏ X) (k : Z' ⟶ W.toLocallyRingedSpace) : Prop :=
  Z.IsCanonicalFor pW f (ι.inv ≫ k)

end Hironaka

namespace AlgebraicGeometry.Scheme.RationalMap

variable {X' X : Scheme.{u}}

/-- "`k₀ = f ∘ k` on an open dense subset of `ℨ`" (p. 147): for a rational application `f : X' ⤏ X` and morphisms
`k : ℨ → X'`, `k₀ : ℨ → X` of locally ringed spaces, there are a representative `g` of `f`, an open dense subset `W` of `ℨ`
and a lift `l` of `k|_W` through the domain of `g` such that `g ∘ l = k₀|_W`.

> This morphism `h(X)` of `ℨ(X)` to `X` determines all the other morphisms `h(X′, f)` by the equality
> `h(X) = f ∘ h(X′, f)`, which makes sense in an open dense subset of `ℨ(X)`.  (p. 147)

Formalization note (encoding): the composition of the rational application `f` with the morphism `k` of locally ringed
spaces is not defined in the paper's generality; "makes sense and holds on an open dense subset" is the existence of the
lift `l` of `k|_W` through `g.domain` with `l ≫ g = k₀|_W` (`Z.restrict`, `Z.ofRestrict`). -/
@[blueprint "def:0.6-comp-agrees"
  (statement := /-- For a rational application $f\colon X'\dashrightarrow X$ and morphisms $k\colon\mathfrak Z\to X'$,
    $k_0\colon\mathfrak Z\to X$ of locally ringed spaces, \emph{$k_0=f\circ k$ on an open dense subset of $\mathfrak Z$}
    means: for some representative $g\colon X'|U\to X$ of $f$ and some open dense $W\subseteq\mathfrak Z$, $k|_W$ factors
    through $X'|U$ and $g$ composed with the factorization is $k_0|_W$. (p.~147.) Formalization note (encoding). -/)
  (latexEnv := "definition")]
def CompAgrees (f : X' ⤏ X) {Z : LocallyRingedSpace.{u}} (k : Z ⟶ X'.toLocallyRingedSpace)
    (k₀ : Z ⟶ X.toLocallyRingedSpace) : Prop :=
  ∃ (g : X'.PartialMap X) (W : TopologicalSpace.Opens Z) (_ : Dense (W : Set Z))
    (l : Z.restrict W.isOpenEmbedding ⟶ g.domain.toScheme.toLocallyRingedSpace),
    g.toRationalMap = f ∧ l ≫ g.domain.ι.toLRSHom = Z.ofRestrict W.isOpenEmbedding ≫ k ∧
      l ≫ g.hom.toLRSHom = Z.ofRestrict W.isOpenEmbedding ≫ k₀

end AlgebraicGeometry.Scheme.RationalMap

namespace Hironaka

variable {B : Type u} [CommRing B]

/-- **Existence of the Zariski space** (p. 146): for a reduced algebraic `B`-scheme `X` there is a locally ringed space with
morphisms `h(X′, f)` having the properties (i) and (ii).

> We can prove that there exists a local-ringed space `ℨ(X)` with morphisms `h(X′, f) : ℨ(X) → X′` for `(X′, f) ∈ 𝔐(X)`,
> which has the following properties: … (p. 146)

Deferred by the paper (fn. 2, p. 114: Ch. 0 "most of the results are stated only with sketchy proofs"); not proved here.
Formalization note (encoding): the locally ringed spaces are in the universe of `X`; the Zariski space is a projective
limit of the schemes `X′` and in the paper's set-up lies in the same universe. -/
@[blueprint "thm:0.6-zariski-existence"
  (statement := /-- Let $X$ be a reduced algebraic $\mathbf B$-scheme. There exists a locally ringed space
    $\mathfrak Z(X)$ with morphisms $h(X',f)\colon\mathfrak Z(X)\to X'$ for $(X',f)\in\mathfrak M(X)$ with the properties
    (i) and (ii) (p.~146--147). Not proved here: deferred by the paper (fn.~2, p.~114). -/)
  (latexEnv := "theorem")]
def ExistsZariskiSpace : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (X : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of B)),
    IsReducedAlgebraicBScheme pX → ∃ Z : ZariskiSpaceData pX, Z.IsUniversal

/-- **Uniqueness of the Zariski space** (p. 147): `ℨ(X)` with the `h(X′, f)` is unique up to an isomorphism of `ℨ(X)`.

> We see that `ℨ(X)` with `h(X′, f)` is unique up to an isomorphism of `ℨ(X)`.  (p. 147)

Stated without proof (p. 147); not proved here.  Formalization note (encoding): two data with (i) and (ii) are related by
an isomorphism compatible with all `h(X′, f)`; the uniqueness of that isomorphism is not asserted by the sentence (it
follows from (ii)). -/
@[blueprint "thm:0.6-zariski-unique"
  (statement := /-- The Zariski space $\mathfrak Z(X)$ with the morphisms $h(X',f)$ is unique up to an isomorphism of
    $\mathfrak Z(X)$ (p.~147): two data with (i) and (ii) are related by an isomorphism compatible with all $h(X',f)$.
    Not proved here: stated without proof. -/)
  (latexEnv := "theorem")]
def ZariskiSpaceUnique : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (X : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of B)),
    IsReducedAlgebraicBScheme pX → ∀ Z Z' : ZariskiSpaceData pX, Z.IsUniversal → Z'.IsUniversal →
      ∃ e : Z.Z ≅ Z'.Z, ∀ m, Z.h m = e.hom ≫ Z'.h m

/-- **`h(X)` determines the other canonical morphisms** (p. 147): `h(X′, f)` is the unique morphism `k : ℨ(X) → X′` with
`h(X) = f ∘ k` on an open dense subset of `ℨ(X)`.

> This morphism `h(X)` of `ℨ(X)` to `X` determines all the other morphisms `h(X′, f)` by the equality
> `h(X) = f ∘ h(X′, f)`, which makes sense in an open dense subset of `ℨ(X)`.  (p. 147)

Stated without proof (p. 147); not proved here.  Reading (an encoding): "determines" is that `h(X′, f)` is the
only morphism `k` satisfying the equality on an open dense subset, and that it does satisfy it (`CompAgrees`). -/
@[blueprint "thm:0.6-zariski-h-determines"
  (statement := /-- The morphism $h(X)\colon\mathfrak Z(X)\to X$ determines all the other morphisms $h(X',f)$ by the
    equality $h(X)=f\circ h(X',f)$, which makes sense in an open dense subset of $\mathfrak Z(X)$ (p.~147): $h(X',f)$ is
    the unique morphism $k$ with $h(X)=f\circ k$ on an open dense subset. Not proved here: stated without proof.
    Formalization note (encoding): the reading of ``determines''. -/)
  (latexEnv := "theorem")]
def ZariskiHDeterminesOthers : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (X : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of B)),
    IsReducedAlgebraicBScheme pX → ∀ Z : ZariskiSpaceData pX, Z.IsUniversal →
      ∀ (m : ModificationClass pX) (k : Z.Z ⟶ m.X'.toLocallyRingedSpace) (k₀ : Z.Z ⟶ X.toLocallyRingedSpace),
        Z.IsCanonicalFor pX (Scheme.RationalMap.id X) k₀ → (m.f.CompAgrees k k₀ ↔ k = Z.h m)

/-- **Functoriality of the Zariski space** (p. 147): a morphism `g : Y → X` of reduced algebraic `B`-schemes has a unique
`ℨ(g) : ℨ(Y) → ℨ(X)` with `h(X) ∘ ℨ(g) = g ∘ h(Y)`.

> If `g : Y → X` is a morphism of reduced algebraic `B`-schemes (resp. reduced analytic `K`-spaces), then we have a unique
> morphism `ℨ(g) : ℨ(Y) → ℨ(X)` such that `h(X) ∘ ℨ(g) = g ∘ h(Y)`.  (p. 147)

Stated without proof (p. 147); not proved here.  **Statement as printed (false in general).**  (1) For `g : Spec k → 𝔸²_k`
the origin (not dominant), `ℨ(Spec k) = Spec k`, and the points of `ℨ(𝔸²_k)` given by the monomial valuations of weights
`(1, √2)` and `(1, √3)` are centered at the origin with residue field `k`; they give two different morphisms `t` with
`h(X) ∘ t = g ∘ h(Y)`, so "unique" fails (existence holds).  (2) The same happens for a dominant `g` on a reducible `Y`: for
`X = 𝔸²_k`, `Y = 𝔸²_k ⊔ Spec k` and `g` the identity on the first summand and the origin on the point, `g` is dominant and
`ℨ(Y) = ℨ(𝔸²_k) ⊔ Spec k`, and the two valuations give two lifts on the `Spec k` summand.  The corrected form is
`ZariskiFunctorialDominant`.  Formalization note (encoding): "morphism of `B`-schemes" is a morphism over `B` (`g ≫ pX = pY`); `ℨ(Y)`, `ℨ(X)` are any data with (i) and (ii). -/
@[blueprint "thm:0.6-zariski-functorial"
  (statement := /-- If $g\colon Y\to X$ is a morphism of reduced algebraic $\mathbf B$-schemes, there is a unique morphism
    $\mathfrak Z(g)\colon\mathfrak Z(Y)\to\mathfrak Z(X)$ such that $h(X)\circ\mathfrak Z(g)=g\circ h(Y)$. (p.~147.) Not
    proved here: stated without proof. \textbf{Statement as printed (false in general):} for $g\colon\operatorname{Spec}k\to\mathbb A^2_k$ the
    origin, $\mathfrak Z(\operatorname{Spec}k)=\operatorname{Spec}k$ and the monomial valuations of weights $(1,\sqrt2)$ and $(1,\sqrt3)$ give two
    different morphisms $t$ with $h(X)\circ t=g\circ h(Y)$; the same holds for the dominant $g\colon\mathbb A^2_k\sqcup
    \operatorname{Spec}k\to\mathbb A^2_k$ (identity on the first summand, the origin on the point). -/)
  (latexEnv := "theorem")]
def ZariskiFunctorial : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (X Y : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of B))
    (pY : Y ⟶ Spec (CommRingCat.of B)), IsReducedAlgebraicBScheme pX → IsReducedAlgebraicBScheme pY →
      ∀ (g : Y ⟶ X), g ≫ pX = pY → ∀ (ZY : ZariskiSpaceData pY) (ZX : ZariskiSpaceData pX),
        ZY.IsUniversal → ZX.IsUniversal →
          ∃! t : ZY.Z ⟶ ZX.Z, ∀ (hY : ZY.Z ⟶ Y.toLocallyRingedSpace) (hX : ZX.Z ⟶ X.toLocallyRingedSpace),
            ZY.IsCanonicalFor pY (Scheme.RationalMap.id Y) hY → ZX.IsCanonicalFor pX (Scheme.RationalMap.id X) hX →
              t ≫ hX = hY ≫ g.toLRSHom

/-- **Corrected form of `ZariskiFunctorial`, for a morphism sending the generic points of the components to generic points**
(p. 147): a morphism `g : Y → X` of reduced algebraic `B`-schemes such that every irreducible component of `Y` is mapped
dominantly onto an irreducible component of `X` has a unique `ℨ(g) : ℨ(Y) → ℨ(X)` with `h(X) ∘ ℨ(g) = g ∘ h(Y)`.

Corrected form of `ZariskiFunctorial` (false in general: the counterexamples there, for a non-dominant `g` and for a dominant `g`
on a reducible `Y`).  Stated, not proved: the classical argument (restriction of valuations along `k(X_j) ⊆ k(Y_i)`) gives it for
integral `X`, `Y` and dominant `g`, and componentwise in general; not checked in detail here.  Formalization note (deviation: a
hypothesis is added to the printed statement): "every irreducible component of `Y` is mapped dominantly onto an irreducible
component of `X`" is encoded as "`g` maps every generic point of an irreducible component of `Y` to a generic point of an
irreducible component of `X`", where a point is the generic point of an irreducible component when it has no proper generization
(`∀ y', y' ⤳ y → y' = y`); for schemes with finitely many irreducible components this is the same condition. -/
@[blueprint "thm:0.6-zariski-functorial-dominant"
  (statement := /-- Let $g\colon Y\to X$ be a morphism of reduced algebraic $\mathbf B$-schemes such that every irreducible
    component of $Y$ is mapped dominantly onto an irreducible component of $X$ (equivalently, $g$ maps the generic point of
    each irreducible component of $Y$ to the generic point of an irreducible component of $X$). Then there is a unique
    morphism $\mathfrak Z(g)\colon\mathfrak Z(Y)\to\mathfrak Z(X)$ such that $h(X)\circ\mathfrak Z(g)=g\circ h(Y)$.
    (Corrected form of \cref{thm:0.6-zariski-functorial}, p.~147, which is false in general: the counterexamples there, for a
    non-dominant $g$ and for a dominant $g$ on a reducible $Y$.) Not proved here: stated, not proved; the classical argument
    (restriction of valuations along $k(X_j)\subseteq k(Y_i)$) gives it for integral $X,Y$ and dominant $g$, and
    componentwise in general; not checked in detail here. -/)
  (latexEnv := "theorem")]
def ZariskiFunctorialDominant : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (X Y : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of B))
    (pY : Y ⟶ Spec (CommRingCat.of B)), IsReducedAlgebraicBScheme pX → IsReducedAlgebraicBScheme pY →
      ∀ g : Y ⟶ X, (∀ y : Y, (∀ y', y' ⤳ y → y' = y) → ∀ x', x' ⤳ g y → x' = g y) →
      g ≫ pX = pY → ∀ (ZY : ZariskiSpaceData pY) (ZX : ZariskiSpaceData pX),
        ZY.IsUniversal → ZX.IsUniversal →
          ∃! t : ZY.Z ⟶ ZX.Z, ∀ (hY : ZY.Z ⟶ Y.toLocallyRingedSpace) (hX : ZX.Z ⟶ X.toLocallyRingedSpace),
            ZY.IsCanonicalFor pY (Scheme.RationalMap.id Y) hY → ZX.IsCanonicalFor pX (Scheme.RationalMap.id X) hX →
              t ≫ hX = hY ≫ g.toLRSHom

/-- **`ℨ(g)` is an isomorphism for a proper modification `g`** (p. 147).

> If `g` is a proper modification, then `ℨ(g)` is an isomorphism of local-ringed spaces.  (p. 147)

Stated without proof (p. 147); not proved here.  Encoding: `g` is a morphism `Y ⟶ X` of reduced algebraic `B`-schemes over
`B` whose class is a proper modification; any morphism `t` with `h(X) ∘ t = g ∘ h(Y)` (the morphism `ℨ(g)` of
`ZariskiFunctorial`) is an isomorphism. -/
@[blueprint "thm:0.6-zariski-proper-modification-iso"
  (statement := /-- If $g\colon Y\to X$ is a morphism of reduced algebraic $\mathbf B$-schemes which is a proper
    modification, then $\mathfrak Z(g)$ is an isomorphism of locally ringed spaces. (p.~147.) Not proved here: stated
    without proof. -/)
  (latexEnv := "theorem")]
def ZariskiProperModificationIso : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (X Y : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of B))
    (pY : Y ⟶ Spec (CommRingCat.of B)), IsReducedAlgebraicBScheme pX → IsReducedAlgebraicBScheme pY →
      ∀ (g : Y ⟶ X), g ≫ pX = pY → g.toRationalMap.IsProperModification pY pX →
        ∀ (ZY : ZariskiSpaceData pY) (ZX : ZariskiSpaceData pX), ZY.IsUniversal → ZX.IsUniversal →
          ∀ t : ZY.Z ⟶ ZX.Z,
            (∀ (hY : ZY.Z ⟶ Y.toLocallyRingedSpace) (hX : ZX.Z ⟶ X.toLocallyRingedSpace),
              ZY.IsCanonicalFor pY (Scheme.RationalMap.id Y) hY → ZX.IsCanonicalFor pX (Scheme.RationalMap.id X) hX →
                t ≫ hX = hY ≫ g.toLRSHom) → IsIso t

/-- **The canonical isomorphism `ℨ(g)` for an arbitrary proper modification** (p. 147): for `(Y, g) ∈ 𝔐(X)` (a proper
modification, not necessarily a morphism) there is a unique isomorphism `t : ℨ(Y) → ℨ(X)` with `h(X) ∘ t = g ∘ h(Y)` on an
open dense subset.

> In fact, a canonical isomorphism `ℨ(g)` is obtained for an arbitrary proper modification `g`, not necessarily a
> morphism.  (p. 147)

Stated without proof (p. 147); not proved here.  Formalization note (encoding): "canonical" is characterized by the
compatibility `h(X) ∘ t = g ∘ h(Y)` on an open dense subset of `ℨ(Y)` (`CompAgrees`), which for a morphism `g` is the
equality defining `ℨ(g)`; the paper does not say how the isomorphism is constructed (a reading). -/
@[blueprint "thm:0.6-zariski-canonical-iso"
  (statement := /-- A canonical isomorphism $\mathfrak Z(g)$ is obtained for an arbitrary proper modification $g$, not
    necessarily a morphism. (p.~147.) Formalization note (encoding): the unique isomorphism $t$ with $h(X)\circ t=g\circ
    h(Y)$ on an open dense subset. Not proved here: stated without proof. -/)
  (latexEnv := "theorem")]
def ZariskiCanonicalIso : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (X : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of B)),
    IsReducedAlgebraicBScheme pX → ∀ m : ModificationClass pX, ∀ (ZY : ZariskiSpaceData m.p)
      (ZX : ZariskiSpaceData pX), ZY.IsUniversal → ZX.IsUniversal →
        ∃! t : ZY.Z ⟶ ZX.Z, IsIso t ∧ ∀ (hY : ZY.Z ⟶ m.X'.toLocallyRingedSpace) (hX : ZX.Z ⟶ X.toLocallyRingedSpace),
          ZY.IsCanonicalFor m.p (Scheme.RationalMap.id m.X') hY → ZX.IsCanonicalFor pX (Scheme.RationalMap.id X) hX →
            m.f.CompAgrees hY (t ≫ hX)

/-! ### Proper and complete morphisms (p. 147) -/

/-- A *proper* morphism of algebraic `B`-preschemes, in the sense of Grothendieck (p. 147).

> The same term in the case of algebraic `B`-preschemes will be used in the sense of Grothendieck, [6, II, Ch. II, § 5].
> (p. 147)

Formalization note (encoding): Mathlib's `IsProper` is separated, universally closed and locally of finite type; the
"proper" of [6, II, 5.4.1] asks "of finite type", i.e. also quasi-compact.  Both are asked here (`IsProper` and
`QuasiCompact`).  Between algebraic `B`-preschemes the second is automatic (the source is a noetherian space) but is
kept so that the definition is Grothendieck's for every morphism.  (The "proper" of `IsProperApplication`, p. 138, uses Mathlib's `IsProper` for the projections; in the situations of this section the two agree.) -/
@[blueprint "def:0.6-proper-morphism"
  (statement := /-- A morphism of algebraic $\mathbf B$-preschemes is \emph{proper} in the sense of Grothendieck [6, II,
    Ch.~II, \S5] (p.~147). Formalization note (encoding): separated, universally closed, locally of finite type and
    quasi-compact. -/)
  (latexEnv := "definition")]
def IsProperMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop := IsProper f ∧ QuasiCompact f

/-- "`f` induces an isomorphism of the restrictions of `X'` and `X` to open dense subsets of their underlying topological
spaces" for a morphism `f` (pp. 147-148).

> … and a morphism `f : X′ → X | V` which is complete and induces an isomorphism of their restrictions to some open
> dense subsets.  (p. 148)

Formalization note (encoding): there are open dense `U ⊆ X'`, `V ⊆ X` with `f(U) ⊆ V` such that `f|_U : U → V` is an
isomorphism. -/
@[blueprint "def:0.6-induces-iso-dense"
  (statement := /-- A morphism $f\colon X'\to X$ \emph{induces an isomorphism of the restrictions to some open dense
    subsets}: there are open dense $U\subseteq X'$, $V\subseteq X$ with $f(U)\subseteq V$ such that $f|_U\colon X'|U\to
    X|V$ is an isomorphism. (p.~148.) -/)
  (latexEnv := "definition")]
def InducesIsoOnDenseOpens {X' X : Scheme.{u}} (f : X' ⟶ X) : Prop :=
  ∃ (U : X'.Opens) (V : X.Opens), Dense (U : Set X') ∧ Dense (V : Set X) ∧
    ∃ h : U ≤ f ⁻¹ᵁ V, IsIso (f.resLE V U h)

/-- **Conditions (i) and (ii) of a complete morphism** (p. 147): the part of "complete" which does not involve Zariski spaces.
The full notion, with condition (iii), is `IsComplete`; this predicate is only the first two conditions.

> Let `f : X′ → X` be a morphism of algebraic `B`-preschemes … Let us assume that `X′` and `X` are both reduced.  We then
> say that `f` is *complete* … if the following conditions are satisfied:
> (i) The morphism `f` is surjective (i.e., so is the underlying continuous mapping),
> (ii) for every point `x′` of `X′`, we can find a 4ple `(U, X̄′, f̄, j)` consisting of an open dense subset `U` of the
> underlying topological space of `X′` which contains `x′`, a reduced algebraic `B`-prescheme `X̄′`, a proper morphism
> `f̄ : X̄′ → X`, and a morphism `j : X′ | U → X̄′` which induces an isomorphism of the same to the restriction of `X̄′` to an
> open dense subset of its underlying topological space and such that `f̄ ∘ j = f | U`; and
> (iii) …  (p. 147)

Formalization note (encoding): the data of the 4ple are an open dense `U ∋ x′`, a scheme `X̄′` with structure morphism, `f̄`,
and `j : X′|U ⟶ X̄′`; "`j` induces an isomorphism onto the restriction of `X̄′` to an open dense subset `O`" is
`j = e ∘ (inclusion of O)` for an isomorphism `e : X′|U ≅ X̄′|O`; "morphism" is a morphism over `B`. -/
@[blueprint "def:0.6-complete-morphism-i-ii"
  (statement := /-- Let $f\colon X'\to X$ be a morphism of reduced algebraic $\mathbf B$-preschemes. Conditions (i) and (ii)
    of ``complete'' (p.~147): (i) $f$ is surjective; (ii) for every point $x'$ of $X'$ there is a 4-ple $(U,\bar X',\bar
    f,j)$ with $U$ open dense containing $x'$, $\bar X'$ a reduced algebraic $\mathbf B$-prescheme, $\bar f\colon\bar
    X'\to X$ proper, $j\colon X'|U\to\bar X'$ inducing an isomorphism onto the restriction of $\bar X'$ to an open dense
    subset and $\bar f\circ j=f|U$. This is only conditions (i) and (ii); the full notion, with condition (iii), is
    \cref{def:0.6-complete-morphism}. -/)
  (latexEnv := "definition")]
def IsCompleteIAndII {X' X : Scheme.{u}} (p' : X' ⟶ Spec (CommRingCat.of B)) (pX : X ⟶ Spec (CommRingCat.of B))
    (f : X' ⟶ X) : Prop :=
  f ≫ pX = p' ∧ IsAlgebraicPreschemeOver p' ∧ IsAlgebraicPreschemeOver pX ∧
    AlgebraicGeometry.IsReduced X' ∧ AlgebraicGeometry.IsReduced X ∧
    Function.Surjective f ∧
    ∀ x' : X', ∃ (U : X'.Opens) (_ : Dense (U : Set X')) (_ : x' ∈ U) (Xb : Scheme.{u})
      (pb : Xb ⟶ Spec (CommRingCat.of B)) (fb : Xb ⟶ X) (j : U.toScheme ⟶ Xb),
        IsAlgebraicPreschemeOver pb ∧ AlgebraicGeometry.IsReduced Xb ∧ fb ≫ pX = pb ∧ IsProperMorphism fb ∧
        j ≫ pb = U.ι ≫ p' ∧
        (∃ (O : Xb.Opens) (_ : Dense (O : Set Xb)) (e : U.toScheme ≅ O.toScheme), j = e.hom ≫ O.ι) ∧
        j ≫ fb = U.ι ≫ f

/-- A 4ple `(U, X̄′, f̄, j)` of condition (ii) of "complete" for a morphism `f : X′ → X` of algebraic `B`-preschemes (p. 147).

> … a 4ple `(U, X̄′, f̄, j)` consisting of an open dense subset `U` of the underlying topological space of `X′` which
> contains `x′`, a reduced algebraic `B`-prescheme `X̄′`, a proper morphism `f̄ : X̄′ → X`, and a morphism `j : X′ | U → X̄′`
> which induces an isomorphism of the same to the restriction of `X̄′` to an open dense subset of its underlying
> topological space and such that `f̄ ∘ j = f | U`.  (p. 147)

Formalization note (encoding): the condition `x′ ∈ U` is not a field (it concerns the point); the isomorphism onto an open
dense subset `O` of `X̄′` is `e` with `j = e ∘ (inclusion of O)`; morphisms are over `B`. -/
@[blueprint "def:0.6-complete-fourple"
  (statement := /-- A 4-ple $(U,\bar X',\bar f,j)$ for a morphism $f\colon X'\to X$ of algebraic $\mathbf B$-preschemes: $U$ an
    open dense subset of $X'$, $\bar X'$ a reduced algebraic $\mathbf B$-prescheme, $\bar f\colon\bar X'\to X$ a proper
    morphism, $j\colon X'|U\to\bar X'$ a morphism which induces an isomorphism of $X'|U$ onto the restriction of $\bar X'$
    to an open dense subset and such that $\bar f\circ j=f|U$ (p.~147). -/)
  (latexEnv := "definition")]
structure CompleteFourple {X' X : Scheme.{u}} (p' : X' ⟶ Spec (CommRingCat.of B)) (pX : X ⟶ Spec (CommRingCat.of B))
    (f : X' ⟶ X) where
  /-- The open dense subset `U` of `X′`. -/
  U : X'.Opens
  dense_U : Dense (U : Set X')
  /-- The scheme `X̄′` with its structure morphism, `f̄` and `j`. -/
  Xb : Scheme.{u}
  pb : Xb ⟶ Spec (CommRingCat.of B)
  fb : Xb ⟶ X
  j : U.toScheme ⟶ Xb
  isAlgebraicPrescheme : IsAlgebraicPreschemeOver pb
  isReduced : AlgebraicGeometry.IsReduced Xb
  fb_over : fb ≫ pX = pb
  isProper : IsProperMorphism fb
  j_over : j ≫ pb = U.ι ≫ p'
  /-- The open dense subset of `X̄′` onto which `j` induces an isomorphism. -/
  O : Xb.Opens
  dense_O : Dense (O : Set Xb)
  e : U.toScheme ≅ O.toScheme
  j_eq : j = e.hom ≫ O.ι
  comp : j ≫ fb = U.ι ≫ f

namespace CompleteFourple

variable {X' X : Scheme.{u}} {p' : X' ⟶ Spec (CommRingCat.of B)} {pX : X ⟶ Spec (CommRingCat.of B)} {f : X' ⟶ X}

/-- The restriction `X̄′ | f̄⁻¹(V)` of the 4ple to the preimage of an open subset `V` of `X` (p. 147). -/
abbrev restr (q : CompleteFourple p' pX f) (V : X.Opens) : Scheme.{u} := (q.fb ⁻¹ᵁ V).toScheme

/-- The structure morphism of `X̄′ | f̄⁻¹(V)`. -/
noncomputable abbrev restrBase (q : CompleteFourple p' pX f) (V : X.Opens) : q.restr V ⟶ Spec (CommRingCat.of B) :=
  (q.fb ⁻¹ᵁ V).ι ≫ q.pb

end CompleteFourple

/-- A *complete* morphism of reduced algebraic `B`-preschemes (p. 147), conditions (i), (ii) and (iii).

> … (iii) every point `x` of `X` admits an open neighborhood `V` in the underlying topological space of `X`, such that
> `X | V` is an algebraic `B`-scheme (resp. an analytic `K`-space) and that, if we identify in a canonical way the Zariski
> spaces `ℨ(X̄′ | f̄⁻¹(V))` for all 4ples `(U, X̄′, f̄, j)` of (ii) and call it `ℨ(X′ | V)`, then the underlying topological
> space of `ℨ(X′ | V)` is equal to the union of `h(X̄′ | f̄⁻¹(V))⁻¹(j(U) ∩ f̄⁻¹(V))` for all `(U, X̄′, f̄, j)`.  (p. 147)

Formalization note (encoding; existence-style reading of "identify in a canonical way"): the paper does not construct the
identification.  It is encoded by existence: there are a locally ringed space `ℨ(X′|V)` and, for every 4ple `q`, a Zariski
space datum `ℨ_q` of `X̄′_q|f̄_q⁻¹(V)` with the property (ii) and an isomorphism `ι_q : ℨ(X′|V) ≅ ℨ_q`, such that the
identifications are compatible with the canonical morphisms in the sense that, for any two 4ples `q`, `q′` and canonical
morphisms `h_q`, `h_{q′}`, on some open dense subset `W` of `ℨ(X′|V)` both `h_q ∘ ι_q` and `h_{q′} ∘ ι_{q′}` lift through
`j_q` and `j_{q′}` to one and the same morphism `W → X′` (this says that the transition `ρ_{q′} ∘ ρ_q⁻¹`, where `ρ_q` is
the rational application `X′|f⁻¹(V) ⤏ X̄′_q|f̄_q⁻¹(V)` of `j_q`, carries `h_q` to `h_{q′}` on `W`, without constructing the
composed rational applications); and the underlying set of `ℨ(X′|V)` is the union, over `q` and the canonical morphisms
`h_q`, of the preimages (under `h_q ∘ ι_q`) of `j_q(U_q) ∩ f̄_q⁻¹(V)`. -/
@[blueprint "def:0.6-complete-morphism"
  (statement := /-- Let $f\colon X'\to X$ be a morphism of algebraic $\mathbf B$-preschemes, $X'$ and $X$ reduced. $f$ is
    \emph{complete} if (i) $f$ is surjective, (ii) for every $x'\in X'$ there is a 4-ple $(U,\bar X',\bar f,j)$ with
    $x'\in U$, and (iii) every point $x$ of $X$ has an open neighbourhood $V$ such that $X|V$ is an algebraic
    $\mathbf B$-scheme and, if we identify in a canonical way the Zariski spaces $\mathfrak Z(\bar X'|\bar f^{-1}(V))$ for all
    4-ples of (ii) and call it $\mathfrak Z(X'|V)$, then the underlying space of $\mathfrak Z(X'|V)$ is the union of the
    $h(\bar X'|\bar f^{-1}(V))^{-1}(j(U)\cap\bar f^{-1}(V))$ for all 4-ples. (p.~147.) Formalization note (encoding):
    the canonical identification is encoded by existence of isomorphisms $\iota_q\colon\mathfrak Z(X'|V)\cong\mathfrak
    Z(\bar X'_q|\bar f_q^{-1}V)$ compatible with the canonical morphisms along the transitions $j_{q'}\circ j_q^{-1}$ on an
    open dense subset (the paper does not construct it). -/)
  (latexEnv := "definition")]
def IsComplete {X' X : Scheme.{u}} (p' : X' ⟶ Spec (CommRingCat.of B)) (pX : X ⟶ Spec (CommRingCat.of B))
    (f : X' ⟶ X) : Prop :=
  IsCompleteIAndII p' pX f ∧
  ∀ x : X, ∃ (V : X.Opens) (_ : x ∈ V), IsAlgebraicSchemeOver (V.ι ≫ pX) ∧
    ∃ (ZV : LocallyRingedSpace.{u}) (Zd : ∀ q : CompleteFourple p' pX f, ZariskiSpaceData (q.restrBase V))
      (ι : ∀ q : CompleteFourple p' pX f, ZV ≅ (Zd q).Z),
      (∀ q, (Zd q).IsUniversal) ∧
      (∀ (q q' : CompleteFourple p' pX f) (k : (Zd q).Z ⟶ (q.restr V).toLocallyRingedSpace)
          (k' : (Zd q').Z ⟶ (q'.restr V).toLocallyRingedSpace),
        (Zd q).IsCanonicalFor (q.restrBase V) (Scheme.RationalMap.id _) k →
        (Zd q').IsCanonicalFor (q'.restrBase V) (Scheme.RationalMap.id _) k' →
        ∃ (W : TopologicalSpace.Opens ZV) (_ : Dense (W : Set ZV))
          (l : ZV.restrict W.isOpenEmbedding ⟶ q.U.toScheme.toLocallyRingedSpace)
          (l' : ZV.restrict W.isOpenEmbedding ⟶ q'.U.toScheme.toLocallyRingedSpace),
          l ≫ q.U.ι.toLRSHom = l' ≫ q'.U.ι.toLRSHom ∧
          l ≫ q.j.toLRSHom = ZV.ofRestrict W.isOpenEmbedding ≫ (ι q).hom ≫ k ≫ (q.fb ⁻¹ᵁ V).ι.toLRSHom ∧
          l' ≫ q'.j.toLRSHom = ZV.ofRestrict W.isOpenEmbedding ≫ (ι q').hom ≫ k' ≫ (q'.fb ⁻¹ᵁ V).ι.toLRSHom) ∧
      ∀ z : ZV, ∃ (q : CompleteFourple p' pX f) (k : (Zd q).Z ⟶ (q.restr V).toLocallyRingedSpace),
        (Zd q).IsCanonicalFor (q.restrBase V) (Scheme.RationalMap.id _) k ∧
        (q.fb ⁻¹ᵁ V).ι (k.base ((ι q).hom.base z)) ∈ Set.range q.j

/-! ### The local uniformization theorem, (LU) and (RS) (pp. 147-148) -/

/-- **The local uniformization theorem of Zariski [24], algebraic case** (pp. 147-148), for the reduced algebraic
`B`-schemes `X` whose dimension satisfies `D` (`D` = "anything" for the printed theorem, `LocalUniformization`).

> **Theorem.**  Let `X` be a reduced algebraic `B`-scheme …, where `B` is a field of characteristic zero.  Let `x` be a
> point of `X`.  Then there exist an open neighborhood `V` of `x` in the underlying topological space of `X`, a
> non-singular algebraic `B`-prescheme … `X′`, and a morphism `f : X′ → X | V` which is complete and induces an
> isomorphism of their restrictions to some open dense subsets.  (pp. 147-148)

Cited (Zariski [24]); not proved here.  Here "complete" is `IsComplete` (conditions (i), (ii) and (iii)).  Formalization note (encoding):
`X|V` is the open subscheme `V`, with structure morphism `V.ι ≫ pX`. -/
@[blueprint "def:0.6-local-uniformization-of-dim"
  (statement := /-- Zariski's local uniformization theorem for reduced algebraic $\mathbf B$-schemes whose dimension
    satisfies a condition $D$ ($\mathbf B$ a field of characteristic zero): for every point $x$ there are an open
    neighbourhood $V$, a non-singular algebraic $\mathbf B$-prescheme $X'$ and a morphism $f\colon X'\to X|V$ which is
    complete and induces an isomorphism of restrictions to open dense subsets. (pp.~147--148.) -/)
  (latexEnv := "definition")]
def LocalUniformizationOfDim (D : WithBot ℕ∞ → Prop) : Prop :=
  ∀ (B : Type u) [Field B] [CharZero B] (X : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of B)),
    IsReducedAlgebraicBScheme pX → D X.dim → ∀ x : X,
      ∃ (V : X.Opens) (_ : x ∈ V) (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of B)) (f : X' ⟶ V.toScheme),
        IsAlgebraicPreschemeOver p' ∧ X'.IsNonsingular ∧ IsComplete p' (V.ι ≫ pX) f ∧ InducesIsoOnDenseOpens f

/-- The local uniformization theorem of Zariski [24] (p. 147), algebraic case, without a restriction on the dimension.
Cited (Zariski [24]); not proved here. -/
@[blueprint "thm:0.6-local-uniformization"
  (statement := /-- \textbf{Local uniformization theorem} (Zariski [24]). Let $X$ be a reduced algebraic $\mathbf
    B$-scheme, $\mathbf B$ a field of characteristic zero, and $x$ a point of $X$. Then there exist an open neighbourhood
    $V$ of $x$, a non-singular algebraic $\mathbf B$-prescheme $X'$ and a morphism $f\colon X'\to X|V$ which is complete
    and induces an isomorphism of the restrictions to some open dense subsets. (pp.~147--148.) Not proved here: cited
    (Zariski [24]). -/)
  (latexEnv := "theorem")]
def LocalUniformization : Prop := LocalUniformizationOfDim.{u} fun _ => True

/-- **(LU)** (p. 148), for the dimensions satisfying `D`: the local uniformization theorem with `V` containing all points
of `X`.

> In the *local uniformization theorem*, we require that `V` contain all the points of `X` for the algebraic case.
> Clearly this requirement leaves the statement equivalent in the algebraic case (but not in the analytic case by any
> trivial means).  With this modification, the theorem will be denoted by (LU).  (p. 148)

Stated without proof (the equivalence is "clear"; p. 148); not proved here.  The equivalence with the theorem is a
separate claim, `LUEquivLocalUniformization`. -/
@[blueprint "def:0.6-LU-of-dim"
  (statement := /-- (LU): the local uniformization theorem with $V$ containing all the points of $X$ (p.~148), for
    reduced algebraic $\mathbf B$-schemes whose dimension satisfies $D$. -/)
  (latexEnv := "definition")]
def LUOfDim (D : WithBot ℕ∞ → Prop) : Prop :=
  ∀ (B : Type u) [Field B] [CharZero B] (X : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of B)),
    IsReducedAlgebraicBScheme pX → D X.dim → ∀ x : X,
      ∃ (V : X.Opens) (_ : x ∈ V) (_ : V = ⊤) (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of B))
        (f : X' ⟶ V.toScheme),
        IsAlgebraicPreschemeOver p' ∧ X'.IsNonsingular ∧ IsComplete p' (V.ι ≫ pX) f ∧ InducesIsoOnDenseOpens f

/-- **(LU)** (p. 148), without a restriction on the dimension.  Stated without proof; not proved here. -/
@[blueprint "prop:0.6-LU"
  (statement := /-- (LU): the local uniformization theorem in the algebraic case with $V$ containing all the points of
    $X$ (p.~148). Not proved here: stated without proof. -/)
  (latexEnv := "proposition")]
def LU : Prop := LUOfDim.{u} fun _ => True

/-- The equivalence of (LU) and the local uniformization theorem in the algebraic case.

> Clearly this requirement leaves the statement equivalent in the algebraic case.  (p. 148)

Stated without proof ("Clearly"); not proved here. -/
@[blueprint "prop:0.6-LU-equivalent"
  (statement := /-- In the algebraic case, requiring that $V$ contain all the points of $X$ leaves the local
    uniformization theorem equivalent: (LU) holds iff the local uniformization theorem holds. (p.~148.) Not proved here:
    stated without proof (``Clearly''). -/)
  (latexEnv := "proposition")]
def LUEquivLocalUniformization : Prop := LU.{u} ↔ LocalUniformization.{u}

/-- **(RS)** (p. 148), for the dimensions satisfying `D`: (LU) with `X′` an algebraic `B`-scheme.

> By requiring that `X′` be an algebraic `B`-*scheme* (resp. an *analytic* `C`-space) in (LU), we obtain a statement
> which we shall denote by (RS), and which is the one called the reduction of singularities by Zariski in the algebraic
> case, and proved by him for `dim(X) ≦ 3`.  (p. 148)

Not proved here: the statement is not asserted in general; for `dim X ≤ 3` it is cited (Zariski; the proof is not printed). -/
@[blueprint "def:0.6-RS-of-dim"
  (statement := /-- (RS): (LU) with $X'$ an algebraic $\mathbf B$-scheme (p.~148), for reduced algebraic $\mathbf
    B$-schemes whose dimension satisfies $D$. -/)
  (latexEnv := "definition")]
def RSOfDim (D : WithBot ℕ∞ → Prop) : Prop :=
  ∀ (B : Type u) [Field B] [CharZero B] (X : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of B)),
    IsReducedAlgebraicBScheme pX → D X.dim → ∀ x : X,
      ∃ (V : X.Opens) (_ : x ∈ V) (_ : V = ⊤) (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of B))
        (f : X' ⟶ V.toScheme),
        IsAlgebraicSchemeOver p' ∧ X'.IsNonsingular ∧ IsComplete p' (V.ι ≫ pX) f ∧ InducesIsoOnDenseOpens f

/-- **(RS)**, the reduction of singularities by Zariski in the algebraic case (p. 148), without a restriction on the
dimension.  The paper says it was proved by Zariski for `dim(X) ≦ 3`; stated here as a `Prop`, not asserted in general. -/
@[blueprint "prop:0.6-RS"
  (statement := /-- (RS): (LU) with $X'$ an algebraic $\mathbf B$-scheme; ``the one called the reduction of
    singularities by Zariski in the algebraic case, and proved by him for $\dim(X)\le3$'' (p.~148). Not proved here (not
    asserted in general). -/)
  (latexEnv := "proposition")]
def RS : Prop := RSOfDim.{u} fun _ => True

/-- **(RS) in dimension at most three** (p. 148): "proved by him for `dim(X) ≦ 3`".  Cited (Zariski); not proved here. -/
@[blueprint "thm:0.6-RS-dim-le-three"
  (statement := /-- (RS) holds for $\dim(X)\le3$ (Zariski; p.~148). Not proved here: cited. -/)
  (latexEnv := "theorem")]
def RSDimLeThree : Prop := RSOfDim.{u} fun d => d ≤ 3

/-- "In the two-dimensional case, the deduction of (RS) from (LU) is *strikingly simple*, according to Zariski [25]" (p. 148).

> In the two-dimensional case, the deduction of (RS) from (LU) is *strikingly simple*, according to Zariski [25].  (p. 148)

Cited (Zariski [25]); not proved here. -/
@[blueprint "prop:0.6-RS-from-LU-dim-two"
  (statement := /-- In the two-dimensional case, (RS) can be deduced from (LU), and the deduction is strikingly simple,
    according to Zariski [25] (p.~148). Not proved here: cited. -/)
  (latexEnv := "proposition")]
def RSFromLUDimTwo : Prop := LUOfDim.{u} (fun d => d = 2) → RSOfDim.{u} (fun d => d = 2)

/-- "The same, in the three-dimensional case, was accomplished also by Zariski [27], but the proof is highly complicated"
(p. 148).

> The same, in the three-dimensional case, was accomplished also by Zariski [27], but the proof is highly complicated, and
> is not of the type to be generalized by any simple means to any higher dimensional case.  (p. 148)

Cited (Zariski [27]); not proved here. -/
@[blueprint "prop:0.6-RS-from-LU-dim-three-zariski"
  (statement := /-- In the three-dimensional case, the deduction of (RS) from (LU) was accomplished by Zariski [27] (p.~148),
    but the proof is highly complicated. Not proved here: cited. -/)
  (latexEnv := "proposition")]
def RSFromLUDimThreeZariski : Prop := LUOfDim.{u} (fun d => d = 3) → RSOfDim.{u} (fun d => d = 3)

end Hironaka

/-! ### Successions with given stages, points as centers -/

namespace Hironaka.MonoidalSuccession

/-- The property `P` holds at every stage of a succession, for the center `D` of the stage `W` and the composite `W ⟶ X₀`
of the earlier monoidal transformations (the centers `D_{ij}` and the morphisms `f_{ij} : X_{ij} → X_i` of p. 148). -/
@[blueprint "def:0.6-all-stages"
  (statement := /-- A property of (center, composite to the starting scheme) holds at every stage of a succession of
    monoidal transformations (the centers $D_{ij}\subseteq X_{ij}$ and morphisms $f_{ij}\colon X_{ij}\to X_i$,
    p.~148). Formalization note (encoding). -/)
  (latexEnv := "definition")]
def AllStages {X₀ : Scheme.{u}} (P : ∀ (W : Scheme.{u}), Subscheme W → (W ⟶ X₀) → Prop) :
    ∀ {W Y : Scheme.{u}}, MonoidalSuccession W Y → (W ⟶ X₀) → Prop
  | _, _, nil _, _ => True
  | _, _, cons D t rest, c => P _ D c ∧ rest.AllStages P (t.f ≫ c)

/-- Every center of the succession is a point: a reduced subscheme whose set of points is a single point (p. 149: "a
succession of monoidal transformations whose centers are points").

Formalization note (encoding): "a point" is a reduced subscheme with one point; the set of points of a subscheme is
closed, so the point is closed. -/
@[blueprint "def:0.6-point-centers"
  (statement := /-- A succession of monoidal transformations has \emph{centers which are points} if each center is a
    reduced subscheme consisting of a single point (p.~149). Formalization note (encoding): the point is closed. -/)
  (latexEnv := "definition")]
def HasPointCenters : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, _, nil _ => True
  | _, _, cons D _ rest => (∃ x, D.pts = {x}) ∧ D = Subscheme.red D ∧ rest.HasPointCenters

end Hironaka.MonoidalSuccession

/-! ### Questions (F) and (F′) (pp. 148-149) -/

namespace Hironaka

variable {B : Type u} [CommRing B]

/-- `f'` is the *canonical rational application* `X₁' ⤏ X₂'` determined by `f : X₁ ⤏ X₂` and the morphisms `g_i : X_i' → X_i`
(pp. 148-149), the composite `g₂⁻¹ ∘ f ∘ g₁`.

> (2) for every point `z` of `G` such that `h_i(z) ∈ U_i` for `i = 1, 2`, the canonical rational application `f′ : X₁′ → X₂′`
> is defined at `h₁′(z)` as well as `f′⁻¹` at `h₂′(z)`, where `h_i′ : ℨ → X_i′` denotes the canonical morphism, for
> `i = 1, 2`.  (p. 149)

Formalization note (encoding): the paper does not define "canonical rational application"; it is `g₂⁻¹ ∘ f ∘ g₁` (the
rational application `h₂⁻¹ ∘ f ∘ h₁` of Question (F′), p. 149), with the compositions of p. 139 (`IsComposite`) and the
inverse of the modification `g₂` (`IsInverseOf`). -/
@[blueprint "def:0.6-canonical-application"
  (statement := /-- For a rational application $f\colon X_1\dashrightarrow X_2$ and morphisms $g_i\colon X_i'\to X_i$ which
    are modifications, the \emph{canonical rational application} $f'\colon X_1'\dashrightarrow X_2'$ is $g_2^{-1}\circ
    f\circ g_1$ (pp.~148--149). Formalization note (encoding): the paper uses ``the canonical rational application''
    without defining it. -/)
  (latexEnv := "definition")]
def IsCanonicalApplication {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (g₁ : Y₁ ⟶ X₁) (g₂ : Y₂ ⟶ X₂) (f : X₁ ⤏ X₂)
    (f' : Y₁ ⤏ Y₂) : Prop :=
  ∃ (a : Y₁ ⤏ X₂) (g₂inv : X₂ ⤏ Y₂), Scheme.RationalMap.IsComposite g₁.toRationalMap f a ∧
    Scheme.RationalMap.IsInverseOf g₂inv g₂.toRationalMap ∧ Scheme.RationalMap.IsComposite a g₂inv f'

/-- The data of Question (F): `ℨ` is identified with the Zariski spaces `ℨ(X₁)` and `ℨ(X₂)` by `ι₁, ι₂`, and the
identification is the canonical isomorphism for the proper modification `f`.

> Let `ℨ = ℨ(X₁) = ℨ(X₂)`, the Zariski spaces canonically identified.  Let `h_i = h(X_i) : ℨ → X_i` be the canonical
> morphisms for `i = 1, 2`.  (p. 148)

Formalization note (encoding): the identification `ℨ(X₁) = ℨ(X₂)` is the canonical isomorphism `ℨ(f)` of p. 147,
characterized by `h₂ = f ∘ h₁` on an open dense subset (`CompAgrees`); both Zariski spaces have the property (ii). -/
@[blueprint "def:0.6-zariski-identified"
  (statement := /-- A locally ringed space $\mathfrak Z$ is \emph{identified} with the Zariski spaces $\mathfrak Z(X_1)$ and
    $\mathfrak Z(X_2)$ of a proper modification $f\colon X_1\dashrightarrow X_2$ by isomorphisms $\iota_1,\iota_2$ such
    that $h_2=f\circ h_1$ on an open dense subset (the canonical isomorphism of p.~147). (p.~148.) Formalization note
    (encoding). -/)
  (latexEnv := "definition")]
def ZariskiIdentified {X₁ X₂ : Scheme.{u}} {p₁ : X₁ ⟶ Spec (CommRingCat.of B)} {p₂ : X₂ ⟶ Spec (CommRingCat.of B)}
    (f : X₁ ⤏ X₂) {Z : LocallyRingedSpace.{u}} (Z₁ : ZariskiSpaceData p₁) (Z₂ : ZariskiSpaceData p₂)
    (ι₁ : Z ≅ Z₁.Z) (ι₂ : Z ≅ Z₂.Z) : Prop :=
  Z₁.IsUniversal ∧ Z₂.IsUniversal ∧
    ∀ (h₁ : Z ⟶ X₁.toLocallyRingedSpace) (h₂ : Z ⟶ X₂.toLocallyRingedSpace),
      Z₁.IsCanonicalVia ι₁ p₁ (Scheme.RationalMap.id X₁) h₁ → Z₂.IsCanonicalVia ι₂ p₂ (Scheme.RationalMap.id X₂) h₂ →
        f.CompAgrees h₁ h₂

/-- The conclusion of Question (F) for the data `(f, ℨ, G, U₁, U₂, h₁, h₂)`: there are morphisms `X_i' → X_i` obtained by
finite successions of monoidal transformations with nowhere dense centers `D_{ij}` which have the properties (1) and (2).

> Then we ask if there exist morphisms `X_i′ → X_i` (`i = 1, 2`) obtained by finite successions of monoidal transformations
> `X_{ij+1} → X_{ij}` with centers `D_{ij}`, nowhere dense in `X_{ij}`, which have the following properties:
> (1) `D_{ij}` has no multiple points contained in `h_{ij}(G) ∩ f_{ij}⁻¹(U_i)`, where `h_{ij} : ℨ → X_{ij}` and
> `f_{ij} : X_{ij} → X_i` are the canonical morphisms, for all `(i, j)`; and
> (2) for every point `z` of `G` such that `h_i(z) ∈ U_i` for `i = 1, 2`, the canonical rational application
> `f′ : X₁′ → X₂′` is defined at `h₁′(z)` as well as `f′⁻¹` at `h₂′(z)`, where `h_i′ : ℨ → X_i′` denotes the canonical
> morphism, for `i = 1, 2`.  (pp. 148-149)

Formalization notes (encoding): the subject of "no multiple points" is the center `D_{ij}`: every point of `D_{ij}` in
`h_{ij}(G) ∩ f_{ij}⁻¹(U_i)` is a simple point of the subscheme `D_{ij}` (`Subscheme.IsSimpleAt`: the local ring of `D_{ij}`
at the point is regular; the convention of Question (E) and of p. 163), so that the centers are non-singular there; `f_{ij}` is the
composite of the monoidal transformations up to stage `j`, and `h_{ij}` the canonical morphism for `(X_{ij}, f_{ij}) ∈
𝔐(X_i)` (`IsCanonicalVia`; its existence is part of the conclusion: the paper uses it tacitly, it holds because a
monoidal transformation with nowhere dense center of a reduced algebraic `B`-scheme is a proper modification); the points of
`h_{ij}(G)` are the images of the points of `G`; "canonical rational application" is `IsCanonicalApplication`, and the
canonical morphisms `h_i′` are asserted to exist. -/
@[blueprint "def:0.6-F-conclusion"
  (statement := /-- The conclusion of Question (F) for given $f$, $\mathfrak Z$, $G$, $U_1,U_2$: there are finite
    successions of monoidal transformations $X_{ij+1}\to X_{ij}$ with nowhere dense centers $D_{ij}$, giving morphisms
    $X_i'\to X_i$, such that (1) $D_{ij}$ has no multiple points (as a subscheme: the local ring of $D_{ij}$ is regular) at its points in $h_{ij}(G)\cap f_{ij}^{-1}(U_i)$ for all $(i,j)$, and
    (2) for every $z\in G$ with $h_i(z)\in U_i$ ($i=1,2$) the canonical rational application $f'$ is defined at $h_1'(z)$
    and $f'^{-1}$ at $h_2'(z)$. (pp.~148--149.) Formalization note (encoding). -/)
  (latexEnv := "definition")]
def HasFSuccessions {X₁ X₂ : Scheme.{u}} {p₁ : X₁ ⟶ Spec (CommRingCat.of B)} {p₂ : X₂ ⟶ Spec (CommRingCat.of B)}
    (f : X₁ ⤏ X₂) {Z : LocallyRingedSpace.{u}} (Z₁ : ZariskiSpaceData p₁) (Z₂ : ZariskiSpaceData p₂)
    (ι₁ : Z ≅ Z₁.Z) (ι₂ : Z ≅ Z₂.Z) (G : Set Z) (U₁ : X₁.Opens) (U₂ : X₂.Opens)
    (h₁ : Z ⟶ X₁.toLocallyRingedSpace) (h₂ : Z ⟶ X₂.toLocallyRingedSpace) : Prop :=
  ∃ (Y₁ Y₂ : Scheme.{u}) (s₁ : MonoidalSuccession X₁ Y₁) (s₂ : MonoidalSuccession X₂ Y₂),
    s₁.NowhereDenseCenters ∧ s₂.NowhereDenseCenters ∧
    s₁.AllStages (fun W D c => ∃ k : Z ⟶ W.toLocallyRingedSpace,
      Z₁.IsCanonicalVia ι₁ (c ≫ p₁) c.toRationalMap k ∧
        ∀ y ∈ D.pts, y ∈ k.base '' G → c y ∈ U₁ → D.IsSimpleAt y) (𝟙 X₁) ∧
    s₂.AllStages (fun W D c => ∃ k : Z ⟶ W.toLocallyRingedSpace,
      Z₂.IsCanonicalVia ι₂ (c ≫ p₂) c.toRationalMap k ∧
        ∀ y ∈ D.pts, y ∈ k.base '' G → c y ∈ U₂ → D.IsSimpleAt y) (𝟙 X₂) ∧
    ∃ (f' : Y₁ ⤏ Y₂) (f'inv : Y₂ ⤏ Y₁) (h₁' : Z ⟶ Y₁.toLocallyRingedSpace) (h₂' : Z ⟶ Y₂.toLocallyRingedSpace),
      IsCanonicalApplication s₁.composite s₂.composite f f' ∧ Scheme.RationalMap.IsInverseOf f'inv f' ∧
      Z₁.IsCanonicalVia ι₁ (s₁.composite ≫ p₁) s₁.composite.toRationalMap h₁' ∧
      Z₂.IsCanonicalVia ι₂ (s₂.composite ≫ p₂) s₂.composite.toRationalMap h₂' ∧
      ∀ z ∈ G, h₁.base z ∈ U₁ → h₂.base z ∈ U₂ → h₁'.base z ∈ f'.domain ∧ h₂'.base z ∈ f'inv.domain

/-- **Question (F)** (p. 148), algebraic case, for the pairs `(X₁, X₂)` whose dimensions satisfy `D` and the subsets `G` of
`ℨ` satisfying `GP` (`GP` = quasi-compact for the printed question; the whole space for the case of interest of p. 149).

> **Question (F).**  Let `f : X₁ → X₂` be a proper modification (not necessarily a morphism) of reduced algebraic `B`-schemes
> (resp. reduced analytic `C`-spaces).  Let `ℨ = ℨ(X₁) = ℨ(X₂)`, the Zariski spaces canonically identified.  Let
> `h_i = h(X_i) : ℨ → X_i` be the canonical morphisms for `i = 1, 2`.  Let `G` be a quasi-compact (resp. compact) subset of the
> underlying topological space of `ℨ`.  Let `U_i` be an open subset of the underlying topological space of `X_i` such that
> `X_i | U_i` is non-singular, for `i = 1, 2`.  We assume that `G ⊂ h₁⁻¹(U₁) ∪ h₂⁻¹(U₂)`.  Then we ask if there exist … (p. 148)

A question: the `Prop` is "the question has an affirmative answer".  Formalization notes (encoding): see `HasFSuccessions`
and `ZariskiIdentified`; `f` is `X₁ ⤏ X₂` with `f.IsProperModification`; "quasi-compact" is `IsCompact`; the Zariski
spaces are any data with (ii), identified with `ℨ` by `ι₁`, `ι₂`; `h_i` are the canonical morphisms. -/
@[blueprint "def:0.6-question-F-of-dim"
  (statement := /-- Question (F), algebraic case, for pairs whose dimensions satisfy $D$ and subsets $G$ of the
    Zariski space satisfying a condition: has it an affirmative answer? (p.~148.) Formalization note (encoding): see the
    conclusion of Question (F). -/)
  (latexEnv := "definition")]
def QuestionFOfDim (D : WithBot ℕ∞ → Prop) (GP : ∀ Z : LocallyRingedSpace.{u}, Set Z → Prop) : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (X₁ X₂ : Scheme.{u}) (p₁ : X₁ ⟶ Spec (CommRingCat.of B))
    (p₂ : X₂ ⟶ Spec (CommRingCat.of B)), IsReducedAlgebraicBScheme p₁ → IsReducedAlgebraicBScheme p₂ →
    D X₁.dim → D X₂.dim → ∀ f : X₁ ⤏ X₂, f.IsProperModification p₁ p₂ →
    ∀ (Z : LocallyRingedSpace.{u}) (Z₁ : ZariskiSpaceData p₁) (Z₂ : ZariskiSpaceData p₂)
      (ι₁ : Z ≅ Z₁.Z) (ι₂ : Z ≅ Z₂.Z), ZariskiIdentified f Z₁ Z₂ ι₁ ι₂ →
    ∀ G : Set Z, GP Z G → ∀ (U₁ : X₁.Opens) (U₂ : X₂.Opens), U₁.toScheme.IsNonsingular →
      U₂.toScheme.IsNonsingular → ∀ (h₁ : Z ⟶ X₁.toLocallyRingedSpace) (h₂ : Z ⟶ X₂.toLocallyRingedSpace),
      Z₁.IsCanonicalVia ι₁ p₁ (Scheme.RationalMap.id X₁) h₁ → Z₂.IsCanonicalVia ι₂ p₂ (Scheme.RationalMap.id X₂) h₂ →
      G ⊆ h₁.base ⁻¹' (U₁ : Set X₁) ∪ h₂.base ⁻¹' (U₂ : Set X₂) →
      HasFSuccessions f Z₁ Z₂ ι₁ ι₂ G U₁ U₂ h₁ h₂

/-- **Question (F)** (p. 148), algebraic case: has it an affirmative answer?  Posed as a question, not asserted. -/
@[blueprint "def:0.6-question-F"
  (statement := /-- \textbf{Question (F).} Let $f\colon X_1\to X_2$ be a proper modification (not necessarily a morphism) of
    reduced algebraic $\mathbf B$-schemes; $\mathfrak Z=\mathfrak Z(X_1)=\mathfrak Z(X_2)$ canonically identified; $h_i$ the
    canonical morphisms; $G$ a quasi-compact subset of $\mathfrak Z$; $U_i$ an open subset of $X_i$ with $X_i|U_i$
    non-singular; $G\subset h_1^{-1}(U_1)\cup h_2^{-1}(U_2)$. Do there exist morphisms $X_i'\to X_i$ obtained by finite
    successions of monoidal transformations with nowhere dense centers $D_{ij}$ such that (1) $D_{ij}$ has no multiple
    points in $h_{ij}(G)\cap f_{ij}^{-1}(U_i)$, and (2) for every $z\in G$ with $h_i(z)\in U_i$ the canonical rational
    application $f'$ is defined at $h_1'(z)$ and $f'^{-1}$ at $h_2'(z)$? (p.~148--149.) The statement is ``the question
    has an affirmative answer''. -/)
  (latexEnv := "definition")]
def QuestionF : Prop := QuestionFOfDim.{u} (fun _ => True) (fun _ G => IsCompact G)

/-- **Question (F), the case of interest in the algebraic case** (p. 149): `G` is the underlying topological space of `ℨ`.

> In the algebraic case, we are interested in the case in which `G` is the underlying topological space of `ℨ`.  (p. 149)

A question (the special case of (F)); the quasi-compactness of `G` is the hypothesis of (F).

The paper then says (p. 149) that in this case "(1) says that the morphisms `g_i` induce `X_i′ | g_i⁻¹(U_i) → X_i | U_i` which are
obtained by finite successions of monoidal transformations with non-singular and nowhere dense centers, and (2) says that
`X₁′ | g₁⁻¹(U₁)` and `X₂′ | g₂⁻¹(U₂)` patch together and make a non-singular algebraic `B`-scheme `X′` with canonical morphisms
to `X₁` and `X₂` which are both proper modifications".  These two readings are stated without proof; they are stated as
`FWholeReadings`. -/
@[blueprint "def:0.6-question-F-whole"
  (statement := /-- Question (F) in the algebraic case with $G$ the underlying topological space of $\mathfrak Z$ (p.~149).
    The statement is ``the question has an affirmative answer''. -/)
  (latexEnv := "definition")]
def QuestionFWhole : Prop := QuestionFOfDim.{u} (fun _ => True) (fun _ G => G = Set.univ ∧ IsCompact G)

/-- **Question (F′)** (p. 149), algebraic case, for the pairs whose dimensions satisfy `D`.

> **Question (F′).**  Let `f : X₁ → X₂` be a proper modification as in question (F).  We assume that both `X₁` and `X₂` are
> non-singular and that, especially in the analytic case, `X₁` and hence `X₂` are compact.  Can one find a proper modification
> `h_i : X_i′ → X_i` for each `i`, which is obtained by a finite succession of monoidal transformations with non-singular
> centers, such that the rational application `h₂⁻¹ ∘ f ∘ h₁` is an isomorphism of `X₁′` to `X₂′`?  (p. 149)

A question; the `Prop` is "the question has an affirmative answer".  Formalization notes (encoding): the proper
modifications `h_i` are the composites `s_i.composite` of successions, with `X_i'` reduced algebraic `B`-schemes (structure
morphism the composite with that of `X_i`); `h₂⁻¹ ∘ f ∘ h₁` is `IsCanonicalApplication`; "isomorphism" is an isomorphism of
schemes over `B` whose class is that rational application. -/
@[blueprint "def:0.6-question-F-prime-of-dim"
  (statement := /-- Question (F$'$), algebraic case, for pairs whose dimensions satisfy a condition $D$ (p.~149). -/)
  (latexEnv := "definition")]
def QuestionFPrimeOfDim (D : WithBot ℕ∞ → Prop) : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (X₁ X₂ : Scheme.{u}) (p₁ : X₁ ⟶ Spec (CommRingCat.of B))
    (p₂ : X₂ ⟶ Spec (CommRingCat.of B)), IsReducedAlgebraicBScheme p₁ → IsReducedAlgebraicBScheme p₂ →
    D X₁.dim → D X₂.dim → X₁.IsNonsingular → X₂.IsNonsingular →
    ∀ f : X₁ ⤏ X₂, f.IsProperModification p₁ p₂ →
      ∃ (Y₁ Y₂ : Scheme.{u}) (s₁ : MonoidalSuccession X₁ Y₁) (s₂ : MonoidalSuccession X₂ Y₂)
        (p₁' : Y₁ ⟶ Spec (CommRingCat.of B)) (p₂' : Y₂ ⟶ Spec (CommRingCat.of B)),
        s₁.HasNonsingularCenters ∧ s₂.HasNonsingularCenters ∧
        IsReducedAlgebraicBScheme p₁' ∧ IsReducedAlgebraicBScheme p₂' ∧
        s₁.composite ≫ p₁ = p₁' ∧ s₂.composite ≫ p₂ = p₂' ∧
        s₁.composite.toRationalMap.IsProperModification p₁' p₁ ∧
        s₂.composite.toRationalMap.IsProperModification p₂' p₂ ∧
        ∃ f' : Y₁ ⤏ Y₂, IsCanonicalApplication s₁.composite s₂.composite f f' ∧
          ∃ e : Y₁ ≅ Y₂, e.hom ≫ p₂' = p₁' ∧ e.hom.toRationalMap = f'

/-- **Question (F′)** (p. 149), algebraic case: has it an affirmative answer?  "We have no answer to it for
`dim(X₁) = dim(X₂) ≧ 3`" (p. 149): it stays a `Prop`, not asserted. -/
@[blueprint "def:0.6-question-F-prime"
  (statement := /-- \textbf{Question (F$'$).} Let $f\colon X_1\to X_2$ be a proper modification as in Question (F) with $X_1$
    and $X_2$ non-singular. Can one find a proper modification $h_i\colon X_i'\to X_i$ for each $i$, obtained by a finite
    succession of monoidal transformations with non-singular centers, such that the rational application $h_2^{-1}\circ
    f\circ h_1$ is an isomorphism of $X_1'$ to $X_2'$? (p.~149.) ``We have no answer to it for $\dim(X_1)=\dim(X_2)\ge3$''.
    The statement is ``the question has an affirmative answer''. -/)
  (latexEnv := "definition")]
def QuestionFPrime : Prop := QuestionFPrimeOfDim.{u} fun _ => True

/-! ### The theorems of Zariski in dimensions two and three and the claims around them (pp. 148-150) -/

/-- Zariski's factorization statement in dimension `n` (p. 149, footnote 23): every proper morphism `f : X′ → X` of algebraic
`B`-schemes, with `X` non-singular of dimension `n`, `X′` non-singular and `f` a modification, is obtained by a succession of
monoidal transformations whose centers are points.

> **Theorem.**²³  Let `X` be a non-singular algebraic `B`-scheme (or, a non-singular analytic `C`-space) of dimension `2`.
> Then every proper morphism `f : X′ → X`, such that `X′` is non-singular and `f` is a modification, is obtained by a
> succession of monoidal transformations whose centers are points.  (p. 149)

Formalization notes (encoding): the structure morphism of `X′` is `f ≫ pX`; "`X′` an algebraic `B`-scheme" is part of the
reading of "proper morphism of algebraic `B`-schemes"; "obtained by a succession" is `s.composite = f`; "proper" is
`IsProperMorphism` (Grothendieck's sense, p. 147). -/
@[blueprint "def:0.6-point-blowup-factorization"
  (statement := /-- The statement $\mathrm{PB}(n)$: let $X$ be a non-singular algebraic $\mathbf B$-scheme of dimension
    $n$; then every proper morphism $f\colon X'\to X$ of algebraic $\mathbf B$-schemes such that $X'$ is non-singular
    and $f$ is a modification is obtained by a succession of monoidal transformations whose centers are points. (The
    theorem of p.~149 for $n=2$.) -/)
  (latexEnv := "definition")]
def PointBlowupFactorization (n : ℕ) : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (X : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of B)),
    IsAlgebraicSchemeOver pX → X.IsNonsingular → X.dim = (n : WithBot ℕ∞) →
    ∀ (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of B)) (f : X' ⟶ X),
      IsAlgebraicSchemeOver p' → f ≫ pX = p' → IsProperMorphism f → X'.IsNonsingular →
      f.toRationalMap.IsModification → ∃ s : MonoidalSuccession X X', s.composite = f ∧ s.HasPointCenters

/-- **Theorem of Zariski, dimension two** (p. 149, footnote 23).

> This theorem is due to Zariski.  (See the Lemma [27, p. 538], and notice that his proof applies to the general case.)
> One may also refer to: Schlichte Abbildungen und lokale Modificationen 4-dimensionaler komplexer Mannigfaltigkeiten, by
> H. Hopf, Comment. Math. Helv., 29 (1955), 132-155.  (fn. 23, p. 149)

Cited (Zariski [27, p. 538]); not proved here. -/
@[blueprint "thm:0.6-zariski-dim-two"
  (statement := /-- \textbf{Theorem}$^{23}$ (Zariski). Let $X$ be a non-singular algebraic $\mathbf B$-scheme of dimension
    $2$. Then every proper morphism $f\colon X'\to X$, such that $X'$ is non-singular and $f$ is a modification, is
    obtained by a succession of monoidal transformations whose centers are points. (p.~149.) Not proved here: cited
    (Zariski [27, p.~538]; fn.~23). -/)
  (latexEnv := "theorem")]
def ZariskiDimTwo : Prop := PointBlowupFactorization.{u} 2

/-- "The same statement for `dim(X) ≧ 3` is false" (p. 149): for every `n ≥ 3` the statement `PointBlowupFactorization n` fails.

> The same statement for `dim(X) ≧ 3` is false.  (p. 149)

Stated without proof (p. 149); not proved here.  Deviation (stronger statement): for each dimension `n ≥ 3` there is a
counterexample (the statement for all `X` of dimension `n` is false). -/
@[blueprint "prop:0.6-point-blowup-fails"
  (statement := /-- The same statement for $\dim(X)\ge3$ is false (p.~149): for every $n\ge3$ there are a non-singular
    algebraic $\mathbf B$-scheme $X$ of dimension $n$ and a proper morphism $X'\to X$ with $X'$ non-singular which is a
    modification and is not obtained by a succession of monoidal transformations whose centers are points. Not proved
    here: stated without proof. -/)
  (latexEnv := "proposition")]
def PointBlowupFactorizationFailsFromThree : Prop := ∀ n : ℕ, 3 ≤ n → ¬ PointBlowupFactorization.{u} n

/-- **Theorem of Zariski, dimension three** (pp. 149-150), (1)-(3).

> **Theorem.**  Let `f : X₁ → X₂`, `ℨ` and `h_i`, `i = 1, 2`, be the same as in the question (F).  We assume that `X₁` and
> `X₂` are reduced algebraic `B`-schemes of dimension `3`, where `B` is a field of characteristic zero.  Let `U_i` be the set
> of simple points of `X_i` for `i = 1, 2`.  Then for each `i`, there exists a modification `g_i : X_i′ → X_i`, which is a proper
> morphism, such that if `U_i′ = g_i⁻¹(U_i)` and `h_i′ : ℨ → X_i′` is the canonical morphism, then
> (1) `X_i′ | U_i′ → X_i | U_i`, induced by `g_i`, is obtained by a finite succession of monoidal transformations with
> non-singular centers, for `i = 1, 2`.
> (2) `V_i′ = h_i′(h₁⁻¹(U₁) ∩ h₂⁻¹(U₂))` is an open subset of `U_i′` for `i = 1, 2`, and
> (3) the canonical modification `p : X₁′ | V₁′ → X₂′ | V₂′` is a proper morphism such that `p⁻¹` has only a finite number of
> points of indeterminacy.  (pp. 149-150)

Cited (Zariski; no reference number is printed at this theorem); not proved here (the paper says Zariski proves it "by means of the above theorem and the theorem of
B. Levi-Zariski").  Formalization notes (encoding): `U_i` is an open subset whose points are exactly the simple points (the
simple locus is open for algebraic schemes over a field of characteristic zero; if it were not open no `U_i` exists and the
statement would be vacuous); `X_i′` is a reduced algebraic `B`-scheme with `g_i` over `B`; the canonical morphisms `h_i′` are
asserted to exist; "the canonical modification `p`" is the morphism `V₁′ → V₂′` whose class is the restriction of the canonical
rational application `f′ = g₂⁻¹ ∘ f ∘ g₁` to `V₁′` (`IsCanonicalApplication`, `precomp`); "`p⁻¹`" is the inverse of the
modification `p` (`IsInverseOf`), its points of indeterminacy (`IsIndeterminacyPoint`) form a finite set.  The sentence after
(3) ("Let `U₂″` be the complement of the points of indeterminacy of `p⁻¹` in `U₂′`.  Then we see that … patch together …") is
stated, without proof, as `DimThreePatching`. -/
@[blueprint "thm:0.6-zariski-dim-three"
  (statement := /-- \textbf{Theorem} (Zariski). Let $f\colon X_1\to X_2$, $\mathfrak Z$, $h_i$ be as in Question (F), $X_1,X_2$
    reduced algebraic $\mathbf B$-schemes of dimension $3$, $\mathbf B$ a field of characteristic zero, $U_i$ the set of simple
    points of $X_i$. Then for each $i$ there exists a modification $g_i\colon X_i'\to X_i$ which is a proper morphism such
    that, with $U_i'=g_i^{-1}(U_i)$ and $h_i'\colon\mathfrak Z\to X_i'$ the canonical morphism: (1) $X_i'|U_i'\to X_i|U_i$ is
    obtained by a finite succession of monoidal transformations with non-singular centers; (2) $V_i'=h_i'(h_1^{-1}(U_1)\cap
    h_2^{-1}(U_2))$ is an open subset of $U_i'$; (3) the canonical modification $p\colon X_1'|V_1'\to X_2'|V_2'$ is a proper
    morphism such that $p^{-1}$ has only a finite number of points of indeterminacy. (pp.~149--150.) Not proved here: cited
    (Zariski). -/)
  (latexEnv := "theorem")]
def ZariskiDimThree : Prop :=
  ∀ (B : Type u) [Field B] [CharZero B] (X₁ X₂ : Scheme.{u}) (p₁ : X₁ ⟶ Spec (CommRingCat.of B))
    (p₂ : X₂ ⟶ Spec (CommRingCat.of B)), IsReducedAlgebraicBScheme p₁ → IsReducedAlgebraicBScheme p₂ →
    X₁.dim = 3 → X₂.dim = 3 → ∀ f : X₁ ⤏ X₂, f.IsProperModification p₁ p₂ →
    ∀ (Z : LocallyRingedSpace.{u}) (Z₁ : ZariskiSpaceData p₁) (Z₂ : ZariskiSpaceData p₂)
      (ι₁ : Z ≅ Z₁.Z) (ι₂ : Z ≅ Z₂.Z), ZariskiIdentified f Z₁ Z₂ ι₁ ι₂ →
    ∀ (U₁ : X₁.Opens) (U₂ : X₂.Opens), (∀ x, x ∈ U₁ ↔ X₁.IsSimpleAt x) → (∀ x, x ∈ U₂ ↔ X₂.IsSimpleAt x) →
    ∀ (h₁ : Z ⟶ X₁.toLocallyRingedSpace) (h₂ : Z ⟶ X₂.toLocallyRingedSpace),
      Z₁.IsCanonicalVia ι₁ p₁ (Scheme.RationalMap.id X₁) h₁ → Z₂.IsCanonicalVia ι₂ p₂ (Scheme.RationalMap.id X₂) h₂ →
      ∃ (Y₁ Y₂ : Scheme.{u}) (p₁' : Y₁ ⟶ Spec (CommRingCat.of B)) (p₂' : Y₂ ⟶ Spec (CommRingCat.of B))
        (g₁ : Y₁ ⟶ X₁) (g₂ : Y₂ ⟶ X₂) (h₁' : Z ⟶ Y₁.toLocallyRingedSpace) (h₂' : Z ⟶ Y₂.toLocallyRingedSpace),
        IsReducedAlgebraicBScheme p₁' ∧ IsReducedAlgebraicBScheme p₂' ∧ g₁ ≫ p₁ = p₁' ∧ g₂ ≫ p₂ = p₂' ∧
        g₁.toRationalMap.IsModification ∧ g₂.toRationalMap.IsModification ∧
        IsProperMorphism g₁ ∧ IsProperMorphism g₂ ∧
        Z₁.IsCanonicalVia ι₁ p₁' g₁.toRationalMap h₁' ∧ Z₂.IsCanonicalVia ι₂ p₂' g₂.toRationalMap h₂' ∧
        (∃ s : MonoidalSuccession U₁.toScheme (g₁ ⁻¹ᵁ U₁).toScheme,
          s.HasNonsingularCenters ∧ s.composite = g₁ ∣_ U₁) ∧
        (∃ s : MonoidalSuccession U₂.toScheme (g₂ ⁻¹ᵁ U₂).toScheme,
          s.HasNonsingularCenters ∧ s.composite = g₂ ∣_ U₂) ∧
        ∃ (V₁ : Y₁.Opens) (V₂ : Y₂.Opens),
          (V₁ : Set Y₁) = h₁'.base '' (h₁.base ⁻¹' (U₁ : Set X₁) ∩ h₂.base ⁻¹' (U₂ : Set X₂)) ∧
          (V₂ : Set Y₂) = h₂'.base '' (h₁.base ⁻¹' (U₁ : Set X₁) ∩ h₂.base ⁻¹' (U₂ : Set X₂)) ∧
          V₁ ≤ g₁ ⁻¹ᵁ U₁ ∧ V₂ ≤ g₂ ⁻¹ᵁ U₂ ∧
          ∃ f' : Y₁ ⤏ Y₂, IsCanonicalApplication g₁ g₂ f f' ∧
            ∃ p : V₁.toScheme ⟶ V₂.toScheme, IsProperMorphism p ∧
              (p ≫ V₂.ι).toRationalMap = f'.precomp V₁.ι (Scheme.Hom.PreimageDense.of_isOpenImmersion _) ∧
              ∃ pinv : V₂.toScheme ⤏ V₁.toScheme, Scheme.RationalMap.IsInverseOf pinv p.toRationalMap ∧
                {y | pinv.IsIndeterminacyPoint y}.Finite

/-- Corollary 1 of Main Theorem II (p. 143) for non-singular algebraic `B`-schemes, `B` a field of characteristic zero, whose
dimension satisfies `D`, as a statement.

> **Corollary 1.**  Let `X` be a non-singular algebraic `B`-scheme with a field `B` of characteristic zero.  Let
> `(J₁, J₂, ⋯, J_e)` with `e ≧ 1` be a finite system of coherent sheaves of non-zero ideals on `X`.  Then there exists a finite
> succession of monoidal transformations `f_i : X(i + 1) → X(i)` with non-singular irreducible centers `D(i)`, where
> `0 ≦ i < r` and `X(0) = X`, which has the following property: If `J_j(i + 1)` denotes the weak transform of `J_j(i)` by `f_i`,
> where `1 ≦ j ≦ e`, `0 ≦ i < r`, and `J_j(0) = J_j`, then (1) `ν(J_j(i)_y)` is a positive constant for the points `y` of `D(i)`,
> for every pair `(i, j)`; and (2) for every point `x` of `X(r)`, we have `J_j(r)_x = O_{X(r),x}` for at least one `j`.  (p. 143)

This is the printed statement (`MainTheorem.Ch0.exists_isTrivializing`), restated as a `Prop` so that it can be a hypothesis
of a claim of p. 150; the dimension restriction `D` is added. -/
@[blueprint "def:0.6-cor1-of-dim"
  (statement := /-- Corollary~1 of Main Theorem~II (p.~143) for non-singular algebraic $\mathbf B$-schemes, $\mathbf B$ a field of
    characteristic zero, of dimension satisfying a condition $D$, as a statement (see \cref{cor:0.3-trivialization}). -/)
  (latexEnv := "definition")]
def CorollaryOneOfDim (D : WithBot ℕ∞ → Prop) : Prop :=
  ∀ (B : Type u) [Field B] [CharZero B] (X : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of B)),
    IsAlgebraicSchemeOver pX → X.IsNonsingular → D X.dim → ∀ {e : ℕ}, 1 ≤ e →
    ∀ J : Fin e → Subscheme X, (∀ j x, (J j).stalkIdeal x ≠ ⊥) →
      ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsTrivializing J

/-- "The deduction of (RS) from (LU) is immediate if the following question is answered affirmatively" (p. 148): Question (F)
answered affirmatively implies that (LU) gives (RS).

> The deduction of (RS) from (LU) is immediate if the following question is answered affirmatively: Question (F).  (p. 148)

Stated without argument (p. 148: "immediate"); not proved here.  (The paper names its input, Question (F).) -/
@[blueprint "prop:0.6-RS-from-LU-given-F"
  (statement := /-- If Question (F) has an affirmative answer, then (RS) follows from (LU) ($\mathbf B$ a field of
    characteristic zero, algebraic case): ``The deduction of (RS) from (LU) is immediate if the following question is
    answered affirmatively'' (p.~148). Not proved here: stated without proof. -/)
  (latexEnv := "proposition")]
def RSFromLUGivenF : Prop := QuestionF.{u} → LU.{u} → RS.{u}

/-- "For `dim(X₁) = dim(X₂) = 2`, we have an affirmative answer to question (F)" (p. 149).

> For `dim(X₁) = dim(X₂) = 2`, we have an affirmative answer to question (F), hence, to (F′).  (p. 149)

Argued by the paper from the theorem of footnote 23 ("In fact, it can be easily derived from the following fact", p. 149; see `QuestionFDimTwoFromZariski`); not proved here. -/
@[blueprint "prop:0.6-F-dim-two"
  (statement := /-- For $\dim(X_1)=\dim(X_2)=2$ Question (F) has an affirmative answer. (p.~149.) Not proved here: argued by the paper from the theorem of footnote~23
    (``it can be easily derived from the following fact''). -/)
  (latexEnv := "proposition")]
def QuestionFDimTwo : Prop := QuestionFOfDim.{u} (fun d => d = 2) (fun _ G => IsCompact G)

/-- "For `dim(X₁) = dim(X₂) = 2`, we have an affirmative answer to question (F), hence, to (F′)" (p. 149): the (F′) half.

Argued by the paper ("hence": from the case of (F) in dimension two, `QuestionFDimTwo`, and the remark that (F′) is a special
case of (F), `QuestionFPrimeOfF`); not proved here. -/
@[blueprint "prop:0.6-F-prime-dim-two"
  (statement := /-- For $\dim(X_1)=\dim(X_2)=2$ Question (F$'$) has an affirmative answer, as a consequence of that of (F).
    (p.~149.) Not proved here: argued by the paper (``hence''), from the case of (F) in dimension two and the remark that (F$'$)
    is a special case of (F). -/)
  (latexEnv := "proposition")]
def QuestionFPrimeDimTwo : Prop := QuestionFPrimeOfDim.{u} fun d => d = 2

/-- "(F′) is a special case of (F)" (p. 149): an affirmative answer to (F) (for the dimensions satisfying `D`) gives one
to (F′).

> As a special case of question (F), we ask the following Question (F′).  (p. 149)

Stated without proof; not proved here. -/
@[blueprint "prop:0.6-F-prime-special-case"
  (statement := /-- Question (F$'$) is a special case of Question (F): an affirmative answer to (F) (for pairs of
    dimension satisfying $D$) gives an affirmative answer to (F$'$). (p.~149.) Not proved here: stated without proof. -/)
  (latexEnv := "proposition")]
def QuestionFPrimeOfF : Prop :=
  ∀ D : WithBot ℕ∞ → Prop, QuestionFOfDim.{u} D (fun _ G => IsCompact G) → QuestionFPrimeOfDim.{u} D

/-- "In fact, it can be easily derived from the following fact" (p. 149): the theorem of footnote 23 gives the affirmative
answer to (F) for `dim(X₁) = dim(X₂) = 2`.

> In fact, it can be easily derived from the following fact: Theorem.²³ …  (p. 149)

The claim names its input (the dimension-two theorem): argued by the paper from it; not proved here. -/
@[blueprint "prop:0.6-F-dim-two-from-zariski"
  (statement := /-- The affirmative answer to Question (F) for $\dim(X_1)=\dim(X_2)=2$ can be easily derived from the theorem
    of footnote~23 (every proper modification of non-singular surfaces is obtained by blowing up points). (p.~149.) Not
    proved here: the claim names its input. -/)
  (latexEnv := "proposition")]
def QuestionFDimTwoFromZariski : Prop := ZariskiDimTwo.{u} → QuestionFDimTwo.{u}

/-- "Using this theorem a finite number of times repeatedly, we can deduce (RS) from (LU) in the three-dimensional algebraic
case" (p. 150).

> Using this theorem a finite number of times repeatedly, we can deduce (RS) from (LU) in the three-dimensional algebraic
> case.  (p. 150)

The claim names its input (the dimension-three theorem): argued by the paper from it; not proved here.  Encoding: "(LU)" and "(RS)"
for the schemes of dimension `3`. -/
@[blueprint "prop:0.6-RS-from-LU-dim-three"
  (statement := /-- Using the dimension-three theorem a finite number of times repeatedly, (RS) can be deduced from (LU) in
    the three-dimensional algebraic case. (p.~150.) Not proved here: the claim names its input. -/)
  (latexEnv := "proposition")]
def RSFromLUDimThree : Prop := ZariskiDimThree.{u} → LUOfDim.{u} (fun d => d = 3) → RSOfDim.{u} (fun d => d = 3)

/-- "A better proof of the last theorem can be obtained by taking Corollary 1 of main theorem II with `dim(X) = 3`, instead of
the theorem of B. Levi-Zariski" (p. 150): the dimension-three theorem follows from the dimension-two theorem and Corollary 1
for `dim = 3`.

> A better proof of the last theorem can be obtained by taking Corollary 1 of main theorem II with `dim(X) = 3`, instead of
> the theorem of B. Levi-Zariski.  (p. 150)

The claim names its inputs: argued by the paper from it; not proved here.  Encoding: the rest of Zariski's proof ("by means of the above
theorem", the theorem of footnote 23) is kept, so the hypotheses are the theorem of footnote 23 and Corollary 1 in dimension three. -/
@[blueprint "prop:0.6-dim-three-from-cor1"
  (statement := /-- A better proof of the dimension-three theorem can be obtained by taking Corollary~1 of Main
    Theorem~II with $\dim(X)=3$ instead of the theorem of B.~Levi--Zariski (the theorem of footnote~23 being kept):
    Corollary~1 in dimension $3$ and the dimension-two theorem imply the dimension-three theorem. (p.~150.) Not proved
    here: the claim names its inputs. -/)
  (latexEnv := "proposition")]
def DimThreeFromCorollaryOne : Prop :=
  ZariskiDimTwo.{u} → CorollaryOneOfDim.{u} (fun d => d = 3) → ZariskiDimThree.{u}

/-! ### The readings of (1) and (2) for `G = ℨ` (p. 149) and the patching sentence of p. 150 -/

/-- Condition (1) of Question (F) for one of the two successions: the centers of the succession have no multiple points in
`h_{ij}(G) ∩ f_{ij}⁻¹(U_i)` (the first two lines of `HasFSuccessions`, isolated). -/
@[blueprint "def:0.6-F-condition-one"
  (statement := /-- Condition (1) of Question (F) (p.~149) for a succession $X_{i0}\to\cdots$ of monoidal transformations of
    $X_i$: each center $D_{ij}$ has no multiple points (as a subscheme) at its points contained in $h_{ij}(G)\cap
    f_{ij}^{-1}(U_i)$, where $h_{ij}$ and $f_{ij}$ are the canonical morphisms. -/)
  (latexEnv := "definition")]
def FConditionOne {B : Type u} [CommRing B] {X₁ : Scheme.{u}} {p₁ : X₁ ⟶ Spec (CommRingCat.of B)}
    (Z₁ : ZariskiSpaceData p₁) {Z : LocallyRingedSpace.{u}} (ι₁ : Z ≅ Z₁.Z) (G : Set Z) (U₁ : X₁.Opens)
    {Y₁ : Scheme.{u}} (s₁ : MonoidalSuccession X₁ Y₁) : Prop :=
  s₁.AllStages (fun W D c => ∃ k : Z ⟶ W.toLocallyRingedSpace,
    Z₁.IsCanonicalVia ι₁ (c ≫ p₁) c.toRationalMap k ∧
      ∀ y ∈ D.pts, y ∈ k.base '' G → c y ∈ U₁ → D.IsSimpleAt y) (𝟙 X₁)

/-- Condition (2) of Question (F) for the morphisms `g_i : X_i′ → X_i` (the last conjunct of `HasFSuccessions`, isolated). -/
@[blueprint "def:0.6-F-condition-two"
  (statement := /-- Condition (2) of Question (F) (p.~149): for every $z\in G$ with $h_i(z)\in U_i$ ($i=1,2$), the canonical
    rational application $f'\colon X_1'\dashrightarrow X_2'$ is defined at $h_1'(z)$ as well as $f'^{-1}$ at $h_2'(z)$,
    $h_i'\colon\mathfrak Z\to X_i'$ the canonical morphisms. -/)
  (latexEnv := "definition")]
def FConditionTwo {B : Type u} [CommRing B] {X₁ X₂ : Scheme.{u}} {p₁ : X₁ ⟶ Spec (CommRingCat.of B)}
    {p₂ : X₂ ⟶ Spec (CommRingCat.of B)} (f : X₁ ⤏ X₂) {Z : LocallyRingedSpace.{u}} (Z₁ : ZariskiSpaceData p₁)
    (Z₂ : ZariskiSpaceData p₂) (ι₁ : Z ≅ Z₁.Z) (ι₂ : Z ≅ Z₂.Z) (G : Set Z) (U₁ : X₁.Opens) (U₂ : X₂.Opens)
    (h₁ : Z ⟶ X₁.toLocallyRingedSpace) (h₂ : Z ⟶ X₂.toLocallyRingedSpace) {Y₁ Y₂ : Scheme.{u}} (g₁ : Y₁ ⟶ X₁)
    (g₂ : Y₂ ⟶ X₂) : Prop :=
  ∃ (f' : Y₁ ⤏ Y₂) (f'inv : Y₂ ⤏ Y₁) (h₁' : Z ⟶ Y₁.toLocallyRingedSpace) (h₂' : Z ⟶ Y₂.toLocallyRingedSpace),
    IsCanonicalApplication g₁ g₂ f f' ∧ Scheme.RationalMap.IsInverseOf f'inv f' ∧
    Z₁.IsCanonicalVia ι₁ (g₁ ≫ p₁) g₁.toRationalMap h₁' ∧ Z₂.IsCanonicalVia ι₂ (g₂ ≫ p₂) g₂.toRationalMap h₂' ∧
    ∀ z ∈ G, h₁.base z ∈ U₁ → h₂.base z ∈ U₂ → h₁'.base z ∈ f'.domain ∧ h₂'.base z ∈ f'inv.domain

/-- The two open subschemes `W₁ ⊆ Y₁`, `W₂ ⊆ Y₂` *patch together* along the rational application `f'`, with extra
property `R` of the patched scheme (pp. 149-150).

> (2) says that `X₁′ | g₁⁻¹(U₁)` and `X₂′ | g₂⁻¹(U₂)` patch together and make a non-singular algebraic `B`-scheme `X′` with
> canonical morphisms to `X₁` and `X₂` which are both proper modifications.  (p. 149)

Formalization note (encoding; existence-style reading of "patch together"): there are a non-singular algebraic `B`-scheme
`X′`, open immersions `a_i` of the two open subschemes into `X′` which cover `X′`, and morphisms `q_i : X′ → X_i` over `B`
which are proper modifications with `q_i ∘ a_i = g_i` on `W_i` (the extra property `R` receives `X′`, its structure morphism, `a₁`, `a₂`, `q₁`, `q₂`); "patch together along `f′`" is that on the overlap
`a₁⁻¹(a₂(W₂))` of `W₁` the open immersions are related by a morphism into `W₂` whose class is the restriction of `f′`.  No gluing
is constructed. -/
@[blueprint "def:0.6-patches-together"
  (statement := /-- Open subschemes $W_1\subseteq Y_1$, $W_2\subseteq Y_2$ \emph{patch together} along $f'\colon
    Y_1\dashrightarrow Y_2$ (and make a scheme with property $R$): there are a non-singular algebraic $\mathbf B$-scheme $X'$,
    open immersions of $W_1$ and $W_2$ into $X'$ which cover it and are related on the overlap by (the restriction of) $f'$,
    and morphisms $q_i\colon X'\to X_i$ over $\mathbf B$ which are proper modifications and restrict to $g_i$ on $W_i$
    (pp.~149--150). Formalization note (encoding): existence; no gluing is constructed. -/)
  (latexEnv := "definition")]
def PatchesTogetherWith {B : Type u} [CommRing B] {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (p₁ : X₁ ⟶ Spec (CommRingCat.of B))
    (p₂ : X₂ ⟶ Spec (CommRingCat.of B)) (g₁ : Y₁ ⟶ X₁) (g₂ : Y₂ ⟶ X₂) (W₁ : Y₁.Opens) (W₂ : Y₂.Opens) (f' : Y₁ ⤏ Y₂)
    (R : ∀ X' : Scheme.{u}, (X' ⟶ Spec (CommRingCat.of B)) → (W₁.toScheme ⟶ X') → (W₂.toScheme ⟶ X') →
      (X' ⟶ X₁) → (X' ⟶ X₂) → Prop) : Prop :=
  ∃ (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of B)) (a₁ : W₁.toScheme ⟶ X') (a₂ : W₂.toScheme ⟶ X')
    (q₁ : X' ⟶ X₁) (q₂ : X' ⟶ X₂),
    IsAlgebraicSchemeOver p' ∧ X'.IsNonsingular ∧
    ∃ (_ : IsOpenImmersion a₁) (_ : IsOpenImmersion a₂), Set.range a₁ ∪ Set.range a₂ = Set.univ ∧
    (∃ φ : (a₁ ⁻¹ᵁ a₂.opensRange).toScheme ⟶ W₂.toScheme,
      φ ≫ a₂ = (a₁ ⁻¹ᵁ a₂.opensRange).ι ≫ a₁ ∧
      (φ ≫ W₂.ι).toRationalMap =
        f'.precomp ((a₁ ⁻¹ᵁ a₂.opensRange).ι ≫ W₁.ι) (Scheme.Hom.PreimageDense.of_isOpenImmersion _)) ∧
    a₁ ≫ q₁ = W₁.ι ≫ g₁ ∧ a₂ ≫ q₂ = W₂.ι ≫ g₂ ∧ q₁ ≫ p₁ = p' ∧ q₂ ≫ p₂ = p' ∧
    q₁.toRationalMap.IsProperModification p' p₁ ∧ q₂.toRationalMap.IsProperModification p' p₂ ∧ R X' p' a₁ a₂ q₁ q₂

/-- **The readings of (1) and (2) of Question (F) in the case `G = ℨ`** (p. 149).

> In this case, (1) says that the morphisms `g_i : X_i′ → X_i` induce `X_i′ | g_i⁻¹(U_i) → X_i | U_i` which are obtained by
> finite successions of monoidal transformations with non-singular and nowhere dense centers, and (2) says that
> `X₁′ | g₁⁻¹(U₁)` and `X₂′ | g₂⁻¹(U₂)` patch together and make a non-singular algebraic `B`-scheme `X′` with canonical
> morphisms to `X₁` and `X₂` which are both proper modifications.  (p. 149)

Stated without proof (p. 149: "says"); not proved here.  Formalization note (encoding): the setting is that of Question (F) with `G`
the whole of `ℨ` (`QuestionFWhole`); the restriction of a succession to the open `U_i` is its base change along the open
immersion (`MonoidalSuccession.baseChangeSucc`), whose target is `X_i′ ×_{X_i} U_i = g_i⁻¹(U_i)`; reading (1) is the equivalence of
condition (1) of (F) with "the base-changed succession has non-singular and nowhere dense centers"; reading (2) is the equivalence of
condition (2) of (F), under condition (1) for both successions, with the existence of the canonical rational application `f′` along
which `X₁′|g₁⁻¹(U₁)` and `X₂′|g₂⁻¹(U₂)` patch together (`PatchesTogetherWith`), the patching being pinned by
`a_i(g_i⁻¹(U_i)) = q_i⁻¹(U_i)` (the images of the two open subschemes are the preimages of the `U_i`).  Both are read as equivalences
("says").  Condition (1) of (F), as in `HasFSuccessions`, contains the existence of the canonical morphisms `h_{ij}`; so reading (1)
also asserts that they exist, and that `h_{ij}` is surjective for `G = ℨ`; the nowhere-density on the right-hand side is automatic. -/
@[blueprint "prop:0.6-F-whole-readings"
  (statement := /-- In Question (F) with $G$ the underlying space of $\mathfrak Z$: (1) holds for a succession with nowhere
    dense centers iff the induced morphism $X_i'|g_i^{-1}(U_i)\to X_i|U_i$ is obtained by a finite succession of monoidal
    transformations with non-singular and nowhere dense centers (the base change of the succession to $U_i$); (2) holds iff
    $X_1'|g_1^{-1}(U_1)$ and $X_2'|g_2^{-1}(U_2)$ patch together (their images in $X'$ being the preimages of $U_1$, $U_2$)
    and make a non-singular algebraic $\mathbf B$-scheme $X'$ with canonical morphisms to $X_1$, $X_2$ which are both proper
    modifications. (p.~149.) Not proved here: stated without
    proof. Formalization note (encoding): equivalences; existence-style patching. -/)
  (latexEnv := "proposition")]
def FWholeReadings : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (X₁ X₂ : Scheme.{u}) (p₁ : X₁ ⟶ Spec (CommRingCat.of B))
    (p₂ : X₂ ⟶ Spec (CommRingCat.of B)), IsReducedAlgebraicBScheme p₁ → IsReducedAlgebraicBScheme p₂ →
    ∀ f : X₁ ⤏ X₂, f.IsProperModification p₁ p₂ →
    ∀ (Z : LocallyRingedSpace.{u}) (Z₁ : ZariskiSpaceData p₁) (Z₂ : ZariskiSpaceData p₂)
      (ι₁ : Z ≅ Z₁.Z) (ι₂ : Z ≅ Z₂.Z), ZariskiIdentified f Z₁ Z₂ ι₁ ι₂ → IsCompact (Set.univ : Set Z) →
    ∀ (U₁ : X₁.Opens) (U₂ : X₂.Opens), U₁.toScheme.IsNonsingular → U₂.toScheme.IsNonsingular →
    ∀ (h₁ : Z ⟶ X₁.toLocallyRingedSpace) (h₂ : Z ⟶ X₂.toLocallyRingedSpace),
      Z₁.IsCanonicalVia ι₁ p₁ (Scheme.RationalMap.id X₁) h₁ → Z₂.IsCanonicalVia ι₂ p₂ (Scheme.RationalMap.id X₂) h₂ →
      Set.univ ⊆ h₁.base ⁻¹' (U₁ : Set X₁) ∪ h₂.base ⁻¹' (U₂ : Set X₂) →
      ∀ (Y₁ Y₂ : Scheme.{u}) (s₁ : MonoidalSuccession X₁ Y₁) (s₂ : MonoidalSuccession X₂ Y₂),
        s₁.NowhereDenseCenters → s₂.NowhereDenseCenters →
        ((FConditionOne Z₁ ι₁ Set.univ U₁ s₁ ↔
            ((s₁.baseChangeSucc U₁.ι).HasNonsingularCenters ∧ (s₁.baseChangeSucc U₁.ι).NowhereDenseCenters)) ∧
          (FConditionOne Z₂ ι₂ Set.univ U₂ s₂ ↔
            ((s₂.baseChangeSucc U₂.ι).HasNonsingularCenters ∧ (s₂.baseChangeSucc U₂.ι).NowhereDenseCenters))) ∧
        (FConditionOne Z₁ ι₁ Set.univ U₁ s₁ → FConditionOne Z₂ ι₂ Set.univ U₂ s₂ →
          (FConditionTwo f Z₁ Z₂ ι₁ ι₂ Set.univ U₁ U₂ h₁ h₂ s₁.composite s₂.composite ↔
            ∃ f' : Y₁ ⤏ Y₂, IsCanonicalApplication s₁.composite s₂.composite f f' ∧
              PatchesTogetherWith p₁ p₂ s₁.composite s₂.composite (s₁.composite ⁻¹ᵁ U₁) (s₂.composite ⁻¹ᵁ U₂) f'
                (fun _ _ a₁ a₂ q₁ q₂ => Set.range a₁ = q₁ ⁻¹' (U₁ : Set X₁) ∧ Set.range a₂ = q₂ ⁻¹' (U₂ : Set X₂))))

/-- The conclusion (1)-(3) of the dimension-three theorem for explicit data (`ZariskiDimThree`, isolated): `Y_i`, `g_i`, the canonical
morphisms `h_i′`, the open sets `V_i′`, the canonical rational application `f′`, the canonical modification `p` and its inverse. -/
@[blueprint "def:0.6-dim-three-conclusion"
  (statement := /-- The properties (1)--(3) of the dimension-three theorem (pp.~149--150) for given modifications
    $g_i\colon X_i'\to X_i$, canonical morphisms $h_i'$, sets $V_i'$, canonical modification $p\colon X_1'|V_1'\to X_2'|V_2'$
    and its inverse. -/)
  (latexEnv := "definition")]
def DimThreeConclusion {B : Type u} [CommRing B] {X₁ X₂ : Scheme.{u}} {p₁ : X₁ ⟶ Spec (CommRingCat.of B)}
    {p₂ : X₂ ⟶ Spec (CommRingCat.of B)} (f : X₁ ⤏ X₂) {Z : LocallyRingedSpace.{u}} (Z₁ : ZariskiSpaceData p₁)
    (Z₂ : ZariskiSpaceData p₂) (ι₁ : Z ≅ Z₁.Z) (ι₂ : Z ≅ Z₂.Z) (U₁ : X₁.Opens) (U₂ : X₂.Opens)
    (h₁ : Z ⟶ X₁.toLocallyRingedSpace) (h₂ : Z ⟶ X₂.toLocallyRingedSpace) {Y₁ Y₂ : Scheme.{u}}
    (p₁' : Y₁ ⟶ Spec (CommRingCat.of B)) (p₂' : Y₂ ⟶ Spec (CommRingCat.of B)) (g₁ : Y₁ ⟶ X₁) (g₂ : Y₂ ⟶ X₂)
    (h₁' : Z ⟶ Y₁.toLocallyRingedSpace) (h₂' : Z ⟶ Y₂.toLocallyRingedSpace) (V₁ : Y₁.Opens) (V₂ : Y₂.Opens)
    (f' : Y₁ ⤏ Y₂) (p : V₁.toScheme ⟶ V₂.toScheme) (pinv : V₂.toScheme ⤏ V₁.toScheme) : Prop :=
  IsReducedAlgebraicBScheme p₁' ∧ IsReducedAlgebraicBScheme p₂' ∧ g₁ ≫ p₁ = p₁' ∧ g₂ ≫ p₂ = p₂' ∧
  g₁.toRationalMap.IsModification ∧ g₂.toRationalMap.IsModification ∧
  IsProperMorphism g₁ ∧ IsProperMorphism g₂ ∧
  Z₁.IsCanonicalVia ι₁ p₁' g₁.toRationalMap h₁' ∧ Z₂.IsCanonicalVia ι₂ p₂' g₂.toRationalMap h₂' ∧
  (∃ s : MonoidalSuccession U₁.toScheme (g₁ ⁻¹ᵁ U₁).toScheme,
    s.HasNonsingularCenters ∧ s.composite = g₁ ∣_ U₁) ∧
  (∃ s : MonoidalSuccession U₂.toScheme (g₂ ⁻¹ᵁ U₂).toScheme,
    s.HasNonsingularCenters ∧ s.composite = g₂ ∣_ U₂) ∧
  (V₁ : Set Y₁) = h₁'.base '' (h₁.base ⁻¹' (U₁ : Set X₁) ∩ h₂.base ⁻¹' (U₂ : Set X₂)) ∧
  (V₂ : Set Y₂) = h₂'.base '' (h₁.base ⁻¹' (U₁ : Set X₁) ∩ h₂.base ⁻¹' (U₂ : Set X₂)) ∧
  V₁ ≤ g₁ ⁻¹ᵁ U₁ ∧ V₂ ≤ g₂ ⁻¹ᵁ U₂ ∧ IsCanonicalApplication g₁ g₂ f f' ∧ IsProperMorphism p ∧
  (p ≫ V₂.ι).toRationalMap = f'.precomp V₁.ι (Scheme.Hom.PreimageDense.of_isOpenImmersion _) ∧
  Scheme.RationalMap.IsInverseOf pinv p.toRationalMap ∧ {y | pinv.IsIndeterminacyPoint y}.Finite

/-- **The patching sentence after the dimension-three theorem** (p. 150).

> Let `U₂″` be the complement of the points of indeterminacy of `p⁻¹` in `U₂′`.  Then we see that `X₁′ | U₁′` and `X₂′ | U₂″` patch
> together by means of `p⁻¹` and give rise to a non-singular algebraic `B`-scheme whose Zariski space is canonically identified with
> the restriction of `ℨ(X₁) = ℨ(X₂)` to the open subset consisting of those points which are mapped either to a simple point of
> `X₁` or (and) to a simple point of `X₂`.  (p. 150)

Stated without proof ("Then we see that"); not proved here.  Formalization note (encoding): for data satisfying (1)-(3)
(`DimThreeConclusion`), `U₂″` is an open subset of `Y₂` whose points are those of `g₂⁻¹(U₂)` outside the image of the finite set of
points of indeterminacy of `p⁻¹` (that it is open is part of the claim); "patch together by means of `p⁻¹`" is
`PatchesTogetherWith` along the canonical rational application `f′` (the inverse of which restricts to `p⁻¹`); the Zariski space of
the patched scheme is identified by existence: a Zariski space datum with the property (ii) of the patched scheme and an
isomorphism from the restriction of `ℨ` to the open subset `h₁⁻¹(U₁) ∪ h₂⁻¹(U₂)` of `ℨ` compatible with the canonical morphisms
to `X₁` and `X₂` (`CompAgrees` with the morphisms `q_i`). -/
@[blueprint "prop:0.6-dim-three-patching"
  (statement := /-- In the situation of the dimension-three theorem, let $U_2''$ be the complement of the points of
    indeterminacy of $p^{-1}$ in $U_2'$. Then $X_1'|U_1'$ and $X_2'|U_2''$ patch together by means of $p^{-1}$ and give rise
    to a non-singular algebraic $\mathbf B$-scheme whose Zariski space is canonically identified with the restriction of
    $\mathfrak Z(X_1)=\mathfrak Z(X_2)$ to the open subset of the points mapped either to a simple point of $X_1$ or (and) to a
    simple point of $X_2$. (p.~150.) Not proved here: stated without proof. Formalization note (encoding): existence-style
    patching and identification. -/)
  (latexEnv := "proposition")]
def DimThreePatching : Prop :=
  ∀ (B : Type u) [Field B] [CharZero B] (X₁ X₂ : Scheme.{u}) (p₁ : X₁ ⟶ Spec (CommRingCat.of B))
    (p₂ : X₂ ⟶ Spec (CommRingCat.of B)), IsReducedAlgebraicBScheme p₁ → IsReducedAlgebraicBScheme p₂ →
    X₁.dim = 3 → X₂.dim = 3 → ∀ f : X₁ ⤏ X₂, f.IsProperModification p₁ p₂ →
    ∀ (Z : LocallyRingedSpace.{u}) (Z₁ : ZariskiSpaceData p₁) (Z₂ : ZariskiSpaceData p₂)
      (ι₁ : Z ≅ Z₁.Z) (ι₂ : Z ≅ Z₂.Z), ZariskiIdentified f Z₁ Z₂ ι₁ ι₂ →
    ∀ (U₁ : X₁.Opens) (U₂ : X₂.Opens), (∀ x, x ∈ U₁ ↔ X₁.IsSimpleAt x) → (∀ x, x ∈ U₂ ↔ X₂.IsSimpleAt x) →
    ∀ (h₁ : Z ⟶ X₁.toLocallyRingedSpace) (h₂ : Z ⟶ X₂.toLocallyRingedSpace),
      Z₁.IsCanonicalVia ι₁ p₁ (Scheme.RationalMap.id X₁) h₁ → Z₂.IsCanonicalVia ι₂ p₂ (Scheme.RationalMap.id X₂) h₂ →
    ∀ (Y₁ Y₂ : Scheme.{u}) (p₁' : Y₁ ⟶ Spec (CommRingCat.of B)) (p₂' : Y₂ ⟶ Spec (CommRingCat.of B))
      (g₁ : Y₁ ⟶ X₁) (g₂ : Y₂ ⟶ X₂) (h₁' : Z ⟶ Y₁.toLocallyRingedSpace) (h₂' : Z ⟶ Y₂.toLocallyRingedSpace)
      (V₁ : Y₁.Opens) (V₂ : Y₂.Opens) (f' : Y₁ ⤏ Y₂) (p : V₁.toScheme ⟶ V₂.toScheme)
      (pinv : V₂.toScheme ⤏ V₁.toScheme),
      DimThreeConclusion f Z₁ Z₂ ι₁ ι₂ U₁ U₂ h₁ h₂ p₁' p₂' g₁ g₂ h₁' h₂' V₁ V₂ f' p pinv →
      ∃ U₂'' : Y₂.Opens, (U₂'' : Set Y₂) = (g₂ ⁻¹ᵁ U₂ : Set Y₂) \ V₂.ι '' {y | pinv.IsIndeterminacyPoint y} ∧
        PatchesTogetherWith p₁ p₂ g₁ g₂ (g₁ ⁻¹ᵁ U₁) U₂'' f'
          (fun X' p' _ _ q₁ q₂ => ∃ (S : TopologicalSpace.Opens Z) (Zd : ZariskiSpaceData p')
            (ι' : Z.restrict S.isOpenEmbedding ≅ Zd.Z),
            (S : Set Z) = h₁.base ⁻¹' (U₁ : Set X₁) ∪ h₂.base ⁻¹' (U₂ : Set X₂) ∧ Zd.IsUniversal ∧
            ∀ k : Zd.Z ⟶ X'.toLocallyRingedSpace, Zd.IsCanonicalFor p' (Scheme.RationalMap.id X') k →
              q₁.toRationalMap.CompAgrees (ι'.hom ≫ k) (Z.ofRestrict S.isOpenEmbedding ≫ h₁) ∧
              q₂.toRationalMap.CompAgrees (ι'.hom ≫ k) (Z.ofRestrict S.isOpenEmbedding ≫ h₂))

end Hironaka
