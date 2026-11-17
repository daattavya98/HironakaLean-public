/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.Defs
public import Architect

/-!
# Ch. 0 §1 (pp. 117–119): generalities on schemes, algebraic part

The algebraic definitions of §1 are Mathlib's; this module records how each is encoded and adds the two
definitions Mathlib has no single notion for (algebraic `B`-preschemes and `B`-schemes, over a scheme base).  The
analytic part of §1 (analytic K-spaces, preanalytic spaces, complexification, Stein spaces, analytic K-covers) is
not formalized.

> A local-ringed space X is by definition a pair of a topological space X and a sheaf of local rings (i.e., sheaf
> of rings whose stalks are local rings) O_X on X which is often referred to as the structural sheaf of X. A
> morphism of local-ringed spaces f: X → Y, where X = (X, O_X) and Y = (Y, O_Y), is by definition a pair of a
> continuous mapping f: X → Y and an f-homomorphism θ: O_Y → O_X which induces for each point x of X a local
> homomorphism θ_x: O_{Y,f(x)} → O_{X,x}, ‘local’ in the sense that it maps the maximal ideal of the first local
> ring into that of the second. (p. 117)

## Dictionary (paper → Mathlib; no new Lean unless stated)

* local-ringed space, morphism, the category `ℛ` (p. 117): `LocallyRingedSpace` and its morphisms (a continuous
  map with a map of structure sheaves whose stalk maps are local).
* `Spec(A)`, prescheme, the category `pre-𝔖` (p. 117): `Scheme.Spec` and `Scheme` (Mathlib's schemes are exactly the
  paper's preschemes, a locally ringed space locally isomorphic to a `Spec`); `pre-𝔖` is a full subcategory of `ℛ`
  (a morphism of `Scheme` is a morphism of locally ringed spaces).
* `S`-prescheme `(X, p)`, the category `pre-𝔖/S`, `S`-morphisms (p. 118): `X ⟶ S` and `Over S`.
* product `X₁ ×_S X₂`, the projections and the canonical bijection `Hom(Q, P) ≃ Hom(Q, F₁) × Hom(Q, F₂)` (p. 118):
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift` (the universal property).
* the diagonal morphism and "this diagonal morphism is an immersion" (p. 118, "In particular ... This diagonal
  morphism is an immersion"): `pullback.diagonal` and the instance `IsImmersion (pullback.diagonal f)`.
* `S`-scheme (the diagonal is a closed subscheme, p. 118): `IsSeparated`.  A *scheme* of the paper is a
  `Spec ℤ`-scheme, i.e. a separated Mathlib scheme (`IsSeparated (terminal.from X)`, `Spec ℤ` is terminal:
  `specZIsTerminal`); so Mathlib's `Scheme` is the paper's *prescheme* (not the paper's scheme).
* "It can be proved that every affine scheme is a scheme, and that if S is a scheme and (X, p) is an S-scheme, then X
  is a scheme" (p. 118): Mathlib's `IsSeparated.of_isAffineHom` and the stability of `IsSeparated` under composition
  (`IsSeparated` is stable under composition).  These, like the fibre-product and diagonal facts above, are cited
  (blanket footnote 6: "cf. Ch. I of Grothendieck [6]"); no Lean statement.
* `B`-prescheme, `B`-scheme, `B`-morphism (p. 118): `X ⟶ Spec B` with `IsSeparated`.
* "of finite type over `Spec B`": `LocallyOfFiniteType` and `QuasiCompact` (the paper's "obtained by patching
  together a finite number of open affine subschemes `Spec A` with `B`-algebras `A` of finite type", p. 119).
* `ℛ/S`, `S`-local-ringed space, `S`-morphism, `B`-local-ringed space (p. 119): `Over S` for locally ringed spaces
  (see `Hironaka/Ch0/BlowingUpModules.lean`).
* "simple", "multiple", "non-singular" (p. 121, stated there for preanalytic spaces and said to "make sense for arbitrary
  local-ringed spaces"): the project's `Scheme.IsSimpleAt` and `Scheme.IsNonsingular` (`Hironaka/Statements.lean`: the local
  ring is regular), for schemes only; the generality of arbitrary local-ringed spaces is not formalized (not needed).  The
  Jacobian-criterion remark that follows is about analytic spaces and is not formalized.

## The structure sheaf of `Spec(A)` (p. 117)

> ... and O_S is the sheaf of localizations of A on S (i.e., for every open subset U of S, Γ(U, O_S) = A_{T(U)} where
> T(U) denotes the multiplicative set of those elements in A which are not contained in any prime ideal in U). (p. 117)

Read literally, the formula `Γ(U, O_S) = A_{T(U)}` for *every* open `U` is false (it holds for the basic opens `D(f)`).  The
statement as printed is recorded as `SpecSectionsAsPrinted` below, marked as false with its counterexample.  Mathlib's `Spec`
(the correct structure sheaf) is used throughout, so nothing depends on the slip.

## Misprints of the source

p. 119 (not quoted here): "prechemes"; and `p₁ = f∘p₂` for `p₁ = p₂∘f` in the definition of an `S`-morphism (the composite `f ∘ p₂` is not
defined; p. 118 has the correct `p₁ = p₂∘g`).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Hironaka

universe u

/-- `p : X ⟶ Spec B` makes `X` an algebraic `B`-prescheme, `B` a noetherian ring: `p` is of finite type.

> We shall be particularly interested in B-schemes where B is a noetherian ring. Assuming this, a B-prescheme (or,
> B-scheme) is said to be algebraic if it is of finite type over Spec(B) (i.e., the structural morphism of the
> B-prescheme to Spec(B) is of finite type). (pp. 118–119)

Definition (pp. 118–119).  Formalization note (encoding): "of finite type" is `LocallyOfFiniteType` and
`QuasiCompact`, as in the other statements of Ch. 0; this is the same as the inline encoding used there, for a
scheme `X` over `Spec B`.  See `Hironaka/Ch0/BlowingUpModules.lean` for the version for locally ringed spaces. -/
@[blueprint "def:0.S1-algebraic-b-prescheme"
  (statement := /-- We shall be particularly interested in $\mathbf B$-schemes where $\mathbf B$ is a noetherian ring.
    Assuming this, a $\mathbf B$-prescheme (or, $\mathbf B$-scheme) is said to be \emph{algebraic} if it is of finite type
    over $\operatorname{Spec}(\mathbf B)$. (pp.~118--119.) Formalization note (encoding): a morphism of finite type is a
    morphism that is locally of finite type and quasi-compact. -/)
  (latexEnv := "definition")]
def IsAlgebraicPreschemeOver {X : Scheme.{u}} {B : Type u} [CommRing B]
    (p : X ⟶ Spec (CommRingCat.of B)) : Prop :=
  IsNoetherianRing B ∧ LocallyOfFiniteType p ∧ QuasiCompact p

/-- `p : X ⟶ Spec B` makes `X` an algebraic `B`-scheme, `B` a noetherian ring: an algebraic `B`-prescheme whose
diagonal is a closed subscheme (`p` is separated).  Definition (pp. 118–119), see `IsAlgebraicPreschemeOver`.

Formalization note (encoding): the paper's schemes are separated (p. 118), and the algebraic `B`-schemes of the Ch. 0
statements are `[LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]`, which is this definition when `B` is
noetherian (for a field `B`, always). -/
@[blueprint "def:0.S1-algebraic-b-scheme"
  (statement := /-- An algebraic $\mathbf B$-scheme is an algebraic $\mathbf B$-prescheme (\textbf B noetherian) which is
    a $\mathbf B$-scheme: the diagonal of $X\times_{\operatorname{Spec}\mathbf B}X$ is a closed subscheme.
    (pp.~118--119.) Formalization note (encoding): a separated morphism of finite type to $\operatorname{Spec}\mathbf B$. -/)
  (latexEnv := "definition")]
def IsAlgebraicSchemeOver {X : Scheme.{u}} {B : Type u} [CommRing B]
    (p : X ⟶ Spec (CommRingCat.of B)) : Prop :=
  IsAlgebraicPreschemeOver p ∧ IsSeparated p

/-- The multiplicative set `T(U)` of p. 117: the elements of `A` not contained in any prime ideal in `U`. -/
def unitsOutsideOpen (A : Type u) [CommRing A] (U : TopologicalSpace.Opens (PrimeSpectrum A)) :
    Submonoid A where
  carrier := {a | ∀ p ∈ U, a ∉ p.asIdeal}
  one_mem' p _ h := p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  mul_mem' {a b} ha hb p hp h := by
    rcases p.isPrime.mem_or_mem h with h | h
    · exact ha p hp h
    · exact hb p hp h

/-- Statement as printed (false): for every commutative ring `A` and every open subset `U` of `Spec A`,
`Γ(U, O_{Spec A}) = A_{T(U)}`, i.e. the canonical map `A_{T(U)} → Γ(U, O_{Spec A})` is bijective.

> ... O_S is the sheaf of localizations of A on S (i.e., for every open subset U of S, Γ(U, O_S) = A_{T(U)} where T(U)
> denotes the multiplicative set of those elements in A which are not contained in any prime ideal in U). (p. 117)

This statement as printed is **false**; it holds for the basic opens `U = D(f)` (`T(U)` is then the set of elements
whose zero set lies in `V(f)`, and `A_{T(U)} = A_f`) but not for every open `U`.  Counterexample (checked by hand, not
formalized): `A = k[s, t, u, v]/(su − tv) ≅ k[ac, ad, bd, bc] ⊂ k[a, b, c, d]`, `U = D(s) ∪ D(t)`.  Then `T(U)` is the set
of non-zero constants (an element outside every prime of `U` has `V(f) ⊆ V(s, t)`, and the only height-one prime containing
`s` and `t` is `P = (s, t)`, which generates the class group `ℤ` of `A`; concretely `f` divides `a^n` in
`k[a, b, c, d]` and lies in `A`, so it is constant), hence `A_{T(U)} = A`; but the section `b/a = v/s = u/t` of the structure
sheaf over `U` is not in `A`.  So the canonical map `A → Γ(U, O)` is not surjective.

Formalization note (encoding): "the canonical map `A_{T(U)} → Γ(U, O_{Spec A})` is bijective" is stated as `Γ(U, O)` being
a localization of `A` at `T(U)` for the canonical map `A ≅ Γ(Spec A, ⊤) → Γ(Spec A, U)` (`IsLocalization`), with Mathlib's `Spec`.  No Lean disproof (the statement is recorded, not a claim to prove). -/
@[blueprint "def:0.S1-spec-sections-as-printed"
  (statement := /-- \textbf{Statement as printed (false).} For every commutative ring $A$ and every open subset $U$ of
    $\operatorname{Spec}(A)$, $\Gamma(U,O_S)=A_{T(U)}$ where $T(U)$ denotes the multiplicative set of those elements in
    $A$ which are not contained in any prime ideal in $U$. (p.~117.) This is false for non-basic open sets (it holds for
    $U=D(f)$). Counterexample: $A=k[s,t,u,v]/(su-tv)\cong k[ac,ad,bd,bc]\subset k[a,b,c,d]$, $U=D(s)\cup D(t)$: $T(U)$ is
    the set of non-zero constants (the only height-one prime containing $s$ and $t$ is $P=(s,t)$, which generates the
    class group $\mathbb Z$), so $A_{T(U)}=A$, but $b/a=v/s=u/t$ is a section over $U$ not in $A$. Formalization note
    (encoding): the canonical map $A\to\Gamma(U,O)$ is a localization at $T(U)$. -/)
  (latexEnv := "proposition")]
def SpecSectionsAsPrinted : Prop :=
  ∀ (A : Type u) [CommRing A] (U : (Spec (CommRingCat.of A)).Opens),
    letI : Algebra A Γ(Spec (CommRingCat.of A), U) :=
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.map (homOfLE le_top).op).hom.toAlgebra
    IsLocalization (unitsOutsideOpen A U) Γ(Spec (CommRingCat.of A), U)

end Hironaka
