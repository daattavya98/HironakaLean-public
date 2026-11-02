/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Architect
public import Hironaka.Ch0.AlgebraicScheme
public import Hironaka.Ch0.Blowup
public import Hironaka.Ch0.RationalApplication
public import Hironaka.Compat.PrimitiveIdeal
public import Hironaka.Compat.RationalMapPrecomp
public import Hironaka.Statements

/-!
# Ch. 0 §5 (p. 141): the fact (*), on which the elimination of points of indeterminacy rests

> (*) Let `f` be a rational application of a non-singular algebraic `B`-scheme `X` to another algebraic `B`-scheme `Y`.
> We assume that `f` is proper.  Then there exists a finite system of coherent sheaves of ideals `≠ (0)`, say `J₁, J₂, …,
> J_d`, on `X`, such that: If `h : X' → X` is any morphism of a non-singular algebraic `B`-scheme `X'` to `X`, and if we
> can write `J'ᵢPᵢ = h⁻¹(Jᵢ)` for each `i` where `Pᵢ` is an invertible sheaf of ideals on `X'` and `J'ᵢ` is a sheaf of
> ideals `≠ (0)` on `X'` which is not divisible by any invertible sheaf of ideals (except `O_{X'}`), then the domain of
> definition of the composition `f ∘ h` is exactly equal to the set of those points `x` of `X'` at which `J'ᵢ,ₓ = O_{X',x}`
> for at least one `i`.  (p. 141, introduced by "In this respect, we note the following fact")

The paper gives neither a proof nor a reference: "(*)" is used without proof or citation, and it is assumed, as in the
paper: a cited leaf.  It is not elementary.  When the morphism of the graph of `f` to `X` is a monoidal transformation of
`X`, it holds with `d = 1` (the paper's remark after (*)), by the universal property of the monoidal transformation.  When
it is not (p. 140: "this possibility is seen by simple examples"), "exactly equal" requires a Chow-type theorem for proper
birational morphisms: every point of the graph has a monoidal transformation of `X` that dominates the graph and is an
isomorphism near that point.  That theorem is neither proved nor cited by the paper, and (*) is assumed here exactly as
the paper assumes it.  (*) is true: a proof by hand (not formalized) applies Chow's lemma in the form of Raynaud–Gruson
(Invent. Math. 13 (1971); Stacks Project, Tag 088R), which the paper does not cite, to an affine neighbourhood of each
point of the graph, and shows, as in Hartshorne II.7.17 but with the local factoriality of `X` in place of an ample sheaf,
that the resulting projective birational morphism to `X` is a monoidal transformation of `X`.

Encodings (none changes the meaning of the printed statement):
* "scheme" is "separated": "If the diagonal of `X ×_S X` is a closed subscheme, then the `S`-prescheme `(X, p)` is called
  an `S`-scheme." (p. 118); the algebraic `B`-schemes are the `B`-schemes (so separated) of finite type (p. 118, 162);
* "the composition `f ∘ h`" exists when `h` has dense preimages (`Scheme.Hom.PreimageDense`, p. 139: "`f⁻¹(V)` is open
  and dense for every open dense subset `V`"), which the statement tacitly assumes;
* "coherent sheaves of ideals `≠ (0)`" are the `Subscheme`s with non-zero stalks at every point (as in Corollary 1);
* "not divisible by any invertible sheaf of ideals" is `Subscheme.IsPrimitive` (`Hironaka/Compat/PrimitiveIdeal.lean`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Hironaka

namespace RationalApplication


/-- **(\*) of p. 141** (cited leaf, used without proof or citation in the paper; assumed, as in the paper).

Let `f` be a proper rational application of a non-singular algebraic `B`-scheme `X` to an algebraic `B`-scheme `Y`.  Then
there is a finite system `J₁, …, J_d` of sheaves of non-zero ideals on `X` such that for every `B`-morphism `h : X' → X` of a
non-singular algebraic `B`-scheme with dense preimages, and every decomposition `h⁻¹(Jᵢ) = J'ᵢ Pᵢ` with `Pᵢ` invertible and
`J'ᵢ` a sheaf of non-zero ideals not divisible by any invertible sheaf of ideals, the domain of definition of `f ∘ h` is
the set of the points where some `J'ᵢ` is trivial. -/
@[blueprint "thm:0.5-fact-star"
  (statement := /-- \textbf{(*)} Let $f$ be a rational application of a non-singular algebraic $\mathbf B$-scheme $X$ to
    another algebraic $\mathbf B$-scheme $Y$. We assume that $f$ is proper. Then there exists a finite system of coherent
    sheaves of ideals $\ne(0)$, say $J_1,\dots,J_d$, on $X$, such that: If $h\colon X'\to X$ is any morphism of a
    non-singular algebraic $\mathbf B$-scheme $X'$ to $X$, and if we can write $J'_iP_i=h^{-1}(J_i)$ for each $i$ where
    $P_i$ is an invertible sheaf of ideals on $X'$ and $J'_i$ is a sheaf of ideals $\ne(0)$ on $X'$ which is not
    divisible by any invertible sheaf of ideals (except $\mathcal O_{X'}$), then the domain of definition of the
    composition $f\circ h$ is exactly equal to the set of those points $x$ of $X'$ at which $J'_{i,x}=\mathcal
    O_{X',x}$ for at least one $i$. (p.~141.) Formalization note (encoding): $B$-schemes are separated (p.~118); the
    composition $f\circ h$ exists when $h$ has dense preimages, which the statement tacitly assumes. Used without proof
    or citation in the paper; assumed, as in the paper. -/)
  (proof := /-- Cited: used without proof or citation in the paper (p.~141, ``we note the following fact''). -/)
  (latexEnv := "theorem")]
theorem exists_finite_system_domain_precomp_eq [Hironaka.Cited.RationalApplicationExistsFiniteSystemDomainPrecompEq.{u}] :
    ∀ {B : Type u} [Field B] [CharZero B] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (CommRingCat.of B)) (pY : Y ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType pX] [QuasiCompact pX] [IsSeparated pX]
    [LocallyOfFiniteType pY] [QuasiCompact pY] [IsSeparated pY]
    (hX : X.IsNonsingular) (f : X ⤏ Y) (hf : f.IsProperApplication pX pY),
    ∃ (d : ℕ) (J : Fin d → Subscheme X), (∀ i x, (J i).stalkIdeal x ≠ ⊥) ∧
      ∀ (X' : Scheme.{u}) (pX' : X' ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType pX'] [QuasiCompact pX']
        [IsSeparated pX'] (_ : X'.IsNonsingular) (h : X' ⟶ X) (_ : h ≫ pX = pX') (hh : h.PreimageDense)
        (P J' : Fin d → Subscheme X'),
        (∀ i, (P i).IsInvertibleIdeal ∧ (∀ x, (J' i).stalkIdeal x ≠ ⊥) ∧ Subscheme.IsPrimitive (J' i) ∧
          ∀ x, (Subscheme.totalTransform h (J i)).stalkIdeal x = (P i).stalkIdeal x * (J' i).stalkIdeal x) →
        ((f.precomp h hh).domain : Set X') = {x | ∃ i, (J' i).stalkIdeal x = ⊤} :=
  @Hironaka.Cited.RationalApplicationExistsFiniteSystemDomainPrecompEq.exists_finite_system_domain_precomp_eq _

end RationalApplication

end Hironaka
