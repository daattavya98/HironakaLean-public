/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch3.PermissibleEffects.Lemma14
public import Hironaka.Ch3.PermissibleEffects.Lemmas15And16
public import Hironaka.Ch3.PermissibleEffects.Theorems3And4

/-!
# Ch. III §5: Effects of permissible monoidal transformations on ν*(J) and τ*(J) (pp. 226–238)

> 5. Effects of permissible monoidal transformations on ν*(J) and τ*(J).
>
> Let R be a regular local ring, and J an ideal in R. Let M be the maximal ideal of R.
> (p. 226)

Definition 8 itself (permissible centers, p. 226) is `IsPermissibleCenter`
(`Hironaka/Ch3/Basic.lean`, `def:III.8`).  This file contains the rest of §5, in the paper's
order:

* p. 226: the equivalent forms (ii)* and (ii)** of condition (ii) of Definition 8;
* Remark 1 (p. 226) and Remark 2 (pp. 226–227): invariance under a local homomorphism which
  transforms a regular system of parameters into such a system;
* Lemma 14 (pp. 227–229), Lemma 15 (pp. 229–231), Lemma 16 (pp. 231–233);
* Theorem 3 (pp. 233–234) and Theorem 4 (pp. 234–236);
* Proposition 1 (pp. 236–238).

## Conventions and encodings

`gr_M(R)` is `AssocGraded (maximalIdeal R)`, `gr^μ_M(R)` is `AssocGraded.homogeneous _ μ` and
`gr_M(J, R)` is `grIdeal (maximalIdeal R) J` (`Hironaka/Compat/Graded.lean`).  `ν_P(f)` is
`Ideal.ordElem P f` and `ν^{(i)}(J)`, `ν*(J)`, `t(J)`, `μ^{(a)}(J)`, `τ^{(a)}(J)` are `nuI`,
`nuStar`, `t`, `mu`, `tau` (`Hironaka/Ch3/NuStar.lean`, `Hironaka/Ch3/TauStar.lean`).
Standard bases are `IsStandardBase` (Definition 3).

*Monoidal transforms are written `T : MonoidalTransform R P`, not `t`*, because `t R J` is the
integer `t(J)` of Definition 6; `R₁ = T.ring`, the canonical homomorphism `R → R₁` is
`T.toRing`, and `J₁`, the strict transform of `J`, is `strictTransformIdeal T J`
(Definition 5, p. 213).

The characters `ν^{(i)}` are indexed by `ℕ+`; for a `0`-indexed `j : Fin m` the paper's
`ν^{(j)}(J)` (1-indexed) is `nuI R J (j : ℕ).succPNat`.

The element `x^{-ν} f` of `R₁` (`x ∈ P` with `PR₁ = (x)R₁`) is, as in Definition 5, the element
`g` of `R₁` with `x ^ ν * g = T.toRing f`; it is unique because `R₁` is a domain.

"`(g₁, …, g_i)` can be extended to a standard base of `J₁`" is `ExtendsToStandardBase` of
`Hironaka/Ch3/Frames.lean` (an initial segment of a standard base).

Lexicographic comparisons of the initial segments `(ν^{(1)}, …, ν^{(i)})` are comparisons in
`Lex (Fin i → ℕ∞)` of `toLex fun j => ν^{(j+1)}` (Mathlib's `Pi.Lex` order is exactly the order
of Definition 2, p. 207).

Equalities of the systems `τ*(J)` (whose index type `Fin (t(J))` depends on `J`) are
transcribed, as in Lemma 13 (`lem:III.13`), as the equality `t(J) = t(J')` of the lengths
together with `τ^{(i)}(J) = τ^{(i)}(J')` for `1 ≤ i ≤ t(J)`.

## Redundant hypotheses which are lemmas of §2

Two facts proved in §2 of this chapter, namely that the canonical homomorphism `R → R₁` of a
monoidal transform is a local homomorphism and that `R₁` is again a regular local ring (when `R/P`
is regular), used to appear in the statements of this file as the instance hypotheses
`[IsLocalHom T.toRing]` and `[IsRegularLocalRing T.ring]` (and, in Remark 2, also for `R₁'` and as
`[(P.map α).IsPrime]`).  These hypotheses are not carried by the statements
wherever the data allow: `MonoidalTransform.isLocalHom_toRing` is a global instance
(`Hironaka/Ch3/Transforms.lean`), the regularity of `R₁` is the global instance
`MonoidalTransform.instIsRegularLocalRing` (from `[P.IsPrime]` and `[IsRegularLocalRing (R ⧸ P)]`,
`MonoidalTransform.isRegularLocalRing_of_isRegularLocalRing_quotient`), and in Remark 2 the
primality of `PR'` and the regularity of `R'/PR'` and of `R₁'` are stated by `haveI` from
`RingHom.MapsRSOP.canonicalLift_properties`.  What remains, and why: `[IsRegularLocalRing T.ring]` in
`tauStar_strictTransform_eq`, `tauStar_strictTransform_eq_of_isResiduallyRational` and
`nuStar_strictTransform_le_of_isResiduallyRational` (hypotheses before the colon, such as the
permissibility of `Q₁` for `J₁`, mention `T.ring`, while the regularity of `R/P` is only a
consequence of the hypothesis "`P` is a permissible center for `J`"), and in the internal
`TransformCoord` lemmas, which carry neither `[P.IsPrime]` nor `[IsRegularLocalRing (R ⧸ P)]`.
That `β : R₁ → R₁'` is local is part of the paper's hypothesis "canonical local homomorphisms".
Likewise a regular local ring is a domain (`[IsDomain R]`, needed to form `MonoidalTransform R P`).

## Files

The section is split into the following files, in the paper's order; this file imports them all.

* `Hironaka.Ch3.PermissibleEffects.Lemma14`
* `Hironaka.Ch3.PermissibleEffects.Lemmas15And16`
* `Hironaka.Ch3.PermissibleEffects.Theorems3And4`
-/

@[expose] public section
