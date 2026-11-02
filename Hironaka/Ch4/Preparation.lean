/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch4.Preparation.Lemmas3To5
public import Hironaka.Ch4.Preparation.Proposition5Lemmas
public import Hironaka.Ch4.Preparation.Proposition5

/-!
# Ch. IV §2 (pp. 286–292): "2. Preparation on resolution data (ℜ^{N,n}_I, U)"

Lemmas 3, 4 and 5 and Proposition 5 (the *preparation theorem on* `(ℜ^{N,n}_I, U)`).

The notation used throughout this section is fixed by the introduction to Chapter IV
(pp. 274–275):

> In this chapter, we shall often find it convenient to express a resolution datum of type
> ℜ^{N,n}_I on a non-singular irreducible algebraic scheme X in the following form:
>
>   ℜ^{N,n}_I = (⋃_{i=1}^α E_i; V_1, V_2, …, V_β; W).
>
> We agree once for all that whenever this expression is taken, all the E_i denote
> non-singular irreducible subschemes of X of codimension one.  We do not require that E_i
> differ from E_j if i ≠ j.  We may find the empty subscheme of X among the E_i, which is a
> non-singular irreducible subscheme of X of codimension one according to our agreement upon
> the codimension of the empty subscheme.  (See the introductory paragraphs of Chapter I.)

Formalization notes.

* `DatumI.Raw` (Ch. I §1) carries the boundary as a *single* subscheme `E`; in this section
  the paper writes it as an explicit finite family `E_1, …, E_α`.  We therefore use a family
  `E : Fin α → Subscheme X` with `∀ i, (E i).IsNonsingularIrreducibleCodimOne` — the
  predicate of `Hironaka/Ch0/AlgebraicScheme.lean`, which, exactly as in the agreement quoted
  above, admits the empty subscheme and does not require the `E i` to be distinct — and write
  `⋃_i E_i` as `Subscheme.unionFam E = ⨅ i, E i`: a union of subschemes is the *meet* of the
  ideal sheaves (`Subscheme.union D D' = D ⊓ D'`, p. 165).  For `α = 0` this is
  `⊤ = Subscheme.empty`, as it should be.
* `red(D)`, the reduced structure on the underlying closed set of a subscheme `D`, is
  `Subscheme.ofClosed D.support`.
* Lean identifiers carry no combining diacritics, so where the paper writes `E′`, `W̄`, `R̄`
  the code writes `Eb`, `Wb`, `Rb`; the paper's notation is kept in the docstrings and in the
  LaTeX of the blueprint nodes.

## Files

The section is split into the following files, in the paper's order; this file imports them all.

* `Hironaka.Ch4.Preparation.Lemmas3To5`
* `Hironaka.Ch4.Preparation.Proposition5Lemmas`
* `Hironaka.Ch4.Preparation.Proposition5`
-/

@[expose] public section
