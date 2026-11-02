/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch4.ImplicationsAB.LemmasAB1ToAB3
public import Hironaka.Ch4.ImplicationsAB.LemmasAB4AndAB5
public import Hironaka.Ch4.ImplicationsAB.PreparedSuccession

/-!
# Ch. IV §3 (pp. 292–310): Proofs of the implications (A) and (B)

> Let `X` be a non-singular irreducible algebraic scheme.  Let `V` be a subscheme of `X` and
> `x` a point of `X`.  Let `S` be the local ring of `X` at `x`, which is a regular local ring,
> and `J` the ideal of `V` in `S`.  Then we denote by `ν*_x(V/X)` the numerical character
> `ν*(J) = (ν^{(1)}(J), ν^{(2)}(J), …)` of the ideal `J` in `S`, which was defined in §1 of
> Ch. III, and by `τ*_x(V/X)` the numerical character `τ*(J) = (τ^{(1)}(J), …, τ^{(t)}(J))`
> with `t = t(J)` of the ideal `J` in `S`, which was defined in §3 of Ch. III.  We shall also
> denote by `τ^{(i)}_x(V/X)` the integer `τ^{(i)}(J)` for `1 ≤ j ≤ t(J)`.  We note that
> `ν*(J) = (0, ∞, ∞, …)` if and only if `x ∉ V`, in which case `t(J) = 1` and
> `τ^{(1)}(J) = 0`.  (pp. 292–293.)

The chapter introduction (pp. 274–275) fixes the notation used throughout:

> In this chapter, we shall often find it convenient to express a resolution datum of type
> `ℜ^{N,n}_I` on a non-singular irreducible algebraic scheme `X` in the following form:
> `ℜ^{N,n}_I = (⋃_{i=1}^α E_i; V_1, V_2, …, V_β; W)`.
> We agree once for all that whenever this expression is taken, all the `E_j` denote
> non-singular irreducible subschemes of `X` of codimension one.  We do not require that `E_i`
> differ from `E_j` if `i ≠ j`.  We may find the empty subscheme of `X` among the `E_i`, which
> is a non-singular irreducible subscheme of `X` of codimension one according to our agreement
> upon the codimension of the empty subscheme.  (See the introductory paragraphs of Chapter I.)
> (p. 274.)

## Contents, in the paper's order

* p. 274: the expression `(⋃ E_i; V_1, …, V_β; W)` (`def:IV.0-expression`);
* p. 292: the symbols `ν*_x(V/X)`, `τ*_x(V/X)`, `τ^{(i)}_x(V/X)`, the systems
  `ν*_x(V_1,…,V_β/X)`, `τ*_x(V_1,…,V_β/X)` and the two inequalities (`def:IV.3-characters`,
  `def:IV.3-inequalities`, `rem:IV.3-nu-star-empty`);
* p. 293: the symbol `S(ℜ)` (`def:IV.3-S`); Theorems A and B (`thm:IV.A`, `thm:IV.B`) are in
  `Hironaka/Ch4/TheoremsAB.lean`;
* pp. 293–294: effective modifications (`def:IV.3-effective-modification`), Lemma (AB.1)
  (`lem:IV.AB-1`) and the claim that Theorems A, B follow from Theorems A*, B*
  (`lem:IV.AB-1-consequence`); Theorems A* and B* (`thm:IV.A-star`, `thm:IV.B-star`) are in
  `Hironaka/Ch4/TheoremsAB.lean`;
* pp. 294–299: the fixed succession `{f_s}` and the data `ℜ(s)`, `E_i(s)`
  (`def:IV.3-succession`), the standing choices (`def:IV.3-standing`), the completion
  `Ŝ`, the schemes `X̂_s` and the morphisms `c_s`, `ĝ_s` (`def:IV.3-setup`), the regular frame
  `(T; z)` with [a]–[e], `X̄_0`, `X̄_s`, `f̄_s` (`def:IV.3-frame`), the existence of all these
  objects (`lem:IV.3-setup-exists`), the open subschemes `X'_s`, `X̂'_s`, `X̄'_s` and the
  sheaves `J̄(s)` of [f]–[i] (`def:IV.3-construction`) with the facts asserted along the way
  (`lem:IV.3-construction-facts`) and the remark on `f̄'_s` (`lem:IV.3-construction-facts-fbar-prime`),
  and the consequence of Theorem 3 of Ch. III recalled on
  p. 299 (`lem:IV.3-thm3-consequence`);
* Lemmas (AB.2), (AB.3), (AB.5), the Corollary of (AB.3) and the local computation of the proof
  of (AB.4) (`lem:IV.AB-2`, `lem:IV.AB-3`, `cor:IV.AB-3`, `lem:IV.AB-4-frames` …
  `lem:IV.AB-4-local`, `lem:IV.AB-5`), in the paper's order: (AB.2), (AB.3) and its Corollary come
  before the frame of pp. 296–298; Lemma (AB.4) and its Corollary, repaired, are in
  `Hironaka/Ch4/ComponentwiseConstruction.lean`;
* pp. 307–308: the prepared succession `g_s` with [(1)], [(2)] and the point `x_0`
  (`def:IV.3-conditions`), Remarks 1 and 2 (`rem:IV.3-1`, `rem:IV.3-2`) and the objects of
  p. 308 (`X̃`, `Ẽ_j`, the datum `ℜ^{N-1}_II`).

Lemma (AB.6) and Remarks 3–5 (`lem:IV.AB-6`, `rem:IV.3-3` … `rem:IV.3-5`) are in
`Hironaka/Ch4/TheoremsAStarBStar.lean`, which also imports `Hironaka/Ch4/CompletionTransforms.lean`
(the assembly of (AB.6)); Theorems A*, B*, A, B and the implications (A), (B) of Ch. I §2
(`thm:IV.A-star`, `thm:IV.B-star`, `thm:IV.A`, `thm:IV.B`, `impl:A`, `impl:B`) are in
`Hironaka/Ch4/TheoremsAB.lean`.

## Formalization notes (every deviation from the paper is flagged here and at its node)

* Lean identifiers cannot carry combining diacritics, so in code the paper's `Ŝ`, `X̂_s`,
  `x̂_0`, `X̄_s`, `X̄'_s`, `J̄(s)`, `f̄_s`, `c̄_s`, `B̄'`, `X̃`, `Ẽ_j`, `J̃`, `B̃` are written
  `Shat`, `Th.X s`, `xhat0`, `Xb s`, `Xbp s`, `Jbar s`, `fbar s`, `cbar s`, `Bb`, `Xt s`,
  `eTilde`, `Jt`, `Bt`.  The paper's notation is kept in the docstrings and in the LaTeX
  statements.
* `ν*` and `τ*` are only defined at a point where the ambient scheme is simple; the
  transforms `X_s` are non-singular (Ch. 0), but that is not available definitionally, so the
  witness `X_s.IsSimpleAt x` is taken as a hypothesis wherever `ν*_x`, `τ*_x` occur (in a
  hypothesis such as condition (3) of Lemma (AB.4) it is part of the condition).
* `τ^{(i)}(J)` is the *total* function `Hironaka.tau` of `Hironaka/Ch3/TauStar.lean`; the
  paper compares `τ^{(i)}` for `1 ≤ i ≤ t(J)`, and we compare for all `i ≥ 1`.  This is
  faithful in the situation in which the paper uses the comparison, because there the two
  characters `ν*` agree, hence so do `t` and `μ*`, and the junk values `τ^{(i)} = 0` for
  `i > t` agree.
* The system `(V_1, …, V_β, W)` of a datum is `AB.datumSystem` (with `W` at the last index), and
  its transform along a finite succession is formed by strict transforms (`AB.succSystem`);
  `AB.succSystem_eq_transformI` checks that these are the members of the transformed datum.
* A resolution datum `(ℜ^{N,n}_I, F)` or `(ℜ^{N,n}_I, U)` is a pair of a `DatumI.Raw` and an
  `AB.Restriction` (closed `F` or open `U`); `S(ℜ)`, permissibility and transforms are defined
  by cases.
* The permissible succession "(finite or infinite)" `{f_s}` of p. 294 is an `AB.Tower`: an
  `ℕ`-indexed sequence of monoidal transformations (finite successions are those with
  eventually empty centers, p. 295), whose initial segments `g_s` are finite successions.
* The running setup of pp. 294–299 is split into the standing assumptions (`AB.Standing`),
  the induced succession of `X̂_0 = Spec(Ŝ)` with the morphisms `c_s` (`AB.Completion`) and the
  frame data (`AB.Frame`).  `Ŝ`, `X̂_0`, `c_0`, `x̂_0`, `X̄_0`, `X̄_s`, `X'_s`, `X̂'_s`, `X̄'_s`,
  `J̄(0)` and `J̄(s)` are *constructed*; the induced succession `{f̂_s}`, the morphisms `c_s`,
  `f̄_s`, the regular frame `(T; z)`, the standard bases, `b` and the generators of `J̄` are
  *recorded* with the properties the paper states, and `lem:IV.3-setup-exists` asserts (as the
  paper does, pp. 295–297) that they exist.  `J`-stability is Definition 11 of Ch. III §9
  (`IsJStable`, `Hironaka/Ch3/JStability.lean`).

## Files

The section is split into the following files, in the paper's order; this file imports them all.

* `Hironaka.Ch4.ImplicationsAB.LemmasAB1ToAB3`
* `Hironaka.Ch4.ImplicationsAB.LemmasAB4AndAB5`
* `Hironaka.Ch4.ImplicationsAB.PreparedSuccession`
-/

@[expose] public section
