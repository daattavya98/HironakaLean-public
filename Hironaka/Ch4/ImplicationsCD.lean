/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch4.ImplicationsCD.LemmasD1AndD2
public import Hironaka.Ch4.ImplicationsCD.LemmasCD3ToCD5
public import Hironaka.Ch4.ImplicationsCD.PreparedSuccession

/-!
# Ch. IV §4 (pp. 311–326): Proofs of the implications (C) and (D)

> Let `X` be a non-singular irreducible algebraic scheme of dimension `N ≧ 1`.  We shall consider
> a resolution datum `ℜ` on `X` which is either of the form `(ℜ^N_II, F)` with closed
> restriction `F`, or `ℜ^N_II` without restriction, where
> `ℜ^N_II = (E_1, …, E_α | J, b | a_1, …, a_α)`.
> Let us recall the definition of the symbols `S(ℜ^N_II)`, `S_*(ℜ^N_II)`, and `S_ν(ℜ^N_II)`
> with a non-negative integer `ν`.
> `S(ℜ^N_II) = {x ∈ X | ∑_{x∈E_i} a_i + ν(J_x) ≧ b}`,
> `S_ν(ℜ^N_II) = {x ∈ S(ℜ^N_II) | ν(J_x) ≧ ν}`,
> `S_*(ℜ^N_II) = S_ν(ℜ^N_II)` with `ν = ν(ℜ^N_II)`, where
> `ν(ℜ^N_II) = max_{x∈S(ℜ^N_II)} {ν(J_x)}`.
> For the case in which `ℜ = (ℜ^N_II, F)`, we shall use the following symbols:
> `S(ℜ) = S(ℜ^N_II) ∩ F`, `S_ν(ℜ) = S_ν(ℜ^N_II) ∩ F` and `ν(ℜ) = max_{x∈S(ℜ)} {ν(J_x)}`,
> which denote the respective sets of points of `X`. …  (p. 311.)

The chapter introduction (p. 275) explains which characteristics of a datum of type `ℜ^N_II`
matter:

> In the treatment of a resolution datum of type `ℜ^N_II` on a non-singular irreducible
> algebraic scheme `X`, say `ℜ^N_II = (E_1, E_2, …, E_α | J, b | a_1, a_2, …, a_α)`, all that
> are essential among its characteristics are the following ones: the set `C(ℜ^N_II)` of those
> irreducible subschemes `E_i` of `X` which are not empty, the integers `a(E) = ∑_{E_i = E} a_i`
> for `E ∈ C(ℜ^N_II)`, `J` and `b`.  In other words, any two resolution data of type `ℜ^N_II` on
> the same `X` may be considered as the same one whenever they have the same `C(ℜ^N_II)`, the
> same `a(E)` for `E ∈ C(ℜ^N_II)`, the same `J` and the same `b`.  …  However, we shall find it
> convenient to identify a resolution datum `ℜ^N_II`
> with the above expression, and to distinguish any two resolution data with different
> expressions.  (p. 275.)

## Contents, in the paper's order

* p. 311: the recalled symbols `S`, `S_ν`, `S_*`, `ν` for `ℜ^N_II` (`rem:IV.4-symbols-II`, which
  records that they are the symbols of Ch. I) and the new symbols `S(ℜ)`, `S_ν(ℜ)`, `ν(ℜ)` for
  `ℜ = (ℜ^N_II, F)` (`def:IV.4-symbols`);
* p. 311: Theorem D (`thm:IV.D`; Theorem C, `thm:IV.C`, is in `Ch4/TheoremC.lean`) and the "i.e." of Theorem D
  (`rem:IV.4-resolved-iff`);
* p. 312: Theorem D* (`thm:IV.D-star`), the deduction "if Theorem D* is verified … `S_1(f*(ℜ))`
  is empty" (`lem:IV.D-star-consequence`) and Lemma (D.1) (`lem:IV.D-1`);
* pp. 312–313: the symbols `K⁰_r`, `A_r`, `K_r`, `k_r` of the proof of Lemma (D.1)
  (`def:IV.D-1-symbols`) and the claims (i)–(iii) of that proof (`lem:IV.D-1-claim`);
* pp. 311–312: "Theorem D follows Theorem D*" (`lem:IV.D-from-D-star`, proved in Lean from
  `lem:IV.D-star-consequence`, `lem:IV.D-1` and the fact, used without comment, that a permissible
  succession leads again to a non-singular irreducible scheme of dimension `N`, `lem:IV.4-ambient`);
* p. 314: Lemma (D.2) (`lem:IV.D-2`) and its consequence via Proposition 4 of §1
  (`lem:IV.4-no-codim-one`);
* pp. 314–316: the running setup: the succession `{f_s}` with `ℜ(s)`, `E_i(s)`, `F(s)`, the point
  `x_0` and the standing assumptions (`def:IV.4-standing`), `ν_{M_0}(J_0) = ν`
  (`lem:IV.4-nu-J0`, proved), the base `[0]`, the frame `(T_0; z_0)` with `[i]`–`[iv]`, `[iii]'`
  and the completion `X̂_s` (`def:IV.4-frame`), `b̄`, `J̄(0)`, `X̄_s`, `f̄_s` and `J̄(s)` of
  `[v]`–`[vii]` (`def:IV.4-construction`), the existence of all this (`lem:IV.4-setup-exists`),
  the facts asserted along the way (`lem:IV.4-construction-facts`, and `lem:IV.4-Pbar`, proved);
* Lemma (CD.3) (`lem:IV.CD-3`), Lemma (CD.4) and its Corollary (`lem:IV.CD-4`, `cor:IV.CD-4`),
  Lemma (CD.5) (`lem:IV.CD-5`);
* pp. 320–321: the prepared succession `h_s` with `[(1)]`, `[(2)]` and `x_0 ∈ h_s(S_ν(ℜ(s)))`
  (`def:IV.4-conditions`, `lem:IV.4-x0`), `X̃`, `Ê_j(s)`, `Ẽ_j`, `α̃` (`def:IV.4-tilde`) and the
  facts stated about them (`lem:IV.4-tilde-facts`);
* pp. 321–322, the case `ν ≧ b`: the datum `ℜ^{N-1}_II` (`def:IV.4-case-ge`), Remark 1
  (`rem:IV.4-1`) and the relation between `ℜ(s+1)` and `f̄_s*(ℜ^{N-1}_II)`
  (`lem:IV.4-case-ge-relation`);
* pp. 322–326, the case `ν < b`: `J̄*(s)`, `c_j` and the datum `ℜ^{N-1}_II`
  (`def:IV.4-case-lt`), Remarks 2 and 3 (`rem:IV.4-2`, `rem:IV.4-3`);
* pp. 321–326, the lifting of a resolving succession of `X̃` to `X_s` ("the proof of Theorems C and
  D* can be easily reduced to the resolution of the `ℜ^{N-1}_II` on `X̃`"): the stage states
  `FrameStage` (the fold `FrameStage.fold` of the stage objects `X̂_s`, `c_s`, `X̄_s`, `J̄(s)` along a
  finite succession, `Frame.canon_stageOf_eq_fold`), `LiftData.Q`, `LiftData.step`, and the core step
  `exists_extension_not_mem_sNuImage` (`lem:IV.4-core-step`; the repair of the `Ẽ_j` enters through
  `DatumII.Raw.resolvable_of_isWeakDatum`);
* the closed restriction: the observation of p. 314 "we may also assume the same for Theorem C"
  (`lem:IV.4-no-codim-one-closed`) and the closed analogues of the preparation
  (`PreparedClosed`, `exists_standing_prepHyp_tower_closed`, `exists_extension_of_resolvableLen_closed`);
* Theorem C itself (`thm:IV.C`), its core step for the closed restriction
  (`lem:IV.4-core-step-closed`) and the implication (C) (`impl:C`) are in
  `Ch4/TheoremC.lean`, because the closed core needs the repaired auxiliary datum of
  `Ch4/AuxiliaryDatumRepair.lean` (which imports this file); p. 326, the conclusion of the paper
  (`thm:I.2-fundamental`) and the implication (D) (`impl:D`) are in
  `Ch4/Conclusion.lean`.

## Formalization notes (every deviation is also flagged at its node)

* Lean identifiers cannot carry combining diacritics: the paper's `Ŝ_0`, `X̂_s`, `x̂_0`,
  `X̄_s`, `f̄_s`, `c̄_s`, `J̄(s)`, `J̄*(s)`, `P̄_{s+1}`, `b̄`, `X̃`, `Ẽ_j`, `Ê_j(s)`, `α̃`, `b̃`,
  `ã_j`, `J̃`, `B̃`, `c_j` are written `AB.Shat`, `Th.X s`, `hS.xh`, `Xb s`, `fbar s`,
  `cbar s`, `Jbar s`, `JbarStar s`, `Pbar s`, `bBar`, `Xt s`, `Etilde s j`, `Ehat s j`, `alphaT`,
  `bt`, `a`, `Jt`, `Bt`, `cT T ℜ r s j`.
* A datum `ℜ` "which is either of the form `(ℜ^N_II, F)` … or `ℜ^N_II` without restriction" is a
  pair of a `DatumII.Raw` and a `CD.Restriction` (`closed F` or `unrestricted`).
* The integer `ν` of the paper is a natural number `ν : ℕ`; the orders `ν(J_x)`, `ν(ℜ)` are the
  `ℕ∞`-valued ones of Ch. I, and the paper's hypothesis `ν = ν(ℜ)` is `(ν : ℕ∞) = ν(ℜ)`.
* The running setup reuses Ch. IV §3: the succession `{f_s}` is an `AB.Tower`, its initial segment
  `h_s` is `T.pre s`, and `Ŝ_0`, `X̂_0`, `c_0`, `x̂_0`, the induced succession `{f̂_s}` with the
  morphisms `c_s` (`AB.Completion`), `X̄_0 = V(z_0)` (`AB.vZ`) and its strict transforms `X̄_s`
  (`AB.strictTransformZeroLocus`) are those of §3.  The choices of p. 315 (`[0]`, `[i]`–`[iv]`, `[iii]'`) are
  recorded existentially (`CD.FrameSpec`), the data kept being `z_0` and the set of the
  `g_{ji}^{b̄/i}`; `J̄(s)` of `[vii]` is formed on all of `X̄_s` by the paper's formula, and
  "`J̄(s)` is defined" is the predicate `IsDefined s` (the conditions (1)–(3) of `[vii]` for all
  `t < s`).
* No `J`-stability (Definition 11 of Ch. III §9) is used in this section: the frame of p. 315
  is not required to be stable.
* The resolution data `ℜ^{N-1}_II` on `X̃` are "not uniquely determined but … arbitrarily fixed"
  (pp. 321, 323); they are given by their `ã_j` and `J̃` subject to the paper's equation, and are
  assumed to be resolution data (the paper calls them so), as in Remarks 3–5 of §3.

## Files

The section is split into the following files, in the paper's order; this file imports them all.

* `Hironaka.Ch4.ImplicationsCD.LemmasD1AndD2`
* `Hironaka.Ch4.ImplicationsCD.LemmasCD3ToCD5`
* `Hironaka.Ch4.ImplicationsCD.PreparedSuccession`
-/

@[expose] public section
