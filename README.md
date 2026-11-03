# HironakaLean: Hironaka's resolution of singularities (1964), formalized as written

This repository is a Lean 4 / Mathlib formalization of

> H. Hironaka, *Resolution of singularities of an algebraic variety over a field of characteristic zero* I, II.
> Annals of Mathematics 79 (1964), 109–203 and 205–326.

It is accompanied by a Palomar submission:

Our goal was to formalize Hironaka's orginal argument. This implies that each cited result (for instance results from local-ring theory) is stated in Lean and not proved: it is a hypothesis. We have made a detailed erratum which will be available along with a separate publication. While a majority amount to typos and trivial errors, we do also find a few non-trivial gaps that have been formalized with a corrected argument.


## What is proved (modulo the cited results)

All statements are proved for algebraic schemes over a ring of Hironaka's class 𝔅 (Ch. I, p. 161; p. 151), and in the
printed form over a field of characteristic zero.

| Paper | Statement | Lean |
|---|---|---|
| Ch. I §2, proved in Ch. IV | The fundamental theorems I₁^{N,n}, I₂^{N,n}, II₁^N, II₂^N, for N > n ≧ −1 | `Hironaka.allFundamentalTheorems_printedRange` (for n ≧ 0 also `…_fundamentalFamily`) |
| Ch. I §3, pp. 172–176 (statement p. 174) | Main Theorem I(n)| `Hironaka.MainTheorem.I_all` |
| Ch. I §3, pp. 176–177 | Main Theorem II(N)| `Hironaka.mainTheorem_II` |
| Ch. 0 §3, p. 132 | Main Theorem I as printed and the weak form | `Hironaka.MainTheorem.Ch0.I`, `…Ch0.I_weak` |
| Ch. 0 §3, pp. 132–133 | Main Theorem I in the strong form, (a)–(c)| `Hironaka.MainTheorem.Ch0.I_strong`, `…Ch0.I_strong_eq` |
| Ch. 0 §3, p. 132 | Corollary| `Hironaka.MainTheorem.Ch0.exists_projective_model` |
| Ch. 0 §4, p. 138 | Main Theorem I\* | `Hironaka.MainTheorem.Ch0.IStar` |
| Ch. 0 §5, pp. 142–143 | Main Theorem II and (B\*) | `Hironaka.MainTheorem.Ch0.II_full`, `…Ch0.B_star` |
| Ch. 0 §5, pp. 143–146 | Corollaries 1, 2 and 3 of Main Theorem II | `…Ch0.exists_isTrivializing`, `…Ch0.exists_isInvertible_subsheaf_pullback`, `…Ch0.exists_isBoundarySimplification`, `…Ch0.exists_isBoundarySimplification_of_singularLocus_subset_of_field` |
| Ch. 0 §5, pp. 140–143 | Question (E)| `Hironaka.RationalApplication.question_E` |
| Ch. 0 §5, pp. 144–145 | Consequences (1), (2), (3) of Corollary 1| `Hironaka.FunctionFieldPair.exists_isObtainedBy_dominates`, `…exists_higherDirectImage_structureSheaf`, `…exists_isObtainedBy_nonsingular_projective` |

The theorems of Ch. II–IV used along the way (Theorems A, B, C, D and A\*, B\*, D\*, the lemmas of Chapters II and III)
are proved too, modulo the same cited results. The blueprint lists each of them with its label.



The hypotheses are bundled in two classes, in `Hironaka/Statements.lean`:
- `Hironaka.HironakaCitedResults`: the **15** cited results that the fundamental and main theorems use;
- `Hironaka.HironakaCitedResultsCh0`: these 15, the cited unique factorization of regular local rings, and 4
statements that the paper states without proof.

Every declaration that rests on a hypothesis takes the bundle, or the classes it uses, as an instance argument, so that its
statement shows what it assumes; for example `theorem MainTheorem.I_all [HironakaCitedResults] (n : ℕ) : MainTheorem.I n`.
The theorems of the table take `HironakaCitedResults`, except Corollary 2, Question (E) and the consequences (1)–(3), which
take `HironakaCitedResultsCh0`.

<!-- The library contains **4 `sorry`s**, and none of the theorems above depends on them:
- the 2 statements that Remark 1 of Ch. III §9 makes without proof (its argument is formalized; no main theorem uses it);
- the global containments asserted by the printed Lemma (AB.4) of Ch. IV §3, and its printed Corollary. They are kept as
  the record of the paper's error described below. Whether these printed statements hold is open (no counterexample is
  known).

Each of the 4 is labelled in its docstring. -->

## Scope

Not formalized:
- the analytic statements of Ch. 0 (§7, and the complex-analytic sentence of p. 132);
- Ch. I §4

## Building

- **Requirements:** [elan](https://github.com/leanprover/elan). The toolchain `leanprover/lean4:v4.35.0-rc3` is pinned in
`lean-toolchain`, and Mathlib and LeanArchitect are pinned to exact commits in `lake-manifest.json`.

```sh
lake exe cache get   # download Mathlib's compiled files
lake build           # builds the library, the three Challenge files and the Solution
```

- **The blueprint.** Its sources are in `blueprint/src/`; `content.tex` is the chapter-by-chapter outline. The
`@[blueprint]` annotations in the Lean sources come from [LeanArchitect](https://github.com/hanwenzhu/LeanArchitect).
To build it:
1. Extract them with `lake build :blueprint`.
2. Build with [leanblueprint](https://github.com/PatrickMassot/leanblueprint) (`leanblueprint web`), which needs a LaTeX installation and plasTeX.

## Checking the statements with Comparator

The theorems are split over three Challenge files, each with its own configuration, so that each file stays under 1,000
lines with a docstring on every definition, per the requirements of Palomar.

| Configuration | Challenge | Theorems | Hypotheses |
|---|---|---|---|
| `comparator.json` | `Challenge.lean` | The fundamental theorems for N > n ≧ −1, Main Theorems I(n) and II(N) | `HironakaCitedResults` |
| `comparator-main-ch0.json` | `ChallengeMainCh0.lean` | Main Theorem I in its four forms, the Corollary of p. 132, Main Theorem I\*, Main Theorem II and (B\*), Corollaries 1 and 3 | `HironakaCitedResults` |
| `comparator-ch0.json` | `ChallengeCh0.lean` | Corollary 2, Question (E), the consequences (1)–(3) | `HironakaCitedResultsCh0` |

To check, please run 

```sh
lake comparator --config comparator.json
lake comparator --config comparator-main-ch0.json
lake comparator --config comparator-ch0.json
```
on a linux machine.

With the `--paranoid` flag, it also runs the other checkers bundled with Lean (`leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`). All three configurations pass the comparator check with the `--paranoid` flag in our local tests.


## Licence

Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim and Oisin Kim. Released under the Apache License 2.0; see `LICENSE`. The paper itself is not included. Short quotations from it, with page references, appear in the docstrings for the purpose of comparison.

## Authors

Daattavya Aggarwal, Minhyong Kim and Oisin Kim.
