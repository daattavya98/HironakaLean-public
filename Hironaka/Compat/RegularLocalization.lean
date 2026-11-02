/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Statements

/-!
# Compatibility layer: localizations of regular local rings are regular (Serre)

> We recall the fact that a localization of a regular local ring by any prime ideal is regular.
> (This fact is due to J. P. Serre, *Sur la dimension homologique des anneaux et des modules
> noethériens*, Proc. of the International Symposium, Tokyo-Nikko (1955), Scientific Council of
> Japan, 1956, pp. 175–189.)  (Ch. III, footnote 9, p. 243)

The paper first uses this fact tacitly in the proof of Theorem 1 of Ch. III §3 (p. 218), where
Theorem 1 is applied to the local rings `R_{P_i}` of a chain of primes of a regular local ring
`R`; it cites it in footnote 9.  Mathlib does not have it (its proof goes through Serre's
homological characterization of regular local rings by finite global dimension; see the TODO
in `Mathlib/RingTheory/RegularLocalRing/Defs.lean`), so it is a cited leaf.  The special case
of a prime `P` with `R/P` regular is proved directly in `Hironaka/Ch3/Stability.lean`.
-/

@[expose] public section

namespace Hironaka

universe u


/-- Footnote 9, p. 243 (Serre): "a localization of a regular local ring by any prime ideal is
regular."  Cited leaf. -/
@[blueprint "lem:regular-localization-serre"
  (statement := /-- Let $R$ be a regular local ring and $P$ a prime ideal of $R$. Then the
    localization $R_P$ is a regular local ring. (Ch.~III, footnote~9, p.~243: ``We recall the
    fact that a localization of a regular local ring by any prime ideal is regular. (This fact
    is due to J.~P.~Serre.)''; used tacitly in the proof of Theorem~1 of Ch.~III, p.~218.) -/)
  (proof := /-- Not proved in the paper: J.-P.~Serre, \emph{Sur la dimension homologique des
    anneaux et des modules noeth\'eriens}, Proc.\ Int.\ Symp.\ Tokyo--Nikko 1955, pp.~175--189
    (a noetherian local ring is regular if and only if it has finite global dimension, and
    finite global dimension passes to localizations). -/)
  (latexEnv := "lemma")]
theorem isRegularLocalRing_localization_of_isRegularLocalRing [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] :
    ∀ (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (P : Ideal R) [P.IsPrime],
    IsRegularLocalRing (Localization.AtPrime P) :=
  @Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.isRegularLocalRing_localization_of_isRegularLocalRing _

end Hironaka
