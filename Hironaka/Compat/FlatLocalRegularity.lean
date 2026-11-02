/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Architect
public import Hironaka.Statements

/-!
# Compatibility layer: regularity and completion along flat local homomorphisms (cited facts)

Two standard theorems of the theory of local rings, used in the proof of property (c) of the
class 𝔅 (Ch. I, p. 161: "if A is an algebra of finite type over S ∈ 𝔅, then every local ring of
Spec(A) belongs to 𝔅"; footnote 31: "Reduce the proof to the case in which S is complete, and
then apply the jacobian criterion").  Neither is stated in the paper; both belong to the theory
of local rings which the paper cites wholesale in footnote 3 of the Introduction (p. 116):

> The two chapters, VII and VIII, of Samuel-Zariski, [18], should cover all that we need from the
> theory of local rings.  A complete reference to the theory may be obtained from M. Nagata [15].

* `isRegularLocalRing_of_flat_of_isRegularLocalRing` (**L3**): regularity descends along flat
  local homomorphisms of noetherian local rings;
* `exists_flat_isLocalHom_adicCompletion_of_flat` (**L4**): a flat local homomorphism of
  noetherian local rings induces a flat local homomorphism of the completions.

The project has private versions of (L3) only for homomorphisms with `m_A B = m_B`
(`Ch3/PermissibleEffects.lean`); the general case is not in Mathlib.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u


/-- **(L3)** Descent of regularity along a flat local homomorphism of noetherian local rings: if
`R → R'` is flat and local and `R'` is regular, then `R` is regular.

Cited, not proved in the paper: footnote 3 (p. 116) refers the theory of local rings to
Samuel–Zariski, Ch. VII–VIII, and Nagata [15].  Standard reference: Matsumura, *Commutative Ring
Theory*, §23 (Thm. 23.7 (i), via Serre's characterization of regular local rings by finite
global dimension; the exact numbering was not checked, nor that in Nagata, *Local Rings*).  The
statement is used in the proof of (c), p. 161, which the paper only sketches. -/
@[blueprint "lem:regular-descent-flat-local"
  (statement := /-- Let $R\to R'$ be a flat local homomorphism of noetherian local rings. If
    $R'$ is regular, then $R$ is regular. -/)
  (proof := /-- Cited, not proved in the paper: footnote~3, p.~116 (``The two chapters, VII and
    VIII, of Samuel-Zariski, [18], should cover all that we need from the theory of local rings.
    A complete reference to the theory may be obtained from M. Nagata [15].''). Standard
    reference: Matsumura, \emph{Commutative Ring Theory}, \S23 (Thm.~23.7~(i); numbering not
    checked). -/)
  (latexEnv := "lemma")]
theorem isRegularLocalRing_of_flat_of_isRegularLocalRing [Hironaka.Cited.IsRegularLocalRingOfFlatOfIsRegularLocalRing.{u}] :
    ∀ {R R' : Type u} [CommRing R]
    [CommRing R'] [IsLocalRing R] [IsNoetherianRing R] [Algebra R R'] [Module.Flat R R']
    [IsRegularLocalRing R'] [IsLocalHom (algebraMap R R')],
    IsRegularLocalRing R :=
  @Hironaka.Cited.IsRegularLocalRingOfFlatOfIsRegularLocalRing.isRegularLocalRing_of_flat_of_isRegularLocalRing _


/-- **(L4)** A flat local homomorphism `R → R'` of noetherian local rings induces a flat local
homomorphism `R̂ → R̂'` of the completions (compatible with the canonical maps).

Cited, not proved in the paper: footnote 3 (p. 116).  Standard reference: Matsumura, *Commutative
Ring Theory*, §8 and §22 (the exact numbering was not checked); EGA 0_III, §10.2.  The
existence form records the compatibility with the canonical maps; the map is the one induced by
`R → R'` on the inverse limits. -/
@[blueprint "lem:completion-flat-local"
  (statement := /-- Let $R\to R'$ be a flat local homomorphism of noetherian local rings. Then
    the induced homomorphism of completions $\hat R\to\hat R'$ is a flat local homomorphism,
    compatible with the canonical maps $R\to\hat R$, $R'\to\hat R'$. -/)
  (proof := /-- Cited, not proved in the paper: footnote~3, p.~116 (``The two chapters, VII and
    VIII, of Samuel-Zariski, [18], should cover all that we need from the theory of local rings.
    A complete reference to the theory may be obtained from M. Nagata [15].''). Standard
    reference: Matsumura, \emph{Commutative Ring Theory}, \S8 and \S22 (numbering not
    checked). -/)
  (latexEnv := "lemma")]
theorem exists_flat_isLocalHom_adicCompletion_of_flat [Hironaka.Cited.ExistsFlatIsLocalHomAdicCompletionOfFlat.{u}] :
    ∀ {R R' : Type u} [CommRing R] [CommRing R']
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing R'] [IsNoetherianRing R'] [Algebra R R']
    [Module.Flat R R'] [IsLocalHom (algebraMap R R')],
    ∃ φ : AdicCompletion (maximalIdeal R) R →+* AdicCompletion (maximalIdeal R') R',
      (∀ x : R, φ (algebraMap R (AdicCompletion (maximalIdeal R) R) x) =
        algebraMap R' (AdicCompletion (maximalIdeal R') R') (algebraMap R R' x)) ∧
      φ.Flat ∧ IsLocalHom φ :=
  @Hironaka.Cited.ExistsFlatIsLocalHomAdicCompletionOfFlat.exists_flat_isLocalHom_adicCompletion_of_flat _

end Hironaka
