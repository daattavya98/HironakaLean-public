/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch3.Basic
public import Hironaka.Compat.CurveResolution
public import Hironaka.Statements

/-!
# Finiteness of integral closures for rings essentially of finite type over a complete local ring
(footnote 10 of Ch. III §6 for non-complete rings; Ch. IV §3, p. 305)

The finiteness condition of footnote 10 (Cor. 3 (c) of Theorem 5, Ch. III) is used on p. 305, in
"applied to a monoidal transform of Ŝ_t with center Q̂_t which is residually algebraic over S_t and
such that S_{t+1} is a localization of the transform" (p. 305), for the local rings `R_1` of monoidal
transforms of the non-complete rings `Ŝ_t = O_{X̂_t,·}`; the paper never verifies it.  These rings
are essentially of finite type over the complete local ring `Ŝ`.

* `finite_integralClosure_of_essFiniteType` (**N**): a domain essentially of finite type over a
  complete noetherian local ring has finite integral closure (Nagata).  A hypothesis: a cited result (Nagata).
* `finite_integralClosure_localization_quotient_of_essFiniteType`: the bridge from (N) to the
  condition of footnote 10 (quotients by a prime, localization at a prime);
* `MonoidalTransform.essFiniteType_comp`, `essFiniteType_stalkStructureMap`: the rings of the
  frame step are essentially of finite type over `Ŝ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Hironaka

universe u

noncomputable section

section Nagata


/-- **(N)** A domain essentially of finite type over a complete noetherian local ring has finite
integral closure in its field of fractions.

Footnote 10 (p. 243): "This follows from the fact that R/Q'' satisfies the finiteness condition.
(Recall the fact that this condition is satisfied by every complete noetherian local ring without
nilpotent elements.)"  Used on p. 305 (Corollary 3 (c) of Theorem 5, Ch. III, for the non-complete
rings of monoidal transforms of `Ŝ_t`).  Cited leaf, a hypothesis.

Truth check of the formalization: `Algebra.EssFiniteType S A` says `A` is the localization of the
finitely generated subalgebra `S[s] ⊆ A` at the elements that are units in `A`; so `A` is a
localization of a finite-type algebra over the Nagata ring `S`, hence Nagata, hence its domains
have finite normalization; no hypothesis on `S → A` (injectivity, locality) or on the
characteristic is needed.  The hypothesis "complete" is `IsAdicComplete (maximalIdeal S) S`.

Footnote 10 (p. 243) "recalls the fact" for complete rings (a citation, without a reference).
The case needed on p. 305, non-complete rings of the (AB.5) step, is cited through footnote 3 of
the Introduction (p. 116: "The two chapters, VII and VIII, of Samuel-Zariski, [18], should cover
all that we need from the theory of local rings.  A complete reference to the theory may be
obtained from M. Nagata [15]."), Nagata's theory of pseudo-geometric rings.

Deviation from the paper (cited-leaf issue): the paper recalls the fact, without reference, for
complete noetherian reduced local rings; the use on p. 305 needs it for local domains essentially
of finite type over a complete local ring, which is the same theory: complete local rings are Nagata
(pseudo-geometric) rings, and finite-type algebras and localizations of Nagata rings are Nagata
(Nagata, *Local rings*, the chapter on pseudo-geometric rings; Matsumura, *Commutative Ring Theory*,
the section on Nagata rings; EGA IV, §7).
The leaf is stated more generally than the case recalled, and contains
`curve_finite_integralClosure` as the case `A = S`. -/
@[blueprint "lem:IV.AB-5-nagata-finite"
  (statement := /-- \textbf{(N)} Let $S$ be a complete noetherian local ring and $A$ a domain
    essentially of finite type over $S$ (a localization of a finitely generated $S$-algebra).
    Then the integral closure of $A$ in its field of fractions is a finite $A$-module.
    (Footnote~10, p.~243: ``This follows from the fact that $R/Q''$ satisfies the finiteness
    condition. (Recall the fact that this condition is satisfied by every complete noetherian
    local ring without nilpotent elements.)'' Used on p.~305.) -/)
  (proof := /-- Cited, not proved in the paper: ``(Recall the fact that this condition is satisfied
    by every complete noetherian local ring without nilpotent elements.)'' (footnote~10, p.~243).
    A complete local ring is a Nagata (pseudo-geometric) ring, and finite-type algebras and
    localizations of Nagata rings are Nagata: M.~Nagata, \emph{Local rings}, Interscience 1962 (the chapter on pseudo-geometric rings);
    H.~Matsumura, \emph{Commutative Ring Theory} (the section on Nagata rings); EGA IV, \S7;
    Mathlib does not have this.

    \textbf{Cited-leaf issue.} The case used on p.~305 is cited through footnote~3 of the
    Introduction (p.~116), which refers the theory of local rings to Zariski--Samuel and to
    Nagata [15].
    The paper recalls the fact, without reference, for complete
    noetherian reduced local rings. The use on p.~305 needs it for local domains essentially of
    finite type over a complete local ring, which is the same theory; the references are supplied
    by the formalization. The leaf is stated more generally than the case recalled, and contains
    \texttt{lem:III.1-derived-normal-ring-finite} as the case $A=S$. -/)
  (latexEnv := "lemma")]
theorem finite_integralClosure_of_essFiniteType [Hironaka.Cited.FiniteIntegralClosureOfEssFiniteType.{u}] :
    ∀ {S A : Type u} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S] [CommRing A] [IsDomain A]
    [Algebra S A] [Algebra.EssFiniteType S A],
    Module.Finite A (integralClosure A (FractionRing A)) :=
  @Hironaka.Cited.FiniteIntegralClosureOfEssFiniteType.finite_integralClosure_of_essFiniteType _

/-- The bridge from (N) to the finiteness condition of footnote 10: for an algebra `A` essentially
of finite type over a complete noetherian local ring `S` and primes `Q'' ≤ Q'` of `A`, the integral
closure of `A_{Q'}/Q''A_{Q'}` in its field of fractions is finite over it.

Deviation from the paper (gap filled): the paper does not verify footnote 10 for the non-complete
rings of p. 305; this reduces it to (N) (`D = A_{Q'}/Q''A_{Q'}` is a domain, a localization of a
quotient of `A`, hence essentially of finite type over `S`).
-/
@[blueprint "lem:IV.AB-5-nagata-bridge"
  (statement := /-- Let $S$ be a complete noetherian local ring, $A$ an $S$-algebra essentially of
    finite type and $Q''\subseteq Q'$ primes of $A$. Then the integral closure of
    $A_{Q'}/Q''A_{Q'}$ in its field of fractions is a finite module over it (the condition of
    footnote~10 of \S6, Ch.~III). -/)
  (proof := /-- $Q''A_{Q'}$ is prime since $Q''\subseteq Q'$, so $D=A_{Q'}/Q''A_{Q'}$ is a domain;
    it is essentially of finite type over $S$ (a localization of $A$, then a quotient); apply
    \cref{lem:IV.AB-5-nagata-finite}. \textbf{Deviation from the paper (gap filled).} The paper does not verify the finiteness condition of footnote~10 for the non-complete rings of p.~305; this reduces it to (N). -/)
  (proofUses := ["lem:IV.AB-5-nagata-finite"])
  (latexEnv := "lemma")]
theorem finite_integralClosure_localization_quotient_of_essFiniteType [Hironaka.Cited.FiniteIntegralClosureOfEssFiniteType.{u}] {S A : Type u} [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S] [CommRing A]
    [Algebra S A] [Algebra.EssFiniteType S A] (Q' Q'' : Ideal A) [Q'.IsPrime] [Q''.IsPrime]
    (hQ : Q'' ≤ Q') :
    Module.Finite (Localization.AtPrime Q' ⧸ Q''.map (algebraMap A (Localization.AtPrime Q')))
      (integralClosure (Localization.AtPrime Q' ⧸
        Q''.map (algebraMap A (Localization.AtPrime Q')))
        (FractionRing (Localization.AtPrime Q' ⧸
          Q''.map (algebraMap A (Localization.AtPrime Q'))))) := by
  have hdisj : Disjoint (Q'.primeCompl : Set A) (Q'' : Set A) :=
    Set.disjoint_left.mpr fun a ha haQ => ha (hQ haQ)
  have hprime : (Q''.map (algebraMap A (Localization.AtPrime Q'))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint Q'.primeCompl _ Q'' inferInstance hdisj
  have : IsDomain (Localization.AtPrime Q' ⧸ Q''.map (algebraMap A (Localization.AtPrime Q'))) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hprime
  exact finite_integralClosure_of_essFiniteType (S := S)

/-- Ring-homomorphism form of the bridge: `α : S → A` essentially of finite type. -/
theorem finite_integralClosure_localization_quotient_of_ringHom_essFiniteType [Hironaka.Cited.FiniteIntegralClosureOfEssFiniteType.{u}] {S A : Type u}
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
    [CommRing A] (α : S →+* A) (hα : α.EssFiniteType) (Q' Q'' : Ideal A) [Q'.IsPrime]
    [Q''.IsPrime] (hQ : Q'' ≤ Q') :
    Module.Finite (Localization.AtPrime Q' ⧸ Q''.map (algebraMap A (Localization.AtPrime Q')))
      (integralClosure (Localization.AtPrime Q' ⧸
        Q''.map (algebraMap A (Localization.AtPrime Q')))
        (FractionRing (Localization.AtPrime Q' ⧸
          Q''.map (algebraMap A (Localization.AtPrime Q'))))) := by
  let _ : Algebra S A := α.toAlgebra
  have _ : Algebra.EssFiniteType S A := hα
  exact finite_integralClosure_localization_quotient_of_essFiniteType (S := S) Q' Q'' hQ

end Nagata

section EssFiniteType

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

/-- The ring `R[x⁻¹P]` of a monoidal transform is a finitely generated `R`-algebra.

Deviation from the paper (gap filled): the paper writes "applied to a monoidal transform of Ŝ_t"
(p. 305) without saying that the transform is essentially of finite type over `Ŝ`.
-/
@[blueprint "lem:IV.AB-5-nagata-blowup-finite-type"
  (statement := /-- Let $R$ be a noetherian domain, $P$ an ideal and $x\in R\setminus\{0\}$. Then
    $R[x^{-1}P]\subseteq\operatorname{Frac}R$ is a finitely generated $R$-algebra. -/)
  (proof := /-- $P=(g_1,\dots,g_r)$, and $p/x=\sum c_ig_i/x$ for $p=\sum c_ig_i$, so
    $R[x^{-1}P]=R[g_1/x,\dots,g_r/x]$. \textbf{Deviation from the paper (gap filled).} The paper writes ``applied to a monoidal transform of $\hat S_t$'' (p.~305) without saying that the transform is essentially of finite type over $\hat S$. -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.finiteType_blowupAlgebra (x : R) :
    Algebra.FiniteType R (blowupAlgebra R P x) := by
  classical
  obtain ⟨G, hG⟩ := IsNoetherian.noetherian P
  rw [← Subalgebra.fg_iff_finiteType]
  refine ⟨G.image fun g => algebraMap R (FractionRing R) g / algebraMap R (FractionRing R) x, ?_⟩
  unfold blowupAlgebra
  refine le_antisymm (Algebra.adjoin_mono ?_) (Algebra.adjoin_le ?_)
  · intro y hy
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    exact ⟨g, hG ▸ Submodule.subset_span (Finset.mem_coe.mpr hg), rfl⟩
  · have key : ∀ p ∈ Submodule.span R (G : Set R),
        algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) x ∈ Algebra.adjoin R
          (↑(G.image fun g => algebraMap R (FractionRing R) g / algebraMap R (FractionRing R) x) :
            Set (FractionRing R)) := by
      intro p hp
      induction hp using Submodule.span_induction with
      | mem g hg =>
        exact Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨g, hg, rfl⟩))
      | zero => simp
      | add a b _ _ ha hb =>
        rw [map_add, add_div]
        exact add_mem ha hb
      | smul r a _ ha =>
        rw [smul_eq_mul, map_mul, mul_div_assoc]
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) ha
    rintro _ ⟨p, hp, rfl⟩
    exact key p (hG ▸ hp)

/-- A monoidal transform of `R` is essentially of finite type over `R`. -/
theorem MonoidalTransform.essFiniteType_toRing (t : MonoidalTransform R P) :
    t.toRing.EssFiniteType := by
  have h1 : (algebraMap R (blowupAlgebra R P t.x)).EssFiniteType := by
    have := MonoidalTransform.finiteType_blowupAlgebra (P := P) t.x
    exact (RingHom.finiteType_algebraMap.mpr this).essFiniteType
  have h2 : (algebraMap (blowupAlgebra R P t.x) t.ring).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization t.ring
      t.M'.primeCompl)
  exact h1.comp h2

/-- A monoidal transform of a ring essentially of finite type over `S` is essentially of finite
type over `S`.

Deviation from the paper (gap filled): as above (p. 305, "a monoidal transform of Ŝ_t").
-/
@[blueprint "lem:IV.AB-5-nagata-monoidal-ess-finite-type"
  (statement := /-- Let $R$ be a regular local domain essentially of finite type over $S$ and $R'$ a
    monoidal transform of $R$. Then $R'$ is essentially of finite type over $S$. -/)
  (proof := /-- $R'=R[x^{-1}P]_{M'}$ is a localization of the finite-type $R$-algebra
    $R[x^{-1}P]$ (\cref{lem:IV.AB-5-nagata-blowup-finite-type}); composites of essentially
    finite-type maps are essentially of finite type. \textbf{Deviation from the paper (gap
    filled).} As above (p.~305, ``a monoidal transform of $\hat S_t$''). -/)
  (proofUses := ["lem:IV.AB-5-nagata-blowup-finite-type"])
  (latexEnv := "lemma")]
theorem MonoidalTransform.essFiniteType_comp (t : MonoidalTransform R P) {S : Type*} [CommRing S]
    (α : S →+* R) (hα : α.EssFiniteType) : (t.toRing.comp α).EssFiniteType :=
  hα.comp t.essFiniteType_toRing

variable {S : Type u} [CommRing S] {Y : Scheme.{u}}

/-- The structure map `S → O_{Y,y}` of a scheme over `Spec S`. -/
def stalkStructureMap (g : Y ⟶ Spec (CommRingCat.of S)) (y : Y) : S →+* Y.presheaf.stalk y :=
  ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (Spec (CommRingCat.of S)).presheaf.germ ⊤ (g y)
    trivial ≫ g.stalkMap y).hom

/-- A stalk of a scheme locally of finite type over `Spec S` is essentially of finite type over
`S`.

Deviation from the paper (gap filled): the paper does not say that the local rings `Ŝ_t` of the
schemes `X̂_t` are essentially of finite type over `Ŝ`; this is Mathlib's
`LocallyOfFiniteType.stalkMap` composed with the localization `Ŝ → O_{Spec Ŝ,p}`.
-/
@[blueprint "lem:IV.AB-5-nagata-stalk-ess-finite-type"
  (statement := /-- Let $Y\to\operatorname{Spec}S$ be locally of finite type and $y\in Y$. Then
    $\mathcal O_{Y,y}$ is essentially of finite type over $S$. -/)
  (proof := /-- The structure map factors as the localization $S\to\mathcal
    O_{\operatorname{Spec}S,g(y)}$ followed by the stalk map of $g$, which is essentially of
    finite type for $g$ locally of finite type. \textbf{Deviation from the paper (gap filled).} The paper does not say that the local rings of the schemes $\hat X_t$ are essentially of finite type over $\hat S$. -/)
  (latexEnv := "lemma")]
theorem essFiniteType_stalkStructureMap (g : Y ⟶ Spec (CommRingCat.of S)) [LocallyOfFiniteType g]
    (y : Y) : (stalkStructureMap g y).EssFiniteType := by
  have h1 : (g.stalkMap y).hom.EssFiniteType := LocallyOfFiniteType.stalkMap g y
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
      (Spec (CommRingCat.of S)).presheaf.germ ⊤ (g y) trivial).hom.EssFiniteType := by
    have h := congrArg CommRingCat.Hom.hom (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of S)
      (show PrimeSpectrum (CommRingCat.of S) from g y))
    rw [← h, CommRingCat.hom_comp]
    have h3 : (algebraMap S (Localization.AtPrime (show PrimeSpectrum (CommRingCat.of S) from
        g y).asIdeal)).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization _
        (show PrimeSpectrum (CommRingCat.of S) from g y).asIdeal.primeCompl)
    have h4 : ((Spec.stalkIso (CommRingCat.of S) (show PrimeSpectrum (CommRingCat.of S) from
        g y)).inv).hom.EssFiniteType :=
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (C := CommRingCat) _).2).essFiniteType
    exact h3.comp h4
  exact h2.comp h1

/-- **The footnote-10 finiteness for a monoidal transform of a ring essentially of finite type
over a complete local ring**: closed from (N). -/
theorem finite_integralClosure_localization_quotient_of_monoidalTransform [Hironaka.Cited.FiniteIntegralClosureOfEssFiniteType.{u}] {S : Type u}
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
    (α : S →+* R) (hα : α.EssFiniteType) (t : MonoidalTransform R P) (Q' Q'' : Ideal t.ring)
    [Q'.IsPrime] [Q''.IsPrime] (hQ : Q'' ≤ Q') :
    Module.Finite (Localization.AtPrime Q' ⧸ Q''.map (algebraMap t.ring (Localization.AtPrime Q')))
      (integralClosure (Localization.AtPrime Q' ⧸
        Q''.map (algebraMap t.ring (Localization.AtPrime Q')))
        (FractionRing (Localization.AtPrime Q' ⧸
          Q''.map (algebraMap t.ring (Localization.AtPrime Q'))))) :=
  finite_integralClosure_localization_quotient_of_ringHom_essFiniteType (t.toRing.comp α)
    (t.essFiniteType_comp α hα) Q' Q'' hQ

end EssFiniteType

section Stalk

variable {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
  [IsAdicComplete (maximalIdeal S) S] {Y : Scheme.{u}}

/-- **The case of shared's helper** (`finiteIntegralClosureLocalizations_monoidalTransform`): a
monoidal transform `t` of the local ring `O_{Y,y}` of a scheme locally of finite type over `Spec S`,
`S` complete local, satisfies the finiteness condition of footnote 10.

This is what shared's `AB.Frame.finiteIntegralClosureLocalizations_monoidalTransform` needs, with
`Y = X̂_s`, `g : X̂_s → X̂_0 = Spec Ŝ`, `y = f̂(x̂)`, from (N).  Paper (p. 305): "applied to a
monoidal transform of Ŝ_t with center Q̂_t which is residually algebraic over S_t and such that
S_{t+1} is a localization of the transform."
-/
@[blueprint "lem:IV.AB-5-nagata-monoidal-transform"
  (statement := /-- Let $S$ be a complete noetherian local ring, $Y\to\operatorname{Spec}S$ locally
    of finite type, $y\in Y$ with $\mathcal O_{Y,y}$ a regular local domain, and $R'$ a monoidal
    transform of $\mathcal O_{Y,y}$. Then for primes $Q''\subseteq Q'$ of $R'$ the integral
    closure of $R'_{Q'}/Q''R'_{Q'}$ in its field of fractions is finite over it (the finiteness
    of footnote~10 for $R'$, used on p.~305). -/)
  (proof := /-- $\mathcal O_{Y,y}$ is essentially of finite type over $S$
    (\cref{lem:IV.AB-5-nagata-stalk-ess-finite-type}), hence so is $R'$
    (\cref{lem:IV.AB-5-nagata-monoidal-ess-finite-type}); apply \cref{lem:IV.AB-5-nagata-bridge}.
    \textbf{Deviation from the paper (gap filled).} The paper does not verify the finiteness. -/)
  (proofUses := ["lem:IV.AB-5-nagata-stalk-ess-finite-type",
    "lem:IV.AB-5-nagata-monoidal-ess-finite-type", "lem:IV.AB-5-nagata-bridge"])
  (latexEnv := "lemma")]
theorem finite_integralClosure_localization_quotient_of_stalk_monoidalTransform [Hironaka.Cited.FiniteIntegralClosureOfEssFiniteType.{u}]
    (g : Y ⟶ Spec (CommRingCat.of S)) [LocallyOfFiniteType g] (y : Y)
    [IsRegularLocalRing (Y.presheaf.stalk y)] [IsDomain (Y.presheaf.stalk y)]
    {P : Ideal (Y.presheaf.stalk y)} (t : MonoidalTransform (Y.presheaf.stalk y) P)
    (Q' Q'' : Ideal t.ring) [Q'.IsPrime] [Q''.IsPrime] (hQ : Q'' ≤ Q') :
    Module.Finite (Localization.AtPrime Q' ⧸ Q''.map (algebraMap t.ring (Localization.AtPrime Q')))
      (integralClosure (Localization.AtPrime Q' ⧸
        Q''.map (algebraMap t.ring (Localization.AtPrime Q')))
        (FractionRing (Localization.AtPrime Q' ⧸
          Q''.map (algebraMap t.ring (Localization.AtPrime Q'))))) :=
  finite_integralClosure_localization_quotient_of_monoidalTransform (stalkStructureMap g y)
    (essFiniteType_stalkStructureMap g y) t Q' Q'' hQ

end Stalk

section Completion

/-- The completion `Ŝ` of a noetherian local ring `S` is complete for its maximal ideal (the form
of completeness needed in (N)). -/
theorem isAdicComplete_maximalIdeal_adicCompletion (S : Type u) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] :
    IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal S) S))
      (AdicCompletion (maximalIdeal S) S) := by
  have h : IsAdicComplete (maximalIdeal S) (AdicCompletion (maximalIdeal S) S) :=
    AdicCompletion.isAdicComplete (IsNoetherian.noetherian _)
  have h2 := curve_isAdicComplete_map (maximalIdeal S) (B := AdicCompletion (maximalIdeal S) S)
  rwa [← AdicCompletion.maximalIdeal_eq_map] at h2

end Completion

end

end Hironaka
