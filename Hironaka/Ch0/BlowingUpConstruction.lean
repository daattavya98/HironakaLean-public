/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch0.BlowingUpProj
public import Hironaka.Compat.StalkSymmetricAlgebra
public import Hironaka.Compat.RestrictedSections

/-!
# Ch. 0 §2 (pp. 124–125): the construction of a blowing-up of an `ℛ`-module

The construction of a blowing-up `(N, Φ)` of an arbitrary `ℛ`-module `M = (X, J)` in `𝓜(ℛ)`, and its claims.  The
ingredients (`𝐏^x`, `𝐏`, the sets `⟨U, ξ⟩`, `B(U, ξ)`, `I(U, ξ)`, the maps `α`, `β`, `γ`, `δ`) are defined as printed;
`(N, Φ)` itself is characterized by the printed conditions (`IsConstruction`).  The claims are `def … : Prop` and are not
proved here.  The paper's deduction "The basic existence theorem of blowing-up can be thus proved" from the two claims is
`basicExistenceOfBlowingUp_of_construction` at the end of this file.

> Now, in general, let M = (X, J) be an ℛ-module with X = (𝐗, O_X). We shall construct a blowing-up (N, Φ) of M in the
> category 𝓜(ℛ), where N = (P, I) with P = (𝐏, O_P). For each x ∈ 𝐗, we write (P^x, I^x) for the restriction
> P(O_x, J_x) | 𝐏^x where 𝐏^x denotes the set of those points of Proj(S_{O_x}(J_x)) which correspond to the unique
> closed point of Spec(O_x). (p. 124)

> Let P^x = (𝐏^x, O_{P^x}). We define the set 𝐏 as the disjoint union of 𝐏^x for all x ∈ 𝐗. We shall define a topology
> on 𝐏, a sheaf of local rings O_P on 𝐏, and a sheaf of O_P-modules I on 𝐏. Let U be any open subset of 𝐗. Let
> A(U) = Γ(U, O_X), J(U) = Γ(U, J), and S(U) = S_{A(U)}(J(U)), the symmetric tensor algebra over A(U). Let ξ be any
> homogeneous element of S(U). For every x ∈ U, we have a canonical homomorphism of S(U) to S_{O_x}(J_x). We denote by
> ξ_x the image of ξ by this homomorphism. We can view 𝐏^x as a set of homogeneous prime ideals in S_{O_x}(J_x), and we
> take the subset 𝐏^x(ξ) of 𝐏^x which consists of those homogeneous prime ideals which do not contain ξ_x. Let us
> denote by ⟨U, ξ⟩ the disjoint union of 𝐏^x(ξ) for all x ∈ U, which is viewed as a subset of 𝐏. We define the topology
> on 𝐏 by taking the family of subsets of the form ⟨U, ξ⟩ as a base of open subsets. For every pair (U, ξ) as above, we
> denote by B(U, ξ) (resp. I(U, ξ)) the homogeneous part of degree 0 (resp. of degree 1) of the ring of fractions of
> S(U) with respect to the powers of ξ. In view of the definition of (P^x, I^x), we see that if x ∈ U, then there exists
> a natural homomorphism of B(U, ξ) (resp. of I(U, ξ)) into Γ(𝐏^x(ξ), O_{P^x}) (resp. into Γ(P^x(ξ), I^x)), where
> 𝐏^x(ξ) = ⟨U, ξ⟩ ∩ 𝐏^x. Let W be any open subset of 𝐏. Then for every ⟨U, ξ⟩ ⊂ W, we have natural homomorphisms α
> (resp. β) of ∏_{x∈X} Γ(W ∩ 𝐏^x, O_{P^x}) (resp. of B(U, ξ)) to ∏_{x∈U} Γ(𝐏^x(ξ), O_{P^x}), and γ (resp. δ) of
> ∏_{x∈X} Γ(W ∩ 𝐏^x, I^x) (resp. of I(U, ξ)) to ∏_{x∈U} Γ(P^x(ξ), I^x). We define the stuctural [sic] sheaf O_P of P as
> follows: For every open subset W of 𝐏, Γ(W, O_P) is the subring of ∏_{x∈X} Γ(W ∩ 𝐏^x, O_{P^x}) consisting of those
> elements r such that for every x ∈ W, there exists s ∈ B(U, ξ) with x ∈ ⟨U, ξ⟩ ⊆ W and α(r) = β(s). We also define
> the sheaf of modules I on P as follows: For every open subset W of 𝐏, Γ(W, I) is the submodule of
> ∏_{x∈X} Γ(W ∩ 𝐏^x, I^x) consisting of those elements t such that for every x ∈ W, there exists u ∈ I(U, ξ) with
> x ∈ ⟨U, ξ⟩ ⊆ W and γ(t) = δ(u). We see that N = (P, I) with P = (𝐏, O_P) is an ℛ-module and that there exists a
> natural morphism Φ: N → M which is compatible with the canonical morphism of P(O_x, J_x) to S(O_x, J_x) for every
> x ∈ X. It is not difficult to prove that (P, Φ) is a blowing-up of M in the category 𝓜(ℛ). (p. 125)

## What is formalized

Step by step: `Hironaka/Compat/StalkSymmetricAlgebra.lean` (`A(U)`, `J(U)`, `S(U)`, `O_x`, `J_x`, `S_{O_x}(J_x)` and the
canonical homomorphism `S(U) → S_{O_x}(J_x)`, `germSym`), `Pts` (`𝐏`), `fibre` (`𝐏^x`), `HomElt`, `fibreBasic`
(`𝐏^x(ξ)`), `basic` (`⟨U, ξ⟩`) and the topology, `Bring` (`B(U, ξ)`), `Iring` (`I(U, ξ)`), `beta` (`β`), `delta` (`δ`),
`OProd`/`IProd` (the products), `alpha`, `gamma`, `IsSectionO`, `IsSectionI` (the printed conditions defining
`Γ(W, O_P)` and `Γ(W, I)`), `canonO`, `canonI`, `IsConstruction` (that `(N, Φ)` is the construction), and the two claims
`ConstructionIsRModule` and `ConstructionIsBlowingUp`.

## Formalization notes (encodings)

* The restriction of a sheaf to a subset `T` of the points of `Proj`, which is not open, is described by the
  sections over any set `V ⊆ T` of points: the functions on `V` with values in the stalks that are locally induced by
  sections over open sets (`Hironaka/Compat/RestrictedSections.lean`, `ORestr`, `IRestr`).  This is used for both
  `O_{P^x}` and `I^x` (the project's `LocallyRingedSpace.restrictSubset`, `Hironaka/Compat/RestrictSubset.lean`, is for rings only); the comparison with it is not proved here.  The sets
  `W ∩ 𝐏^x` and `𝐏^x(ξ)` are used as sets of points: the paper's sections over open subsets of `𝐏^x` are sections over
  these sets, which are open in `𝐏^x`.
* `𝐏^x` is the set of homogeneous primes `q` of `S_{O_x}(J_x)` with `q ∩ O_x = 𝔪_x` ("the points which correspond to the
  unique closed point"); that this is the preimage of the closed point under the canonical morphism is not proved here.
* The topology is the one generated by the sets `⟨U, ξ⟩`; that they form a base (as printed) is not proved here.
* `Γ(W, O_P)` and `Γ(W, I)` are given by the printed conditions on `∏_x Γ(W ∩ 𝐏^x, ·)` (`IsSectionO`, `IsSectionI`).  That
  they are a subring and a submodule, that restriction maps preserve them, that `O_P` is a sheaf of local rings, that
  `I` is a sheaf of `O_P`-modules and that `Φ` is a morphism are the paper's "we see" (and "subring", "submodule"); they are not
  proved here.  So `N` and `Φ` are not defined: the claims are stated about any pair `(N, Φ)` of an `ℛ`-module and a
  morphism that is the construction (`IsConstruction`): the space of `N` is `𝐏`, the sections of `O_N` and `I_N` over `W`
  correspond, by injective ring (resp. additive, compatible) homomorphisms compatible with restriction, exactly to the
  families with the printed conditions, and `Φ` lies over `(x, q) ↦ x` with `Φ♯(a)_x = a_x / 1` and `Φ♭(j)_x = ι(j_x) / 1`.
* In "for every `x ∈ W`" the point is a point of `W ⊆ 𝐏` (the letter `x` is also used for points of `𝐗`).
* "natural homomorphism" (`β`, `δ`) is `a / ξⁿ ↦ a_x / ξ_xⁿ`; `α`, `γ` are the restrictions.

## Misprints of the source

p. 125: "the stuctural sheaf" for "structural"; "(P, Φ) is a blowing-up of M" where `(N, Φ)` is meant; `𝐏^x(ξ)` and `P^x(ξ)` are used for the same set; `∏_{x∈X}` for `∏_{x∈𝐗}`.

-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ProjDegreeOne ProjectiveSpectrum.DegreeOne

set_option synthInstance.maxHeartbeats 400000

namespace Hironaka.Construction

universe u

variable (M : RModule.{u})

/-- The grading of `S_{O_x}(J_x)` by the symmetric powers. -/
abbrev stalkGrading (x : M.X.toTopCat) : ℕ → Submodule (stalkRing x) (symStalk M.J x) :=
  symmetricGrading (stalkRing x) (stalkMod M.J x)

/-- `Proj(S_{O_x}(J_x))`, as a scheme. -/
abbrev ProjAt (x : M.X.toTopCat) : Scheme.{u} := Proj (stalkGrading M x)

/-- `𝐏^x`: the points of `Proj(S_{O_x}(J_x))` over the closed point of `Spec(O_x)`.

> For each x ∈ 𝐗, we write (P^x, I^x) for the restriction P(O_x, J_x) | 𝐏^x where 𝐏^x denotes the set of those points of
> Proj(S_{O_x}(J_x)) which correspond to the unique closed point of Spec(O_x). (p. 124)

Definition (p. 124).  Formalization note (encoding): the points are the homogeneous primes `q` with `q ∩ O_x = 𝔪_x`. -/
@[blueprint "def:0.S2-construction-fibre"
  (statement := /-- For each $x\in\mathbf X$, $\mathbf P^x$ denotes the set of those points of $\operatorname{Proj}(S_{O_x}(J_x))$ which
    correspond to the unique closed point of $\operatorname{Spec}(O_x)$. (p.~124.) Formalization note (encoding): the
    homogeneous primes $q$ with $q\cap O_x=\mathfrak m_x$. -/)
  (latexEnv := "definition")]
def fibre (x : M.X.toTopCat) : Set (ProjectiveSpectrum (stalkGrading M x)) :=
  {q | q.asHomogeneousIdeal.toIdeal.comap (algebraMap (stalkRing x) (symStalk M.J x)) =
    IsLocalRing.maximalIdeal (stalkRing x)}

/-- The set `𝐏`: the disjoint union of the `𝐏^x`, `x ∈ 𝐗`.

> We define the set 𝐏 as the disjoint union of 𝐏^x for all x ∈ 𝐗. (p. 125)

Definition (p. 125). -/
@[blueprint "def:0.S2-construction-points"
  (statement := /-- We define the set $\mathbf P$ as the disjoint union of $\mathbf P^x$ for all $x\in\mathbf X$. (p.~125.) -/)
  (latexEnv := "definition")]
def Pts : Type u := (x : M.X.toTopCat) × fibre M x

variable {M}

/-- A homogeneous element `ξ` of `S(U)` (with its degree).

> Let ξ be any homogeneous element of S(U). (p. 125)

Formalization note (encoding): the degree is part of the data. -/
structure HomElt (U : Opens M.X) where
  /-- The degree. -/
  deg : ℕ
  /-- The element. -/
  elt : symSections M.J U
  /-- `elt` is homogeneous of degree `deg`. -/
  mem : elt ∈ symmetricGrading (sectionsRing U) (sectionsMod M.J U) deg

/-- `𝐏^x(ξ)`: the points of `𝐏^x` that are homogeneous primes not containing `ξ_x`.

> We can view 𝐏^x as a set of homogeneous prime ideals in S_{O_x}(J_x), and we take the subset 𝐏^x(ξ) of 𝐏^x which
> consists of those homogeneous prime ideals which do not contain ξ_x. (p. 125)

Definition (p. 125). -/
def fibreBasic {U : Opens M.X} (ξ : HomElt U) {x : M.X.toTopCat} (hx : x ∈ U) :
    Set (ProjectiveSpectrum (stalkGrading M x)) :=
  {q | q ∈ fibre M x ∧ germSym hx ξ.elt ∉ q.asHomogeneousIdeal.toIdeal}

/-- `⟨U, ξ⟩`: the disjoint union of the `𝐏^x(ξ)` for `x ∈ U`, as a subset of `𝐏`.

> Let us denote by ⟨U, ξ⟩ the disjoint union of 𝐏^x(ξ) for all x ∈ U, which is viewed as a subset of 𝐏. (p. 125)

Definition (p. 125). -/
@[blueprint "def:0.S2-construction-basic"
  (statement := /-- Let $\langle U,\xi\rangle$ denote the disjoint union of $\mathbf P^x(\xi)$ for all $x\in U$, viewed as a subset
    of $\mathbf P$. (p.~125.) -/)
  (latexEnv := "definition")]
def basic {U : Opens M.X} (ξ : HomElt U) : Set (Pts M) :=
  {p | ∃ hx : p.1 ∈ U, p.2.1 ∈ fibreBasic ξ hx}

variable (M) in
/-- The topology on `𝐏` with the sets `⟨U, ξ⟩` as a base of open sets.

> We define the topology on 𝐏 by taking the family of subsets of the form ⟨U, ξ⟩ as a base of open subsets. (p. 125)

Definition (p. 125).  Formalization note (encoding): the topology generated by these sets; the paper does not show
that they form a base, and this is not proved here. -/
@[blueprint "def:0.S2-construction-topology"
  (statement := /-- We define the topology on $\mathbf P$ by taking the family of subsets of the form $\langle U,\xi\rangle$ as a
    base of open subsets. (p.~125.) Formalization note (encoding): the topology generated by these sets. -/)
  (latexEnv := "definition")]
instance : TopologicalSpace (Pts M) :=
  TopologicalSpace.generateFrom {S | ∃ (U : Opens M.X) (ξ : HomElt U), S = basic ξ}

/-- `B(U, ξ)`: the homogeneous part of degree `0` of the ring of fractions of `S(U)` with respect to the powers
of `ξ`.

> For every pair (U, ξ) as above, we denote by B(U, ξ) (resp. I(U, ξ)) the homogeneous part of degree 0 (resp. of
> degree 1) of the ring of fractions of S(U) with respect to the powers of ξ. (p. 125)

Definition (p. 125).  Formalization note (encoding): Mathlib's `HomogeneousLocalization.Away`. -/
abbrev Bring {U : Opens M.X} (ξ : HomElt U) : Type u :=
  HomogeneousLocalization.Away (symmetricGrading (sectionsRing U) (sectionsMod M.J U)) ξ.elt

/-- `I(U, ξ)`: the homogeneous part of degree `1` of the ring of fractions of `S(U)` with respect to the powers
of `ξ`: the fractions `a / ξⁿ` with `a` of degree `n · deg ξ + 1`.

> … I(U, ξ) the homogeneous part of … degree 1 of the ring of fractions of S(U) with respect to the powers of ξ. (p. 125)

Definition (p. 125). -/
def Iring {U : Opens M.X} (ξ : HomElt U) : Type u :=
  {y : Localization.Away ξ.elt //
    ∃ (n : ℕ) (a : symmetricGrading (sectionsRing U) (sectionsMod M.J U) (n * ξ.deg + 1)),
      y = Localization.mk (a : symSections M.J U) ⟨ξ.elt ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers ξ.elt) n⟩}

/-- The germ map as a graded ring homomorphism `S(U) → S_{O_x}(J_x)`. -/
def germGraded {U : Opens M.X} {x : M.X.toTopCat} (hx : x ∈ U) :
    symmetricGrading (sectionsRing U) (sectionsMod M.J U) →+*ᵍ stalkGrading M x where
  toRingHom := germSym hx
  map_mem := fun {i _} h => germSym_mem_grading hx i h

/-- The natural homomorphism `β : B(U, ξ) → Γ(𝐏^x(ξ), O_{P^x})` (p. 125: "if `x ∈ U`, then there exists a natural
homomorphism of `B(U, ξ)` into `Γ(𝐏^x(ξ), O_{P^x})`"): `a / ξⁿ ↦ a_x / ξ_xⁿ`, the section of the structure sheaf of
`Proj(S_{O_x}(J_x))` over `D₊(ξ_x)` given by the image of the fraction under the germ map (Mathlib's
`awayToSection`), restricted to `𝐏^x(ξ)`. -/
def beta {U : Opens M.X} (ξ : HomElt U) {x : M.X.toTopCat} (hx : x ∈ U) (b : Bring ξ) :
    ORestr (stalkGrading M x) (fibreBasic ξ hx) :=
  let b' : HomogeneousLocalization.Away (stalkGrading M x) (germSym hx ξ.elt) :=
    HomogeneousLocalization.map (germGraded hx)
      (Submonoid.powers_le.mpr (Submonoid.mem_powers (germSym hx ξ.elt))) b
  let t := (ProjectiveSpectrum.Proj.awayToSection (stalkGrading M x) (germSym hx ξ.elt)).hom b'
  ⟨fun q => t.1 ⟨q.1, (ProjectiveSpectrum.mem_basicOpen _ _ _).mpr q.2.2⟩,
    fun q => ⟨ProjectiveSpectrum.basicOpen (stalkGrading M x) (germSym hx ξ.elt),
      (ProjectiveSpectrum.mem_basicOpen _ _ _).mpr q.2.2, t, fun _ _ => rfl⟩⟩

/-- The localization map `S(U)_ξ → (S_{O_x}(J_x))_q` induced by the germ map, for a point `q` with `ξ_x ∉ q`. -/
def lam {U : Opens M.X} (ξ : HomElt U) {x : M.X.toTopCat} (hx : x ∈ U)
    (q : ProjectiveSpectrum (stalkGrading M x))
    (hq : germSym hx ξ.elt ∉ q.asHomogeneousIdeal.toIdeal) :
    Localization.Away ξ.elt →+* Localization q.asHomogeneousIdeal.toIdeal.primeCompl :=
  IsLocalization.map (Localization q.asHomogeneousIdeal.toIdeal.primeCompl) (germSym hx)
    (Submonoid.powers_le.mpr (show ξ.elt ∈ q.asHomogeneousIdeal.toIdeal.primeCompl.comap (germSym hx)
      from hq))

theorem lam_mk {U : Opens M.X} (ξ : HomElt U) {x : M.X.toTopCat} (hx : x ∈ U)
    (q : ProjectiveSpectrum (stalkGrading M x))
    (hq : germSym hx ξ.elt ∉ q.asHomogeneousIdeal.toIdeal) (n : ℕ) (a : symSections M.J U) :
    lam ξ hx q hq (Localization.mk a ⟨ξ.elt ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers ξ.elt) n⟩) =
      Localization.mk (germSym hx a) ⟨germSym hx ξ.elt ^ n,
        Submonoid.pow_mem q.asHomogeneousIdeal.toIdeal.primeCompl (show germSym hx ξ.elt ∈ _ from hq) n⟩ := by
  rw [Localization.mk_eq_mk', lam, IsLocalization.map_mk', ← Localization.mk_eq_mk']
  congr 1
  exact Subtype.ext (map_pow _ _ _)

theorem lam_mem {U : Opens M.X} (ξ : HomElt U) {x : M.X.toTopCat} (hx : x ∈ U)
    (q : ProjectiveSpectrum (stalkGrading M x))
    (hq : germSym hx ξ.elt ∉ q.asHomogeneousIdeal.toIdeal) (y : Iring ξ) :
    lam ξ hx q hq y.1 ∈ ProjectiveSpectrum.DegreeOne.stalk (stalkGrading M x) q := by
  obtain ⟨n, a, hy⟩ := y.2
  rw [hy, lam_mk]
  have h1 : germSym hx ξ.elt ^ n ∈ stalkGrading M x (n * ξ.deg) := by
    have := SetLike.pow_mem_graded n (germSym_mem_grading hx ξ.deg ξ.mem)
    rwa [smul_eq_mul] at this
  exact ⟨n * ξ.deg, ⟨germSym hx a, germSym_mem_grading hx _ a.2⟩, ⟨_, h1⟩,
    Submonoid.pow_mem _ (show germSym hx ξ.elt ∈ _ from hq) n, rfl⟩

/-- The natural homomorphism `δ : I(U, ξ) → Γ(𝐏^x(ξ), I^x)` (p. 125: "if `x ∈ U`, then there exists a natural
homomorphism of `I(U, ξ)` into `Γ(𝐏^x(ξ), I^x)`"): `a / ξⁿ ↦ a_x / ξ_xⁿ`, a section of the sheaf of degree-one
elements of `Proj(S_{O_x}(J_x))` over `D₊(ξ_x)`, restricted to `𝐏^x(ξ)`. -/
def delta {U : Opens M.X} (ξ : HomElt U) {x : M.X.toTopCat} (hx : x ∈ U) (y : Iring ξ) :
    IRestr (stalkGrading M x) (fibreBasic ξ hx) :=
  let t : (inType (stalkGrading M x)).1.obj
      (op (ProjectiveSpectrum.basicOpen (stalkGrading M x) (germSym hx ξ.elt))) :=
    ⟨fun q => ⟨lam ξ hx q.1 ((ProjectiveSpectrum.mem_basicOpen _ _ _).mp q.2) y.1,
        lam_mem ξ hx q.1 ((ProjectiveSpectrum.mem_basicOpen _ _ _).mp q.2) y⟩,
      fun q => by
        obtain ⟨n, a, hy⟩ := y.2
        have h1 : germSym hx ξ.elt ^ n ∈ stalkGrading M x (n * ξ.deg) := by
          have := SetLike.pow_mem_graded n (germSym_mem_grading hx ξ.deg ξ.mem)
          rwa [smul_eq_mul] at this
        refine ⟨_, q.2, 𝟙 _, n * ξ.deg, ⟨germSym hx a, germSym_mem_grading hx _ a.2⟩, ⟨_, h1⟩,
          fun q' => (den (stalkGrading M x) q'.1).pow_mem
            ((ProjectiveSpectrum.mem_basicOpen _ _ _).mp q'.2) n, fun q' => ?_⟩
        change lam ξ hx q'.1 _ y.1 = _
        rw [hy]
        exact lam_mk ξ hx q'.1 _ n a⟩
  ⟨fun q => ⟨lam ξ hx q.1 q.2.2 y.1, lam_mem ξ hx q.1 q.2.2 y⟩,
    fun q => ⟨_, (ProjectiveSpectrum.mem_basicOpen _ _ _).mpr q.2.2, t, fun _ _ => rfl⟩⟩

variable (W : Set (Pts M))

/-- `W ∩ 𝐏^x`, as a set of points of `Proj(S_{O_x}(J_x))`. -/
def fibreSet (x : M.X.toTopCat) : Set (ProjectiveSpectrum (stalkGrading M x)) :=
  {q | ∃ h : q ∈ fibre M x, (⟨x, ⟨q, h⟩⟩ : Pts M) ∈ W}

variable {W}

theorem fibreSet_mono {W' : Set (Pts M)} (h : W' ⊆ W) (x : M.X.toTopCat) :
    fibreSet W' x ⊆ fibreSet W x := fun _ ⟨hq, hW⟩ => ⟨hq, h hW⟩

variable (W)

/-- `∏_{x ∈ 𝐗} Γ(W ∩ 𝐏^x, O_{P^x})`. -/
abbrev OProd : Type u := ∀ x : M.X.toTopCat, ORestr (stalkGrading M x) (fibreSet W x)

/-- `∏_{x ∈ 𝐗} Γ(W ∩ 𝐏^x, I^x)`, a module over `OProd`. -/
abbrev IProd : Type u := ∀ x : M.X.toTopCat, IRestr (stalkGrading M x) (fibreSet W x)

variable {W}

/-- Restriction of the products to a smaller subset. -/
def resO {W' : Set (Pts M)} (h : W' ⊆ W) : OProd W →+* OProd W' :=
  RingHom.pi fun x => (ORestr.res (fibreSet_mono h x)).comp (Pi.evalRingHom _ x)

/-- Restriction of the products to a smaller subset (a function; its additivity is not needed). -/
def resI {W' : Set (Pts M)} (h : W' ⊆ W) (t : IProd W) : IProd W' :=
  fun x => IRestr.res (fibreSet_mono h x) (t x)

theorem fibreBasic_subset {U : Opens M.X} (ξ : HomElt U) (hsub : basic ξ ⊆ W) {x : M.X.toTopCat}
    (hx : x ∈ U) : fibreBasic ξ hx ⊆ fibreSet W x :=
  fun _ hq => ⟨hq.1, hsub ⟨hx, hq⟩⟩

/-- The natural homomorphism `α : ∏_{x ∈ 𝐗} Γ(W ∩ 𝐏^x, O_{P^x}) → ∏_{x ∈ U} Γ(𝐏^x(ξ), O_{P^x})`, for `⟨U, ξ⟩ ⊆ W`
(restriction of sections). -/
def alpha {U : Opens M.X} (ξ : HomElt U) (hsub : basic ξ ⊆ W) :
    OProd W →+* (∀ x : U, ORestr (stalkGrading M x.1) (fibreBasic ξ x.2)) :=
  RingHom.pi fun x => (ORestr.res (fibreBasic_subset ξ hsub x.2)).comp (Pi.evalRingHom _ x.1)

/-- The natural homomorphism `γ : ∏_{x ∈ 𝐗} Γ(W ∩ 𝐏^x, I^x) → ∏_{x ∈ U} Γ(𝐏^x(ξ), I^x)`, for `⟨U, ξ⟩ ⊆ W`
(restriction of sections; a function, its additivity is not needed). -/
def gamma {U : Opens M.X} (ξ : HomElt U) (hsub : basic ξ ⊆ W) (t : IProd W) :
    ∀ x : U, IRestr (stalkGrading M x.1) (fibreBasic ξ x.2) :=
  fun x => IRestr.res (fibreBasic_subset ξ hsub x.2) (t x.1)

/-- `β` on all of `U`: `B(U, ξ) → ∏_{x ∈ U} Γ(𝐏^x(ξ), O_{P^x})`. -/
def betaAll {U : Opens M.X} (ξ : HomElt U) (b : Bring ξ) :
    ∀ x : U, ORestr (stalkGrading M x.1) (fibreBasic ξ x.2) := fun x => beta ξ x.2 b

/-- `δ` on all of `U`: `I(U, ξ) → ∏_{x ∈ U} Γ(𝐏^x(ξ), I^x)`. -/
def deltaAll {U : Opens M.X} (ξ : HomElt U) (y : Iring ξ) :
    ∀ x : U, IRestr (stalkGrading M x.1) (fibreBasic ξ x.2) := fun x => delta ξ x.2 y

/-- The elements `r` of `∏_{x ∈ 𝐗} Γ(W ∩ 𝐏^x, O_{P^x})` that are sections of the structural sheaf `O_P` over `W`.

> For every open subset W of 𝐏, Γ(W, O_P) is the subring of ∏_{x∈X} Γ(W ∩ 𝐏^x, O_{P^x}) consisting of those elements r such
> that for every x ∈ W, there exists s ∈ B(U, ξ) with x ∈ ⟨U, ξ⟩ ⊆ W and α(r) = β(s). (p. 125)

Definition (p. 125).  Formalization note (encoding): the condition only; that these form a subring is not proved
here (see the module docstring). -/
@[blueprint "def:0.S2-construction-sections-O"
  (statement := /-- For every open subset $W$ of $\mathbf P$, $\Gamma(W,O_P)$ is the subring of
    $\prod_{x}\Gamma(W\cap\mathbf P^x,O_{P^x})$ consisting of those elements $r$ such that for every point of $W$ there exists
    $s\in B(U,\xi)$ with the point in $\langle U,\xi\rangle\subseteq W$ and $\alpha(r)=\beta(s)$. (p.~125.)
    Formalization note (encoding): the condition on $r$; that these elements form a subring is not proved here. -/)
  (latexEnv := "definition")]
def IsSectionO (r : OProd W) : Prop :=
  ∀ p ∈ W, ∃ (U : Opens M.X) (ξ : HomElt U) (_ : p ∈ basic ξ) (hsub : basic ξ ⊆ W) (s : Bring ξ),
    alpha ξ hsub r = betaAll ξ s

/-- The elements `t` of `∏_{x ∈ 𝐗} Γ(W ∩ 𝐏^x, I^x)` that are sections of the sheaf of modules `I` over `W`.

> For every open subset W of 𝐏, Γ(W, I) is the submodule of ∏_{x∈X} Γ(W ∩ 𝐏^x, I^x) consisting of those elements t such
> that for every x ∈ W, there exists u ∈ I(U, ξ) with x ∈ ⟨U, ξ⟩ ⊆ W and γ(t) = δ(u). (p. 125)

Definition (p. 125).  Formalization note (encoding): the condition only; see the module docstring. -/
@[blueprint "def:0.S2-construction-sections-I"
  (statement := /-- For every open subset $W$ of $\mathbf P$, $\Gamma(W,I)$ is the submodule of
    $\prod_{x}\Gamma(W\cap\mathbf P^x,I^x)$ consisting of those elements $t$ such that for every point of $W$ there exists
    $u\in I(U,\xi)$ with the point in $\langle U,\xi\rangle\subseteq W$ and $\gamma(t)=\delta(u)$. (p.~125.)
    Formalization note (encoding): the condition on $t$. -/)
  (latexEnv := "definition")]
def IsSectionI (t : IProd W) : Prop :=
  ∀ p ∈ W, ∃ (U : Opens M.X) (ξ : HomElt U) (_ : p ∈ basic ξ) (hsub : basic ξ ⊆ W) (u : Iring ξ),
    gamma ξ hsub t = deltaAll ξ u

open Classical in
variable (M) in
/-- The component at `x` of the section of `O_P` over `W` induced by `a ∈ A(U)`: the image of the germ `a_x` in the
degree-zero part of `S_{O_x}(J_x)` (zero for `x ∉ U`, where it is not used). -/
def canonO {U : Opens M.X} (a : sectionsRing U) (W : Set (Pts M)) : OProd W := fun x =>
  ⟨fun q => if hx : x ∈ U then
      HomogeneousLocalization.fromZeroRingHom (stalkGrading M x) _ (zeroHom (stalkGrading M x) (germRing hx a))
    else 0,
    fun q => by
      by_cases hx : x ∈ U
      · exact ⟨⊤, trivial, structureRingHom (stalkGrading M x) (germRing hx a), fun q' _ => by
          simp only [dif_pos hx]; rfl⟩
      · exact ⟨⊤, trivial, 0, fun q' _ => by simp only [dif_neg hx]; rfl⟩⟩

open Classical in
/-- The component at `x` of the section of `I` over `W` induced by `j ∈ J(U)`: the image `ι(j_x) / 1` of the germ
`j_x ∈ J_x = S_{O_x}(J_x)₁` (zero for `x ∉ U`). -/
def canonI {U : Opens M.X} (j : sectionsMod M.J U) (W : Set (Pts M)) : IProd W := fun x =>
  ⟨fun q => if hx : x ∈ U then
      (degreeOneSection (stalkGrading M x)
        (SymmetricAlgebra.ι (stalkRing x) (stalkMod M.J x) (germMod hx j))
        (symmetric_ι_mem _ _ _)).1 ⟨q.1, trivial⟩
    else 0,
    fun q => by
      by_cases hx : x ∈ U
      · exact ⟨⊤, trivial, degreeOneSection (stalkGrading M x)
          (SymmetricAlgebra.ι (stalkRing x) (stalkMod M.J x) (germMod hx j))
          (symmetric_ι_mem _ _ _), fun q' _ => by simp only [dif_pos hx]⟩
      · exact ⟨⊤, trivial, 0, fun q' _ => by simp only [dif_neg hx]; rfl⟩⟩

/-- Images of nested open sets are nested. -/
theorem imgMono {N : RModule.{u}} (e : N.X.toTopCat ≃ₜ Pts M) {W W' : Opens N.X} (hle : W' ≤ W) :
    e '' (W' : Set N.X.toTopCat) ⊆ e '' (W : Set N.X.toTopCat) :=
  Set.image_mono (show (W' : Set N.X.toTopCat) ⊆ W from hle)

/-- `(N, Φ)` is the construction of pp. 124–125 for `M`: the space of `N` is `𝐏` with the topology generated by the sets
`⟨U, ξ⟩`, the sections of `O_N` and of `I_N` over an open `W` are exactly the families satisfying the printed
conditions (as subring, resp. submodule, of the products `∏_x Γ(W ∩ 𝐏^x, ·)`, compatibly with restriction), and `Φ` lies
over `(x, q) ↦ x` and is compatible with the canonical morphisms `P(O_x, J_x) → S(O_x, J_x)`.

Definition (pp. 124–125; the construction `N = (P, I)` with `Φ`), as a characterization of the output because the
printed properties of the construction ("we see that `N` is an `ℛ`-module") are not proved here. -/
@[blueprint "def:0.S2-construction"
  (statement := /-- The construction of pp.~124--125: given an $\mathcal R$-module $M=(X,J)$, $N=(P,I)$ with $P=(\mathbf P,O_P)$ and
    $\Phi\colon N\to M$, where $\mathbf P$ carries the topology with base $\langle U,\xi\rangle$ and $\Gamma(W,O_P)$,
    $\Gamma(W,I)$ are the sub-objects of the products defined above. Formalization note (encoding): stated as a
    characterization of a pair $(N,\Phi)$, since that $N$ is an $\mathcal R$-module is not proved here. -/)
  (latexEnv := "definition")]
def IsConstruction (N : RModule.{u}) (Φ : N ⟶ M) : Prop :=
  ∃ (e : N.X.toTopCat ≃ₜ Pts M)
    (θO : ∀ W : Opens N.X, sectionsRing W →+* OProd (e '' (W : Set N.X.toTopCat)))
    (θI : ∀ W : Opens N.X, sectionsMod N.J W → IProd (e '' (W : Set N.X.toTopCat))),
    (∀ p, Φ.f.base p = (e p).1) ∧
    (∀ W : Opens N.X, Function.Injective (θO W) ∧ Set.range (θO W) = {r | IsSectionO r}) ∧
    (∀ W : Opens N.X, Function.Injective (θI W) ∧ Set.range (θI W) = {t | IsSectionI t}) ∧
    (∀ (W : Opens N.X) a b, θI W (a + b) = θI W a + θI W b) ∧
    (∀ (W : Opens N.X) (r : sectionsRing W) (m : sectionsMod N.J W), θI W (r • m) = fun x => θO W r x • θI W m x) ∧
    (∀ (W W' : Opens N.X) (hle : W' ≤ W) (s : sectionsRing W),
      θO W' ((N.X.presheaf.map (homOfLE hle).op).hom s) = resO (imgMono e hle) (θO W s)) ∧
    (∀ (W W' : Opens N.X) (hle : W' ≤ W) (m : sectionsMod N.J W),
      θI W' ((N.J.val.presheaf.map (homOfLE hle).op).hom m) = resI (imgMono e hle) (θI W m)) ∧
    (∀ (U : Opens M.X) (a : sectionsRing U),
      θO ((Opens.map Φ.f.base).obj U) ((Φ.f.c.app (op U)).hom a) = canonO M a _) ∧
    (∀ (U : Opens M.X) (j : sectionsMod M.J U),
      θI ((Opens.map Φ.f.base).obj U)
        ((((OModules.pullbackPushforwardAdjunction Φ.f).homEquiv _ _ Φ.φ).val.app (op U)).hom j) =
          canonI j _)

/-- The construction yields, for every `ℛ`-module `M`, an `ℛ`-module `N` and a morphism `Φ : N → M`.

> We see that N = (P, I) with P = (𝐏, O_P) is an ℛ-module and that there exists a natural morphism Φ: N → M which is
> compatible with the canonical morphism of P(O_x, J_x) to S(O_x, J_x) for every x ∈ X. (p. 125)

Stated without argument ("we see", p. 125); not proved here. -/
@[blueprint "prop:0.S2-construction-is-rmodule"
  (statement := /-- We see that $N=(P,I)$ with $P=(\mathbf P,O_P)$ is an $\mathcal R$-module and that there exists a natural morphism
    $\Phi\colon N\to M$ which is compatible with the canonical morphism of $P(O_x,J_x)$ to $S(O_x,J_x)$ for every $x$.
    (p.~125.) Not proved here: stated without argument. -/)
  (latexEnv := "proposition")]
def ConstructionIsRModule : Prop :=
  ∀ M : RModule.{u}, ∃ (N : RModule.{u}) (Φ : N ⟶ M), IsConstruction N Φ

/-- `(P, Φ)` is a blowing-up of `M` in the category `𝓜(ℛ)`.

> It is not difficult to prove that (P, Φ) is a blowing-up of M in the category 𝓜(ℛ). (p. 125)

Stated without proof (p. 125); not proved here. -/
@[blueprint "thm:0.S2-construction-blowing-up"
  (statement := /-- It is not difficult to prove that $(P,\Phi)$ is a blowing-up of $M$ in the category
    $\mathcal M(\mathcal R)$. (p.~125.) Not proved here: stated without proof. -/)
  (latexEnv := "theorem")]
def ConstructionIsBlowingUp : Prop :=
  ∀ (M N : RModule.{u}) (Φ : N ⟶ M), IsConstruction N Φ → IsBlowingUp (𝟭 RModule.{u}) Φ

end Hironaka.Construction

namespace Hironaka

/-- The basic existence theorem of blowing-up, deduced from the construction of pp. 124–125.

> We see that N = (P, I) with P = (𝐏, O_P) is an ℛ-module and that there exists a natural morphism Φ: N → M which is
> compatible with the canonical morphism of P(O_x, J_x) to S(O_x, J_x) for every x ∈ X. It is not difficult to prove
> that (P, Φ) is a blowing-up of M in the category 𝓜(ℛ). The basic existence theorem of blowing-up can be thus
> proved. (p. 125)

Printed steps, in the printed order: (1) the construction gives an `ℛ`-module `N` and a morphism `Φ : N → M`
(`Construction.ConstructionIsRModule`: stated without argument, "We see that", p. 125; assumed, as in the paper);
(2) `(N, Φ)` is a blowing-up of `M` in `𝓜(ℛ)` (`Construction.ConstructionIsBlowingUp`: stated without proof, "It is not
difficult to prove that", p. 125; assumed, as in the paper); (3) hence `M` admits a blowing-up in `𝓜(ℛ)`: "The basic
existence theorem of blowing-up can be thus proved". -/
theorem basicExistenceOfBlowingUp_of_construction (hR : Construction.ConstructionIsRModule.{u})
    (hB : Construction.ConstructionIsBlowingUp.{u}) : BasicExistenceOfBlowingUp.{u} := by
  intro M
  -- (1) "We see that N = (P, I) with P = (𝐏, O_P) is an ℛ-module and that there exists a natural morphism Φ: N → M …"
  obtain ⟨N, Φ, hΦ⟩ := hR M
  -- (2) "It is not difficult to prove that (P, Φ) is a blowing-up of M in the category 𝓜(ℛ)."
  have h2 : IsBlowingUp (𝟭 RModule.{u}) Φ := hB M N Φ hΦ
  -- (3) "The basic existence theorem of blowing-up can be thus proved."
  exact ⟨N, Φ, h2⟩

end Hironaka

end
