/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch3.Basic
public import Hironaka.Ch3.NuStar
public import Hironaka.Ch3.TauStar
public import Hironaka.Ch3.Transforms
public import Hironaka.Ch3.Frames
public import Hironaka.Ch3.Stability
public import Hironaka.Ch0.NormalFlatness
public import Hironaka.Compat.FrameTransformCriterion
public import Hironaka.Compat.NormalizedStandardBase
public import Hironaka.Compat.PermissibleCenterBlowdown
public import Hironaka.Compat.NormalFlatnessLocalization
public import Hironaka.Compat.FrameLeadingCoefficient
public import Hironaka.Compat.TauParametersInPrime
public import Hironaka.Compat.FrameWithElement
public import Hironaka.Compat.Proposition2Steps
public import Hironaka.Compat.CompleteRationalBaseChange
public import Hironaka.Compat.TauZBaseChange
public import Hironaka.Compat.CompleteRationalFrameBaseChange
public import Hironaka.Compat.TauZCoreGraded
public import Hironaka.Compat.TauZAdapted
public import Hironaka.Ch3.FramePermissibleCenters
public import Hironaka.Statements

/-!
# Ch. III §8: Effects of permissible monoidal transformations on a normalized standard base
(pp. 253–261)

> 8. Effects of permissible monoidal transformations on a normalized standard base
>
> Let (S; z₁, …, z_r) be a regular frame of R, and P a prime ideal in R such that R/P is
> regular. Let R₁ be a monoidal transform of R with center P. We have an element x of R₁ such
> that PR₁ = (x)R₁. Such an element x of R₁ is uniquely determined up to a unit multiple of
> R₁. We shall say that (S; z₁, …, z_r) admits a frame transform in R₁ if there exist x ∈ R₁
> with (x)R₁ = PR₁ and a monoidal transform S₁ of S with center P ∩ S such that
> (S₁; z₁/x, …, z_r/x) is a regular frame of R₁ in a canonical manner.  (p. 253)

Contents, in the paper's order:

* p. 253: the denominator `x` of a monoidal transform (`lem:III.8-denominator`, proved);
* pp. 253–254: frame transforms — the definition (`def:III.8-admits-frame-transform`), the
  consequences "`P ⊇ (z)R`, `S/P ∩ S` regular, `S₁` unique"
  (`lem:III.8-frame-transform-unique`), the criterion by non-units
  (`lem:III.8-frame-transform-criterion`), and the frame transform `(S₁; z₁/x, …, z_r/x)` itself
  as a regular frame of `R₁` (`def:III.8-frame-transform`);
* Lemma 20 (pp. 254–256, `lem:III.20`) and Lemma 21 (pp. 256–258, `lem:III.21`);
* footnote 11 (p. 259): existence of a normalized standard base with respect to any regular
  τ-frame of a complete `R` (`lem:III.8-normalized-standard-base-exists`);
* Proposition 2 (pp. 258–259, `prop:III.8-2`);
* Corollary 1 (pp. 259–260, `cor:III.prop2-1`; footnote 12: "cf. Zariski [29].") and
  Corollary 2 (pp. 260–261, `cor:III.prop2-2`).

## Encoding

* A monoidal transform `R₁` of `R` with center `P` is `T : MonoidalTransform R P`, with
  `R₁ = T.ring` and canonical homomorphism `T.toRing : R → R₁`; the strict transform `J₁` of `J`
  is `strictTransformIdeal T J` (Definition 5).  That `R → R₁` is a local homomorphism and that
  `R₁` is a regular local ring are lemmas of §2 (pp. 209–210); as in the other files of Ch. III
  they appear as the instance hypotheses `[IsLocalHom T.toRing]` and `[IsRegularLocalRing T.ring]`.
  Likewise `[IsDomain R]` (needed to form `MonoidalTransform R P`) is a hypothesis.
* The coefficient ring `S` of a regular frame is a domain by the background lemma
  `Transforms.isDomain_of_isRegularLocalRing` (§2, proved): this is the local instance
  `RegularFrame.isDomain_S` below, needed to speak of monoidal transforms of `S`.
* `P ∩ S`, for a regular frame `(S; z)` of `R` (whose structure map `S → R` is injective), is the
  ideal `P.comap (algebraMap F.S R)` of `S`, and "`x ∈ P ∩ S`" is an element `x : F.S` whose image
  in `R` lies in `P`.
* `x⁻ᵛ f` (for `x` generating `PR₁` and `f ∈ R`) is, as in Definition 5 and Theorem 5, the
  element `g` of `R₁` with `xᵛ * g = f` in `R₁`; `R₁` is a domain, so `g` is unique.  Likewise
  `z_j/x` is the element `w_j` of `R₁` with `x * w_j = z_j`.
* `ν_P(f)` is `Ideal.ordElem P f`; `ν^{(j)}(J)` is `nuI R J j` (indexed by `ℕ+`; the paper's
  `j`-th element of a `0`-indexed system `f : Fin i → R` is `f j` and its character is
  `nuI R J (j : ℕ).succPNat`); `τ_{(z)}(f₁, …, f_i)` is `tauZ R z f`, `τ(f₁, …, f_i)` is
  `tauZ R ![] f` (Definition 10*), and `τ_{(z)}(f)` of one element is that of the one-element
  system `fun _ : Fin 1 => f`.
* "`(f₁, …, f_i, f)` can be extended to a standard base of `J`" is
  `ExtendsToStandardBase J (Fin.snoc f f')` (an initial segment of a standard base).
* "`R` has the same characteristic as its residue field" is
  `ringChar R = ringChar (ResidueField R)`: Mathlib has no named notion of equal characteristic
  (`Mathlib/Algebra/CharP/MixedCharZero.lean` only treats mixed and equal characteristic *zero*).
  "perfect field" is Mathlib's `PerfectField`.
* "`gr_P(R/J)` is flat over `R/P`" is, as in condition (ii) of Definition 8,
  `IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J))` (Definition 1 of Ch. 0: every graded
  piece is free, which for the noetherian local ring `R/J` is equivalent to the flatness of
  `gr_{P/J}(R/J)` over `R/P`); `R_Q` is `Localization.AtPrime Q`.

## Misprints of the printed text (marked [sic] in the proof texts)

* p. 253: "`z_i = x(z_i/x) ∈ PR₁ ∩ R₁ = P`" — the intersection is with `R`.
* p. 254 (proof of Lemma 20): "the residue field of `S̃` is separable algebraic over that of
  `S̃`" — read "over that of `S`".
* p. 259, footnote 11: "`(f₁, …, f_r, g)` can be extended to a standard base" — read
  "`(f₁, …, f_i, g)`".
* p. 260 (proof of Corollary 1): "`P₁ = (P₁)R₁` with `P₁ = P₁ ∩ R₁'`" — the primes are missing:
  "`P₁ = (P₁')R₁` with `P₁' = P₁ ∩ R₁'`".
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

/-! ### The denominator of a monoidal transform (p. 253) -/

section Denominator

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

/-- p. 253: "Let `(S; z₁, …, z_r)` be a regular frame of `R`, and `P` a prime ideal in `R` such
that `R/P` is regular. Let `R₁` be a monoidal transform of `R` with center `P`. We have an
element `x` of `R₁` such that `PR₁ = (x)R₁`. Such an element `x` of `R₁` is uniquely determined
up to a unit multiple of `R₁`."

The existence is `MonoidalTransform.span_xR_eq_map` of §2 (`x = T.xR`, the image of the element
defining `R[x⁻¹P]`); the uniqueness holds because `R₁` is a domain
(`Ideal.span_singleton_eq_span_singleton`).

(Formalization note: the regular frame of the setting plays no role in these two sentences and
does not appear in the statement; the standing hypotheses "`P` prime, `R/P` regular" are kept,
although the proof does not use them.) -/
@[blueprint "lem:III.8-denominator"
  (statement := /-- Let $R$ be a regular local ring, $P$ a prime ideal in $R$ such that $R/P$ is
    regular, and $R_1$ a monoidal transform of $R$ with center $P$
    (\cref{def:III.2-monoidal-transform}). We have an element $x$ of $R_1$ such that
    $PR_1=(x)R_1$. Such an element $x$ of $R_1$ is uniquely determined up to a unit multiple of
    $R_1$. (p.~253.) -/)
  (proof := /-- Stated without proof in the paper. If $R_1$ is a localization of $R[x^{-1}P]$
    with $x\in P$, then $PR_1=(x)R_1$, since every $p\in P$ is $x\cdot(p/x)$ with
    $p/x\in R[x^{-1}P]$ (\S2, p.~209). If $(x)R_1=(x')R_1$, then $x$ and $x'$ are associated
    elements of the domain $R_1$, i.e.\ $x'=ux$ with a unit $u$ of $R_1$. -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.exists_generator_unique_up_to_unit [P.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] (T : MonoidalTransform R P) :
    (∃ x : T.ring, Ideal.span {x} = P.map T.toRing) ∧
      ∀ x x' : T.ring, Ideal.span {x} = P.map T.toRing → Ideal.span {x'} = P.map T.toRing →
        ∃ u : (T.ring)ˣ, x' = u * x := by
  refine ⟨⟨T.xR, T.span_xR_eq_map⟩, fun x x' hx hx' => ?_⟩
  -- `(x)R₁ = (x')R₁` in the domain `R₁`: `x` and `x'` are associated
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (hx.trans hx'.symm)
  exact ⟨u, by rw [← hu, mul_comm]⟩

end Denominator

/-! ### Frame transforms (pp. 253–254) -/

section Domain

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The coefficient ring `S` of a regular frame `(S; z₁, …, z_r)` (Definition 9(1)) is a regular
local ring, hence a domain.  A regular local ring is a domain by the background lemma
`Transforms.isDomain_of_isRegularLocalRing` of §2 (not in Mathlib; proved in
`Hironaka/Compat/RegularQuotient.lean`, used tacitly by the paper).  This is needed to speak of
monoidal transforms of `S` (`MonoidalTransform` is defined for domains) and is made a *local*
instance of this file. -/
theorem RegularFrame.isDomain_S (F : RegularFrame R) : IsDomain F.S :=
  Transforms.isDomain_of_isRegularLocalRing F.S

end Domain

attribute [local instance] RegularFrame.isDomain_S

section FrameTransform

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

namespace RegularFrame

variable (F : RegularFrame R) {P : Ideal R}

open Classical in
/-- p. 253: "We shall say that `(S; z₁, …, z_r)` admits a frame transform in `R₁` if there exist
`x ∈ R₁` with `(x)R₁ = PR₁` and a monoidal transform `S₁` of `S` with center `P ∩ S` such that
`(S₁; z₁/x, …, z_r/x)` is a regular frame of `R₁` in a canonical manner."

A term of `F.FrameTransform T` is the data witnessing this for the regular frame
`F = (S; z₁, …, z_r)` of `R` and the monoidal transform `R₁ = T.ring`: the element `x ∈ R₁`, the
monoidal transform `S₁` of `S` with center `P ∩ S` (`TS`), the local homomorphism
`β : S₁ → R₁`, and the elements `w_j = z_j/x` of `R₁`, together with the conditions saying that
`(S₁; w₁, …, w_r)` is a regular frame of `R₁` (Definition 9(1)) "in a canonical manner".

(Formalization notes.
* `z_j/x` is the element `w j` of `R₁` with `x * w j = z_j` (`mul_w`); it is unique, `R₁` being a
  domain and `x ≠ 0`.
* "In a canonical manner" is encoded by: (i) `β : S₁ → R₁` is the *canonical* local homomorphism,
  i.e. it is local and `β ∘ (S → S₁) = (R → R₁) ∘ (S → R)` (`IsCanonicalLift`, p. 211); and
  (ii) the isomorphism `R₁/(w₁, …, w_r)R₁ ≅ S₁` of Definition 9(1) is the canonical one, i.e.
  the composite `S₁ → R₁ → R₁/(w)R₁` is bijective (`quot_bijective`), as for
  `RegularFrame.quot_bijective`.
* The remaining conditions of a regular frame are that `S₁` is a regular local ring
  (`isRegular`) and that `(w₁, …, w_r)` can be extended to a regular system of parameters of
  `R₁` (`extends_rsop`).
* The standing hypotheses of p. 253 on `P` ("a prime ideal in `R` such that `R/P` is regular")
  are imposed on the statements below, not on this definition.) -/
@[blueprint "def:III.8-admits-frame-transform"
  (statement := /-- Let $(S;z_1,\dots,z_r)$ be a regular frame of $R$ (\cref{def:III.9}), $P$ a
    prime ideal in $R$ such that $R/P$ is regular, and $R_1$ a monoidal transform of $R$ with
    center $P$ (\cref{def:III.2-monoidal-transform}). We say that $(S;z_1,\dots,z_r)$
    \emph{admits a frame transform in $R_1$} if there exist $x\in R_1$ with $(x)R_1=PR_1$ and
    a monoidal transform $S_1$ of $S$ with center $P\cap S$ such that $(S_1;z_1/x,\dots,z_r/x)$
    is a regular frame of $R_1$ in a canonical manner. (p.~253.)

    (Formalization note: the data of a frame transform are $x$, $S_1$, a local homomorphism
    $\beta\colon S_1\to R_1$ and elements $w_j\in R_1$ with $xw_j=z_j$ (the quotients
    $z_j/x$, unique since $R_1$ is a domain). ``$(S_1;w_1,\dots,w_r)$ is a regular frame of
    $R_1$ in a canonical manner'' is encoded as: $S_1$ is a regular local ring; $\beta$ is the
    canonical local homomorphism, i.e.\ it is local and
    $\beta\circ(S\to S_1)=(R\to R_1)\circ(S\to R)$ (p.~211); $(w_1,\dots,w_r)$ can be extended
    to a regular system of parameters of $R_1$; and the composite
    $S_1\to R_1\to R_1/(w_1,\dots,w_r)R_1$ is an isomorphism (the canonical form of the
    isomorphism $R_1/(w)R_1\cong S_1$ of Definition~9(1)). $P\cap S$ is the preimage of $P$
    under $S\to R$.) -/)
  (latexEnv := "definition")]
structure FrameTransform (T : MonoidalTransform R P) where
  /-- The denominator `x ∈ R₁`. -/
  x : T.ring
  /-- `(x)R₁ = PR₁`. -/
  span_x : Ideal.span {x} = P.map T.toRing
  /-- The monoidal transform `S₁` of `S` with center `P ∩ S`. -/
  TS : MonoidalTransform F.S (P.comap (algebraMap F.S R))
  /-- The local homomorphism `S₁ → R₁`. -/
  β : TS.ring →+* T.ring
  /-- `S₁ → R₁` is the canonical local homomorphism: it is local and it commutes with `S → R`
  and the canonical homomorphisms `S → S₁` and `R → R₁`. -/
  canonical : IsCanonicalLift (algebraMap F.S R) TS T β
  /-- `S₁` is a regular local ring. -/
  isRegular : IsRegularLocalRing TS.ring
  /-- The elements `w_j = z_j/x` of `R₁`. -/
  w : Fin F.r → T.ring
  /-- `x · (z_j/x) = z_j` in `R₁`. -/
  mul_w : ∀ j, x * w j = T.toRing (F.z j)
  /-- `(z₁/x, …, z_r/x)` can be extended to a regular system of parameters of `R₁`. -/
  extends_rsop : ExtendsToRSOP T.ring (Finset.image w Finset.univ)
  /-- `R₁/(z₁/x, …, z_r/x)R₁` is canonically isomorphic to `S₁`: the composite
  `S₁ → R₁ → R₁/(w)R₁` is bijective. -/
  quot_bijective :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span (Set.range w))).comp β)

/-- p. 253: "`(S; z₁, …, z_r)` admits a frame transform in `R₁`": there exists a frame transform
of the regular frame `F` in `R₁ = T.ring` (`FrameTransform`, which carries the encoding notes). -/
@[blueprint "def:III.8-admits-frame-transform"
  (statement := /-- $(S;z_1,\dots,z_r)$ admits a frame transform in $R_1$ if there exist
    $x\in R_1$ with $(x)R_1=PR_1$ and a monoidal transform $S_1$ of $S$ with center $P\cap S$
    such that $(S_1;z_1/x,\dots,z_r/x)$ is a regular frame of $R_1$ in a canonical manner.
    (p.~253.) -/)
  (latexEnv := "definition")]
def AdmitsFrameTransform (T : MonoidalTransform R P) : Prop :=
  Nonempty (F.FrameTransform T)

namespace FrameTransform

variable {F} {T : MonoidalTransform R P}

/-- p. 254: "We shall call `(S₁; z₁/x, …, z_r/x)` the frame transform of `(S; z₁, …, z_r)` in
`R₁` (with denominator `x`)."

The regular frame of `R₁` (Definition 9(1)) with coefficient ring `S₁`, structure map the
canonical local homomorphism `β : S₁ → R₁`, and system `(w₁, …, w_r)`, `w_j = z_j/x`; the
isomorphism `R₁/(w)R₁ ≅ S₁` is the inverse of the canonical isomorphism `S₁ → R₁/(w)R₁` of
`quot_bijective`.  All data (`S₁`, its ring structure, the algebra structure `β`, `r`, `w`)
come from the frame transform; the remaining fields are propositions. -/
@[blueprint "def:III.8-frame-transform"
  (statement := /-- Notation as in \cref{def:III.8-admits-frame-transform}. We call
    $(S_1;z_1/x,\dots,z_r/x)$ the \emph{frame transform} of $(S;z_1,\dots,z_r)$ in $R_1$ (with
    denominator $x$); it is a regular frame of $R_1$ (\cref{def:III.9}). (p.~254.)
    (Formalization note: the regular frame of $R_1$ with coefficient ring $S_1$, structure map
    the canonical local homomorphism $S_1\to R_1$ and system $(w_1,\dots,w_r)$, $w_j=z_j/x$,
    attached to the data of a frame transform.) -/)
  (latexEnv := "definition")]
noncomputable def toRegularFrame [IsRegularLocalRing T.ring] (FT : F.FrameTransform T) :
    RegularFrame T.ring where
  S := FT.TS.ring
  isRegular := FT.isRegular
  algebra := FT.β.toAlgebra
  isLocalHom := FT.canonical.isLocalHom
  r := F.r
  z := FT.w
  z_injective i j h := F.z_injective (T.toRing_injective (by rw [← FT.mul_w, ← FT.mul_w, h]))
  extends_rsop := FT.extends_rsop
  quot_bijective := FT.quot_bijective

@[simp]
theorem toRegularFrame_r [IsRegularLocalRing T.ring] (FT : F.FrameTransform T) :
    FT.toRegularFrame.r = F.r := rfl

@[simp]
theorem toRegularFrame_z [IsRegularLocalRing T.ring] (FT : F.FrameTransform T) :
    FT.toRegularFrame.z = FT.w := rfl

/-- The canonical map `R → R'` of a monoidal transform is injective. -/
private theorem toRing_injective_aux' {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {P : Ideal R} (t : MonoidalTransform R P) : Function.Injective t.toRing := by
  have h1 : Function.Injective (algebraMap R (blowupAlgebra R P t.x)) := by
    intro a b hab
    have := congrArg (fun y : blowupAlgebra R P t.x => (y : FractionRing R)) hab
    simp only [Subalgebra.coe_algebraMap] at this
    exact IsFractionRing.injective R (FractionRing R) this
  have h2 : Function.Injective (algebraMap (blowupAlgebra R P t.x) t.ring) :=
    IsLocalization.injective t.ring (Ideal.primeCompl_le_nonZeroDivisors t.M')
  exact h2.comp h1

/-- Every element of `R[x⁻¹P]` is `c/xⁿ` with `c ∈ Pⁿ`. -/
private theorem exists_eq_div_pow_aux {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {P : Ideal R} (t : MonoidalTransform R P) (a : blowupAlgebra R P t.x) :
    ∃ (n : ℕ) (c : R), c ∈ P ^ n ∧
      (a : FractionRing R) = algebraMap R (FractionRing R) c /
        algebraMap R (FractionRing R) t.x ^ n := by
  have hx0 : algebraMap R (FractionRing R) t.x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr t.x_ne_zero
  obtain ⟨a, ha⟩ := a
  simp only
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨1, p, by rwa [pow_one], by rw [pow_one]⟩
  | algebraMap r => exact ⟨0, r, by simp, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨n, c, hc, rfl⟩ := hy
    obtain ⟨m, d, hd, rfl⟩ := hz
    refine ⟨n + m, c * t.x ^ m + d * t.x ^ n, add_mem ?_ ?_, ?_⟩
    · rw [pow_add]
      exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow t.x_mem m)
    · rw [pow_add, mul_comm (P ^ n)]
      exact Ideal.mul_mem_mul hd (Ideal.pow_mem_pow t.x_mem n)
    · rw [div_add_div _ _ (pow_ne_zero _ hx0) (pow_ne_zero _ hx0)]
      simp only [map_add, map_mul, map_pow, pow_add]
      ring
  | mul y z _ _ hy hz =>
    obtain ⟨n, c, hc, rfl⟩ := hy
    obtain ⟨m, d, hd, rfl⟩ := hz
    refine ⟨n + m, c * d, by rw [pow_add]; exact Ideal.mul_mem_mul hc hd, ?_⟩
    rw [map_mul, pow_add, div_mul_div_comm]

/-- Conversely `c/xⁿ ∈ R[x⁻¹P]` for `c ∈ Pⁿ`. -/
private theorem div_pow_mem_aux {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {P : Ideal R} (t : MonoidalTransform R P) {n : ℕ} {c : R} (hc : c ∈ P ^ n) :
    algebraMap R (FractionRing R) c / algebraMap R (FractionRing R) t.x ^ n ∈
      blowupAlgebra R P t.x := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hc
    refine Submodule.mul_induction_on (C := fun c => algebraMap R (FractionRing R) c /
      algebraMap R (FractionRing R) t.x ^ (n + 1) ∈ blowupAlgebra R P t.x) hc ?_ ?_
    · intro a ha b hb
      rw [map_mul, pow_succ, mul_div_mul_comm]
      exact Subalgebra.mul_mem _ (ih ha) (Algebra.subset_adjoin ⟨b, hb, rfl⟩)
    · intro a b ha hb
      rw [map_add, add_div]
      exact Subalgebra.add_mem _ ha hb

/-- `ν ≤ ν_I(f)` implies `f ∈ Iᵛ`. -/
private theorem mem_pow_of_le_ordElem_aux' {A : Type*} [CommRing A] {I : Ideal A} {f : A}
    {ν : ℕ} (h : (ν : ℕ∞) ≤ Ideal.ordElem I f) : f ∈ I ^ ν := by
  by_contra hf
  cases ν with
  | zero => exact hf (by simp)
  | succ m =>
    have h' := h.trans (Ideal.ordElem_le_of_notMem hf)
    rw [Nat.cast_le] at h'
    omega

/-- `PR₁ ∩ R = P` for a monoidal transform `R₁` of `R` with a prime center `P` such that `R/P` is
regular: if `f = x · (a/s)` in `R₁` with `a = c/xⁿ`, `s = d/xⁿ` (`c, d ∈ Pⁿ`, `s ∉ M'`), then
`cx = fd`, and `f ∉ P` would give `ν_P(d) ≥ n + 1` (orders along `P` are additive), i.e.
`s = x · (d/xⁿ⁺¹) ∈ M'`. -/
private theorem comap_map_toRing_eq_aux {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {P : Ideal R} [P.IsPrime] [IsRegularLocalRing (R ⧸ P)]
    (T : MonoidalTransform R P) : (P.map T.toRing).comap T.toRing = P := by
  have hx0 : algebraMap R (FractionRing R) T.x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr T.x_ne_zero
  refine le_antisymm (fun f hf => ?_) Ideal.le_comap_map
  by_contra hfP
  rw [Ideal.mem_comap, ← T.span_xR_eq_map, Ideal.mem_span_singleton'] at hf
  obtain ⟨y, hy⟩ := hf
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective T.M'.primeCompl y
  -- `a · x = f · s` in `R[x⁻¹P]`
  have hA : a * algebraMap R _ T.x = algebraMap R _ f * (s : blowupAlgebra R P T.x) := by
    apply IsLocalization.injective T.ring (Ideal.primeCompl_le_nonZeroDivisors T.M')
    have hy' : IsLocalization.mk' T.ring a s *
        algebraMap (blowupAlgebra R P T.x) T.ring (algebraMap R _ T.x) =
        algebraMap (blowupAlgebra R P T.x) T.ring (algebraMap R _ f) := hy
    rw [map_mul, map_mul, ← IsLocalization.mk'_spec T.ring a s, mul_right_comm, hy']
  -- common denominators
  obtain ⟨n₁, c₁, hc₁, ha⟩ := exists_eq_div_pow_aux T a
  obtain ⟨n₂, d₂, hd₂, hs⟩ := exists_eq_div_pow_aux T (s : blowupAlgebra R P T.x)
  set c := c₁ * T.x ^ n₂
  set d := d₂ * T.x ^ n₁
  have hc : c ∈ P ^ (n₁ + n₂) := by
    rw [pow_add]; exact Ideal.mul_mem_mul hc₁ (Ideal.pow_mem_pow T.x_mem _)
  have hd : d ∈ P ^ (n₁ + n₂) := by
    rw [pow_add, mul_comm (P ^ n₁)]; exact Ideal.mul_mem_mul hd₂ (Ideal.pow_mem_pow T.x_mem _)
  have hs' : ((s : blowupAlgebra R P T.x) : FractionRing R) =
      algebraMap R (FractionRing R) d / algebraMap R (FractionRing R) T.x ^ (n₁ + n₂) := by
    rw [hs, div_eq_div_iff (pow_ne_zero _ hx0) (pow_ne_zero _ hx0)]
    simp only [d, map_mul, map_pow, pow_add]
    ring
  -- `c x = f d` in `R`
  have hcx : c * T.x = f * d := by
    apply IsFractionRing.injective R (FractionRing R)
    have := congrArg (fun z : blowupAlgebra R P T.x => (z : FractionRing R)) hA
    simp only [MulMemClass.coe_mul, Subalgebra.coe_algebraMap] at this
    rw [ha, hs'] at this
    rw [div_mul_eq_mul_div, mul_div_assoc', div_eq_div_iff (pow_ne_zero _ hx0)
      (pow_ne_zero _ hx0)] at this
    simp only [c, d, map_mul, map_pow] at this ⊢
    apply mul_right_cancel₀ (pow_ne_zero n₁ hx0)
    rw [pow_add] at this
    linear_combination this
  -- orders along `P`
  have hf0 : Ideal.ordElem P f = 0 := by
    have := Ideal.ordElem_le_of_notMem (m := 0) (by rwa [zero_add, pow_one])
    exact le_antisymm (by exact_mod_cast this) (by simp)
  have hdP : d ∈ P ^ (n₁ + n₂ + 1) := by
    apply mem_pow_of_le_ordElem_aux'
    have h1 : ((n₁ + n₂ + 1 : ℕ) : ℕ∞) ≤ Ideal.ordElem P (c * T.x) := by
      apply Ideal.le_ordElem
      rw [pow_succ]
      exact Ideal.mul_mem_mul hc T.x_mem
    rw [hcx, ordElem_mul_of_isRegularLocalRing P inferInstance, hf0, zero_add] at h1
    exact h1
  -- then `s = x · (d/xⁿ⁺¹) ∈ M'`
  apply s.2
  have hq := div_pow_mem_aux T hdP
  have hsx : (s : blowupAlgebra R P T.x) =
      algebraMap R (blowupAlgebra R P T.x) T.x * ⟨_, hq⟩ := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, Subalgebra.coe_algebraMap]
    rw [hs', pow_succ]
    field_simp
  rw [hsx]
  have hxM : T.x ∈ maximalIdeal R :=
    le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance) T.x_mem
  exact T.M'.mul_mem_right _ (T.le (Ideal.mem_map_of_mem _ hxM))

/-- Two monoidal transforms `S₁`, `S₁'` of `S` with center `Q` which admit canonical local
homomorphisms into a monoidal transform `R₁` of `R` over `φ : S → R` (with `S → R₁` injective)
are the same local ring in the field of quotients of `S`: an element `c/d` of `S₁` (`c, d ∈ Qⁿ`,
`d/x₁ⁿ ∉ M₁'`) is `(c/x₂ⁿ)/(d/x₂ⁿ)` with `d/x₂ⁿ ∉ M₂'`, because the images of `x₁` and `x₂` in
`R₁` both generate `QR₁`. -/
private theorem subring_le_of_isCanonicalLift_aux {S R : Type u} [CommRing S]
    [IsRegularLocalRing S] [IsDomain S] [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (φ : S →+* R) {Q : Ideal S} {P : Ideal R} (T : MonoidalTransform R P)
    (hinj : Function.Injective (T.toRing.comp φ)) (t₁ t₂ : MonoidalTransform S Q)
    (β₁ : t₁.ring →+* T.ring) (β₂ : t₂.ring →+* T.ring) (h₁ : IsCanonicalLift φ t₁ T β₁)
    (h₂ : IsCanonicalLift φ t₂ T β₂) : t₁.subring ≤ t₂.subring := by
  have hx0 : ∀ t : MonoidalTransform S Q, algebraMap S (FractionRing S) t.x ≠ 0 := fun t =>
    (map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr t.x_ne_zero
  -- the images of `x₁`, `x₂` in `R₁` generate `QR₁`, hence are associated
  have hgen : ∀ (t : MonoidalTransform S Q) (β : t.ring →+* T.ring),
      IsCanonicalLift φ t T β → Ideal.span {T.toRing (φ t.x)} = Q.map (T.toRing.comp φ) := by
    intro t β h
    rw [← h.comm, ← Ideal.map_map, ← t.span_xR_eq_map, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z => Ideal.span {z}) (RingHom.congr_fun h.comm t.x).symm
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp
    ((hgen t₁ β₁ h₁).trans (hgen t₂ β₂ h₂).symm)
  -- `β(ι(e)) · xⁿ = φ(d)` in `R₁` for `e = d/xⁿ`
  have hβ : ∀ (t : MonoidalTransform S Q) (β : t.ring →+* T.ring), IsCanonicalLift φ t T β →
      ∀ (n : ℕ) (d : S) (e : blowupAlgebra S Q t.x),
      (e : FractionRing S) = algebraMap S _ d / algebraMap S _ t.x ^ n →
      β (algebraMap _ t.ring e) * T.toRing (φ t.x) ^ n = T.toRing (φ d) := by
    intro t β h n d e he
    have hA : e * algebraMap S _ t.x ^ n = algebraMap S (blowupAlgebra S Q t.x) d := by
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap, he]
      field_simp [hx0 t]
    have := congrArg (fun z => β (algebraMap (blowupAlgebra S Q t.x) t.ring z)) hA
    simp only [map_mul, map_pow] at this
    rw [← RingHom.comp_apply β, ← RingHom.comp_apply β] at this
    have hc : ∀ z : S, β (algebraMap (blowupAlgebra S Q t.x) t.ring (algebraMap S _ z)) =
        T.toRing (φ z) := fun z => RingHom.congr_fun h.comm z
    rw [RingHom.comp_apply, RingHom.comp_apply, hc, hc] at this
    exact this
  rintro _ ⟨y, rfl⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective t₁.M'.primeCompl y
  obtain ⟨n₁, c₁, hc₁, ha⟩ := exists_eq_div_pow_aux t₁ a
  obtain ⟨n₂, d₂, hd₂, hs⟩ := exists_eq_div_pow_aux t₁ (s : blowupAlgebra S Q t₁.x)
  set n := n₁ + n₂
  set c := c₁ * t₁.x ^ n₂
  set d := d₂ * t₁.x ^ n₁
  have hc : c ∈ Q ^ n := by
    rw [pow_add]; exact Ideal.mul_mem_mul hc₁ (Ideal.pow_mem_pow t₁.x_mem _)
  have hd : d ∈ Q ^ n := by
    rw [pow_add, mul_comm (Q ^ n₁)]; exact Ideal.mul_mem_mul hd₂ (Ideal.pow_mem_pow t₁.x_mem _)
  have ha' : (a : FractionRing S) = algebraMap S _ c / algebraMap S _ t₁.x ^ n := by
    rw [ha, div_eq_div_iff (pow_ne_zero _ (hx0 t₁)) (pow_ne_zero _ (hx0 t₁))]
    simp only [c, n, map_mul, map_pow, pow_add]
    ring
  have hs' : ((s : blowupAlgebra S Q t₁.x) : FractionRing S) =
      algebraMap S _ d / algebraMap S _ t₁.x ^ n := by
    rw [hs, div_eq_div_iff (pow_ne_zero _ (hx0 t₁)) (pow_ne_zero _ (hx0 t₁))]
    simp only [d, n, map_mul, map_pow, pow_add]
    ring
  -- the element `s' = d/x₂ⁿ` of `S[x₂⁻¹Q]` is not in `M₂'`
  let a' : blowupAlgebra S Q t₂.x := ⟨_, div_pow_mem_aux t₂ hc⟩
  let s' : blowupAlgebra S Q t₂.x := ⟨_, div_pow_mem_aux t₂ hd⟩
  have hs'M : s' ∈ t₂.M'.primeCompl := by
    intro hmem
    have hnu : ¬ IsUnit (β₂ (algebraMap _ t₂.ring s')) := fun hunit =>
      (IsLocalization.AtPrime.isUnit_to_map_iff t₂.ring t₂.M' s').mp
        (h₂.isLocalHom.map_nonunit _ hunit) hmem
    apply hnu
    have e₁ := hβ t₁ β₁ h₁ n d s hs'
    have e₂ := hβ t₂ β₂ h₂ n d s' rfl
    have hunit₁ : IsUnit (β₁ (algebraMap _ t₁.ring (s : blowupAlgebra S Q t₁.x))) :=
      (IsLocalization.map_units t₁.ring s).map β₁
    have hX0 : T.toRing (φ t₁.x) ≠ 0 := fun h0 =>
      t₁.x_ne_zero (hinj (by rw [RingHom.comp_apply, h0, map_zero]))
    rw [← hu, mul_pow, ← mul_assoc, ← e₁] at e₂
    have e₃ : β₂ (algebraMap _ t₂.ring s') * ↑u ^ n =
        β₁ (algebraMap _ t₁.ring (s : blowupAlgebra S Q t₁.x)) := by
      apply mul_right_cancel₀ (pow_ne_zero n hX0)
      rw [mul_right_comm]
      exact e₂
    exact isUnit_of_mul_isUnit_left (e₃ ▸ hunit₁)
  refine ⟨IsLocalization.mk' t₂.ring a' ⟨s', hs'M⟩, ?_⟩
  -- both are `c/d`
  have hv := (IsLocalization.lift_mk'_spec (M := t₁.M'.primeCompl) (S := t₁.ring)
    (g := (blowupAlgebra S Q t₁.x).val.toRingHom) (hg := _) a
    (t₁.toFractionRing (IsLocalization.mk' t₁.ring a s)) s).mp rfl
  refine (IsLocalization.lift_mk'_spec (M := t₂.M'.primeCompl) (S := t₂.ring)
    (g := (blowupAlgebra S Q t₂.x).val.toRingHom) (hg := _) a' _ ⟨s', hs'M⟩).mpr ?_
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_val] at hv ⊢
  rw [ha', hs'] at hv
  show algebraMap S _ c / algebraMap S _ t₂.x ^ n =
    algebraMap S _ d / algebraMap S _ t₂.x ^ n * _
  rw [div_mul_eq_mul_div, div_left_inj' (pow_ne_zero _ (hx0 t₂))]
  rw [div_mul_eq_mul_div, div_left_inj' (pow_ne_zero _ (hx0 t₁))] at hv
  exact hv

/-- For a regular frame `(S; z)` of `R` and an ideal `P ⊇ (z)R`, `S/(P ∩ S) ≅ R/P`: the composite
`S → R → R/P` is surjective, `R/(z)R` being canonically isomorphic to `S`. -/
private theorem quotEquiv_of_idealZ_le_aux {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) {P : Ideal R} (hzP : F.idealZ ≤ P) :
    Nonempty (F.S ⧸ P.comap (algebraMap F.S R) ≃+* R ⧸ P) := by
  have hsurj : Function.Surjective ((Ideal.Quotient.mk P).comp (algebraMap F.S R)) := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨s, hs⟩ := F.quot_bijective.2 (Ideal.Quotient.mk _ r)
    refine ⟨s, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq]
    rw [RingHom.comp_apply, Ideal.Quotient.eq] at hs
    exact hzP hs
  have hker : RingHom.ker ((Ideal.Quotient.mk P).comp (algebraMap F.S R)) =
      P.comap (algebraMap F.S R) := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)⟩

/-- pp. 253–254: "Clearly, these conditions imply that `z_i = x(z_i/x) ∈ PR₁ ∩ R = P` for all
`i`, i.e., `P ⊇ (z₁, …, z_r)R`, and hence that `S/P ∩ S` is regular. Moreover, `S₁` is then the
unique monoidal transform of `S` with center `P ∩ S` which admits a canonical local homomorphism
`S₁ → R₁`."

(Formalization notes: the printed text reads "`PR₁ ∩ R₁ = P`"; the intersection is with `R`,
and the equality `PR₁ ∩ R = P` used in the sentence is recorded as the first conclusion.
"Unique monoidal transform" is uniqueness of `S₁` as a subring of the field of quotients of `S`
(`MonoidalTransform.subring`), a `MonoidalTransform` being the data `(x, M')` producing one; a
canonical local homomorphism `S₁' → R₁` is an `IsCanonicalLift` over `S → R`.) -/
@[blueprint "lem:III.8-frame-transform-unique"
  (statement := /-- Notation as in \cref{def:III.8-admits-frame-transform}, and let
    $(S_1;z_1/x,\dots,z_r/x)$ be a frame transform of $(S;z_1,\dots,z_r)$ in $R_1$. Then
    $z_i=x(z_i/x)\in PR_1\cap R=P$ for all $i$, i.e.\ $P\supseteq(z_1,\dots,z_r)R$, and hence
    $S/P\cap S$ is regular. Moreover, $S_1$ is then the unique monoidal transform of $S$ with
    center $P\cap S$ which admits a canonical local homomorphism $S_1\to R_1$.
    (pp.~253--254.) (Formalization note: the printed text reads ``$PR_1\cap R_1=P$''; the
    intersection is with $R$. Uniqueness of $S_1$ is uniqueness as a subring of the field of
    quotients of $S$.) -/)
  (proof := /-- The paper's only argument is the one contained in the statement (p.~253):
    ``Clearly, these conditions imply that $z_i=x(z_i/x)\in PR_1\cap R=P$ for all $i$, i.e.,
    $P\supseteq(z_1,\dots,z_r)R$, and hence that $S/P\cap S$ is regular''; the uniqueness of
    $S_1$ is asserted without further argument. [Editorial gloss, not in the paper: $S/P\cap S$
    is isomorphic to $R/P$ because $R/(z_1,\dots,z_r)R$ is canonically isomorphic to $S$ and
    $P\supseteq(z_1,\dots,z_r)R$.] -/)
  (latexEnv := "lemma")]
theorem idealZ_le_and_unique [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing]
    [IsRegularLocalRing T.ring] (FT : F.FrameTransform T) :
    (P.map T.toRing).comap T.toRing = P ∧ F.idealZ ≤ P ∧
      IsRegularLocalRing (F.S ⧸ P.comap (algebraMap F.S R)) ∧
      ∀ (TS' : MonoidalTransform F.S (P.comap (algebraMap F.S R))) (β' : TS'.ring →+* T.ring),
        IsCanonicalLift (algebraMap F.S R) TS' T β' → TS'.subring = FT.TS.subring := by
  -- `PR₁ ∩ R = P` (`P` prime with `R/P` regular)
  have hcomap : (P.map T.toRing).comap T.toRing = P := comap_map_toRing_eq_aux T
  -- "`z_i = x(z_i/x) ∈ PR₁ ∩ R = P` for all `i`, i.e., `P ⊇ (z₁, …, z_r)R`"
  have hzP : F.idealZ ≤ P := by
    rw [RegularFrame.idealZ, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    show F.z j ∈ P
    rw [← hcomap, Ideal.mem_comap, ← FT.mul_w j, ← FT.span_x]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨hcomap, hzP, ?_, ?_⟩
  · -- "and hence that `S/P ∩ S` is regular": `S/P ∩ S ≅ R/P`
    obtain ⟨e⟩ := quotEquiv_of_idealZ_le_aux F hzP
    exact IsRegularLocalRing.of_ringEquiv e.symm
  · -- "`S₁` is then the unique monoidal transform of `S` with center `P ∩ S` …": `S → R₁` is
    -- injective, since `S₁ → R₁/(z/x)R₁` is bijective
    intro TS' β' h'
    have hβ : Function.Injective FT.β := fun a b hab =>
      FT.quot_bijective.1 (by rw [RingHom.comp_apply, RingHom.comp_apply, hab])
    have hinj : Function.Injective (T.toRing.comp (algebraMap F.S R)) := by
      rw [← FT.canonical.comm]
      exact hβ.comp (toRing_injective_aux' FT.TS)
    exact le_antisymm
      (subring_le_of_isCanonicalLift_aux _ T hinj TS' FT.TS β' FT.β h' FT.canonical)
      (subring_le_of_isCanonicalLift_aux _ T hinj FT.TS TS' FT.β β' FT.canonical h')

end FrameTransform

/-- p. 254, "if" direction of the criterion for frame transforms (see `admitsFrameTransform_iff`):
if `x ∈ S` satisfies `PR₁ = (x)R₁` and `z_j = x w_j` with `w_j` non-units of `R₁`, then
`(S; z₁, …, z_r)` admits a frame transform in `R₁`.

Deviation from the paper (gap filled): the paper asserts the criterion ("We see that ...", p. 254)
without any argument.  Lean proves the "if" direction as follows; write `φ : S → R` for the
structure map, `ρ : R → R/(z)R ≅ S` for the retraction (`RegularFrame.retraction`), `X` for the
image of `T.x` in `R₁` and `x₁` for the image of `x`.
1. `z_j = x₁ w_j ∈ PR₁ ∩ R = P`, so `P ⊇ (z)R`, `P ∩ S` is prime and `S/P ∩ S ≅ R/P` is regular.
2. `T.x ∉ (z)R` (else `X ∈ x₁ M₁ R₁ = X M₁ R₁`), hence `ξ := ρ(T.x) ∈ P ∩ S` is non-zero and
   `φ(ξ) = X (1 - m)` with `m ∈ (w)R₁ ⊆ M₁`; thus `φ(ξ)` generates `PR₁` and the fractions
   `c/ξⁿ` (`c ∈ (P ∩ S)ⁿ`) map to `R₁`: the preimage `M'` of `M₁` in `S[ξ⁻¹(P ∩ S)]` defines the
   monoidal transform `S₁ = S[ξ⁻¹(P ∩ S)]_{M'}` of `S` with center `P ∩ S`, the canonical local
   homomorphism `β : S₁ → R₁`, and `S₁` is regular (`S/P ∩ S` is regular).
3. The ring homomorphism `ρ̃ : R₁ → Frac S`, `c/Xⁿ ↦ ρ(c)/ξⁿ` has kernel `(w)R₁`
   (`MonoidalTransform.exists_ringHom_fractionRing_ker_eq`; this uses
   `(z)R ∩ Pⁿ = (z)Pⁿ⁻¹`, `exists_eq_sum_mul_of_mem_span_of_mem_pow`) and `ρ̃ ∘ β` is the inclusion
   of `S₁` in `Frac S`; the same formula shows `R₁ = β(S₁) + (w)R₁`.  Hence `S₁ → R₁/(w)R₁` is
   bijective.
4. For every set `I` of indices the ideal `(w_i)_{i ∈ I}` of `R₁` is prime (kernel of the analogous
   map to `Frac (R/(z_i)_{i ∈ I})`) and `w_k ∉ (w_i)_{i ∈ I}` for `k ∉ I`; by induction on `I`,
   `dim R₁/(w) + r ≤ dim R₁`.  As `R₁/(w)R₁ ≅ S₁` is regular, `(w)` extends to a regular system of
   parameters of `R₁`.
The hypothesis "`x ∈ P ∩ S`" of the criterion is redundant (it follows from `PR₁ = (x)R₁` and
`PR₁ ∩ R = P`) and is not used. -/
theorem nonempty_frameTransform_of_exists_denominator [P.IsPrime] [IsRegularLocalRing (R ⧸ P)]
    (T : MonoidalTransform R P) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring] (x : F.S)
    (hx : P.map T.toRing = Ideal.span {T.toRing (algebraMap F.S R x)})
    (w : Fin F.r → T.ring)
    (hw : ∀ j, T.toRing (algebraMap F.S R x) * w j = T.toRing (F.z j))
    (hwu : ∀ j, ¬ IsUnit (w j)) : Nonempty (F.FrameTransform T) := by
  classical
  set φ := algebraMap F.S R with hφ
  set x₁ := T.toRing (φ x) with hx₁
  have hX0 : T.xR ≠ 0 := fun h => T.x_ne_zero (T.toRing_injective (h.trans (map_zero _).symm))
  obtain ⟨u, hu⟩ : ∃ u : T.ring ˣ, T.xR * u = x₁ :=
    Ideal.span_singleton_eq_span_singleton.mp (T.span_xR_eq_map.trans hx)
  have hwM : ∀ j, w j ∈ maximalIdeal T.ring := fun j => (IsLocalRing.mem_maximalIdeal _).mpr (hwu j)
  -- `(z) ⊆ P`
  have hcomap := FrameTransform.comap_map_toRing_eq_aux T
  have hzP : ∀ j, F.z j ∈ P := by
    intro j
    rw [← hcomap, Ideal.mem_comap, ← hw j, hx]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hidealZ : F.idealZ ≤ P := Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hzP j)
  -- `T.x ∉ (z)`
  have hxZ : T.x ∉ F.idealZ := by
    intro h
    change T.x ∈ Ideal.span (Set.range F.z) at h
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h
    have h1 : T.xR = T.xR * ((u : T.ring) * ∑ i, T.toRing (c i) * w i) := by
      calc T.xR = T.toRing (∑ i, c i * F.z i) := by rw [hc]; rfl
        _ = ∑ i, T.toRing (c i) * (x₁ * w i) := by simp only [map_sum, map_mul, hw]
        _ = _ := by
          rw [← hu, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
    have h2 : (1 : T.ring) = (u : T.ring) * ∑ i, T.toRing (c i) * w i :=
      mul_left_cancel₀ hX0 (by rw [mul_one]; exact h1)
    have : (1 : T.ring) ∈ maximalIdeal T.ring := by
      rw [h2]
      exact Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hwM i))
    exact (IsLocalRing.maximalIdeal.isMaximal T.ring).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  -- `ξ = ρ(T.x)`
  set Q := P.comap φ with hQ
  set ξ := F.retraction T.x with hξ
  have hξ0 : ξ ≠ 0 := fun h => hxZ ((F.retraction_eq_zero_iff _).mp h)
  have hξQ : ξ ∈ Q := F.retraction_mem_comap hidealZ T.x_mem
  obtain ⟨m, hm𝔴, hξm⟩ : ∃ m ∈ Ideal.span (Set.range w), T.toRing (φ ξ) = T.xR * (1 - m) := by
    have h := F.sub_algebraMap_retraction_mem T.x
    change T.x - φ ξ ∈ Ideal.span (Set.range F.z) at h
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h
    refine ⟨(u : T.ring) * ∑ i, T.toRing (c i) * w i, ?_, ?_⟩
    · exact Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun i _ =>
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
    · have h2 := congrArg T.toRing hc
      simp only [map_sum, map_mul, map_sub, ← hw] at h2
      rw [← hu] at h2
      have h3 : T.toRing (φ ξ) = T.xR - ∑ i, T.toRing (c i) * (T.xR * ↑u * w i) := by
        rw [h2]
        show T.toRing (φ ξ) = T.toRing T.x - (T.toRing T.x - T.toRing (φ ξ))
        ring
      rw [h3, mul_sub, mul_one, Finset.mul_sum, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  have hm𝔴M : m ∈ maximalIdeal T.ring :=
    (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hwM j) : Ideal.span (Set.range w) ≤ _) hm𝔴
  have hunit : IsUnit (1 - m) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits m hm𝔴M
  have hφ₁ξ0 : T.toRing (φ ξ) ≠ 0 := by
    rw [hξm]; exact mul_ne_zero hX0 hunit.ne_zero
  -- the lift `γ : S[ξ⁻¹Q] → R₁`
  have hP : ∀ q ∈ Q, ∃ y : T.ring, (T.toRing.comp φ) ξ * y = (T.toRing.comp φ) q := by
    intro q hq
    have h1 : T.toRing (φ q) ∈ Ideal.span {T.xR} := by
      rw [T.span_xR_eq_map]; exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mp hq)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp h1
    obtain ⟨v, hv⟩ := hunit
    refine ⟨e * ↑v⁻¹, ?_⟩
    simp only [RingHom.comp_apply]
    rw [hξm, ← hv]
    calc T.xR * ↑v * (e * ↑v⁻¹) = T.xR * e * (↑v * ↑v⁻¹) := by ring
      _ = T.xR * e := by rw [Units.mul_inv, mul_one]
      _ = e * T.xR := mul_comm _ _
      _ = _ := he
  obtain ⟨γ₀, hγ₀1, hγ₀2⟩ := blowupAlgebra.exists_ringHom_of_map_mem (P := Q) hξQ hξ0
    (T.toRing.comp φ) hφ₁ξ0 hP
  -- the monoidal transform `S₁`
  have hM'le : (maximalIdeal F.S).map (algebraMap F.S (blowupAlgebra F.S Q ξ)) ≤
      Ideal.comap γ₀ (maximalIdeal T.ring) := by
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, Ideal.mem_comap, hγ₀1, RingHom.comp_apply]
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      ((IsLocalRing.mem_maximalIdeal s).mp hs)
        (isUnit_of_map_unit φ s (isUnit_of_map_unit T.toRing _ hu))
  obtain ⟨TS, γ, hTSx, hγ1, hγ2, hTSM⟩ :
      ∃ (TS : MonoidalTransform F.S Q) (γ : blowupAlgebra F.S Q TS.x →+* T.ring),
        TS.x = ξ ∧ (∀ s : F.S, γ (algebraMap F.S _ s) = T.toRing (φ s)) ∧
        (∀ (n : ℕ) (c : F.S) (b : blowupAlgebra F.S Q TS.x),
          (b : FractionRing F.S) = algebraMap F.S (FractionRing F.S) c /
            algebraMap F.S (FractionRing F.S) TS.x ^ n →
          T.toRing (φ TS.x) ^ n * γ b = T.toRing (φ c)) ∧
        TS.M' = Ideal.comap γ (maximalIdeal T.ring) :=
    ⟨⟨ξ, hξQ, hξ0, Ideal.comap γ₀ (maximalIdeal T.ring), inferInstance, hM'le⟩, γ₀, rfl,
      hγ₀1, hγ₀2, rfl⟩
  -- the canonical local homomorphism `β : S₁ → R₁`
  have hmem : ∀ a : blowupAlgebra F.S Q TS.x, a ∈ TS.M' ↔ γ a ∈ maximalIdeal T.ring := fun a => by
    rw [hTSM, Ideal.mem_comap]
  have hβunit : ∀ y : TS.M'.primeCompl, IsUnit (γ (y : blowupAlgebra F.S Q TS.x)) := by
    intro y
    have hy : (y : blowupAlgebra F.S Q TS.x) ∉ TS.M' := y.2
    exact IsLocalRing.notMem_maximalIdeal.mp (fun h => hy ((hmem _).mpr h))
  set β : TS.ring →+* T.ring :=
    IsLocalization.lift (M := TS.M'.primeCompl) (S := TS.ring) hβunit with hβdef
  have hβγ : ∀ b : blowupAlgebra F.S Q TS.x, β (algebraMap _ TS.ring b) = γ b :=
    fun b => IsLocalization.lift_eq hβunit b
  have hcan : IsCanonicalLift φ TS T β := by
    refine ⟨⟨fun a ha => ?_⟩, ?_⟩
    · obtain ⟨⟨b, s⟩, hmk⟩ := IsLocalization.mk'_surjective TS.M'.primeCompl a
      have hmk' : IsLocalization.mk' TS.ring b s = a := hmk
      have h1 : β a * γ (s : blowupAlgebra F.S Q TS.x) = γ b := by
        rw [← hβγ, ← hβγ, ← map_mul, ← hmk', IsLocalization.mk'_spec]
      have h2 : IsUnit (γ b) := h1 ▸ ha.mul (hβunit s)
      have hb : b ∈ TS.M'.primeCompl := fun hbM =>
        (IsLocalRing.notMem_maximalIdeal.mpr h2) ((hmem b).mp hbM)
      rw [← hmk']
      exact (IsLocalization.AtPrime.isUnit_mk'_iff TS.ring TS.M' b s).mpr hb
    · ext s
      simp only [RingHom.comp_apply]
      have : TS.toRing s = algebraMap _ TS.ring (algebraMap F.S (blowupAlgebra F.S Q TS.x) s) := rfl
      rw [this, hβγ, hγ1]
  -- `S₁` is regular
  have hQprime : Q.IsPrime := inferInstanceAs (Ideal.comap φ P).IsPrime
  have hQ0 : Q ≠ ⊥ := fun h => hξ0 (by simpa [h] using hξQ)
  have hSQ : IsRegularLocalRing (F.S ⧸ Q) := by
    obtain ⟨e⟩ := FrameTransform.quotEquiv_of_idealZ_le_aux F hidealZ
    exact IsRegularLocalRing.of_ringEquiv e.symm
  have hreg : IsRegularLocalRing TS.ring :=
    (MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map TS hQprime hQ0 hSQ).1
  -- the retraction `ρ : R₁ → Frac S`
  obtain ⟨ρ, hρ1, hρker⟩ := MonoidalTransform.exists_ringHom_fractionRing_ker_eq (P := P)
    inferInstance F.z_injective F.extends_rsop hzP T hx hw hwM F.retraction Finset.univ
    (fun c => (F.retraction_eq_zero_iff c).trans (by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; rfl)) hξ0
  have hρker' : RingHom.ker ρ = Ideal.span (Set.range w) := by
    rw [hρker]; congr 1; simp
  have hrtφ : ∀ s : F.S, F.retraction (φ s) = s := F.retraction_algebraMap
  have hργ : ∀ e : blowupAlgebra F.S Q TS.x,
      ρ (γ e) = ((e : blowupAlgebra F.S Q TS.x) : FractionRing F.S) := by
    intro e
    obtain ⟨n, c, hc, he⟩ := blowupAlgebra.exists_eq_div_pow TS.x_mem TS.x_ne_zero e
    have h2 := congrArg ρ (hγ2 n c e he)
    simp only [map_mul, map_pow, hρ1, hrtφ] at h2
    have hx0 : algebraMap F.S (FractionRing F.S) TS.x ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective F.S (FractionRing F.S))).mpr TS.x_ne_zero
    rw [he, eq_div_iff (pow_ne_zero _ hx0), mul_comm]
    exact h2
  -- approximation: every element of `R[x⁻¹P]` is, modulo `(w)`, the image of an element of `S₁`
  have happrox : ∀ b : blowupAlgebra R P T.x, ∃ e : blowupAlgebra F.S Q TS.x,
      algebraMap _ T.ring b - γ e ∈ Ideal.span (Set.range w) := by
    intro b
    obtain ⟨n, c, hc, hb⟩ := blowupAlgebra.exists_eq_div_pow T.x_mem T.x_ne_zero b
    have hrtc : F.retraction c ∈ Q ^ n := by
      have h1 : F.retraction c ∈ (P ^ n).map F.retraction := Ideal.mem_map_of_mem _ hc
      rw [Ideal.map_pow] at h1
      refine Ideal.pow_right_mono ?_ n h1
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      exact F.retraction_mem_comap hidealZ hp
    refine ⟨⟨_, blowupAlgebra.div_pow_mem (P := Q) (x := TS.x) (n := n) hrtc⟩, ?_⟩
    rw [← hρker', RingHom.mem_ker, map_sub, hργ]
    have h1 := congrArg ρ (MonoidalTransform.algebraMap_mul_xR_pow_eq T n c b hb)
    simp only [map_mul, map_pow, hρ1] at h1
    have hx0 : algebraMap F.S (FractionRing F.S) TS.x ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective F.S (FractionRing F.S))).mpr TS.x_ne_zero
    have h2 : ρ (algebraMap _ T.ring b) * algebraMap F.S (FractionRing F.S) TS.x ^ n =
        algebraMap F.S (FractionRing F.S) (F.retraction c) := by
      have hT : T.xR = T.toRing T.x := rfl
      rw [hT, hρ1] at h1
      rw [hTSx]
      exact h1
    have h3 : ρ (algebraMap _ T.ring b) = algebraMap F.S (FractionRing F.S) (F.retraction c) /
        algebraMap F.S (FractionRing F.S) TS.x ^ n := by
      rw [eq_div_iff (pow_ne_zero _ hx0)]; exact h2
    rw [h3]
    exact sub_self _
  -- `S₁ → R₁/(w)R₁` is bijective
  set 𝔴 := Ideal.span (Set.range w) with h𝔴
  have h𝔴M : 𝔴 ≤ maximalIdeal T.ring :=
    Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hwM j)
  have hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔴).comp β) := by
    intro t'
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective t'
    obtain ⟨⟨a, s⟩, hmk⟩ := IsLocalization.mk'_surjective T.M'.primeCompl v
    have hmk' : IsLocalization.mk' T.ring a s = v := hmk
    obtain ⟨ea, hea⟩ := happrox a
    obtain ⟨es, hes⟩ := happrox (s : blowupAlgebra R P T.x)
    have hys : IsUnit (algebraMap _ T.ring (s : blowupAlgebra R P T.x)) :=
      IsLocalization.map_units T.ring s
    have hes' : es ∈ TS.M'.primeCompl := by
      intro hesM
      have h1 : γ es ∈ maximalIdeal T.ring := (hmem es).mp hesM
      have h2 : algebraMap _ T.ring (s : blowupAlgebra R P T.x) ∈ maximalIdeal T.ring := by
        have := add_mem (h𝔴M hes) h1
        simpa using this
      exact IsLocalRing.notMem_maximalIdeal.mpr hys h2
    refine ⟨IsLocalization.mk' TS.ring ea ⟨es, hes'⟩, ?_⟩
    simp only [RingHom.comp_apply]
    set σ : TS.ring := IsLocalization.mk' TS.ring ea ⟨es, hes'⟩ with hσ
    have h1 : β σ * γ es = γ ea := by
      rw [← hβγ, ← hβγ, ← map_mul, hσ, IsLocalization.mk'_spec]
    have h2 : v * algebraMap _ T.ring (s : blowupAlgebra R P T.x) = algebraMap _ T.ring a := by
      rw [← hmk']; exact IsLocalization.mk'_spec T.ring a s
    rw [Ideal.Quotient.eq]
    obtain ⟨t, ht⟩ := hys
    have h3 : (β σ - v) * algebraMap _ T.ring (s : blowupAlgebra R P T.x) ∈ 𝔴 := by
      have : (β σ - v) * algebraMap _ T.ring (s : blowupAlgebra R P T.x) =
          β σ * (algebraMap _ T.ring (s : blowupAlgebra R P T.x) - γ es) -
            (algebraMap _ T.ring a - γ ea) := by
        rw [← h2, ← h1]; ring
      rw [this]
      exact sub_mem (Ideal.mul_mem_left _ _ hes) hea
    have h4 : β σ - v = ((β σ - v) * algebraMap _ T.ring (s : blowupAlgebra R P T.x)) *
        (↑t⁻¹ : T.ring) := by
      rw [← ht, mul_assoc, Units.mul_inv, mul_one]
    rw [h4]
    exact Ideal.mul_mem_right _ _ h3
  have hinj : Function.Injective ((Ideal.Quotient.mk 𝔴).comp β) := by
    rw [injective_iff_map_eq_zero]
    intro σ hσ
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hσ
    obtain ⟨⟨e, s'⟩, hmk⟩ := IsLocalization.mk'_surjective TS.M'.primeCompl σ
    have hmk' : IsLocalization.mk' TS.ring e s' = σ := hmk
    have h1 : β σ * γ (s' : blowupAlgebra F.S Q TS.x) = γ e := by
      rw [← hβγ, ← hβγ, ← map_mul, ← hmk', IsLocalization.mk'_spec]
    have hker : β σ ∈ RingHom.ker ρ := by rw [hρker']; exact hσ
    have h2 : ρ (γ e) = 0 := by
      rw [← h1, map_mul, RingHom.mem_ker.mp hker, zero_mul]
    rw [hργ] at h2
    have h3 : e = 0 := Subtype.ext h2
    rw [← hmk', h3, IsLocalization.mk'_zero]
  have hbij : Function.Bijective ((Ideal.Quotient.mk 𝔴).comp β) := ⟨hinj, hsurj⟩
  -- `(w_i)_{i ∈ I}` is prime and `w_k ∉ (w_i)_{i ∈ I}` for `k ∉ I`
  have hwI : ∀ I : Finset (Fin F.r), (Ideal.span (w '' (I : Set (Fin F.r)))).IsPrime ∧
      ∀ k, k ∉ I → w k ∉ Ideal.span (w '' (I : Set (Fin F.r))) := by
    intro I
    have hKext : ExtendsToRSOP R (I.image F.z) :=
      ExtendsToRSOP.mono F.extends_rsop (Finset.image_subset_image (Finset.subset_univ _))
    have hKprime : (Ideal.span ((I.image F.z : Finset R) : Set R)).IsPrime := hKext.isPrime_span
    have : IsDomain (R ⧸ Ideal.span ((I.image F.z : Finset R) : Set R)) :=
      (Ideal.Quotient.isDomain_iff_prime _).mpr hKprime
    have hKZ : Ideal.span ((I.image F.z : Finset R) : Set R) ≤ F.idealZ :=
      Ideal.span_le.mpr fun y hy => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
        exact Ideal.subset_span ⟨i, rfl⟩
    obtain ⟨ρI, hρI1, hρIker⟩ := MonoidalTransform.exists_ringHom_fractionRing_ker_eq (P := P)
      inferInstance F.z_injective F.extends_rsop hzP T hx hw hwM
      (Ideal.Quotient.mk (Ideal.span ((I.image F.z : Finset R) : Set R))) I
      (fun c => Ideal.Quotient.eq_zero_iff_mem)
      (fun h => hxZ (hKZ (Ideal.Quotient.eq_zero_iff_mem.mp h)))
    refine ⟨hρIker ▸ RingHom.ker_isPrime ρI, fun k hk hmem' => ?_⟩
    have h1 : ρI (w k) = 0 := by rw [← RingHom.mem_ker, hρIker]; exact hmem'
    have h2 : ρI (T.toRing (F.z k)) = 0 := by rw [← hw k, map_mul, h1, mul_zero]
    rw [hρI1] at h2
    have h3 : (Ideal.Quotient.mk (Ideal.span ((I.image F.z : Finset R) : Set R))) (F.z k) = 0 :=
      (map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h2
    obtain ⟨Z, hsub, hZ⟩ := F.extends_rsop
    exact rsop_notMem_span hZ (fun y hy => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
        exact hsub (Finset.mem_image_of_mem F.z (Finset.mem_univ i)))
      (hsub (Finset.mem_image_of_mem F.z (Finset.mem_univ k)))
      (fun hkI => by
        obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hkI
        exact hk (F.z_injective hik ▸ hi))
      (Ideal.Quotient.eq_zero_iff_mem.mp h3)
  -- the dimension count
  have hchain : ∀ I : Finset (Fin F.r),
      ringKrullDim (T.ring ⧸ Ideal.span (w '' (I : Set (Fin F.r)))) + (I.card : WithBot ℕ∞) ≤
        ringKrullDim T.ring := by
    intro I
    induction I using Finset.induction_on with
    | empty =>
      simp only [Finset.card_empty, Nat.cast_zero, add_zero]
      exact ringKrullDim_le_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    | insert k I' hk ih =>
      obtain ⟨hprime, hnot⟩ := hwI I'
      have : IsDomain (T.ring ⧸ Ideal.span (w '' (I' : Set (Fin F.r)))) :=
        (Ideal.Quotient.isDomain_iff_prime _).mpr hprime
      have hr' : Ideal.Quotient.mk (Ideal.span (w '' (I' : Set (Fin F.r)))) (w k) ∈
          nonZeroDivisors (T.ring ⧸ Ideal.span (w '' (I' : Set (Fin F.r)))) :=
        mem_nonZeroDivisors_of_ne_zero fun h => hnot k hk (Ideal.Quotient.eq_zero_iff_mem.mp h)
      have hle : Ideal.span (w '' (I' : Set (Fin F.r))) ≤
          Ideal.span (w '' ((insert k I' : Finset (Fin F.r)) : Set (Fin F.r))) :=
        Ideal.span_mono (Set.image_mono (by simp))
      have hwk : w k ∈ Ideal.span (w '' ((insert k I' : Finset (Fin F.r)) : Set (Fin F.r))) :=
        Ideal.subset_span ⟨k, by simp, rfl⟩
      let f' : (T.ring ⧸ Ideal.span (w '' (I' : Set (Fin F.r)))) →+*
          (T.ring ⧸ Ideal.span (w '' ((insert k I' : Finset (Fin F.r)) : Set (Fin F.r)))) :=
        Ideal.Quotient.lift _ (Ideal.Quotient.mk _) fun a ha =>
          Ideal.Quotient.eq_zero_iff_mem.mpr (hle ha)
      have hf' : Function.Surjective f' :=
        Ideal.Quotient.lift_surjective_of_surjective _ _ Ideal.Quotient.mk_surjective
      have h1 := ringKrullDim_succ_le_of_surjective f' hf' hr'
        (Ideal.Quotient.eq_zero_iff_mem.mpr hwk)
      calc ringKrullDim (T.ring ⧸ Ideal.span (w '' ((insert k I' : Finset (Fin F.r)) :
              Set (Fin F.r)))) + ((insert k I').card : WithBot ℕ∞)
          = (ringKrullDim (T.ring ⧸ Ideal.span (w '' ((insert k I' : Finset (Fin F.r)) :
              Set (Fin F.r)))) + 1) + (I'.card : WithBot ℕ∞) := by
            rw [Finset.card_insert_of_notMem hk, Nat.cast_add, Nat.cast_one]
            abel
        _ ≤ ringKrullDim (T.ring ⧸ Ideal.span (w '' (I' : Set (Fin F.r)))) +
              (I'.card : WithBot ℕ∞) := add_le_add_left h1 _
        _ ≤ ringKrullDim T.ring := ih
  -- `(w)` extends to a regular system of parameters of `R₁`
  have hwinj : Function.Injective w := fun j j' h => by
    apply F.z_injective
    apply T.toRing_injective
    rw [← hw j, ← hw j', h]
  have hKcard : ((Finset.univ : Finset (Fin F.r)).image w).card =
      (Finset.univ : Finset (Fin F.r)).card := by
    rw [Finset.card_image_of_injective _ hwinj]
  have hspanK : Ideal.span (((Finset.univ : Finset (Fin F.r)).image w : Finset T.ring) :
      Set T.ring) = 𝔴 := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have : IsRegularLocalRing TS.ring := hreg
  have hregK : IsRegularLocalRing
      (T.ring ⧸ Ideal.span (((Finset.univ : Finset (Fin F.r)).image w : Finset T.ring) :
        Set T.ring)) := by
    rw [hspanK]
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.ofBijective _ hbij)
  have hext1 : ExtendsToRSOP T.ring (Finset.image w Finset.univ) := by
    refine rsop_extends_of_quotient_regular (fun k hk => ?_) ?_
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hk
      exact hwM j
    · have := hchain Finset.univ
      rw [hKcard]
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      rw [Finset.coe_univ, Set.image_univ] at this
      exact this
  exact ⟨{ x := x₁
           span_x := hx.symm
           TS := TS
           β := β
           canonical := hcan
           isRegular := hreg
           w := w
           mul_w := hw
           extends_rsop := hext1
           quot_bijective := hbij }⟩

/-- p. 254: "We see that `(S; z₁, …, z_r)` admits a frame transform in `R₁` if and only if there
exist `x ∈ P ∩ S` such that `PR₁ = (x)R₁` and `(z₁/x, …, z_r/x)` are all non-units of `R₁`."

(Formalization notes: `x ∈ P ∩ S` is an element `x` of `S` whose image in `R` lies in `P`;
"`z_j/x` is a non-unit of `R₁`" is: there is `w_j ∈ R₁` with `x · w_j = z_j` in `R₁`, and `w_j`
is not a unit.) -/
@[blueprint "lem:III.8-frame-transform-criterion"
  (statement := /-- Notation as in \cref{def:III.8-admits-frame-transform}. Then
    $(S;z_1,\dots,z_r)$ admits a frame transform in $R_1$ if and only if there exist
    $x\in P\cap S$ such that $PR_1=(x)R_1$ and $(z_1/x,\dots,z_r/x)$ are all non-units of
    $R_1$. (p.~254.) (Formalization note: ``$z_j/x$ is a non-unit of $R_1$'' is recorded as the
    existence of $w_j\in R_1$ with $xw_j=z_j$ in $R_1$ which is not a unit.) -/)
  (proof := /-- ``We see that'' (p.~254); no proof is given in the paper.

    \textbf{Deviation from the paper (gap filled).} The ``only if'' direction: the denominator
    $x$ of $S_1$ works, since $P=(z)R+(P\cap S)R$ (as $R/(z)R\cong S$ canonically and
    $P\supseteq(z)R$), whence $PR_1\subseteq(x)R_1+(x_{R_1})M_1$ and Nakayama gives
    $PR_1=(x)R_1$. The ``if'' direction (not argued in the paper): put $\xi=\rho(x_{R_1})$, where
    $\rho\colon R\to R/(z)R\cong S$ is the retraction; then $\xi\in P\cap S$ and the image of
    $\xi$ in $R_1$ is an associate of $x_{R_1}$. The fractions $c/\xi^n$ ($c\in(P\cap S)^n$) map
    into $R_1$; the preimage of $M_1$ defines a monoidal transform $S_1$ of $S$ with center
    $P\cap S$ and a canonical local homomorphism $S_1\to R_1$. The map $c/x^n\mapsto
    \rho(c)/\xi^n$ from $R_1$ to the field of fractions of $S$ has kernel $(z_1/x,\dots,z_r/x)R_1$,
    because $(z)\cap P^n=(z)P^{n-1}$ (the $z_j$ being part of a regular system of parameters);
    hence $S_1\to R_1/(z/x)R_1$ is bijective. Finally $(z_i/x)_{i\in I}R_1$ is prime for every set
    $I$ of indices and $z_k/x\notin(z_i/x)_{i\in I}R_1$ for $k\notin I$, so
    $\dim R_1/(z/x)R_1+r\le\dim R_1$ and $(z_1/x,\dots,z_r/x)$ extends to a regular system of
    parameters of the regular local ring $R_1$. -/)
  (latexEnv := "lemma")]
theorem admitsFrameTransform_iff [P.IsPrime] [IsRegularLocalRing (R ⧸ P)]
    (T : MonoidalTransform R P) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring] :
    F.AdmitsFrameTransform T ↔
      ∃ x : F.S, algebraMap F.S R x ∈ P ∧
        P.map T.toRing = Ideal.span {T.toRing (algebraMap F.S R x)} ∧
        ∃ w : Fin F.r → T.ring,
          (∀ j, T.toRing (algebraMap F.S R x) * w j = T.toRing (F.z j)) ∧
            ∀ j, ¬ IsUnit (w j) := by
  constructor
  · -- "only if": the denominator `x` of `S₁` works.  `P = (z)R + (P ∩ S)R` (`R/(z)R ≅ S`
    -- canonically, `P ⊇ (z)R`), so `PR₁ ⊆ (x)R₁ + (x_{R₁}) M₁` and Nakayama gives `PR₁ = (x)R₁`.
    rintro ⟨FT⟩
    classical
    obtain ⟨-, hzP, -, -⟩ := FrameTransform.idealZ_le_and_unique FT
    have hxS : algebraMap F.S R FT.TS.x ∈ P := FT.TS.x_mem
    have hwM : ∀ j, FT.w j ∈ maximalIdeal T.ring := by
      obtain ⟨s, hsub, hs⟩ := FT.extends_rsop
      intro j
      rw [← hs.1]
      exact Ideal.subset_span (hsub (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    set a₀ := T.toRing (algebraMap F.S R FT.TS.x) with ha₀
    have key : P.map T.toRing ≤
        Ideal.span {a₀} ⊔ Ideal.span {FT.x} * maximalIdeal T.ring := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      obtain ⟨s, hs⟩ := F.quot_bijective.2 (Ideal.Quotient.mk _ p)
      rw [RingHom.comp_apply, Ideal.Quotient.eq] at hs
      have hsP : algebraMap F.S R s ∈ P := by
        have h := add_mem (hzP hs) hp
        rwa [sub_add_cancel] at h
      -- `T.toRing (φ s) ∈ (a₀)`, through `S₁`
      have h1 : T.toRing (algebraMap F.S R s) ∈ Ideal.span {a₀} := by
        have hmem : FT.TS.toRing s ∈ (P.comap (algebraMap F.S R)).map FT.TS.toRing :=
          Ideal.mem_map_of_mem _ hsP
        rw [← FT.TS.span_xR_eq_map, Ideal.mem_span_singleton'] at hmem
        obtain ⟨c, hc⟩ := hmem
        have hβ : ∀ y : F.S, FT.β (FT.TS.toRing y) = T.toRing (algebraMap F.S R y) := fun y =>
          RingHom.congr_fun FT.canonical.comm y
        refine Ideal.mem_span_singleton'.mpr ⟨FT.β c, ?_⟩
        rw [ha₀, ← hβ, ← hβ, ← map_mul, ← hc]
        rfl
      -- `T.toRing (φ s - p) ∈ (x_{R₁}) M₁`
      have h2 : T.toRing (algebraMap F.S R s - p) ∈ Ideal.span {FT.x} * maximalIdeal T.ring := by
        have hle : (Ideal.span (Set.range F.z)).map T.toRing ≤
            Ideal.span {FT.x} * maximalIdeal T.ring := by
          rw [Ideal.map_span, Ideal.span_le]
          rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
          rw [← FT.mul_w j]
          exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (hwM j)
        exact hle (Ideal.mem_map_of_mem _ hs)
      rw [Ideal.mem_comap]
      have hp' : T.toRing p = T.toRing (algebraMap F.S R s) -
          T.toRing (algebraMap F.S R s - p) := by
        rw [map_sub]
        ring
      rw [hp']
      exact sub_mem (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
    have hx : FT.x ∈ P.map T.toRing := FT.span_x ▸ Ideal.mem_span_singleton_self _
    obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.mp (key hx)
    obtain ⟨m, hm, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
    obtain ⟨v, hv⟩ := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits m hm
    have hxI : FT.x ∈ Ideal.span {a₀} := by
      have h1m : FT.x * (1 - m) = i := by
        linear_combination (-1 : T.ring) * hiy
      have h' : FT.x = i * ↑v⁻¹ := by
        rw [← h1m, ← hv, mul_assoc, Units.mul_inv, mul_one]
      rw [h']
      exact Ideal.mul_mem_right _ _ hi
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hxI
    refine ⟨FT.TS.x, hxS, ?_, fun j => c * FT.w j, fun j => ?_, fun j hu => ?_⟩
    · apply le_antisymm
      · rw [← FT.span_x, Ideal.span_le, Set.singleton_subset_iff]
        exact hxI
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        exact Ideal.mem_map_of_mem _ hxS
    · rw [← FT.mul_w j, ← hc]
      ring
    · exact (IsLocalRing.mem_maximalIdeal _).mp (hwM j) (isUnit_of_mul_isUnit_right hu)
  · rintro ⟨x, -, hx, w, hw, hwu⟩
    exact F.nonempty_frameTransform_of_exists_denominator T x hx w hw hwu

end RegularFrame

end FrameTransform

/-! ### Lemma 20 (pp. 254–256) -/

/-! #### Auxiliary results for Lemma 20

Lemma 20 is proved here directly for the given `R`, `S` and `R₁`, without the reduction to complete
`S`, `R` and a residually rational `R₁` of p. 254 (see the deviation notes of Lemma 20).  The
auxiliary results are of two kinds: general statements about coefficient fields and standard bases,
and the comparison of the power series expansions with respect to `(S; z)` and its frame
transform `(S₁; w)`.  They are stated in the form needed again for Lemma 21. -/

section Lemma20Generic

/-- **Descent of ideal membership along an extension of the coefficient field**: if `κ : K → K₁` is
an injective homomorphism of a field `K` into a ring `K₁`, `p` and the `q_j` are polynomials over
`K` and `κ p` lies in the ideal of `K₁[Z]` generated by the `κ q_j`, then `p` lies in the ideal of
`K[Z]` generated by the `q_j` (a `K`-linear left inverse of `κ`, applied to the coefficients).
Used for the extension `k = R/M → k₁ = R₁/M₁` of residue fields in Lemma 20 (p. 255, where the
paper compares `k[Z]` with `k[W] ⊆ gr_{M₁}(R₁)`; residual rationality is not needed). -/
theorem mem_span_range_of_map_mem_span_range {K K₁ : Type*} [Field K] [CommRing K₁]
    (κ : K →+* K₁) (hκ : Function.Injective κ) {σ ι : Type*} [Fintype ι]
    (q : ι → MvPolynomial σ K) {p : MvPolynomial σ K}
    (h : MvPolynomial.map κ p ∈ Ideal.span (Set.range fun j => MvPolynomial.map κ (q j))) :
    p ∈ Ideal.span (Set.range q) := by
  classical
  let _ : Algebra K K₁ := κ.toAlgebra
  have hinj : Function.Injective (Algebra.linearMap K K₁) := hκ
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K K₁)
    (LinearMap.ker_eq_bot.mpr hinj)
  -- `Λ` applies `lam` to the coefficients
  let Λf : MvPolynomial σ K₁ → MvPolynomial σ K :=
    fun p => ∑ m ∈ p.support, MvPolynomial.monomial m (lam (p.coeff m))
  have hΛc : ∀ (c : MvPolynomial σ K₁) m, (Λf c).coeff m = lam (c.coeff m) := by
    intro c m
    simp only [Λf, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    by_cases hm : m ∈ c.support
    · rw [Finset.sum_eq_single_of_mem m hm (fun m' _ hm' => by simp [hm'])]
      simp
    · have : c.coeff m = 0 := MvPolynomial.notMem_support_iff.mp hm
      rw [this, map_zero]
      exact Finset.sum_eq_zero fun m' hm' => by
        have : m' ≠ m := fun e => hm (e ▸ hm')
        simp [this]
  let Λ : MvPolynomial σ K₁ →+ MvPolynomial σ K :=
    AddMonoidHom.mk' Λf fun c d => by
      ext m
      have haddK : ∀ u v : MvPolynomial σ K, (u + v).coeff m = u.coeff m + v.coeff m :=
        fun u v => by simp
      have haddK₁ : ∀ u v : MvPolynomial σ K₁, (u + v).coeff m = u.coeff m + v.coeff m :=
        fun u v => by simp
      rw [hΛc, haddK, hΛc, hΛc, haddK₁, map_add]
  have hΛ : ∀ c, Λ c = Λf c := fun _ => rfl
  have h1 : ∀ p, Λ (MvPolynomial.map κ p) = p := by
    intro p
    ext m
    rw [hΛ, hΛc, MvPolynomial.coeff_map]
    exact LinearMap.congr_fun hlam (p.coeff m)
  have h2 : ∀ (c : MvPolynomial σ K₁) (q : MvPolynomial σ K),
      Λ (c * MvPolynomial.map κ q) = Λ c * q := by
    intro c q
    ext m
    rw [hΛ, hΛc, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPolynomial.coeff_map, hΛ, hΛc]
    have : c.coeff x.1 * κ (q.coeff x.2) = q.coeff x.2 • c.coeff x.1 := by
      rw [Algebra.smul_def, mul_comm]
      rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  rw [Ideal.mem_span_range_iff_exists_fun] at h ⊢
  obtain ⟨c, hc⟩ := h
  refine ⟨fun j => Λ (c j), ?_⟩
  rw [← h1 p, ← hc, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h2]

/-- The field extension `k = R/M → k₁ = R₁/M₁` of residue fields induced by a local homomorphism
`R → R₁` (the paper's identification of `k` with a subfield of `k₁`, "`k[Z] ⊆ k[W]`" of p. 255). -/
noncomputable def quotientMaximalIdealMap {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (α : A →+* B) [IsLocalHom α] :
    A ⧸ maximalIdeal A →+* B ⧸ maximalIdeal B :=
  Ideal.quotientMap (maximalIdeal B) α fun a ha =>
    (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp ha (IsLocalHom.map_nonunit a hu)

theorem quotientMaximalIdealMap_mk {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (α : A →+* B) [IsLocalHom α] (a : A) :
    quotientMaximalIdealMap α (Ideal.Quotient.mk (maximalIdeal A) a) =
      Ideal.Quotient.mk (maximalIdeal B) (α a) :=
  Ideal.quotientMap_mk

theorem quotientMaximalIdealMap_injective {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (α : A →+* B) [IsLocalHom α] :
    Function.Injective (quotientMaximalIdealMap α) := by
  let _ : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  exact (quotientMaximalIdealMap α).injective

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The maximal ideal is a permissible center for every ideal `J ⊆ M` (the graded pieces
`Mᵖ/Mᵖ⁺¹` of `R/J` are vector spaces over the residue field): the case "`P =` the maximal ideal
`M₁` of `R₁`" of Lemma 18, applied in the proof of Lemma 20 (p. 256). -/
private theorem isPermissibleCenter_maximalIdeal_aux (J : Ideal R) (hJ : J ≤ maximalIdeal R) :
    IsPermissibleCenter R J (maximalIdeal R) := by
  refine Or.inr ⟨(maximalIdeal.isMaximal R).isPrime, hJ, ?_, ?_⟩
  · let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
    infer_instance
  · have hmax : ((maximalIdeal R).map (Ideal.Quotient.mk J)).IsMaximal :=
      isMaximal_map_quotientMk_of_le hJ
    intro p
    let _ : Field ((R ⧸ J) ⧸ (maximalIdeal R).map (Ideal.Quotient.mk J)) :=
      Ideal.Quotient.field _
    exact Module.Free.of_divisionRing _ _

/-- A system `(g₁, …, g_i)` of elements of `J` with `ν_M(g_j) = ν^{(j)}(J)` whose initial forms are
successively independent (the initial form of `g_k` is not in the ideal generated by those of `g_j`,
`j < k`) can be extended to a standard base of `J`: repeated application of
`extendsToStandardBase_snoc`, starting from any standard base of `J`. -/
theorem extendsToStandardBase_of_forall_initialForm_notMem_span (J : Ideal R) {i : ℕ}
    (g : Fin i → R) (hgJ : ∀ j, g j ∈ J) (μ : Fin i → ℕ)
    (hord : ∀ j, Ideal.ordElem (maximalIdeal R) (g j) = μ j) (hmono : Monotone μ)
    (hnu : ∀ j : Fin i, (μ j : ℕ∞) = nuI R J (j : ℕ).succPNat)
    (hirr : ∀ k : Fin i, initialForm (maximalIdeal R) (g k) ∉ Ideal.span
      (Set.range fun j : Fin k => initialForm (maximalIdeal R) (g (Fin.castLE k.2.le j)))) :
    ExtendsToStandardBase J g := by
  classical
  have key : ∀ (k : ℕ) (hk : k ≤ i),
      ExtendsToStandardBase J (fun j : Fin k => g (Fin.castLE hk j)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      obtain ⟨m, G, hG⟩ := exists_isStandardBase J
      exact ⟨m, G, Nat.zero_le _, hG, fun j => j.elim0⟩
    | succ k ih =>
      intro hk
      have hk' : k < i := hk
      have hsnoc : (Fin.snoc (fun j : Fin k => g (Fin.castLE hk'.le j)) (g ⟨k, hk'⟩) :
          Fin (k + 1) → R) = fun j : Fin (k + 1) => g (Fin.castLE hk j) := by
        funext j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · rw [Fin.snoc_last]
          rfl
        · rw [Fin.snoc_castSucc]
          rfl
      rw [← hsnoc]
      refine extendsToStandardBase_snoc J _ (g ⟨k, hk'⟩) (ih hk'.le) (hgJ _) (μ ⟨k, hk'⟩)
        (hord _) (fun j => ?_) (le_of_eq ((hnu ⟨k, hk'⟩))) (hirr ⟨k, hk'⟩)
      rw [hord]
      exact_mod_cast hmono (show (Fin.castLE hk'.le j : Fin i) ≤ ⟨k, hk'⟩ from
        Fin.mk_le_mk.mpr j.2.le)
  exact key i le_rfl

/-- **A system whose image under a base change extends to a standard base extends to one**
(the descent used for "the conclusions (a) and (b) are replaced by equivalent ones", p. 254): if
`α : R → R'` transforms a regular system of parameters into one (so `ν_{M'}(α a) = ν_M(a)`,
`ν^{(j)}(JR') = ν^{(j)}(J)`, and `ᾱ : gr_M(R) → gr_{M'}(R')` is a ring homomorphism carrying initial
forms to initial forms), `f_j ∈ J`, and `(α f₁, …, α f_i)` can be extended to a standard base of
`JR'`, then `(f₁, …, f_i)` can be extended to a standard base of `J`: the orders are those of
`ν^{(j)}`, and the initial forms are successively independent since their images are. -/
theorem extendsToStandardBase_of_map {R' : Type u} [CommRing R'] [IsRegularLocalRing R']
    (α : R →+* R') [IsLocalHom α] (hα : RingHom.MapsRSOP α) (J : Ideal R) {i : ℕ}
    (f : Fin i → R) (hfJ : ∀ j, f j ∈ J)
    (h : ExtendsToStandardBase (J.map α) (fun j => α (f j))) : ExtendsToStandardBase J f := by
  classical
  obtain ⟨m, gs, him, hgs, hgsf⟩ := h
  have hord' : ∀ j : Fin i, Ideal.ordElem (maximalIdeal R') (α (f j)) =
      nuI R' (J.map α) (j : ℕ).succPNat := fun j => by
    have := ordElem_eq_nuI_of_isStandardBase (J.map α) gs hgs (Fin.castLE him j)
    rwa [hgsf j] at this
  have hord : ∀ j : Fin i, Ideal.ordElem (maximalIdeal R) (f j) = nuI R J (j : ℕ).succPNat :=
    fun j => by
    rw [← ordElem_map_of_mapsRSOP α hα, hord' j, ← nuI_map_eq_of_mapsRSOP α hα J]
  -- the initial forms are successively independent
  have hirr : ∀ k : Fin i, initialForm (maximalIdeal R) (f k) ∉ Ideal.span
      (Set.range fun j : Fin k => initialForm (maximalIdeal R) (f (Fin.castLE k.2.le j))) := by
    intro k hmem
    refine hgs.2.2.2.2 (Fin.castLE him k) ?_
    have hmap := Ideal.mem_map_of_mem (grMapMax α hα) hmem
    rw [Ideal.map_span, ← Set.range_comp] at hmap
    have e1 : initialForm (maximalIdeal R') (gs (Fin.castLE him k)) =
        grMapMax α hα (initialForm (maximalIdeal R) (f k)) := by
      rw [hgsf k, initialForm_map_of_mapsRSOP α hα]
    have e2 : (fun j : Fin (Fin.castLE him k : ℕ) => initialForm (maximalIdeal R')
        (gs (Fin.castLE (Fin.castLE him k).2.le j))) =
        (grMapMax α hα) ∘ fun j : Fin k =>
          initialForm (maximalIdeal R) (f (Fin.castLE k.2.le j)) := by
      funext j
      have : (Fin.castLE (Fin.castLE him k).2.le j : Fin m) =
          Fin.castLE him (Fin.castLE k.2.le j) := Fin.ext rfl
      rw [this, hgsf, Function.comp_apply, initialForm_map_of_mapsRSOP α hα]
    show initialForm (maximalIdeal R') (gs (Fin.castLE him k)) ∈ Ideal.span
      (Set.range fun j : Fin (Fin.castLE him k : ℕ) => initialForm (maximalIdeal R')
        (gs (Fin.castLE (Fin.castLE him k).2.le j)))
    rw [e1, e2]
    exact hmap
  have hfin : ∀ j : Fin i, Ideal.ordElem (maximalIdeal R) (f j) ≠ ⊤ := fun j hj => by
    refine hirr j ?_
    have : initialForm (maximalIdeal R) (f j) = 0 := by rw [initialForm, dite_eq_left hj]
    rw [this]
    exact zero_mem _
  refine extendsToStandardBase_of_forall_initialForm_notMem_span J f hfJ
    (fun j => (Ideal.ordElem (maximalIdeal R) (f j)).toNat) (fun j => by
      rw [ENat.natCast_toNat (hfin j)]) ?_ (fun j => by
      rw [ENat.natCast_toNat (hfin j)]; exact hord j) hirr
  intro j j' hjj'
  have h1 := nuI_mono J (show (j : ℕ).succPNat ≤ (j' : ℕ).succPNat from
    PNat.coe_le_coe _ _ |>.mp (by simpa using hjj'))
  have h2 : ((Ideal.ordElem (maximalIdeal R) (f j)).toNat : ℕ∞) ≤
      ((Ideal.ordElem (maximalIdeal R) (f j')).toNat : ℕ∞) := by
    rw [ENat.natCast_toNat (hfin j), ENat.natCast_toNat (hfin j'), hord j, hord j']
    exact h1
  exact_mod_cast h2

private theorem ord_span_singleton_aux {A : Type*} [CommRing A] (I : Ideal A) (x : A) :
    Ideal.ord I (Ideal.span {x}) = Ideal.ordElem I x := by
  simp only [Ideal.ord, Ideal.ordElem, Ideal.span_singleton_le_iff_mem]

/-- **The order of `x^{-ν} f` does not exceed `ν_M(f)`** (p. 256: "since `ν_M(f) = ν_{i+1}`, this
implies `ν_{M₁}(g) = ν_{i+1}`.  (See Lemma 8 of §3.)"): Lemma 8 (`nu_weakTransform_le`), which is
stated for ideals, applied to the principal ideal `(f)`, whose weak transform is the principal ideal
`(x^{-ν} f)`. -/
theorem ordElem_le_of_pow_mul_eq_toRing [IsDomain R] (P : Ideal R) [P.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] (T : MonoidalTransform R P) [IsLocalHom T.toRing]
    [IsRegularLocalRing T.ring]
    (halg : RingHom.IsResiduallyAlgebraic (R := R) (R' := T.ring) T.toRing)
    {f' : R} (hf'0 : f' ≠ 0) {ν : ℕ} (hν1 : 1 ≤ ν) (hP : Ideal.ordElem P f' = ν)
    (hM : Ideal.ordElem (maximalIdeal R) f' = ν)
    {x' g' : T.ring} (hx' : Ideal.span {x'} = P.map T.toRing)
    (hg' : x' ^ ν * g' = T.toRing f') :
    Ideal.ordElem (maximalIdeal T.ring) g' ≤ ν := by
  classical
  have hJ0 : Ideal.span {f'} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hord : Ideal.ord P (Ideal.span {f'}) = Ideal.nu (Ideal.span {f'}) := by
    rw [ord_span_singleton_aux, Ideal.nu, ord_span_singleton_aux, hP, hM]
  have h8 := nu_weakTransform_le R (Ideal.span {f'}) hJ0 P hord T halg
  have hx'0 : x' ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), zero_mul] at hg'
    exact hf'0 (T.toRing_injective (by rw [← hg', map_zero]))
  have hweak : weakTransformIdeal T (Ideal.span {f'}) = Ideal.span {g'} := by
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro y ⟨x, hx, f, hf, ν', hν', hy⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hf
      rw [ord_span_singleton_aux, hP] at hν'
      have hν'ν : ν' ≤ ν := by exact_mod_cast hν'
      obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (hx.trans hx'.symm)
      have hx0 : x ≠ 0 := fun h0 => hx'0 (by rw [← hu, h0, zero_mul])
      refine Ideal.mem_span_singleton'.mpr ⟨T.toRing a * (x ^ (ν - ν') * u ^ ν), ?_⟩
      refine mul_left_cancel₀ (pow_ne_zero ν' hx0) ?_
      rw [hy, map_mul, ← hg', ← hu]
      have : x ^ ν = x ^ ν' * x ^ (ν - ν') := by rw [← pow_add]; congr 1; omega
      rw [mul_pow, this]
      ring
    · rw [Set.singleton_subset_iff]
      exact Ideal.subset_span ⟨x', hx', f', Ideal.mem_span_singleton_self f', ν,
        by rw [ord_span_singleton_aux, hP], hg'⟩
  rw [hweak, Ideal.nu, ord_span_singleton_aux] at h8
  rwa [Ideal.nu, ord_span_singleton_aux, hM] at h8

namespace RegularFrame

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The polynomial `Q ∈ k[Z]` with `Q(Z) = φ` for an initial form `φ ∈ k[Z]` given by
`τ_{(z)}(f) = 0` (p. 251: "We have `φ_j ∈ k[Z]`"); it is homogeneous of the degree `ν_M(f)`. -/
theorem exists_isHomogeneous_frameAlgHom_eq_initialForm (F : RegularFrame R) {f : R} {d : ℕ}
    (hfd : Ideal.ordElem (maximalIdeal R) f = d)
    (hτ : tauZ R F.z (fun _ : Fin 1 => f) = 0) :
    ∃ Q : MvPolynomial (Fin F.r) (R ⧸ maximalIdeal R), Q.IsHomogeneous d ∧
      frameAlgHom F.z Q = initialForm (maximalIdeal R) f := by
  have h := F.initialForm_mem_adjoin_of_tauZ_eq_zero f hτ
  rw [Algebra.adjoin_range_eq_range_aeval] at h
  obtain ⟨Q, hQ⟩ := h
  refine ⟨Q, F.isHomogeneous_of_frameAlgHom_mem_homogeneous ?_, hQ⟩
  show frameAlgHom F.z Q ∈ _
  rw [show frameAlgHom F.z Q = initialForm (maximalIdeal R) f from hQ,
    initialForm_eq_mk _ hfd]
  exact AssocGraded.mk_mem_homogeneous _ _

end RegularFrame

end Lemma20Generic

section Lemma20Expansion

open MvPolynomial

namespace RegularFrame

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}
  {F : RegularFrame R} {T : MonoidalTransform R P}

private theorem prod_C_mul_X_pow_eq_C_mul_monomial {S : Type*} [CommRing S] {σ : Type*} (a : S)
    (d : σ →₀ ℕ) :
    d.prod (fun n e => (C a * X n : MvPolynomial σ S) ^ e) = C (a ^ d.degree) * monomial d 1 := by
  classical
  rw [monomial_eq, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_one, one_mul]
  rw [Finsupp.degree_apply, map_pow]

/-- The ideal `(z)R` is mapped into `(w)R₁` by `R → R₁`: `z_j = x w_j` (p. 253). -/
theorem FrameTransform.map_idealZ_le [IsRegularLocalRing T.ring] (FT : F.FrameTransform T) :
    F.idealZ.map T.toRing ≤ FT.toRegularFrame.idealZ := by
  rw [RegularFrame.idealZ, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  rw [← FT.mul_w j]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

theorem FrameTransform.map_idealZ_pow_le [IsRegularLocalRing T.ring] (FT : F.FrameTransform T)
    (n : ℕ) : (F.idealZ ^ n).map T.toRing ≤ FT.toRegularFrame.idealZ ^ n := by
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono FT.map_idealZ_le n

/-- The canonical homomorphism `S₁ → R₁` commutes with `S → R` and the transforms. -/
theorem FrameTransform.beta_toRing (FT : F.FrameTransform T) (s : F.S) :
    FT.β (FT.TS.toRing s) = T.toRing (algebraMap F.S R s) :=
  RingHom.congr_fun FT.canonical.comm s

/-- The substitution `Z_j ↦ x Z_j` of polynomials over `S`, composed with `S → S₁`: the
polynomial expressing `f ∈ S[z]` as a polynomial `f(x w)` in the `w_j` over `S₁`. -/
noncomputable def FrameTransform.substPoly (FT : F.FrameTransform T) (x : F.S) :
    MvPolynomial (Fin F.r) F.S →+* MvPolynomial (Fin F.r) FT.TS.ring :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp FT.TS.toRing)
    fun j => MvPolynomial.C (FT.TS.toRing x) * MvPolynomial.X j

theorem FrameTransform.coeff_substPoly (FT : F.FrameTransform T) (x : F.S)
    (G : MvPolynomial (Fin F.r) F.S) (B : Fin F.r →₀ ℕ) :
    (FT.substPoly x G).coeff B = FT.TS.toRing (G.coeff B) * FT.TS.toRing x ^ B.degree := by
  classical
  induction G using MvPolynomial.induction_on' with
  | monomial d c =>
    simp only [substPoly, eval₂Hom_monomial, RingHom.coe_comp, Function.comp_apply,
      prod_C_mul_X_pow_eq_C_mul_monomial]
    rw [C_mul_monomial, C_mul_monomial, coeff_monomial, coeff_monomial]
    by_cases h : d = B
    · subst h; simp
    · simp [h]
  | add p q hp hq =>
    have h1 : ∀ (u v : MvPolynomial (Fin F.r) FT.TS.ring),
        (u + v).coeff B = u.coeff B + v.coeff B := fun u v => by simp
    have h2 : ∀ (u v : MvPolynomial (Fin F.r) F.S),
        (u + v).coeff B = u.coeff B + v.coeff B := fun u v => by simp
    rw [map_add, h1, hp, hq, h2, map_add, add_mul]

theorem FrameTransform.toRing_evZ [IsRegularLocalRing T.ring] (FT : F.FrameTransform T)
    (x : F.S) (h7' : FT.x = T.toRing (algebraMap F.S R x)) (G : MvPolynomial (Fin F.r) F.S) :
    T.toRing (F.evZ G) = FT.toRegularFrame.evZ (FT.substPoly x G) := by
  let E1 : MvPolynomial (Fin F.r) FT.TS.ring →+* T.ring := FT.toRegularFrame.evZ.toRingHom
  have : T.toRing.comp F.evZ.toRingHom = E1.comp (FT.substPoly x) := by
    refine MvPolynomial.ringHom_ext (fun s => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply]
      have h1 : F.evZ.toRingHom (C s) = algebraMap F.S R s := by
        show F.evZ (C s) = _
        rw [evZ, aeval_C]
      have h2 : FT.substPoly x (C s) = C (FT.TS.toRing s) := by
        simp [substPoly]
      have h3 : E1 (C (FT.TS.toRing s)) = FT.β (FT.TS.toRing s) := by
        exact aeval_C _ _
      rw [h1, h2, h3, FT.beta_toRing]
    · simp only [RingHom.comp_apply]
      have h1 : F.evZ.toRingHom (X j) = F.z j := by
        show F.evZ (X j) = _
        rw [evZ, aeval_X]
      have h2 : FT.substPoly x (X j) = C (FT.TS.toRing x) * X j := by
        simp [substPoly]
      have h3 : E1 (C (FT.TS.toRing x) * X j) = FT.β (FT.TS.toRing x) * FT.w j := by
        show FT.toRegularFrame.evZ (C (FT.TS.toRing x) * X j) = _
        exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (aeval_C _ _) (aeval_X _ _))
      rw [h1, h2, h3, FT.beta_toRing, ← h7', FT.mul_w]
  exact RingHom.congr_fun this G

/-- **The expansion coefficients of `x^{-ν} a`** (p. 255: "`g = Σ d_A w^A` with
`d_A = c_A x^{|A|-ν}`"): for `a ∈ R` and `b ∈ R₁` with `xᵛ b = a` in `R₁` (`x` the denominator),
`xᵛ c_A(b) = x^{|A|} c_A(a)` in `S₁` for the expansion coefficients `c_A` with respect to
`(S₁; w)` and `(S; z)`.  The paper obtains this from the power series expansion of `a` in
`S{z₁, …, z_r}` and the substitution `z_j = x w_j`; here the coefficients are compared through the
truncations `a ≡ G(z) mod (z)^{|A|+1}`, so no completion is needed. -/
theorem FrameTransform.expCoeff_div [IsRegularLocalRing T.ring] (FT : F.FrameTransform T)
    (x : F.S) (h7' : FT.x = T.toRing (algebraMap F.S R x)) (a : R) (b : T.ring) (ν : ℕ)
    (hb : FT.x ^ ν * b = T.toRing a) (A : Fin F.r →₀ ℕ) :
    FT.TS.toRing x ^ ν * (show FT.TS.ring from FT.toRegularFrame.expCoeff b A) =
      FT.TS.toRing x ^ A.degree * FT.TS.toRing (F.expCoeff a A) := by
  obtain ⟨G, hG⟩ := exists_evZ_sub_mem_pow F (A.degree + 1) a
  obtain ⟨G', hG'⟩ : ∃ G' : MvPolynomial (Fin F.r) FT.TS.ring,
      b - FT.toRegularFrame.evZ G' ∈ FT.toRegularFrame.idealZ ^ (A.degree + 1) :=
    exists_evZ_sub_mem_pow FT.toRegularFrame (A.degree + 1) b
  have hxβ : FT.β (FT.TS.toRing x) = FT.x := by rw [FT.beta_toRing, h7']
  -- `toRing a - evZ (substPoly G) ∈ (w)^(|A|+1)`
  have h1 : T.toRing a - FT.toRegularFrame.evZ (FT.substPoly x G) ∈
      FT.toRegularFrame.idealZ ^ (A.degree + 1) := by
    rw [← FT.toRing_evZ x h7', ← map_sub]
    exact FT.map_idealZ_pow_le _ (Ideal.mem_map_of_mem _ hG)
  have h2 : FT.toRegularFrame.evZ (FT.substPoly x G - C (FT.TS.toRing x ^ ν) * G') ∈
      FT.toRegularFrame.idealZ ^ (A.degree + 1) := by
    have e : FT.toRegularFrame.evZ (C (FT.TS.toRing x ^ ν) * G') =
        FT.x ^ ν * FT.toRegularFrame.evZ G' := by
      refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ rfl)
      refine (aeval_C _ _).trans ?_
      show FT.β (FT.TS.toRing x ^ ν) = FT.x ^ ν
      rw [map_pow, hxβ]
    have e2 : FT.toRegularFrame.evZ (FT.substPoly x G - C (FT.TS.toRing x ^ ν) * G') =
        FT.toRegularFrame.evZ (FT.substPoly x G) - FT.x ^ ν * FT.toRegularFrame.evZ G' :=
      (map_sub _ _ _).trans (congrArg₂ (· - ·) rfl e)
    rw [e2]
    have : FT.toRegularFrame.evZ (FT.substPoly x G) - FT.x ^ ν * FT.toRegularFrame.evZ G' =
        -(T.toRing a - FT.toRegularFrame.evZ (FT.substPoly x G)) +
          FT.x ^ ν * (b - FT.toRegularFrame.evZ G') := by
      rw [← hb]; ring
    rw [this]
    exact add_mem (neg_mem h1) (Ideal.mul_mem_left _ _ hG')
  have h3 := coeff_eq_zero_of_evZ_mem_pow FT.toRegularFrame h2 A (Nat.lt_succ_self _)
  have h4 : (FT.substPoly x G).coeff A - FT.TS.toRing x ^ ν * G'.coeff A = 0 := by
    have : ((FT.substPoly x G) - C (FT.TS.toRing x ^ ν) * G').coeff A =
        (FT.substPoly x G).coeff A - FT.TS.toRing x ^ ν * G'.coeff A := by
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul]
    rw [← this]; exact h3
  rw [FT.coeff_substPoly, sub_eq_zero] at h4
  rw [← expCoeff_eq F hG (Nat.lt_succ_self _)] at h4
  have h5 : G'.coeff A = FT.toRegularFrame.expCoeff b A :=
    (expCoeff_eq FT.toRegularFrame hG' (Nat.lt_succ_self _)).symm
  rw [h5] at h4
  exact h4.symm.trans (mul_comm _ _)

end RegularFrame

end Lemma20Expansion

section Lemma20InitialForms

open MvPolynomial

namespace RegularFrame

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}
  {F : RegularFrame R} {T : MonoidalTransform R P} [IsLocalHom T.toRing]
  [IsRegularLocalRing T.ring]

/-- **The coefficients of the initial form of `x^{-ν} f`** (p. 255: "`ψ_j = φ_j(W₁, …, W_r) +
λ_j`" and "the assumption (8) implies that `ψ_j = φ_j(W₁, …, W_r)`"): let `f ∈ Mᵈ` have its
initial form `[f]_d = P(Z)` with `P ∈ k[Z]` homogeneous of degree `d`, and let `g ∈ M₁ᵈ`,
`x^d g = f`, have its initial form `[g]_d = Q(W)` with `Q ∈ k₁[W]` homogeneous of degree `d`.
Then `Q = κ P`, `κ` the residue field extension `k → k₁`.  The proof compares the coefficients of
`Z^A`, `|A| = d`: they are the residues of the expansion coefficients `c_A(f)`, `c_A(g)`
(`coeff_eq_residue_expCoeff_of_frameAlgHom_eq_mk`), and `c_A(g) = c_A(f)` for `|A| = d`
(`expCoeff_div`, i.e. `d_A = c_A x^{|A|-ν}` of p. 255). -/
theorem FrameTransform.eq_map_of_frameAlgHom_eq_mk (FT : F.FrameTransform T) (x : F.S)
    (h7' : FT.x = T.toRing (algebraMap F.S R x)) (hx0 : FT.TS.toRing x ≠ 0)
    {d : ℕ} {f : R} (hf : f ∈ maximalIdeal R ^ d)
    {Pf : MvPolynomial (Fin F.r) (R ⧸ maximalIdeal R)} (hP : Pf.IsHomogeneous d)
    (hfP : frameAlgHom F.z Pf = AssocGraded.mk (maximalIdeal R) d f hf)
    {g : T.ring} (hg : FT.x ^ d * g = T.toRing f) (hgM : g ∈ maximalIdeal T.ring ^ d)
    {Q : MvPolynomial (Fin F.r) (T.ring ⧸ maximalIdeal T.ring)} (hQ : Q.IsHomogeneous d)
    (hgQ : frameAlgHom FT.w Q = AssocGraded.mk (maximalIdeal T.ring) d g hgM) :
    Q = MvPolynomial.map (quotientMaximalIdealMap T.toRing) Pf := by
  classical
  ext A
  rw [MvPolynomial.coeff_map]
  by_cases hA : A.degree = d
  · have h1 := FT.toRegularFrame.coeff_eq_residue_expCoeff_of_frameAlgHom_eq_mk hgM hQ hgQ A hA
    have h2 := F.coeff_eq_residue_expCoeff_of_frameAlgHom_eq_mk hf hP hfP A hA
    have hdiv := FT.expCoeff_div x h7' f g d hg A
    rw [hA] at hdiv
    have hc : (show FT.TS.ring from FT.toRegularFrame.expCoeff g A) =
        FT.TS.toRing (F.expCoeff f A) :=
      mul_left_cancel₀ (pow_ne_zero d hx0) hdiv
    refine h1.trans ?_
    rw [h2, quotientMaximalIdealMap_mk]
    congr 1
    exact (congrArg FT.β hc).trans (FT.beta_toRing _)
  · rw [hQ.coeff_eq_zero (by simpa using hA), hP.coeff_eq_zero (by simpa using hA), map_zero]

/-- **The initial forms of `g_j = x^{-ν_j} f_j`** (p. 255: "`ψ_j = φ_j(W₁, …, W_r)` for
`1 ≤ j ≤ i`"): if the initial forms `φ_j` of `f_j` lie in `k[Z]` (`τ_{(z)}(f_j) = 0`) and
those `ψ_j` of `g_j` in `k₁[W]` (`τ_{(w)}(g_j) = 0`), where `ν_M(f_j) = ν_{M₁}(g_j) = ν_j`,
then `φ_j = P_j(Z)`, `ψ_j = (κ P_j)(W)` for the same homogeneous polynomials `P_j` of degree `ν_j`
over `k`, `κ : k → k₁` the residue field extension. -/
theorem FrameTransform.exists_polynomials_initialForm (FT : F.FrameTransform T) (x : F.S)
    (h7' : FT.x = T.toRing (algebraMap F.S R x)) (hx0 : FT.TS.toRing x ≠ 0) {i : ℕ}
    (f : Fin i → R) (g : Fin i → T.ring) (ν : Fin i → ℕ)
    (hf : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = ν j)
    (h2 : ∀ j, tauZ R F.z (fun _ : Fin 1 => f j) = 0)
    (hg : ∀ j, FT.x ^ ν j * g j = T.toRing (f j))
    (hgM : ∀ j, Ideal.ordElem (maximalIdeal T.ring) (g j) = ν j)
    (h8 : ∀ j, tauZ T.ring FT.w (fun _ : Fin 1 => g j) = 0) :
    ∃ Pf : Fin i → MvPolynomial (Fin F.r) (R ⧸ maximalIdeal R),
      (∀ j, (Pf j).IsHomogeneous (ν j)) ∧
      (∀ j, frameAlgHom F.z (Pf j) = initialForm (maximalIdeal R) (f j)) ∧
      (∀ j, frameAlgHom FT.w (MvPolynomial.map (quotientMaximalIdealMap T.toRing) (Pf j)) =
        initialForm (maximalIdeal T.ring) (g j)) := by
  classical
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let _ : Field (T.ring ⧸ maximalIdeal T.ring) := Ideal.Quotient.field _
  choose Pf hPh hPf using fun j => F.exists_isHomogeneous_frameAlgHom_eq_initialForm (hf j) (h2 j)
  obtain ⟨Qg, hQh, hQg⟩ : ∃ Qg : Fin i → MvPolynomial (Fin F.r) (T.ring ⧸ maximalIdeal T.ring),
      (∀ j, (Qg j).IsHomogeneous (ν j)) ∧
        ∀ j, frameAlgHom FT.w (Qg j) = initialForm (maximalIdeal T.ring) (g j) := by
    choose Q hQ1 hQ2 using fun j =>
      FT.toRegularFrame.exists_isHomogeneous_frameAlgHom_eq_initialForm (hgM j) (h8 j)
    exact ⟨Q, hQ1, hQ2⟩
  refine ⟨Pf, hPh, hPf, fun j => ?_⟩
  have : Qg j = MvPolynomial.map (quotientMaximalIdealMap T.toRing) (Pf j) := by
    refine FT.eq_map_of_frameAlgHom_eq_mk x h7' hx0 (Ideal.mem_pow_of_ordElem (hf j)) (hPh j) ?_
      (hg j) (Ideal.mem_pow_of_ordElem (hgM j)) (hQh j) ?_
    · rw [hPf j, initialForm_eq_mk _ (hf j)]
    · rw [hQg j, initialForm_eq_mk _ (hgM j)]
  rw [← this]
  exact hQg j

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **The `E`-set of `(g₁, …, g_i)` is that of `(f₁, …, f_i)`** (p. 255: "This is enough for that
we have the same `E`-set of `I` with respect to `(k; Z₁, …, Z_r)` as that of `I'` with respect to
`(k; W₁, …, W_r)`"), given the polynomials `P_j` with `φ_j = P_j(Z)`, `ψ_j = (κ P_j)(W)`: `I' =
I · k₁[W]`, and the `E`-set does not change under the extension of the coefficient field
`k → k₁` (Remark 1, `eSet_map_of_injective`). -/
theorem FrameTransform.frameESet_eq_of_polynomials (FT : F.FrameTransform T) {i : ℕ}
    (f : Fin i → R) (g : Fin i → T.ring) (ν : Fin i → ℕ)
    (Pf : Fin i → MvPolynomial (Fin F.r) (R ⧸ maximalIdeal R))
    (hPh : ∀ j, (Pf j).IsHomogeneous (ν j))
    (hPf : ∀ j, frameAlgHom F.z (Pf j) = initialForm (maximalIdeal R) (f j))
    (hQg : ∀ j, frameAlgHom FT.w (MvPolynomial.map (quotientMaximalIdealMap T.toRing) (Pf j)) =
      initialForm (maximalIdeal T.ring) (g j)) :
    frameESet FT.w g = frameESet F.z f := by
  classical
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let _ : Field (T.ring ⧸ maximalIdeal T.ring) := Ideal.Quotient.field _
  have hI : frameInitialIdeal F.z f = Ideal.span (Set.range Pf) := by
    unfold frameInitialIdeal
    congr 1
    ext ψ
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, F.frameAlgHom_injective (by rw [hj, hPf j])⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, hPf j⟩
  have hI' : frameInitialIdeal FT.w g = Ideal.span
      (Set.range fun j => MvPolynomial.map (quotientMaximalIdealMap T.toRing) (Pf j)) := by
    unfold frameInitialIdeal
    congr 1
    ext ψ
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, FT.toRegularFrame.frameAlgHom_injective ((hj.trans (hQg j).symm).symm)⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, hQg j⟩
  have hhom : (frameInitialIdeal F.z f).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin F.r) (R ⧸ maximalIdeal R)) := by
    rw [hI]
    apply Ideal.homogeneous_span
    rintro _ ⟨j, rfl⟩
    exact ⟨ν j, hPh j⟩
  have hmap : frameInitialIdeal FT.w g =
      (frameInitialIdeal F.z f).map (MvPolynomial.map (quotientMaximalIdealMap T.toRing)) := by
    rw [hI', hI, Ideal.map_span, ← Set.range_comp]
    rfl
  have key := (eSet_map_of_injective (quotientMaximalIdealMap T.toRing)
    (quotientMaximalIdealMap_injective _) (frameInitialIdeal F.z f) hhom).2
    (fun a ha b hab => (mul_eq_zero.mp hab).resolve_left
      ((map_ne_zero_iff _ (quotientMaximalIdealMap_injective _)).mpr ha))
  unfold frameESet
  rw [hmap]
  exact key

/-- **Independence of the initial forms is preserved** (the step "`(g₁, …, g_i)` can be extended to
a standard base of `J₁`" needed for Lemma 18 in `R₁`, not argued on p. 256): if
`φ_k ∉ (φ_j)_{j<k} gr_M(R)` then `ψ_k ∉ (ψ_j)_{j<k} gr_{M₁}(R₁)`.  Proof: `ψ_j = (κ P_j)(W)`, the
retraction `gr_{M₁}(R₁) → k₁[W]` and the descent of ideal membership along `k → k₁`
(`mem_span_range_of_map_mem_span_range`). -/
theorem FrameTransform.initialForm_notMem_span_of_polynomials (FT : F.FrameTransform T) {i : ℕ}
    (f : Fin i → R) (g : Fin i → T.ring)
    (Pf : Fin i → MvPolynomial (Fin F.r) (R ⧸ maximalIdeal R))
    (hPf : ∀ j, frameAlgHom F.z (Pf j) = initialForm (maximalIdeal R) (f j))
    (hQg : ∀ j, frameAlgHom FT.w (MvPolynomial.map (quotientMaximalIdealMap T.toRing) (Pf j)) =
      initialForm (maximalIdeal T.ring) (g j)) (k : Fin i)
    (hind : initialForm (maximalIdeal R) (f k) ∉ Ideal.span (Set.range fun j : Fin k =>
      initialForm (maximalIdeal R) (f (Fin.castLE k.2.le j)))) :
    initialForm (maximalIdeal T.ring) (g k) ∉ Ideal.span (Set.range fun j : Fin k =>
      initialForm (maximalIdeal T.ring) (g (Fin.castLE k.2.le j))) := by
  classical
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let _ : Field (T.ring ⧸ maximalIdeal T.ring) := Ideal.Quotient.field _
  obtain ⟨π, hπ⟩ : ∃ π : AssocGraded (maximalIdeal T.ring) →ₐ[T.ring ⧸ maximalIdeal T.ring]
      MvPolynomial (Fin F.r) (T.ring ⧸ maximalIdeal T.ring),
      ∀ Q, π (frameAlgHom FT.w Q) = Q := FT.toRegularFrame.exists_retraction_frameAlgHom
  intro hmem
  apply hind
  have h1 := Ideal.mem_map_of_mem (π : AssocGraded (maximalIdeal T.ring) →+*
    MvPolynomial (Fin F.r) (T.ring ⧸ maximalIdeal T.ring)) hmem
  rw [Ideal.map_span, ← Set.range_comp] at h1
  have h1' : MvPolynomial.map (quotientMaximalIdealMap T.toRing) (Pf k) ∈
      Ideal.span (Set.range fun j : Fin k =>
        MvPolynomial.map (quotientMaximalIdealMap T.toRing) (Pf (Fin.castLE k.2.le j))) := by
    have e1 : π (initialForm (maximalIdeal T.ring) (g k)) =
        MvPolynomial.map (quotientMaximalIdealMap T.toRing) (Pf k) :=
      (congrArg π (hQg k)).symm.trans (hπ _)
    have e2 : ((π : AssocGraded (maximalIdeal T.ring) →+*
        MvPolynomial (Fin F.r) (T.ring ⧸ maximalIdeal T.ring)) ∘ fun j : Fin k =>
          initialForm (maximalIdeal T.ring) (g (Fin.castLE k.2.le j))) =
        fun j : Fin k =>
          MvPolynomial.map (quotientMaximalIdealMap T.toRing) (Pf (Fin.castLE k.2.le j)) := by
      funext j
      exact (congrArg π (hQg (Fin.castLE k.2.le j))).symm.trans (hπ _)
    rw [e2] at h1
    exact e1 ▸ h1
  have h2' := mem_span_range_of_map_mem_span_range (quotientMaximalIdealMap T.toRing)
    (quotientMaximalIdealMap_injective _) (fun j : Fin k => Pf (Fin.castLE k.2.le j)) h1'
  have h3 := Ideal.mem_map_of_mem
    (frameAlgHom F.z : MvPolynomial (Fin F.r) (R ⧸ maximalIdeal R)
      →+* AssocGraded (maximalIdeal R)) h2'
  rw [Ideal.map_span, ← Set.range_comp] at h3
  have e3 : ((frameAlgHom F.z : MvPolynomial (Fin F.r) (R ⧸ maximalIdeal R)
      →+* AssocGraded (maximalIdeal R)) ∘ fun j : Fin k => Pf (Fin.castLE k.2.le j)) =
      fun j : Fin k => initialForm (maximalIdeal R) (f (Fin.castLE k.2.le j)) := by
    funext j
    exact hPf _
  rw [e3] at h3
  exact (hPf k) ▸ h3

end RegularFrame

end Lemma20InitialForms



/-! ### Lemma 21 (pp. 256–258) -/

/-! ### Auxiliary results for the proof of Proposition 2 (pp. 258–259) -/

section Rescale

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

namespace RegularFrame

variable {F : RegularFrame R} {P : Ideal R} {T : MonoidalTransform R P}
  [IsRegularLocalRing T.ring]

/-- Rescaling the denominator of a frame transform by a unit `v` of `R₁`: `(S₁; v⁻¹ w₁, …)` is the
frame transform with denominator `x v` (the denominator is only determined up to a unit,
p. 253). -/
noncomputable def FrameTransform.rescaleDenominator (FT : F.FrameTransform T) (v : T.ringˣ) :
    F.FrameTransform T where
  x := FT.x * v
  span_x := by rw [Ideal.span_singleton_mul_right_unit v.isUnit]; exact FT.span_x
  TS := FT.TS
  β := FT.β
  canonical := FT.canonical
  isRegular := FT.isRegular
  w := fun j => ((v⁻¹ : T.ringˣ) : T.ring) * FT.w j
  mul_w := fun j => by
    rw [← FT.mul_w j]
    calc FT.x * (v : T.ring) * (((v⁻¹ : T.ringˣ) : T.ring) * FT.w j)
        = FT.x * ((v : T.ring) * ((v⁻¹ : T.ringˣ) : T.ring)) * FT.w j := by ring
      _ = FT.x * FT.w j := by rw [Units.mul_inv, mul_one]
  extends_rsop := by
    classical
    have h := FT.extends_rsop.image_of_associated (fun a => ((v⁻¹ : T.ringˣ) : T.ring) * a)
      (fun a _ b _ hab => by simpa using hab)
      (fun a _ => ⟨v⁻¹, mul_comm _ _⟩)
    rwa [Finset.image_image] at h
  quot_bijective := by
    have hspan : Ideal.span (Set.range fun j => ((v⁻¹ : T.ringˣ) : T.ring) * FT.w j) =
        Ideal.span (Set.range FT.w) := by
      refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
      · rintro _ ⟨j, rfl⟩
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
      · rintro _ ⟨j, rfl⟩
        have : FT.w j = (v : T.ring) * (((v⁻¹ : T.ringˣ) : T.ring) * FT.w j) := by
          rw [← mul_assoc, Units.mul_inv, one_mul]
        rw [SetLike.mem_coe, this]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    show Function.Bijective ((Ideal.Quotient.mk (Ideal.span (Set.range fun j =>
      ((v⁻¹ : T.ringˣ) : T.ring) * FT.w j))).comp FT.β)
    rw [hspan]
    exact FT.quot_bijective

/-- Given a frame transform, the denominator may be replaced by any generator of `PR₁` of the form
`T.toRing (algebraMap x)`, `x ∈ S` (a copy of `exists_frameTransform_x_eq` of
`Hironaka/Ch3/JStability.lean`, which lies downstream of this file). -/
theorem exists_frameTransform_denominator_eq [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] (x : F.S)
    (hxP : algebraMap F.S R x ∈ P)
    (hx : P.map T.toRing = Ideal.span {T.toRing (algebraMap F.S R x)})
    {w : Fin F.r → T.ring} (hw : ∀ j, T.toRing (algebraMap F.S R x) * w j = T.toRing (F.z j))
    (hnu : ∀ j, ¬ IsUnit (w j)) :
    ∃ FT : F.FrameTransform T, FT.x = T.toRing (algebraMap F.S R x) := by
  have hex : F.AdmitsFrameTransform T :=
    (RegularFrame.admitsFrameTransform_iff (F := F) T).mpr ⟨x, hxP, hx, w, hw, hnu⟩
  obtain ⟨FT⟩ := hex
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (FT.span_x.trans hx)
  exact ⟨FT.rescaleDenominator u, hu⟩

end RegularFrame

end Rescale

section FrameTransformLift

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {F : RegularFrame R}
  {S' : Type u} [CommRing S'] [IsRegularLocalRing S'] {a : F.S →+* S'} [IsLocalHom a]
  {P : Ideal R} {T : MonoidalTransform R P}

/-- **Lifting a frame transform along the base change `R → S̃{z}`** (p. 254: "`R₁` by a monoidal
transform `R̃₁` of `R̃` with centre `PR̃` which admits a canonical local homomorphism `R₁ → R̃₁`",
and "`(S̃; z₁, …, z_r)` admits a frame transform in `R̃₁`"): given the frame transform `FT` of
`(S; z)` in `R₁` with denominator `x ∈ S`, the frame `(S̃; z)` of `R̃ = S̃⟦z⟧` admits a frame
transform in the canonical lift `R̃₁` of `R₁` with denominator the image `a(x)` of `x`, whose
elements `z_j/a(x)` are the images `β(z_j/x)` of the `z_j/x`. -/
theorem RegularFrame.FrameTransform.exists_baseChange [P.IsPrime] [IsRegularLocalRing (R ⧸ P)]
    [IsLocalHom T.toRing] [IsRegularLocalRing T.ring] (ha : RingHom.MapsRSOP a)
    (L : BaseChangeLift (F.baseChangeHom a) T) (FT : F.FrameTransform T) (x : F.S)
    (hxP : algebraMap F.S R x ∈ P)
    (h7 : P.map T.toRing = Ideal.span {T.toRing (algebraMap F.S R x)})
    (h7' : FT.x = T.toRing (algebraMap F.S R x)) :
    ∃ FT' : (F.baseChange S').FrameTransform L.T',
      FT'.x = L.T'.toRing (algebraMap S' (MvPowerSeries (Fin F.r) S') (a x)) ∧
        ∀ j, FT'.w j = L.β (FT.w j) := by
  classical
  have hα := F.mapsRSOP_baseChangeHom a ha
  obtain ⟨hP', hq'⟩ := RingHom.MapsRSOP.isPrime_map_and_isRegularLocalRing_quotient hα
    (inferInstance : P.IsPrime) inferInstance
  have := hP'
  have := hq'
  have := L.isRegularLocalRing hα
  have := L.isLocalHom_toRing
  have hxP' := F.algebraMap_mem_map_baseChangeHom (a := a) x hxP
  have hx' := L.map_eq_span_baseChange x h7
  have hw' : ∀ j, L.T'.toRing (algebraMap S' (MvPowerSeries (Fin F.r) S') (a x)) * L.β (FT.w j) =
      L.T'.toRing ((F.baseChange S').z j) := by
    intro j
    rw [L.toRing_algebraMap_baseChange, ← map_mul, ← h7', FT.mul_w j,
      ← F.baseChangeHom_z' a j, L.toRing_baseChangeHom]
  have hnu : ∀ j, ¬ IsUnit (L.β (FT.w j)) := by
    intro j hj
    refine absurd (isUnit_of_map_unit L.β _ hj) ?_
    obtain ⟨s, hsub, hs⟩ := FT.extends_rsop
    have hwM : FT.w j ∈ maximalIdeal T.ring := by
      rw [← hs.1]
      exact Ideal.subset_span (hsub (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    exact hwM
  obtain ⟨FT', hFT'⟩ := RegularFrame.exists_frameTransform_denominator_eq (F := F.baseChange S')
    (P := P.map (F.baseChangeHom a)) (T := L.T') (a x) hxP' hx' hw' hnu
  refine ⟨FT', hFT', fun j => ?_⟩
  have hFTx0 : FT.x ≠ 0 := by
    intro h0
    have h1 : P.map T.toRing = ⊥ := by rw [← FT.span_x, h0, Ideal.span_singleton_eq_bot]
    exact T.x_ne_zero (T.toRing_injective ((Ideal.mem_bot.mp (h1 ▸ Ideal.mem_map_of_mem T.toRing T.x_mem)).trans
      (map_zero _).symm))
  have hx0 : L.T'.toRing (algebraMap S' (MvPowerSeries (Fin F.r) S') (a x)) ≠ 0 := by
    rw [L.toRing_algebraMap_baseChange, ← h7']
    exact (map_ne_zero_iff _ (L.injective_β hα)).mpr hFTx0
  have h1 := FT'.mul_w j
  rw [hFT'] at h1
  exact mul_left_cancel₀ hx0 (h1.trans (hw' j).symm)

end FrameTransformLift

section FrameTransformLiftInner

attribute [local instance] RegularFrame.isDomain_S

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {F : RegularFrame R}
  {F0 : RegularFrame F.S} {S0 : Type u} [CommRing S0] [IsRegularLocalRing S0]
  {a₀ : F0.S →+* S0} [IsLocalHom a₀] {P : Ideal R} {T : MonoidalTransform R P}

local notation "S1" => MvPowerSeries (Fin F0.r) S0
local notation "R1" => MvPowerSeries (Fin F.r) (MvPowerSeries (Fin F0.r) S0)
local notation "aa" => F0.baseChangeHom a₀
local notation "αα" => F.baseChangeHom (F0.baseChangeHom a₀)

/-- **Lifting the frame transform of the inner frame** (for the nested frames `(S; z)` of `R` and
`(S₀; w)` of `S` of the reformulation of Lemma 25, pp. 270–271: "the proof of (ii) of (c) can be
reduced to the case in which the residue field `k` of `S₀` is algebraically closed"): let
`a₀ : S₀ → S̃₀` be a local homomorphism transforming a regular system of parameters into one, `S̃ =
S̃₀⟦w⟧`, `R̃ = S̃⟦z⟧`, `FT'` a lift of the frame transform `FT` of `(S; z)` in `R₁` (denominator the
image of `y ∈ S₀`; for instance the `FT'` of `exists_baseChange`, whose denominator is the image of
`a(x)`, `x = y`), `FT0` a frame transform of `(S₀; w)` in the monoidal
transform `S₁` of `S` with denominator `y`.  Then the frame `(S̃₀; w)` of `S̃` admits a frame
transform in the monoidal transform `S̃₁` of `FT'`, with denominator the image of `a₀ y`, whose
elements `w/ỹ` have the same image in `R̃₁` as the images `β(w/y)` of the `w/y`. -/
theorem RegularFrame.FrameTransform.exists_baseChange_inner [P.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (ha₀ : RingHom.MapsRSOP a₀)
    (L : BaseChangeLift (F.baseChangeHom (F0.baseChangeHom a₀)) T) (FT : F.FrameTransform T)
    (y : F0.S) (hyP : algebraMap F.S R (algebraMap F0.S F.S y) ∈ P)
    (h7' : FT.x = T.toRing (algebraMap F.S R (algebraMap F0.S F.S y)))
    (FT0 : F0.FrameTransform FT.TS) (h0 : FT0.x = FT.TS.toRing (algebraMap F0.S F.S y))
    (FT' : (F.baseChange (MvPowerSeries (Fin F0.r) S0)).FrameTransform L.T')
    (h7'' : FT'.x = L.T'.toRing (algebraMap (MvPowerSeries (Fin F0.r) S0)
      (MvPowerSeries (Fin F.r) (MvPowerSeries (Fin F0.r) S0))
      (F0.baseChangeHom a₀ (algebraMap F0.S F.S y)))) :
    ∃ FT0' : (F0.baseChange S0).FrameTransform FT'.TS,
      FT0'.x = FT'.TS.toRing (algebraMap S0 (MvPowerSeries (Fin F0.r) S0) (a₀ y)) ∧
        ∀ j, FT'.β (FT0'.w j) = L.β (FT.β (FT0.w j)) := by
  classical
  have ha := F0.mapsRSOP_baseChangeHom a₀ ha₀
  have hα := F.mapsRSOP_baseChangeHom (F0.baseChangeHom a₀) ha
  obtain ⟨hPp, hPq⟩ := RingHom.MapsRSOP.isPrime_map_and_isRegularLocalRing_quotient hα
    (inferInstance : P.IsPrime) inferInstance
  have := hPp
  have := hPq
  have := L.isRegularLocalRing hα
  have := L.isLocalHom_toRing
  have := FT'.canonical.isLocalHom
  have := FT.canonical.isLocalHom
  have := FT0.canonical.isLocalHom
  set Q' : Ideal S1 := (P.map αα).comap (algebraMap S1 R1) with hQ'
  have hQ'prime : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hQ'reg : IsRegularLocalRing (S1 ⧸ Q') := FT'.idealZ_le_and_unique.2.2.1
  -- the center `Q = P ∩ S` of the inner transform
  have hQprime : (P.comap (algebraMap F.S R)).IsPrime := Ideal.comap_isPrime _ _
  have hQreg : IsRegularLocalRing (F.S ⧸ P.comap (algebraMap F.S R)) :=
    FT.idealZ_le_and_unique.2.2.1
  have := hQprime
  have := hQreg
  have hxR : Ideal.span {FT'.TS.xR} = Q'.map FT'.TS.toRing := FT'.TS.span_xR_eq_map
  -- `FT'.x ≠ 0`
  have hx0 : FT'.x ≠ 0 := by
    intro h0
    have h1 : (P.map αα).map L.T'.toRing = ⊥ := by
      rw [← FT'.span_x, h0, Ideal.span_singleton_eq_bot]
    exact L.T'.x_ne_zero (L.T'.toRing_injective ((Ideal.mem_bot.mp
      (h1 ▸ Ideal.mem_map_of_mem L.T'.toRing L.T'.x_mem)).trans (map_zero _).symm))
  -- the image of `ã₀ y` in `R̃₁`
  have hcomm : ∀ s : S1, FT'.β (FT'.TS.toRing s) =
      L.T'.toRing (algebraMap S1 R1 s) := fun s => RingHom.congr_fun FT'.canonical.comm s
  have hCy : algebraMap S0 S1 (a₀ y) = aa (algebraMap F0.S F.S y) := by
    rw [F0.baseChangeHom_algebraMap a₀ y, algebraMap_mvPowerSeries_eq_C]
  have hβe : FT'.β (FT'.TS.toRing (algebraMap S0 S1 (a₀ y))) = FT'.x := by
    rw [hcomm, hCy, h7'']
  -- `ỹ ∈ Q'`
  have hyQ : algebraMap S0 S1 (a₀ y) ∈ Q' := by
    rw [hCy, hQ', Ideal.mem_comap]
    exact F.algebraMap_mem_map_baseChangeHom (algebraMap F0.S F.S y) hyP
  have heI : FT'.TS.toRing (algebraMap S0 S1 (a₀ y)) ∈ Q'.map FT'.TS.toRing :=
    Ideal.mem_map_of_mem _ hyQ
  -- `(ỹ) S̃₁ = Q' S̃₁`
  have hspan : Q'.map FT'.TS.toRing =
      Ideal.span {FT'.TS.toRing (algebraMap S0 S1 (a₀ y))} := by
    rw [← hxR] at heI ⊢
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp heI
    have hξ : FT'.β FT'.TS.xR ∈ Ideal.span {FT'.x} := by
      rw [FT'.span_x]
      have h1 : FT'.TS.xR ∈ Q'.map FT'.TS.toRing := hxR ▸ Ideal.mem_span_singleton_self _
      have h2 := Ideal.mem_map_of_mem FT'.β h1
      have h3 : (Q'.map FT'.TS.toRing).map FT'.β ≤ (P.map αα).map L.T'.toRing := by
        refine Ideal.map_le_iff_le_comap.mpr ?_
        refine Ideal.map_le_iff_le_comap.mpr ?_
        intro q hq
        change FT'.β (FT'.TS.toRing q) ∈ (P.map αα).map L.T'.toRing
        rw [hcomm q]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mp hq)
      exact h3 h2
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hξ
    have hs' : IsUnit s := by
      refine isUnit_of_map_unit FT'.β _ ?_
      have h3 : FT'.x = FT'.x * (u * FT'.β s) := by
        calc FT'.x = FT'.β (FT'.TS.toRing (algebraMap S0 S1 (a₀ y))) := hβe.symm
          _ = FT'.β (s * FT'.TS.xR) := by rw [← hs]
          _ = FT'.x * (u * FT'.β s) := by rw [map_mul, ← hu]; ring
      have h4 : u * FT'.β s = 1 := mul_left_cancel₀ hx0 (h3.symm.trans (mul_one _).symm)
      exact isUnit_iff_exists_inv.mpr ⟨u, by rw [mul_comm]; exact h4⟩
    rw [← hs, mul_comm]
    exact (Ideal.span_singleton_mul_right_unit hs' _).symm
  have := FT.isRegular
  have := FT'.isRegular
  have := FT0.isRegular
  -- `z_j ∈ Q` for the elements of the inner frame
  have hz0 : ∀ j, algebraMap F.S R (F0.z j) ∈ P := by
    intro j
    have h1 : FT.TS.toRing (F0.z j) ∈ (P.comap (algebraMap F.S R)).map FT.TS.toRing := by
      rw [← FT0.span_x, ← FT0.mul_w j]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have h2 := (FT0.idealZ_le_and_unique).1
    have h3 : F0.z j ∈ ((P.comap (algebraMap F.S R)).map FT.TS.toRing).comap FT.TS.toRing :=
      Ideal.mem_comap.mpr h1
    rw [h2] at h3
    exact h3
  have hXj : ∀ j, (F0.baseChange S0).z j ∈ Q' := by
    intro j
    rw [hQ', Ideal.mem_comap, ← F0.baseChangeHom_z' a₀ j]
    have h1 := RingHom.congr_fun (F.baseChangeHom_comp_algebraMap (F0.baseChangeHom a₀))
      (F0.z j)
    simp only [RingHom.comp_apply] at h1
    rw [← h1]
    exact Ideal.mem_map_of_mem _ (hz0 j)
  have hex : ∀ j, ∃ w : FT'.TS.ring, FT'.TS.toRing (algebraMap S0 S1 (a₀ y)) * w =
      FT'.TS.toRing ((F0.baseChange S0).z j) := by
    intro j
    have h1 : FT'.TS.toRing ((F0.baseChange S0).z j) ∈ Q'.map FT'.TS.toRing :=
      Ideal.mem_map_of_mem _ (hXj j)
    rw [hspan] at h1
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp h1
    exact ⟨w, by rw [mul_comm]; exact hw⟩
  choose w' hw' using hex
  -- the images in `R̃₁`
  have hFTx : FT'.x = L.β FT.x := by
    rw [h7'', L.toRing_algebraMap_baseChange, h7']
  have hβ0 : FT.β FT0.x = FT.x := by
    rw [h0, ← RingHom.comp_apply, FT.canonical.comm, RingHom.comp_apply, h7']
  have himg : ∀ j, FT'.β (w' j) = L.β (FT.β (FT0.w j)) := by
    intro j
    apply mul_left_cancel₀ hx0
    calc FT'.x * FT'.β (w' j)
        = FT'.β (FT'.TS.toRing (algebraMap S0 S1 (a₀ y)) * w' j) := by rw [map_mul, hβe]
      _ = FT'.β (FT'.TS.toRing ((F0.baseChange S0).z j)) := by rw [hw' j]
      _ = L.T'.toRing (algebraMap S1 R1 ((F0.baseChange S0).z j)) := hcomm _
      _ = L.T'.toRing (algebraMap S1 R1 (aa (F0.z j))) := by rw [F0.baseChangeHom_z' a₀ j]
      _ = L.T'.toRing (αα (algebraMap F.S R (F0.z j))) := by
        rw [← RingHom.comp_apply (algebraMap S1 R1), ← F.baseChangeHom_comp_algebraMap]
        rfl
      _ = L.β (T.toRing (algebraMap F.S R (F0.z j))) := L.toRing_baseChangeHom _
      _ = L.β (FT.β (FT.TS.toRing (F0.z j))) := by
        rw [← RingHom.comp_apply FT.β, ← RingHom.comp_apply, FT.canonical.comm]
        rfl
      _ = L.β (FT.β (FT0.x * FT0.w j)) := by rw [FT0.mul_w j]
      _ = FT'.x * L.β (FT.β (FT0.w j)) := by rw [map_mul, map_mul, hβ0, hFTx]
  have hnu : ∀ j, ¬ IsUnit (w' j) := by
    intro j hj
    have hwM : FT0.w j ∈ maximalIdeal FT.TS.ring := by
      obtain ⟨s, hsub, hs⟩ := FT0.extends_rsop
      rw [← hs.1]
      exact Ideal.subset_span (hsub (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    have h1 : ¬ IsUnit (L.β (FT.β (FT0.w j))) := fun hu =>
      hwM (isUnit_of_map_unit FT.β _ (isUnit_of_map_unit L.β _ hu))
    exact h1 (himg j ▸ hj.map FT'.β)
  have hq0 : Q'.IsPrime := hQ'prime
  have he0 : FT'.TS.toRing (algebraMap S0 S1 (a₀ y)) ≠ 0 := by
    intro h
    exact hx0 (by rw [← hβe, h, map_zero])
  let T0 : MonoidalTransform S1 Q' := FT'.TS
  have hreg1 : IsRegularLocalRing T0.ring := FT'.isRegular
  have hdom1 : IsDomain FT'.TS.ring := Transforms.isDomain_of_isRegularLocalRing _
  obtain ⟨FT0', hFT0'x⟩ := RegularFrame.exists_frameTransform_denominator_eq
    (F := F0.baseChange S0) (P := Q') (T := T0) (a₀ y) hyQ hspan hw' hnu
  refine ⟨FT0', hFT0'x, fun j => ?_⟩
  have h1 : FT0'.x * FT0'.w j = T0.toRing ((F0.baseChange S0).z j) := FT0'.mul_w j
  rw [hFT0'x] at h1
  have key : ∀ {A : Type u} [CommRing A] [IsDomain A] {e w w' z : A}, e ≠ 0 → e * w = z →
      e * w' = z → w = w' := fun he h1 h2 => mul_left_cancel₀ he (h1.trans h2.symm)
  have : FT0'.w j = w' j := key (A := FT'.TS.ring) he0 h1 (hw' j)
  rw [this, himg]

end FrameTransformLiftInner

section ResidueS1

attribute [local instance] RegularFrame.isDomain_S

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {F : RegularFrame R}
  {P : Ideal R} {T : MonoidalTransform R P}

/-- If `R₁` is residually rational over `R`, so is the monoidal transform `S₁` of `S`
(`S₁/N₁ = R₁/M₁` and `S/N = R/M`). -/
theorem RegularFrame.FrameTransform.isResiduallyRational_TS [IsLocalHom T.toRing]
    [IsRegularLocalRing T.ring] (FT : F.FrameTransform T)
    (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing) :
    haveI := FT.isRegular
    RingHom.IsResiduallyRational (R := F.S) (R' := FT.TS.ring) FT.TS.toRing := by
  have := FT.isRegular
  have := FT.canonical.isLocalHom
  intro c
  obtain ⟨c₀, rfl⟩ := IsLocalRing.residue_surjective c
  have hβ : Function.Bijective (ResidueField.map FT.β) :=
    FT.toRegularFrame.residueField_map_algebraMap_bijective
  have hF : Function.Bijective (ResidueField.map (algebraMap F.S R)) :=
    F.residueField_map_algebraMap_bijective
  obtain ⟨e, he⟩ := hrat (IsLocalRing.residue T.ring (FT.β c₀))
  obtain ⟨s, hs⟩ := hF.2 e
  obtain ⟨s₀, rfl⟩ := IsLocalRing.residue_surjective s
  refine ⟨IsLocalRing.residue F.S s₀, ?_⟩
  rw [ResidueField.map_residue]
  apply hβ.1
  rw [ResidueField.map_residue, ResidueField.map_residue]
  rw [← he, ← hs, ResidueField.map_residue, ResidueField.map_residue]
  congr 1
  exact (RingHom.congr_fun FT.canonical.comm s₀)

/-- **Coordinates for a frame transform** (p. 256, proof of Lemma 21: "We choose a regular system
of parameters of `R`, say `(z₁, …, z_r, x, x₁, …, x_t, y₁, …, y_s)`, such that `P ∩ S =
(x, x₁, …, x_t)S`, that `y_j ∈ S` for `1 ≤ j ≤ s`, and that `u_j = x_j/x ∈ M₁` for `1 ≤ j ≤ t`.
Then `(w₁, …, w_r, x, u₁, …, u_t, y₁, …, y_s)` is a regular system of parameters of `R₁`"), for a
residually rational `R₁`, `x` the denominator of the frame transform.  The regular systems of
parameters are given as families indexed by `Fin ((r + t) + (s + 1))` listing, in this order,
`z`, `x₁, …, x_t`, `x`, `y₁, …, y_s`.

This version also records that the `u_k` are images of elements `u'_k` of `S₁` and that
`(x, x₁, …, x_t, y₁, …, y_s)` generates the maximal ideal of `S` and `(x, u'_1, …, u'_t, y₁, …,
y_s)` that of `S₁` (the minimal base of `P ∩ S` and the regular systems of parameters of `S`, `S₁`
behind the choice of coordinates of p. 256; used for the two frames of Lemma 25, pp. 271–272). -/
theorem RegularFrame.FrameTransform.exists_coordinates_spans [P.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (FT : F.FrameTransform T)
    (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing) (x : F.S)
    (hxP : algebraMap F.S R x ∈ P) (h7' : FT.x = T.toRing (algebraMap F.S R x)) :
    ∃ (t s : ℕ) (xs : Fin t → F.S) (ys : Fin s → F.S) (u : Fin t → T.ring)
      (u' : Fin t → FT.TS.ring),
      (∀ k, u k = FT.β (u' k)) ∧
      Ideal.span ({x} ∪ Set.range xs ∪ Set.range ys : Set F.S) = maximalIdeal F.S ∧
      (haveI := FT.isRegular;
        Ideal.span ({FT.TS.toRing x} ∪ Set.range u' ∪ Set.range (fun l => FT.TS.toRing (ys l)) :
          Set FT.TS.ring) = maximalIdeal FT.TS.ring) ∧
      (∀ k, T.toRing (algebraMap F.S R (xs k)) = FT.x * u k) ∧
      Ideal.span (Set.range (Fin.append (Fin.append F.z (fun k => algebraMap F.S R (xs k)))
        (Fin.cons (algebraMap F.S R x) (fun l => algebraMap F.S R (ys l))) :
          Fin ((F.r + t) + (s + 1)) → R)) = maximalIdeal R ∧
      (((F.r + t) + (s + 1) : ℕ) : WithBot ℕ∞) = ringKrullDim R ∧
      Ideal.span (Set.range (Fin.append (Fin.append FT.w u)
        (Fin.cons FT.x (fun l => T.toRing (algebraMap F.S R (ys l)))) :
          Fin ((F.r + t) + (s + 1)) → T.ring)) = maximalIdeal T.ring ∧
      (((F.r + t) + (s + 1) : ℕ) : WithBot ℕ∞) = ringKrullDim T.ring ∧
      P = Ideal.span (Set.range (Fin.append F.z (fun k => algebraMap F.S R (xs k))) ∪
        {algebraMap F.S R x}) := by
  classical
  have hreg1 := FT.isRegular
  have hloc1 := FT.canonical.isLocalHom
  set Q : Ideal F.S := P.comap (algebraMap F.S R) with hQ
  have hQprime : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQreg : IsRegularLocalRing (F.S ⧸ Q) := FT.idealZ_le_and_unique.2.2.1
  have hxQ : x ∈ Q := hxP
  have hFTx0 : FT.x ≠ 0 := by
    intro h0
    have h1 : P.map T.toRing = ⊥ := by rw [← FT.span_x, h0, Ideal.span_singleton_eq_bot]
    exact T.x_ne_zero (T.toRing_injective ((Ideal.mem_bot.mp
      (h1 ▸ Ideal.mem_map_of_mem T.toRing T.x_mem)).trans (map_zero _).symm))
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hFTx0 (by rw [h7']; simp)
  have hQ0 : Q ≠ ⊥ := fun h => hx0 (by simpa [h] using hxQ)
  have hratS := FT.isResiduallyRational_TS hrat
  obtain ⟨t, s, x₀, xs₀, ys, hrsop, hcard, hQeq, x', hx', hrsop₁⟩ :=
    MonoidalTransform.exists_rsop_of_isResiduallyRational FT.TS hQprime hQ0 hQreg hratS
  set τ : F.S →+* FT.TS.ring := FT.TS.toRing with hτ
  have hβτ : ∀ a : F.S, FT.β (τ a) = T.toRing (algebraMap F.S R a) := fun a =>
    RingHom.congr_fun FT.canonical.comm a
  -- the maximal ideal of `S₁` and of `S`
  have hN₁ : Ideal.span ((({τ x₀} ∪ Finset.image x' Finset.univ ∪
      Finset.image (fun j => τ (ys j)) Finset.univ : Finset FT.TS.ring)) : Set FT.TS.ring) =
        maximalIdeal FT.TS.ring := hrsop₁.1
  have hN : Ideal.span ((({x₀} ∪ Finset.image xs₀ Finset.univ ∪ Finset.image ys Finset.univ :
      Finset F.S)) : Set F.S) = maximalIdeal F.S := hrsop.1
  have hx'M : ∀ k, x' k ∈ maximalIdeal FT.TS.ring := fun k => by
    rw [← hN₁]; exact Ideal.subset_span (by simp)
  have hQeq' : Q = Ideal.span ({x₀} ∪ Set.range xs₀) := hQeq
  have hx₀Q : x₀ ∈ Q := by
    rw [hQeq']; exact Ideal.subset_span (by simp)
  have hxsQ : ∀ k, xs₀ k ∈ Q := fun k => by
    rw [hQeq']; exact Ideal.subset_span (by simp)
  have hQ' : Q = Ideal.span (Set.range (Fin.cons x₀ xs₀ : Fin (t + 1) → F.S)) := by
    rw [hQeq', span_range_cons, ← Ideal.span_union]
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp (hQ' ▸ hxQ)
  rw [Fin.sum_univ_succ] at hc
  simp only [Fin.cons_zero, Fin.cons_succ] at hc
  -- `x = a x₀ + Σ b_k xs₀_k`
  set a : F.S := c 0 with ha
  set b : Fin t → F.S := fun k => c k.succ with hb
  set σ : FT.TS.ring := τ a + ∑ k, τ (b k) * x' k with hσ
  have hτx : τ x = τ x₀ * σ := by
    rw [← hc, map_add, map_sum, hσ, mul_add, Finset.mul_sum]
    congr 1
    · rw [map_mul]; ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, ← hx' k]; ring
  have hτx₀P : T.toRing (algebraMap F.S R x₀) ∈ P.map T.toRing :=
    Ideal.mem_map_of_mem _ hx₀Q
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp (FT.span_x ▸ hτx₀P)
  have hσunit : IsUnit σ := by
    refine isUnit_of_map_unit FT.β _ ?_
    have h1 : FT.x = FT.x * (e * FT.β σ) := by
      calc FT.x = T.toRing (algebraMap F.S R x) := h7'
        _ = FT.β (τ x) := (hβτ x).symm
        _ = FT.β (τ x₀) * FT.β σ := by rw [hτx, map_mul]
        _ = T.toRing (algebraMap F.S R x₀) * FT.β σ := by rw [hβτ]
        _ = FT.x * (e * FT.β σ) := by rw [← he]; ring
    have h2 : e * FT.β σ = 1 := mul_left_cancel₀ hFTx0 (h1.symm.trans (mul_one _).symm)
    exact isUnit_iff_exists_inv.mpr ⟨e, by rw [mul_comm]; exact h2⟩
  have haunit : IsUnit a := by
    refine isUnit_of_map_unit τ _ ?_
    by_contra hna
    have h1 : τ a ∈ maximalIdeal FT.TS.ring := hna
    have h2 : σ ∈ maximalIdeal FT.TS.ring :=
      add_mem h1 (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hx'M k))
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 hσunit
  obtain ⟨σi, hσi⟩ := hσunit.exists_right_inv
  obtain ⟨ai, hai⟩ := haunit.exists_right_inv
  have hσi' : σi * σ = 1 := by rw [mul_comm]; exact hσi
  have hai' : ai * a = 1 := by rw [mul_comm]; exact hai
  have hc' : a * x₀ + ∑ k, b k * xs₀ k = x := hc
  have hx₀rel : x₀ = ai * x - ∑ k, (ai * b k) * xs₀ k := by
    have : ai * x = x₀ + ∑ k, (ai * b k) * xs₀ k := by
      rw [← hc', mul_add, ← mul_assoc, hai', one_mul, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this]; ring
  have hτx₀ : τ x₀ = τ x * σi := by
    calc τ x₀ = τ x₀ * (σ * σi) := by rw [hσi, mul_one]
      _ = τ x * σi := by rw [hτx]; ring
  have hx'σ : ∀ k, x' k = σ * (σi * x' k) := fun k => by
    rw [← mul_assoc, hσi, one_mul]
  -- dimension of `S` and of `S₁`
  have hdimS : ringKrullDim F.S = ((t + 1 + s : ℕ) : WithBot ℕ∞) := by
    rw [← hrsop.2, hcard]
  have hresalg : RingHom.IsResiduallyAlgebraic (R := F.S) (R' := FT.TS.ring) FT.TS.toRing :=
    RingHom.isResiduallyAlgebraic_of_isResiduallyRational _ hratS
  have hdimS₁ : ringKrullDim FT.TS.ring = ringKrullDim F.S :=
    (FT.TS.ringKrullDim_eq_iff hQprime hQ0 hQreg).mpr hresalg
  -- `S`-side spans in `R`
  have hxQ' : algebraMap F.S R x₀ ∈ Ideal.span ({algebraMap F.S R x} ∪
      Set.range (fun k => algebraMap F.S R (xs₀ k)) : Set R) := by
    rw [hx₀rel, map_sub, map_mul, map_sum]
    refine sub_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inl rfl))) ?_
    exact Ideal.sum_mem _ fun k _ => by
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inr ⟨k, rfl⟩))
  refine ⟨t, s, xs₀, ys, fun k => FT.β (σi * x' k), fun k => σi * x' k, fun k => rfl, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `(x, x₁, …, x_t, y₁, …, y_s)` generates the maximal ideal of `S`
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro _ ((rfl | ⟨k, rfl⟩) | ⟨l, rfl⟩)
      · exact le_maximalIdeal (Ideal.IsPrime.ne_top hQprime) hxQ
      · rw [← hN]; exact Ideal.subset_span (by simp)
      · rw [← hN]; exact Ideal.subset_span (by simp)
    · rw [← hN]
      refine Ideal.span_le.mpr ?_
      intro y hy
      simp only [Finset.coe_union, Finset.coe_singleton, Finset.coe_image, Finset.coe_univ,
        Set.image_univ, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hy
      rcases hy with (rfl | ⟨k, rfl⟩) | ⟨l, rfl⟩
      · rw [hx₀rel]
        refine sub_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inl (Or.inl rfl))))
          (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ?_)
        exact Ideal.subset_span (Or.inl (Or.inr ⟨k, rfl⟩))
      · exact Ideal.subset_span (Or.inl (Or.inr ⟨k, rfl⟩))
      · exact Ideal.subset_span (Or.inr ⟨l, rfl⟩)
  · -- `(x, u'_1, …, u'_t, y₁, …, y_s)` generates the maximal ideal of `S₁`
    have hτx₀N' : τ x₀ ∈ maximalIdeal FT.TS.ring := by
      rw [← hN₁]; exact Ideal.subset_span (by simp)
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro _ ((rfl | ⟨k, rfl⟩) | ⟨l, rfl⟩)
      · rw [hτx]; exact Ideal.mul_mem_right _ _ hτx₀N'
      · exact Ideal.mul_mem_left _ _ (hx'M k)
      · rw [← hN₁]; exact Ideal.subset_span (by simp)
    · rw [← hN₁]
      refine Ideal.span_le.mpr ?_
      intro y hy
      simp only [Finset.coe_union, Finset.coe_singleton, Finset.coe_image, Finset.coe_univ,
        Set.image_univ, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hy
      rcases hy with (rfl | ⟨k, rfl⟩) | ⟨l, rfl⟩
      · rw [hτx₀]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inl (Or.inl rfl)))
      · rw [hx'σ k]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inl (Or.inr ⟨k, rfl⟩)))
      · exact Ideal.subset_span (Or.inr ⟨l, rfl⟩)
  · intro k
    calc T.toRing (algebraMap F.S R (xs₀ k)) = FT.β (τ (xs₀ k)) := (hβτ _).symm
      _ = FT.β (τ x₀ * x' k) := by rw [hx']
      _ = FT.β (τ x * (σi * x' k)) := by
        congr 1
        rw [hτx]
        calc τ x₀ * x' k = τ x₀ * (σ * σi) * x' k := by rw [hσi, mul_one]
          _ = τ x₀ * σ * (σi * x' k) := by ring
      _ = FT.x * FT.β (σi * x' k) := by rw [map_mul, h7', hβτ]
  · -- the regular system of parameters of `R`
    rw [span_range_append, span_range_append, span_range_cons,
      F.maximalIdeal_eq_idealZ_sup_map]
    have hmemT : ∀ y ∈ (({x₀} ∪ Finset.image xs₀ Finset.univ ∪ Finset.image ys Finset.univ :
        Finset F.S) : Set F.S), algebraMap F.S R y ∈ Ideal.span (Set.range F.z) ⊔
          Ideal.span (Set.range fun k => algebraMap F.S R (xs₀ k)) ⊔
          (Ideal.span {algebraMap F.S R x} ⊔
            Ideal.span (Set.range fun l => algebraMap F.S R (ys l))) := by
      intro y hy
      simp only [Finset.coe_union, Finset.coe_singleton, Finset.coe_image, Finset.coe_univ,
        Set.image_univ, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hy
      rcases hy with (rfl | ⟨k, rfl⟩) | ⟨l, rfl⟩
      · have h := hxQ'
        rw [Ideal.span_union] at h
        obtain ⟨u1, hu1, u2, hu2, hsum⟩ := Submodule.mem_sup.mp h
        rw [← hsum]
        exact add_mem (Ideal.mem_sup_right (Ideal.mem_sup_left hu1))
          (Ideal.mem_sup_left (Ideal.mem_sup_right hu2))
      · exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
      · exact Ideal.mem_sup_right (Ideal.mem_sup_right (Ideal.subset_span ⟨l, rfl⟩))
    apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
      · exact le_sup_left
      · refine Ideal.span_le.mpr ?_
        rintro _ ⟨k, rfl⟩
        refine Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ?_)
        rw [← hN]; exact Ideal.subset_span (by simp)
      · refine Ideal.span_le.mpr ?_
        rintro _ rfl
        refine Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ?_)
        exact le_maximalIdeal (Ideal.IsPrime.ne_top hQprime) hxQ
      · refine Ideal.span_le.mpr ?_
        rintro _ ⟨l, rfl⟩
        refine Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ?_)
        rw [← hN]; exact Ideal.subset_span (by simp)
    · refine sup_le ?_ ?_
      · exact (le_sup_left.trans le_sup_left)
      · rw [← hN, Ideal.map_span]
        exact Ideal.span_le.mpr (by rintro _ ⟨y, hy, rfl⟩; exact hmemT y hy)
  · rw [F.ringKrullDim_eq_add, hdimS, ← Nat.cast_add]
    exact congrArg _ (by omega)
  · -- the regular system of parameters of `R₁`
    rw [span_range_append, span_range_append, span_range_cons]
    have hM1 : maximalIdeal T.ring = Ideal.span (Set.range FT.w) ⊔
        (maximalIdeal FT.TS.ring).map FT.β := FT.toRegularFrame.maximalIdeal_eq_idealZ_sup_map
    rw [hM1]
    have hτx₀N : τ x₀ ∈ maximalIdeal FT.TS.ring := by
      rw [← hN₁]; exact Ideal.subset_span (by simp)
    have hysN : ∀ l, τ (ys l) ∈ maximalIdeal FT.TS.ring := fun l => by
      rw [← hN₁]; exact Ideal.subset_span (by simp)
    have hFTx : FT.x = FT.β (τ x) := by rw [h7', hβτ]
    apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
      · exact le_sup_left
      · refine Ideal.span_le.mpr ?_
        rintro _ ⟨k, rfl⟩
        exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ (hx'M k)))
      · refine Ideal.span_le.mpr ?_
        rintro _ rfl
        refine Ideal.mem_sup_right ?_
        rw [hFTx]
        exact Ideal.mem_map_of_mem _ (by rw [hτx]; exact Ideal.mul_mem_right _ _ hτx₀N)
      · refine Ideal.span_le.mpr ?_
        rintro _ ⟨l, rfl⟩
        refine Ideal.mem_sup_right ?_
        show T.toRing (algebraMap F.S R (ys l)) ∈ _
        rw [← hβτ]
        exact Ideal.mem_map_of_mem _ (hysN l)
    · refine sup_le (le_sup_left.trans le_sup_left) ?_
      rw [← hN₁, Ideal.map_span]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨y, hy, rfl⟩
      simp only [Finset.coe_union, Finset.coe_singleton, Finset.coe_image, Finset.coe_univ,
        Set.image_univ, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hy
      rcases hy with (rfl | ⟨k, rfl⟩) | ⟨l, rfl⟩
      · -- `β(τ x₀) = FT.x · β σi`
        refine Ideal.mem_sup_right (Ideal.mem_sup_left ?_)
        rw [hτx₀, map_mul, ← hFTx]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      · refine Ideal.mem_sup_left (Ideal.mem_sup_right ?_)
        rw [hx'σ k, map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
      · refine Ideal.mem_sup_right (Ideal.mem_sup_right ?_)
        rw [hβτ]
        exact Ideal.subset_span ⟨l, rfl⟩
  · rw [FT.toRegularFrame.ringKrullDim_eq_add]
    show _ = (F.r : WithBot ℕ∞) + ringKrullDim FT.TS.ring
    rw [hdimS₁, hdimS, ← Nat.cast_add]
    exact congrArg _ (by omega)
  · -- `P = (z, x₁, …, x_t, x)R`
    have hzP : F.idealZ ≤ P := FT.idealZ_le_and_unique.2.1
    apply le_antisymm
    · intro p hp
      have hp1 := F.sub_algebraMap_retraction_mem p
      have hret : F.retraction p ∈ Q := F.retraction_mem_comap hzP hp
      have hmap : algebraMap F.S R (F.retraction p) ∈ Ideal.span
          (Set.range (Fin.append F.z (fun k => algebraMap F.S R (xs₀ k))) ∪
            {algebraMap F.S R x}) := by
        have h1 : Q.map (algebraMap F.S R) ≤ Ideal.span
            (Set.range (Fin.append F.z (fun k => algebraMap F.S R (xs₀ k))) ∪
              {algebraMap F.S R x}) := by
          rw [hQeq', Ideal.map_span]
          refine Ideal.span_le.mpr ?_
          rintro _ ⟨y, hy, rfl⟩
          rcases hy with rfl | ⟨k, rfl⟩
          · refine (Ideal.span_mono ?_) hxQ'
            rintro _ (rfl | ⟨k, rfl⟩)
            · exact Or.inr rfl
            · exact Or.inl ⟨Fin.natAdd F.r k, by simp⟩
          · exact Ideal.subset_span (Or.inl ⟨Fin.natAdd F.r k, by simp⟩)
        exact h1 (Ideal.mem_map_of_mem _ hret)
      have : p = (p - algebraMap F.S R (F.retraction p)) + algebraMap F.S R (F.retraction p) := by
        ring
      rw [this]
      refine add_mem ?_ hmap
      have : p - algebraMap F.S R (F.retraction p) ∈ F.idealZ := hp1
      refine (Ideal.span_mono ?_ : F.idealZ ≤ _) this
      rintro _ ⟨j, rfl⟩
      exact Or.inl ⟨Fin.castAdd _ j, by simp⟩
    · refine Ideal.span_le.mpr ?_
      rintro _ (⟨i, rfl⟩ | rfl)
      · refine Fin.addCases (fun j => ?_) (fun k => ?_) i
        · simp only [Fin.append_left]; exact hzP (Ideal.subset_span ⟨j, rfl⟩)
        · simp only [Fin.append_right]; exact hxsQ k
      · exact hxP

/-- **Coordinates for a frame transform** (p. 256, proof of Lemma 21: "We choose a regular system
of parameters of `R`, say `(z₁, …, z_r, x, x₁, …, x_t, y₁, …, y_s)`, such that `P ∩ S =
(x, x₁, …, x_t)S`, that `y_j ∈ S` for `1 ≤ j ≤ s`, and that `u_j = x_j/x ∈ M₁` for `1 ≤ j ≤ t`.
Then `(w₁, …, w_r, x, u₁, …, u_t, y₁, …, y_s)` is a regular system of parameters of `R₁`"), for a
residually rational `R₁`, `x` the denominator of the frame transform.  The regular systems of
parameters are given as families indexed by `Fin ((r + t) + (s + 1))` listing, in this order,
`z`, `x₁, …, x_t`, `x`, `y₁, …, y_s`. -/
theorem RegularFrame.FrameTransform.exists_coordinates [P.IsPrime] [IsRegularLocalRing (R ⧸ P)]
    [IsLocalHom T.toRing] [IsRegularLocalRing T.ring] (FT : F.FrameTransform T)
    (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing) (x : F.S)
    (hxP : algebraMap F.S R x ∈ P) (h7' : FT.x = T.toRing (algebraMap F.S R x)) :
    ∃ (t s : ℕ) (xs : Fin t → F.S) (ys : Fin s → F.S) (u : Fin t → T.ring),
      (∀ k, T.toRing (algebraMap F.S R (xs k)) = FT.x * u k) ∧
      Ideal.span (Set.range (Fin.append (Fin.append F.z (fun k => algebraMap F.S R (xs k)))
        (Fin.cons (algebraMap F.S R x) (fun l => algebraMap F.S R (ys l))) :
          Fin ((F.r + t) + (s + 1)) → R)) = maximalIdeal R ∧
      (((F.r + t) + (s + 1) : ℕ) : WithBot ℕ∞) = ringKrullDim R ∧
      Ideal.span (Set.range (Fin.append (Fin.append FT.w u)
        (Fin.cons FT.x (fun l => T.toRing (algebraMap F.S R (ys l)))) :
          Fin ((F.r + t) + (s + 1)) → T.ring)) = maximalIdeal T.ring ∧
      (((F.r + t) + (s + 1) : ℕ) : WithBot ℕ∞) = ringKrullDim T.ring ∧
      P = Ideal.span (Set.range (Fin.append F.z (fun k => algebraMap F.S R (xs k))) ∪
        {algebraMap F.S R x}) := by
  obtain ⟨t, s, xs, ys, u, -, -, -, -, h1, h2, h3, h4, h5, h6⟩ :=
    FT.exists_coordinates_spans hrat x hxP h7'
  exact ⟨t, s, xs, ys, u, h1, h2, h3, h4, h5, h6⟩

end ResidueS1

section CoordGlue

open scoped Classical

attribute [local instance] RegularFrame.isDomain_S

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {F : RegularFrame R}
  {P : Ideal R} {T : MonoidalTransform R P}

/-- The regular system of parameters `(z, x₁, …, x_t, x, y₁, …, y_s)` of `R`. -/
noncomputable def coordV (x : F.S) {t s : ℕ} (xs : Fin t → F.S) (ys : Fin s → F.S) :
    Fin ((F.r + t) + (s + 1)) → R :=
  Fin.append (Fin.append F.z (fun k => algebraMap F.S R (xs k)))
    (Fin.cons (algebraMap F.S R x) (fun l => algebraMap F.S R (ys l)))

/-- The regular system of parameters `(w, u₁, …, u_t, x, y₁, …, y_s)` of `R₁`. -/
noncomputable def coordV₁ (FT : F.FrameTransform T) {t s : ℕ} (ys : Fin s → F.S)
    (u : Fin t → T.ring) : Fin ((F.r + t) + (s + 1)) → T.ring :=
  Fin.append (Fin.append FT.w u)
    (Fin.cons FT.x (fun l => T.toRing (algebraMap F.S R (ys l))))

theorem coordV₁_natAdd_zero (FT : F.FrameTransform T) {t s : ℕ} (ys : Fin s → F.S)
    (u : Fin t → T.ring) :
    coordV₁ FT ys u ⟨F.r + t, by omega⟩ = FT.x := by
  have : (⟨F.r + t, by omega⟩ : Fin ((F.r + t) + (s + 1))) = Fin.natAdd (F.r + t) 0 :=
    Fin.ext rfl
  rw [this, coordV₁, Fin.append_right, Fin.cons_zero]

theorem toRing_coordV_lt (FT : F.FrameTransform T) {t s : ℕ} (x : F.S) (xs : Fin t → F.S)
    (ys : Fin s → F.S) (u : Fin t → T.ring)
    (hxs : ∀ k, T.toRing (algebraMap F.S R (xs k)) = FT.x * u k)
    (i : Fin ((F.r + t) + (s + 1))) (hi : i.val < F.r + t) :
    T.toRing (coordV x xs ys i) = FT.x * coordV₁ FT ys u i := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin (F.r + t), i = Fin.castAdd (s + 1) j := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  refine Fin.addCases (fun a => ?_) (fun k => ?_) j
  · simp only [coordV, coordV₁, Fin.append_left]
    exact (FT.mul_w a).symm
  · simp only [coordV, coordV₁, Fin.append_left, Fin.append_right]
    exact hxs k

theorem toRing_coordV_x (FT : F.FrameTransform T) {t s : ℕ} (x : F.S) (xs : Fin t → F.S)
    (ys : Fin s → F.S) (u : Fin t → T.ring) (h7' : FT.x = T.toRing (algebraMap F.S R x)) :
    T.toRing (coordV x xs ys ⟨F.r + t, by omega⟩) = coordV₁ FT ys u ⟨F.r + t, by omega⟩ := by
  have : (⟨F.r + t, by omega⟩ : Fin ((F.r + t) + (s + 1))) = Fin.natAdd (F.r + t) 0 :=
    Fin.ext rfl
  rw [coordV₁_natAdd_zero, this, coordV, Fin.append_right, Fin.cons_zero, h7']

theorem toRing_coordV_gt (FT : F.FrameTransform T) {t s : ℕ} (x : F.S) (xs : Fin t → F.S)
    (ys : Fin s → F.S) (u : Fin t → T.ring) (i : Fin ((F.r + t) + (s + 1)))
    (hi : F.r + t < i.val) :
    T.toRing (coordV x xs ys i) = coordV₁ FT ys u i := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin (s + 1), i = Fin.natAdd (F.r + t) j :=
    ⟨⟨i.val - (F.r + t), by omega⟩, Fin.ext (by simp; omega)⟩
  induction j using Fin.cases with
  | zero => exfalso; simp at hi
  | succ l => simp [coordV, coordV₁]

/-- **Lemma K for the regular system of parameters `(w, u, x, y)` of `R₁`** (the ideal
`(x, y)R₁`): every element of `(x, y)R₁ ∩ M₁^k` is `Σ v_i d_i` with `d_i ∈ M₁^{k-1}`. -/
theorem coordV₁_lemmaK (FT : F.FrameTransform T) [IsLocalHom T.toRing]
    [IsRegularLocalRing T.ring] {t s : ℕ} (ys : Fin s → F.S) (u : Fin t → T.ring)
    (hspan₁ : Ideal.span (Set.range (coordV₁ FT ys u)) = maximalIdeal T.ring)
    (hdim₁ : (((F.r + t) + (s + 1) : ℕ) : WithBot ℕ∞) = ringKrullDim T.ring) :
    ∀ a ∈ Ideal.span (coordV₁ FT ys u '' {i : Fin ((F.r + t) + (s + 1)) | ¬ i.val < F.r + t}),
      ∀ k : ℕ, a ∈ maximalIdeal T.ring ^ k →
      ∃ d : Fin ((F.r + t) + (s + 1)) → T.ring, (∀ i, d i ∈ maximalIdeal T.ring ^ (k - 1)) ∧
        a = ∑ i, (if i ∈ {i : Fin ((F.r + t) + (s + 1)) | i.val < F.r + t} then 0
          else coordV₁ FT ys u i * d i) := by
  intro a ha k hak
  set v := coordV₁ FT ys u with hv
  set Z : Finset T.ring := Finset.univ.image v with hZdef
  have hspanN : (maximalIdeal T.ring).spanFinrank = (F.r + t) + (s + 1) := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := T.ring)
    rw [← hdim₁] at h
    exact_mod_cast h
  have hZ : IsRegularSystemOfParameters T.ring Z := by
    refine rsop_of_span_of_card_le ?_ ?_
    · rw [hZdef, Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact hspan₁
    · rw [hspanN]
      calc Z.card ≤ (Finset.univ : Finset (Fin ((F.r + t) + (s + 1)))).card :=
            Finset.card_image_le
        _ = _ := by simp
  have hZcard : Z.card = (F.r + t) + (s + 1) := by
    rw [rsop_card_eq_spanFinrank hZ, hspanN]
  have hvinj : Function.Injective v := by
    have := Finset.card_image_iff.mp (by rw [hZcard]; simp : (Finset.univ.image v).card =
      (Finset.univ : Finset (Fin ((F.r + t) + (s + 1)))).card)
    exact fun a b hab => this (Finset.mem_coe.mpr (Finset.mem_univ a))
      (Finset.mem_coe.mpr (Finset.mem_univ b)) hab
  set z : Fin (s + 1) → T.ring := fun j => v (Fin.natAdd (F.r + t) j) with hz
  have hzinj : Function.Injective z := hvinj.comp (Fin.natAdd_injective _ _)
  have hext : ExtendsToRSOP T.ring (Finset.image z Finset.univ) := by
    refine (ExtendsToRSOP.of_isRegularSystemOfParameters hZ).mono ?_
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have hPreg : IsRegularLocalRing (T.ring ⧸ maximalIdeal T.ring) := by
    let _ := Ideal.Quotient.field (maximalIdeal T.ring)
    infer_instance
  have hzP : ∀ i, z i ∈ maximalIdeal T.ring := fun i => by
    rw [← hspan₁]; exact Ideal.subset_span ⟨_, rfl⟩
  have hset : coordV₁ FT ys u '' {i : Fin ((F.r + t) + (s + 1)) | ¬ i.val < F.r + t} =
      ((Finset.univ.image z : Finset T.ring) : Set T.ring) := by
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i.val - (F.r + t), by omega⟩, by simp [hz, hv]; congr 1; ext; simp; omega⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Fin.natAdd (F.r + t) j, by simp, rfl⟩
  have haK : a ∈ Ideal.span ((Finset.univ.image z : Finset T.ring) : Set T.ring) := hset ▸ ha
  have : (maximalIdeal T.ring).IsPrime := (maximalIdeal.isMaximal T.ring).isPrime
  obtain ⟨d, hd, had⟩ := exists_eq_sum_mul_of_mem_span_of_mem_pow hzinj hext hPreg hzP Finset.univ
    haK hak
  refine ⟨Fin.addCases (fun _ => 0) d, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simpa using hd j
  · calc a = ∑ j : Fin (s + 1), z j * d j := by simpa using had
      _ = _ := by
        conv_rhs => rw [Fin.sum_univ_add]
        simp [hz]

end CoordGlue

section CoreInstantiate

open MvPolynomial
open scoped Classical

attribute [local instance] RegularFrame.isDomain_S
attribute [local instance] Ideal.Quotient.field

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {F : RegularFrame R}
  {P : Ideal R} {T : MonoidalTransform R P}

omit [IsDomain R] in
/-- The set of the first `r + t + 1` regular parameters is the generating set of `P`. -/
theorem coordV_image_le_eq (x : F.S) {t s : ℕ} (xs : Fin t → F.S) (ys : Fin s → F.S) :
    coordV x xs ys '' {i : Fin ((F.r + t) + (s + 1)) | i.val ≤ F.r + t} =
      Set.range (Fin.append F.z (fun k => algebraMap F.S R (xs k))) ∪ {algebraMap F.S R x} := by
  ext y
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases hlt : i.val < F.r + t
    · left
      obtain ⟨j, rfl⟩ : ∃ j : Fin (F.r + t), i = Fin.castAdd (s + 1) j :=
        ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
      exact ⟨j, by rw [coordV, Fin.append_left]⟩
    · right
      obtain ⟨j, rfl⟩ : ∃ j : Fin (s + 1), i = Fin.natAdd (F.r + t) j :=
        ⟨⟨i.val - (F.r + t), by have := i.2; omega⟩, Fin.ext (by
          simp only [Set.mem_ofPred_eq] at hi; simp; omega)⟩
      have hj : j = 0 := Fin.ext (by
        simp only [Set.mem_ofPred_eq] at hi; simp at hi; simp; omega)
      subst hj
      rw [coordV, Fin.append_right, Fin.cons_zero]
      rfl
  · rintro (⟨j, rfl⟩ | h)
    · refine ⟨Fin.castAdd (s + 1) j, ?_, ?_⟩
      · show (j : ℕ) ≤ F.r + t
        have := j.2
        omega
      · rw [coordV, Fin.append_left]
    · rw [Set.mem_singleton_iff] at h
      subst h
      refine ⟨Fin.natAdd (F.r + t) 0, ?_, ?_⟩
      · show F.r + t + 0 ≤ F.r + t
        omega
      · rw [coordV, Fin.append_right, Fin.cons_zero]

/-- A residually rational local homomorphism induces an isomorphism of the residue fields. -/
theorem exists_residueEquiv [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing) :
    ∃ ρ : T.ring ⧸ maximalIdeal T.ring ≃+* R ⧸ maximalIdeal R,
      (ρ.symm : R ⧸ maximalIdeal R →+* T.ring ⧸ maximalIdeal T.ring) =
        quotientMaximalIdealMap T.toRing := by
  have hbij : Function.Bijective (quotientMaximalIdealMap T.toRing) := by
    refine ⟨quotientMaximalIdealMap_injective T.toRing, fun c => ?_⟩
    obtain ⟨e, he⟩ := hrat c
    obtain ⟨e₀, rfl⟩ := IsLocalRing.residue_surjective e
    refine ⟨Ideal.Quotient.mk _ e₀, ?_⟩
    rw [quotientMaximalIdealMap_mk, ← he, ResidueField.map_residue]
    rfl
  exact ⟨(RingEquiv.ofBijective (quotientMaximalIdealMap T.toRing) hbij).symm,
    RingHom.ext fun c => rfl⟩

/-- **The comparison of the initial forms of `f` and `x^{-μ} f` in the polynomial pictures given
by coordinates** `(z, x_k, x, y)` of `R` and `(w, u, x, y)` of `R₁` (p. 256: "the initial forms of
`f_{i+j}` are contained in `k[Z₁, …, Z_r, X₁, …, X_t]`"; p. 257: "`ψ = φ(W, U) + λ`, `λ ∈ (X, Y)
gr`"): see `forms_correspond`. -/
theorem forms_of_coordinates [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing]
    [IsRegularLocalRing T.ring] (FT : F.FrameTransform T) (x : F.S)
    (h7' : FT.x = T.toRing (algebraMap F.S R x)) (hx0 : FT.x ≠ 0) {t' s : ℕ}
    (xs : Fin t' → F.S) (ys : Fin s → F.S) (u : Fin t' → T.ring)
    (hxs : ∀ k, T.toRing (algebraMap F.S R (xs k)) = FT.x * u k)
    (hspan : Ideal.span (Set.range (coordV x xs ys)) = maximalIdeal R)
    (hdim : (((F.r + t') + (s + 1) : ℕ) : WithBot ℕ∞) = ringKrullDim R)
    (hspan₁ : Ideal.span (Set.range (coordV₁ FT ys u)) = maximalIdeal T.ring)
    (hdim₁ : (((F.r + t') + (s + 1) : ℕ) : WithBot ℕ∞) = ringKrullDim T.ring)
    (hPeq : P = Ideal.span (Set.range (Fin.append F.z (fun k => algebraMap F.S R (xs k))) ∪
      {algebraMap F.S R x}))
    (ρ : T.ring ⧸ maximalIdeal T.ring ≃+* R ⧸ maximalIdeal R)
    (hρ : (ρ.symm : R ⧸ maximalIdeal R →+* T.ring ⧸ maximalIdeal T.ring) =
      quotientMaximalIdealMap T.toRing) :
    ∀ (μ : ℕ) (f : R) (g : T.ring), f ∈ P ^ μ → Ideal.ordElem (maximalIdeal R) f = μ →
      Ideal.ordElem (maximalIdeal T.ring) g = μ → FT.x ^ μ * g = T.toRing f →
      (gradedSemiModel ρ (coordV x xs ys) hspan hdim).Φ.symm (initialForm (maximalIdeal R) f) ∈
          supported (T.ring ⧸ maximalIdeal T.ring)
            {i : Fin ((F.r + t') + (s + 1)) | i.val < F.r + t'} ∧
        (gradedSemiModel (RingEquiv.refl (T.ring ⧸ maximalIdeal T.ring)) (coordV₁ FT ys u)
            hspan₁ hdim₁).Φ.symm (initialForm (maximalIdeal T.ring) g) -
          (gradedSemiModel ρ (coordV x xs ys) hspan hdim).Φ.symm
            (initialForm (maximalIdeal R) f) ∈
          outIdeal (K := T.ring ⧸ maximalIdeal T.ring)
            {i : Fin ((F.r + t') + (s + 1)) | i.val < F.r + t'} := by
  classical
  have hdom1 : IsDomain T.ring := Transforms.isDomain_of_isRegularLocalRing _
  intro μ f g hfP hford hgord hgrel
  have hfM : f ∈ maximalIdeal R ^ μ := Ideal.mem_pow_of_ordElem hford
  have hgM : g ∈ maximalIdeal T.ring ^ μ := Ideal.mem_pow_of_ordElem hgord
  have hfP' : f ∈ Ideal.span (coordV x xs ys ''
      {i : Fin ((F.r + t') + (s + 1)) | i.val ≤ F.r + t'}) ^ μ := by
    rw [coordV_image_le_eq, ← hPeq]
    exact hfP
  have hform := forms_correspond T.toRing (coordV x xs ys) (coordV₁ FT ys u) hspan hdim
    hspan₁ hdim₁ FT.x hx0 (coordV₁_natAdd_zero FT ys u) (toRing_coordV_lt FT x xs ys u hxs)
    ((toRing_coordV_x FT x xs ys u h7').trans (coordV₁_natAdd_zero FT ys u))
    (toRing_coordV_gt FT x xs ys u) (coordV₁_lemmaK FT ys u hspan₁ hdim₁) hfP' hfM hgrel hgM
  have hsymm : (gradedSemiModel ρ (coordV x xs ys) hspan hdim).Φ.symm
      (initialForm (maximalIdeal R) f) =
      MvPolynomial.map (quotientMaximalIdealMap T.toRing)
        ((gradedModel (coordV x xs ys) hspan hdim).symm
          (AssocGraded.mk (maximalIdeal R) μ f hfM)) := by
    rw [gradedSemiModel_symm, hρ, initialForm_eq_mk _ hford]
  have hsymm₁ : (gradedSemiModel (RingEquiv.refl (T.ring ⧸ maximalIdeal T.ring))
      (coordV₁ FT ys u) hspan₁ hdim₁).Φ.symm (initialForm (maximalIdeal T.ring) g) =
      (gradedModel (coordV₁ FT ys u) hspan₁ hdim₁).symm
        (AssocGraded.mk (maximalIdeal T.ring) μ g hgM) := by
    rw [gradedSemiModel_symm, initialForm_eq_mk _ hgord]
    have : ((RingEquiv.refl (T.ring ⧸ maximalIdeal T.ring)).symm :
        T.ring ⧸ maximalIdeal T.ring →+* T.ring ⧸ maximalIdeal T.ring) = RingHom.id _ := rfl
    rw [this, MvPolynomial.map_id]
  refine ⟨?_, ?_⟩
  · rw [hsymm]
    exact map_mem_supported_of_mem _ hform.1
  · rw [hsymm₁, hsymm]
    exact hform.2

/-- **The polynomial pictures of `gr_M(R)` and `gr_{M₁}(R₁)` with the indices of `Z_l`, `W_l`**
(p. 256: the coordinates `(z, x_k, x, y)` of `R`, `(w, u, x, y)` of `R₁`, and the identifications
`gr_M(R) = k[Z, X, Y]`, `gr_{M₁}(R₁) = k[W, U, X, Y]`; `R₁` residually rational, so `k = k₁` is
used as the common field): two semilinear models over `K = R₁/M₁` in which the variable `X_{zI l}`
goes to `Z_l` resp. `W_l`, the set `U` of the variables `Z, X_1, …, X_t`, with the comparison of
the initial forms of `f` and `x^{-μ} f` (`forms_correspond`; p. 255: "`ψ_j = φ_j(W₁, …, W_r) +
λ_j`, `λ_j ∈ (X, Y) gr`, see the proof of Lemma 14 of §5"). -/
theorem exists_models_zI [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing]
    [IsRegularLocalRing T.ring] (FT : F.FrameTransform T)
    (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing) (x : F.S)
    (hxP : algebraMap F.S R x ∈ P) (h7' : FT.x = T.toRing (algebraMap F.S R x))
    (hx0 : FT.x ≠ 0) :
    ∃ (n : ℕ) (M : SemiModel (T.ring ⧸ maximalIdeal T.ring) (R ⧸ maximalIdeal R)
        (AssocGraded (maximalIdeal R)) n)
      (M₁ : SemiModel (T.ring ⧸ maximalIdeal T.ring) (T.ring ⧸ maximalIdeal T.ring)
        (AssocGraded (maximalIdeal T.ring)) n) (zI : Fin F.r → Fin n) (U : Set (Fin n)),
      (∀ (d : ℕ) (p : MvPolynomial (Fin n) (T.ring ⧸ maximalIdeal T.ring)),
        p ∈ homogeneousSubmodule (Fin n) (T.ring ⧸ maximalIdeal T.ring) d ↔
          M.Φ p ∈ AssocGraded.homogeneous (maximalIdeal R) d) ∧
      (∀ (d : ℕ) (p : MvPolynomial (Fin n) (T.ring ⧸ maximalIdeal T.ring)),
        p ∈ homogeneousSubmodule (Fin n) (T.ring ⧸ maximalIdeal T.ring) d ↔
          M₁.Φ p ∈ AssocGraded.homogeneous (maximalIdeal T.ring) d) ∧
      Set.range zI ⊆ U ∧ Function.Injective zI ∧
      (∀ l, M.Φ (X (zI l)) = frameForm F.z l) ∧
      (∀ l, M₁.Φ (X (zI l)) = frameForm FT.w l) ∧
      (∀ c, M.ρ.symm c = quotientMaximalIdealMap T.toRing c) ∧ (∀ c, M₁.ρ c = c) ∧
      ∀ (μ : ℕ) (f : R) (g : T.ring), f ∈ P ^ μ → Ideal.ordElem (maximalIdeal R) f = μ →
        Ideal.ordElem (maximalIdeal T.ring) g = μ → FT.x ^ μ * g = T.toRing f →
        M.Φ.symm (initialForm (maximalIdeal R) f) ∈ supported (T.ring ⧸ maximalIdeal T.ring) U ∧
          M₁.Φ.symm (initialForm (maximalIdeal T.ring) g) -
            M.Φ.symm (initialForm (maximalIdeal R) f) ∈
              outIdeal (K := T.ring ⧸ maximalIdeal T.ring) U := by
  classical
  have hdom1 : IsDomain T.ring := Transforms.isDomain_of_isRegularLocalRing _
  obtain ⟨t', s, xs, ys, u, hxs, hspanR, hdimR, hspanR₁, hdimR₁, hPeq⟩ :=
    FT.exists_coordinates hrat x hxP h7'
  obtain ⟨ρ, hρ⟩ := exists_residueEquiv hrat
  have hspan : Ideal.span (Set.range (coordV x xs ys)) = maximalIdeal R := hspanR
  have hspan₁ : Ideal.span (Set.range (coordV₁ FT ys u)) = maximalIdeal T.ring := hspanR₁
  refine ⟨(F.r + t') + (s + 1), gradedSemiModel ρ (coordV x xs ys) hspan hdimR,
    gradedSemiModel (RingEquiv.refl (T.ring ⧸ maximalIdeal T.ring)) (coordV₁ FT ys u)
      hspan₁ hdimR₁, fun l : Fin F.r => Fin.castAdd (s + 1) (Fin.castAdd t' l),
    {i | i.val < F.r + t'},
    gradedSemiModel_hhom ρ (coordV x xs ys) hspan hdimR,
    gradedSemiModel_hhom (RingEquiv.refl (T.ring ⧸ maximalIdeal T.ring)) (coordV₁ FT ys u)
      hspan₁ hdimR₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨l, rfl⟩
    show (Fin.castAdd (s + 1) (Fin.castAdd t' l) : Fin ((F.r + t') + (s + 1))).val < F.r + t'
    simp only [Fin.val_castAdd]
    have := l.2
    omega
  · intro a b hab
    have h1 : (Fin.castAdd (s + 1) (Fin.castAdd t' a) : Fin ((F.r + t') + (s + 1))).val =
        (Fin.castAdd (s + 1) (Fin.castAdd t' b) : Fin ((F.r + t') + (s + 1))).val :=
      congrArg Fin.val hab
    simp only [Fin.val_castAdd] at h1
    exact Fin.ext h1
  · intro l
    rw [gradedSemiModel_X, RegularFrame.frameForm_eq_mk F l]
    exact AssocGraded.mk_congr _ _ (by simp [coordV])
  · intro l
    rw [gradedSemiModel_X]
    show _ = frameForm FT.toRegularFrame.z l
    rw [FT.toRegularFrame.frameForm_eq_mk l]
    exact AssocGraded.mk_congr _ _ (by simp [coordV₁])
  · intro c
    exact (RingHom.congr_fun hρ c)
  · intro c
    rfl
  · exact forms_of_coordinates FT x h7' hx0 xs ys u hxs hspan hdimR hspan₁ hdimR₁ hPeq ρ hρ

/-- **The polynomial pictures of `gr_M(R)` and `gr_{M₁}(R₁)`** (p. 256): see `exists_models_zI`;
this version records the set `Zv` of the variables `Z` and the pull-backs of the span of the
`Z_l`, `W_l`. -/
theorem exists_models [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing]
    [IsRegularLocalRing T.ring] (FT : F.FrameTransform T)
    (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing) (x : F.S)
    (hxP : algebraMap F.S R x ∈ P) (h7' : FT.x = T.toRing (algebraMap F.S R x))
    (hx0 : FT.x ≠ 0) :
    ∃ (n : ℕ) (M : SemiModel (T.ring ⧸ maximalIdeal T.ring) (R ⧸ maximalIdeal R)
        (AssocGraded (maximalIdeal R)) n)
      (M₁ : SemiModel (T.ring ⧸ maximalIdeal T.ring) (T.ring ⧸ maximalIdeal T.ring)
        (AssocGraded (maximalIdeal T.ring)) n) (U Zv : Set (Fin n)),
      (∀ (d : ℕ) (p : MvPolynomial (Fin n) (T.ring ⧸ maximalIdeal T.ring)),
        p ∈ homogeneousSubmodule (Fin n) (T.ring ⧸ maximalIdeal T.ring) d ↔
          M.Φ p ∈ AssocGraded.homogeneous (maximalIdeal R) d) ∧
      (∀ (d : ℕ) (p : MvPolynomial (Fin n) (T.ring ⧸ maximalIdeal T.ring)),
        p ∈ homogeneousSubmodule (Fin n) (T.ring ⧸ maximalIdeal T.ring) d ↔
          M₁.Φ p ∈ AssocGraded.homogeneous (maximalIdeal T.ring) d) ∧
      Zv ⊆ U ∧
      M.pull (Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z))) =
        Submodule.span (T.ring ⧸ maximalIdeal T.ring) (X '' Zv) ∧
      M₁.pull (Submodule.span (T.ring ⧸ maximalIdeal T.ring) (Set.range (frameForm FT.w))) =
        Submodule.span (T.ring ⧸ maximalIdeal T.ring) (X '' Zv) ∧
      ∀ (μ : ℕ) (f : R) (g : T.ring), f ∈ P ^ μ → Ideal.ordElem (maximalIdeal R) f = μ →
        Ideal.ordElem (maximalIdeal T.ring) g = μ → FT.x ^ μ * g = T.toRing f →
        M.Φ.symm (initialForm (maximalIdeal R) f) ∈ supported (T.ring ⧸ maximalIdeal T.ring) U ∧
          M₁.Φ.symm (initialForm (maximalIdeal T.ring) g) -
            M.Φ.symm (initialForm (maximalIdeal R) f) ∈
              outIdeal (K := T.ring ⧸ maximalIdeal T.ring) U := by
  obtain ⟨n, M, M₁, zI, U, hhom, hhom₁, hzU, -, hzM, hzM₁, -, -, hforms⟩ :=
    exists_models_zI FT hrat x hxP h7' hx0
  refine ⟨n, M, M₁, U, Set.range zI, hhom, hhom₁, hzU, ?_, ?_, hforms⟩
  · exact M.pull_span_range _ zI hzM
  · exact M₁.pull_span_range _ zI hzM₁

/-- **The instantiation of the assembly, with the choice of the coordinates** (pp. 256–258): see
`core_assembly_printed` and `exists_models`.  The hypothesis `hZTa` is the printed "`T_a` must
contain `Z_1, …, Z_r`, by (1), (2) and (11)" (p. 256) and `hφ` is Lemma 19 on the `R`-side, "by Lemma 19
of §7, `φ ∈ k[Z_1, …, Z_r, X_1, …, X_τ]`" (p. 257). -/
theorem core_instantiate_printed [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing]
    [IsRegularLocalRing T.ring] (FT : F.FrameTransform T)
    (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing) (x : F.S)
    (hxP : algebraMap F.S R x ∈ P) (h7' : FT.x = T.toRing (algebraMap F.S R x)) (hx0 : FT.x ≠ 0)
    (J : Ideal R) (a : ℕ) (ha : 1 ≤ a) (hat : a ≤ t R J)
    (hat₁ : a ≤ t T.ring (strictTransformIdeal T J))
    (hτ : tau T.ring (strictTransformIdeal T J) a = tau R J a)
    {N : ℕ} (G : Fin N → R) (d : Fin N → ℕ)
    (hG : ∀ T', IsTauSubmodule R J T' (mu R J a) ↔ IsTauZSubmodule R G T')
    (hGord : ∀ j, Ideal.ordElem (maximalIdeal R) (G j) = d j) (hdμ : ∀ j, d j ≤ mu R J a)
    (hGP : ∀ j, G j ∈ P ^ d j) (g : Fin N → T.ring)
    (hgrel : ∀ j, FT.x ^ d j * g j = T.toRing (G j))
    (hgord : ∀ j, Ideal.ordElem (maximalIdeal T.ring) (g j) = d j)
    (hψT : ∀ j, initialForm (maximalIdeal T.ring) (g j) ∈
      Algebra.adjoin (T.ring ⧸ maximalIdeal T.ring) (tauSubmodule T.ring
        (strictTransformIdeal T J) a : Set (AssocGraded (maximalIdeal T.ring))))
    (hZT : Submodule.span (T.ring ⧸ maximalIdeal T.ring) (Set.range (frameForm FT.w)) ≤
      tauSubmodule T.ring (strictTransformIdeal T J) a)
    (hZTa : Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z)) ≤
      tauSubmodule R J a) (i₀ : Fin N)
    (hφ : initialForm (maximalIdeal R) (G i₀) ∈ Algebra.adjoin (R ⧸ maximalIdeal R)
      ((tauSubmodule R J a ⊔ Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z)) :
        Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))) :
          Set (AssocGraded (maximalIdeal R)))) :
    Module.finrank (R ⧸ maximalIdeal R)
        ↥(tauZSubmodule R (fun _ : Fin 1 => G i₀) ⊔
          Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z))) =
      Module.finrank (T.ring ⧸ maximalIdeal T.ring)
        ↥(tauZSubmodule T.ring (fun _ : Fin 1 => g i₀) ⊔
          Submodule.span (T.ring ⧸ maximalIdeal T.ring) (Set.range (frameForm FT.w))) := by
  classical
  obtain ⟨n, M, M₁, U, Zv, hhom, hhom₁, hZv, hZ, hZ₁, hforms⟩ :=
    exists_models FT hrat x hxP h7' hx0
  have hGd : ∀ j, initialForm (maximalIdeal R) (G j) ∈
      AssocGraded.homogeneous (maximalIdeal R) (d j) := fun j => by
    rw [initialForm_eq_mk _ (hGord j)]
    exact AssocGraded.mk_mem_homogeneous _ _
  have hf := fun j => hforms (d j) (G j) (g j) (hGP j) (hGord j) (hgord j) (hgrel j)
  exact core_assembly_printed M M₁ hhom hhom₁ J (strictTransformIdeal T J) a ha hat hat₁ hτ G d
    hG hGd hdμ g U (fun j => (hf j).1) (fun j => (hf j).2) hψT _ _ Zv hZv hZ hZ₁ hZT hZTa i₀ hφ

end CoreInstantiate

section Lemma20Printed

open MvPolynomial

attribute [local instance] Ideal.Quotient.field

/-- `Φ(Σ q_A X_{zI}^A)` for the polynomial picture of a semilinear model: if `Φ` sends the variables
`X_{zI l}` to `z_l`, then `Φ (rename zI (map ρ⁻¹ q)) = q(z)` (the polynomials in the variables
`Z` of the model are the polynomials of the frame's initial forms). -/
theorem SemiModel.Φ_rename_map_eq {k k₁ G : Type u} [Field k] [Field k₁] [CommRing G]
    [Algebra k₁ G] {n r : ℕ} (M : SemiModel k k₁ G n) (zI : Fin r → Fin n) (z : Fin r → G)
    (hz : ∀ l, M.Φ (X (zI l)) = z l) (q : MvPolynomial (Fin r) k₁) :
    M.Φ (rename zI (MvPolynomial.map (M.ρ.symm : k₁ →+* k) q)) = aeval z q := by
  let φ : MvPolynomial (Fin r) k₁ →+* G :=
    ((M.Φ : MvPolynomial (Fin n) k →+* G).comp
      (rename zI : MvPolynomial (Fin r) k →ₐ[k] MvPolynomial (Fin n) k).toRingHom).comp
        (MvPolynomial.map (M.ρ.symm : k₁ →+* k))
  have : φ = (aeval z : MvPolynomial (Fin r) k₁ →ₐ[k₁] G).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun l => ?_)
    · simp only [φ, RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C,
        AlgHom.toRingHom_eq_coe, MvPolynomial.rename_C, RingHom.coe_coe,
        MvPolynomial.aeval_C]
      rw [M.map_C, RingEquiv.apply_symm_apply]
    · simp only [φ, RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_X,
        AlgHom.toRingHom_eq_coe, MvPolynomial.rename_X, RingHom.coe_coe,
        MvPolynomial.aeval_X]
      exact hz l
  exact RingHom.congr_fun this q

theorem SemiModel.symm_aeval_eq {k k₁ G : Type u} [Field k] [Field k₁] [CommRing G]
    [Algebra k₁ G] {n r : ℕ} (M : SemiModel k k₁ G n) (zI : Fin r → Fin n) (z : Fin r → G)
    (hz : ∀ l, M.Φ (X (zI l)) = z l) (q : MvPolynomial (Fin r) k₁) :
    M.Φ.symm (aeval z q) = rename zI (MvPolynomial.map (M.ρ.symm : k₁ →+* k) q) := by
  rw [← M.Φ_rename_map_eq zI z hz q, RingEquiv.symm_apply_apply]

/-- `rename` of a polynomial in the variables `Z` lies in `supported U` as soon as the image of the
renaming does. -/
theorem rename_mem_supported_of_range_subset {K : Type*} [CommSemiring K] {n r : ℕ}
    (zI : Fin r → Fin n) (U : Set (Fin n)) (hU : Set.range zI ⊆ U)
    (q : MvPolynomial (Fin r) K) : rename zI q ∈ supported K U := by
  rw [mem_supported]
  intro i hi
  have h1 := vars_rename zI q (Finset.mem_coe.mp hi)
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h1
  exact hU ⟨j, rfl⟩

namespace RegularFrame

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}
  {F : RegularFrame R} {T : MonoidalTransform R P} [IsLocalHom T.toRing]
  [IsRegularLocalRing T.ring]

/-- **The initial forms of `g_j = x^{-ν_j} f_j` when `R₁` is residually rational** (p. 255, in the
coordinates of `R` and `R₁`: "By (9), we have `ψ_j = φ_j(W₁, …, W_r) + λ_j` for `1 ≤ j ≤ i` where
`λ_j ∈ (X, Y₁, …, Y_s) gr_{M₁}(R₁)`. (See the proof of Lemma 14 of §5.) Therefore the assumption
(8) implies that `ψ_j = φ_j(W₁, …, W_r)`"): `φ_j = P_j(Z)`, `ψ_j = (κ P_j)(W)` for the same
homogeneous `P_j` of degree `ν_j`, `κ : k → k₁` the residue field isomorphism.  In the coordinates
`(z, x_k, x, y)` of `R` and `(w, u, x, y)` of `R₁` (`exists_models_zI`) the comparison of the
initial forms of `f_j` and `g_j` is `forms_correspond` (the paper's "`ψ_j = φ_j(W) + λ_j`"); (8)
puts `ψ_j` in `k[W]`, so `λ_j` (an element of `(X, Y) gr` lying in `k[W, Z, X_k]`) is zero. -/
theorem FrameTransform.exists_polynomials_initialForm_of_isResiduallyRational
    [P.IsPrime] [IsRegularLocalRing (R ⧸ P)]
    (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing)
    (FT : F.FrameTransform T) (x : F.S) (hxP : algebraMap F.S R x ∈ P)
    (h7' : FT.x = T.toRing (algebraMap F.S R x)) (hx0 : FT.x ≠ 0) {i : ℕ}
    (f : Fin i → R) (g : Fin i → T.ring) (ν : Fin i → ℕ)
    (hfP : ∀ j, f j ∈ P ^ ν j)
    (hf : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = ν j)
    (h2 : ∀ j, tauZ R F.z (fun _ : Fin 1 => f j) = 0)
    (hg : ∀ j, FT.x ^ ν j * g j = T.toRing (f j))
    (hgM : ∀ j, Ideal.ordElem (maximalIdeal T.ring) (g j) = ν j)
    (h8 : ∀ j, tauZ T.ring FT.w (fun _ : Fin 1 => g j) = 0) :
    ∃ Pf : Fin i → MvPolynomial (Fin F.r) (R ⧸ maximalIdeal R),
      (∀ j, (Pf j).IsHomogeneous (ν j)) ∧
      (∀ j, frameAlgHom F.z (Pf j) = initialForm (maximalIdeal R) (f j)) ∧
      (∀ j, frameAlgHom FT.w (MvPolynomial.map (quotientMaximalIdealMap T.toRing) (Pf j)) =
        initialForm (maximalIdeal T.ring) (g j)) := by
  classical
  have hdom1 : IsDomain T.ring := Transforms.isDomain_of_isRegularLocalRing _
  choose Pf hPh hPf using fun j => F.exists_isHomogeneous_frameAlgHom_eq_initialForm (hf j) (h2 j)
  obtain ⟨Qg, hQh, hQg⟩ : ∃ Qg : Fin i → MvPolynomial (Fin F.r) (T.ring ⧸ maximalIdeal T.ring),
      (∀ j, (Qg j).IsHomogeneous (ν j)) ∧
        ∀ j, frameAlgHom FT.w (Qg j) = initialForm (maximalIdeal T.ring) (g j) := by
    choose Q hQ1 hQ2 using fun j =>
      FT.toRegularFrame.exists_isHomogeneous_frameAlgHom_eq_initialForm (hgM j) (h8 j)
    exact ⟨Q, hQ1, hQ2⟩
  refine ⟨Pf, hPh, hPf, fun j => ?_⟩
  suffices hQ : Qg j = MvPolynomial.map (quotientMaximalIdealMap T.toRing) (Pf j) by
    rw [← hQ]; exact hQg j
  obtain ⟨n, M, M₁, zI, U, hhom, hhom₁, hzU, hzinj, hzM, hzM₁, hρM, hρM₁, hforms⟩ :=
    exists_models_zI FT hrat x hxP h7' hx0
  obtain ⟨-, hdiff⟩ := hforms (ν j) (f j) (g j) (hfP j) (hf j) (hgM j) (hg j)
  have hinf : initialForm (maximalIdeal R) (f j) = aeval (frameForm F.z) (Pf j) := by
    rw [← hPf j]; rfl
  have hing : initialForm (maximalIdeal T.ring) (g j) = aeval (frameForm FT.w) (Qg j) := by
    rw [← hQg j]; rfl
  have hp := M.symm_aeval_eq zI (frameForm F.z) hzM (Pf j)
  have hq := M₁.symm_aeval_eq zI (frameForm FT.w) hzM₁ (Qg j)
  rw [hinf, hp] at hdiff
  rw [hing, hq] at hdiff
  have hsub : rename zI (MvPolynomial.map (M₁.ρ.symm : _ →+* _) (Qg j)) -
      rename zI (MvPolynomial.map (M.ρ.symm : _ →+* _) (Pf j)) ∈
        supported (T.ring ⧸ maximalIdeal T.ring) U :=
    sub_mem (rename_mem_supported_of_range_subset zI U hzU _)
      (rename_mem_supported_of_range_subset zI U hzU _)
  have h0 := (projOut_eq_zero_iff U _).mpr hdiff
  rw [projOut_of_mem_supported U hsub] at h0
  have hren := rename_injective zI hzinj (sub_eq_zero.mp h0)
  have hρ₁ : (M₁.ρ.symm : T.ring ⧸ maximalIdeal T.ring →+* T.ring ⧸ maximalIdeal T.ring) =
      RingHom.id _ :=
    RingHom.ext fun c => (by
      have := hρM₁ (M₁.ρ.symm c)
      rwa [RingEquiv.apply_symm_apply] at this : c = M₁.ρ.symm c).symm
  have hρ₀ : (M.ρ.symm : _ →+* _) = quotientMaximalIdealMap T.toRing := RingHom.ext hρM
  rw [hρ₁, MvPolynomial.map_id, hρ₀] at hren
  exact hren

end RegularFrame

end Lemma20Printed

section Lemma20Reduction

open MvPolynomial

attribute [local instance] Ideal.Quotient.field

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {F : RegularFrame R}
  {S' : Type u} [CommRing S'] [IsRegularLocalRing S'] [IsDomain S'] {a : F.S →+* S'}
  [IsLocalHom a] {P : Ideal R} {T : MonoidalTransform R P} [IsLocalHom T.toRing]
  [IsRegularLocalRing T.ring]

namespace RegularFrame

omit [IsDomain S'] [IsLocalHom a] [IsLocalHom T.toRing] [IsRegularLocalRing T.ring] in
/-- **The canonical homomorphism `S₁ → S̃₁` of the frame transforms** (p. 254: "all the assumptions
(1)–(10) remain valid, and the conclusions (a) and (b) are replaced by equivalent ones"): for the
frame transform `(S₁; w)` of `(S; z)` in `R₁` and the frame transform `(S̃₁; w̃)` of `(S̃; z)` in
the canonical lift `R̃₁` with `w̃_j = β(w_j)`, there is a ring homomorphism `γ : S₁ → S̃₁` with
`β̃ ∘ γ = β_L ∘ β` (`β : S₁ → R₁`, `β̃ : S̃₁ → R̃₁`, `β_L : R₁ → R̃₁`).  The paper does not
construct it.  It is `π̃ ∘ β_L ∘ β`, `π̃ : R̃₁ → R̃₁/(w̃) ≅ S̃₁` the retraction; that
`β_L(β(S₁)) ⊆ β̃(S̃₁)` follows
since two homomorphisms `S₁ → R̃₁` which agree on `S` agree (every element of `S₁ ⊆ Frac S` is a
quotient of elements of `S`). -/
theorem FrameTransform.exists_gamma (hainj : Function.Injective a)
    (L : BaseChangeLift (F.baseChangeHom a) T) [IsRegularLocalRing L.T'.ring]
    [IsLocalHom L.T'.toRing] (FT : F.FrameTransform T)
    (FT' : (F.baseChange S').FrameTransform L.T') :
    ∃ γ : FT.TS.ring →+* FT'.TS.ring, ∀ s, FT'.β (γ s) = L.β (FT.β s) := by
  classical
  have := FT.isRegular
  have := FT'.isRegular
  have hβ' : Function.Injective FT'.β := fun x y h =>
    FT'.quot_bijective.1 (by rw [RingHom.comp_apply, RingHom.comp_apply, h])
  let e' : FT'.TS.ring ≃+* L.T'.ring ⧸ Ideal.span (Set.range FT'.w) :=
    RingEquiv.ofBijective _ FT'.quot_bijective
  let π : L.T'.ring →+* FT'.TS.ring := e'.symm.toRingHom.comp (Ideal.Quotient.mk _)
  have hπ : ∀ s, π (FT'.β s) = s := fun s => e'.symm_apply_apply s
  have hfrac : ∀ s : FT.TS.ring, ∃ σ₁ σ₂ : F.S, σ₂ ≠ 0 ∧
      FT.TS.toRing σ₂ * s = FT.TS.toRing σ₁ := by
    intro s
    obtain ⟨σ₁, σ₂, hσ₂, hs⟩ := IsFractionRing.div_surjective (A := F.S)
      (FT.TS.toFractionRing s)
    have hσ₂0 : σ₂ ≠ 0 := nonZeroDivisors.ne_zero hσ₂
    have hne : algebraMap F.S (FractionRing F.S) σ₂ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective F.S (FractionRing F.S))).mpr hσ₂0
    refine ⟨σ₁, σ₂, hσ₂0, FT.TS.injective_toFractionRing ?_⟩
    rw [map_mul, FT.TS.toFractionRing_toRing, FT.TS.toFractionRing_toRing, ← hs]
    field_simp
  have hcomp : ∀ σ : F.S, L.β (FT.β (FT.TS.toRing σ)) = FT'.β (FT'.TS.toRing (a σ)) := by
    intro σ
    rw [FT.beta_toRing σ, ← L.toRing_baseChangeHom, FT'.beta_toRing (a σ)]
    exact congrArg L.T'.toRing (RingHom.congr_fun (F.baseChangeHom_comp_algebraMap (a := a)) σ)
  have hinj0 : ∀ σ : F.S, σ ≠ 0 → FT'.β (FT'.TS.toRing (a σ)) ≠ 0 := fun σ hσ =>
    (map_ne_zero_iff _ hβ').mpr ((map_ne_zero_iff _ FT'.TS.toRing_injective).mpr
      ((map_ne_zero_iff _ hainj).mpr hσ))
  refine ⟨π.comp (L.β.comp FT.β), fun s => ?_⟩
  obtain ⟨σ₁, σ₂, hσ₂, hs⟩ := hfrac s
  refine mul_left_cancel₀ (hinj0 σ₂ hσ₂) ?_
  have e1 : ∀ σ : F.S, FT'.β (π (L.β (FT.β (FT.TS.toRing σ)))) =
      FT'.β (FT'.TS.toRing (a σ)) := fun σ => by rw [hcomp σ, hπ]
  calc FT'.β (FT'.TS.toRing (a σ₂)) * FT'.β ((π.comp (L.β.comp FT.β)) s)
      = FT'.β (π (L.β (FT.β (FT.TS.toRing σ₂)))) * FT'.β ((π.comp (L.β.comp FT.β)) s) := by
        rw [e1]
    _ = FT'.β (π (L.β (FT.β (FT.TS.toRing σ₂ * s)))) := by
        simp only [RingHom.comp_apply, map_mul]
    _ = FT'.β (π (L.β (FT.β (FT.TS.toRing σ₁)))) := by rw [hs]
    _ = FT'.β (FT'.TS.toRing (a σ₁)) := e1 σ₁
    _ = L.β (FT.β (FT.TS.toRing σ₁)) := (hcomp σ₁).symm
    _ = L.β (FT.β (FT.TS.toRing σ₂ * s)) := by rw [hs]
    _ = L.β (FT.β (FT.TS.toRing σ₂)) * L.β (FT.β s) := by simp only [map_mul]
    _ = FT'.β (FT'.TS.toRing (a σ₂)) * L.β (FT.β s) := by rw [hcomp σ₂]

omit [IsDomain S'] [IsLocalHom a] [IsLocalHom T.toRing] in
/-- `β_L ∘ ev_w = ev_{w̃} ∘ γ` on polynomials in the `Z_j` (the evaluation of a frame). -/
theorem FrameTransform.evZ_lift (L : BaseChangeLift (F.baseChangeHom a) T)
    [IsRegularLocalRing L.T'.ring] [IsLocalHom L.T'.toRing] (FT : F.FrameTransform T)
    (FT' : (F.baseChange S').FrameTransform L.T') (γ : FT.TS.ring →+* FT'.TS.ring)
    (hγ : ∀ s, FT'.β (γ s) = L.β (FT.β s)) (hw : ∀ j, FT'.w j = L.β (FT.w j))
    (G : MvPolynomial (Fin F.r) FT.TS.ring) :
    L.β (evZ FT.toRegularFrame G) = evZ FT'.toRegularFrame (MvPolynomial.map γ G) := by
  have : (L.β.comp (evZ FT.toRegularFrame).toRingHom) =
      ((evZ FT'.toRegularFrame).toRingHom.comp (MvPolynomial.map γ)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun l => ?_)
    · show L.β (evZ FT.toRegularFrame (C c)) =
        evZ FT'.toRegularFrame (MvPolynomial.map γ (C c))
      erw [MvPolynomial.map_C]
      unfold evZ
      erw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
      exact (hγ c).symm
    · show L.β (evZ FT.toRegularFrame (X l)) =
        evZ FT'.toRegularFrame (MvPolynomial.map γ (X l))
      erw [MvPolynomial.map_X]
      unfold evZ
      erw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
      show L.β (FT.w l) = FT'.w l
      exact (hw l).symm
  exact RingHom.congr_fun this G

omit [IsDomain S'] [IsLocalHom a] [IsLocalHom T.toRing] in
/-- **The expansion coefficients are compatible with the base change** (p. 254: "the conclusions
(a) and (b) are replaced by equivalent ones"): `c_A(β_L h) = γ(c_A(h))` for the expansions over
`(S₁; w)` and `(S̃₁; w̃)`.  Both are read off a polynomial `G` with `h ≡ G(w)` modulo `(w)^{|A|+1}`
(`expCoeff_eq`), and `β_L` carries `G(w)` to `(γ G)(w̃)` and `(w)^n R₁` into `(w̃)^n R̃₁`. -/
theorem FrameTransform.expCoeff_lift (L : BaseChangeLift (F.baseChangeHom a) T)
    [IsRegularLocalRing L.T'.ring] [IsLocalHom L.T'.toRing] (FT : F.FrameTransform T)
    (FT' : (F.baseChange S').FrameTransform L.T') (γ : FT.TS.ring →+* FT'.TS.ring)
    (hγ : ∀ s, FT'.β (γ s) = L.β (FT.β s)) (hw : ∀ j, FT'.w j = L.β (FT.w j))
    (h : T.ring) (A : Fin F.r →₀ ℕ) :
    FT'.toRegularFrame.expCoeff (L.β h) A = γ (FT.toRegularFrame.expCoeff h A) := by
  classical
  obtain ⟨G, hG⟩ := exists_evZ_sub_mem_pow FT.toRegularFrame (A.degree + 1) h
  have e1 : FT.toRegularFrame.expCoeff h A = G.coeff A :=
    expCoeff_eq FT.toRegularFrame hG (Nat.lt_succ_self _)
  have hI : FT.toRegularFrame.idealZ.map L.β ≤ FT'.toRegularFrame.idealZ := by
    rw [RegularFrame.idealZ, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨l, hw l⟩
  have hG' : L.β h - evZ FT'.toRegularFrame (MvPolynomial.map γ G) ∈
      FT'.toRegularFrame.idealZ ^ (A.degree + 1) := by
    rw [← FT.evZ_lift L FT' γ hγ hw G, ← map_sub]
    have h1 := Ideal.mem_map_of_mem L.β hG
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hI _ h1
  rw [expCoeff_eq FT'.toRegularFrame hG' (Nat.lt_succ_self _), e1]
  exact MvPolynomial.coeff_map γ G A

attribute [local instance] MvPolynomial.gradedAlgebra in
omit [IsDomain S'] [IsLocalHom a] [IsLocalHom T.toRing] in
/-- **The `E`-set is compatible with the base change** (Remark 1 of §7 for the extension of the
residue fields `k₁ → k̃₁`): if the initial forms of `g_j` lie in `k₁[W]`, the `E`-set of
`(β_L g_1, …, β_L g_i)` with respect to `(k̃₁; W̃)` is the `E`-set of `(g_1, …, g_i)` with respect
to `(k₁; W)`. -/
theorem FrameTransform.frameESet_lift (L : BaseChangeLift (F.baseChangeHom a) T)
    [IsRegularLocalRing L.T'.ring] [IsLocalHom L.T'.toRing] (hβ : RingHom.MapsRSOP L.β)
    (FT : F.FrameTransform T) (FT' : (F.baseChange S').FrameTransform L.T')
    (hw : ∀ j, FT'.w j = L.β (FT.w j)) {i : ℕ} (g : Fin i → T.ring)
    (hg : ∀ j, initialForm (maximalIdeal T.ring) (g j) ∈ Set.range (frameAlgHom FT.w)) :
    frameESet FT'.w (fun j => L.β (g j)) = frameESet FT.w g := by
  classical
  let _ : Field (T.ring ⧸ maximalIdeal T.ring) := Ideal.Quotient.field _
  let _ : Field (L.T'.ring ⧸ maximalIdeal L.T'.ring) := Ideal.Quotient.field _
  choose Pf hPf using hg
  have hI : frameInitialIdeal FT.w g = Ideal.span (Set.range Pf) := by
    unfold frameInitialIdeal
    congr 1
    ext ψ
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, FT.toRegularFrame.frameAlgHom_injective ((hPf j).trans hj.symm)⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, hPf j⟩
  have hQ : ∀ j, frameAlgHom FT'.w (MvPolynomial.map (residueQuotMap L.β) (Pf j)) =
      initialForm (maximalIdeal _) (L.β (g j)) := by
    intro j
    have h1 := grMapMax_frameAlgHom L.β hβ FT.w FT'.w (fun l => hw l) (Pf j)
    rw [hPf j, ← initialForm_map_of_mapsRSOP _ hβ] at h1
    exact h1.symm
  have hI' : frameInitialIdeal FT'.w (fun j => L.β (g j)) =
      Ideal.span (Set.range fun j => MvPolynomial.map (residueQuotMap L.β) (Pf j)) := by
    unfold frameInitialIdeal
    congr 1
    ext ψ
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, FT'.toRegularFrame.frameAlgHom_injective ((hQ j).trans hj.symm)⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, hQ j⟩
  have hhom : (frameInitialIdeal FT.w g).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin F.r) (T.ring ⧸ maximalIdeal T.ring)) := by
    rw [hI]
    apply Ideal.homogeneous_span
    rintro _ ⟨j, rfl⟩
    obtain ⟨d, hd⟩ := initialForm_mem_homogeneous_aux' (maximalIdeal T.ring) (g j)
    exact ⟨d, FT.toRegularFrame.isHomogeneous_of_frameAlgHom_mem_homogeneous
      (by rw [← hPf j] at hd; exact hd)⟩
  have hmap : frameInitialIdeal FT'.w (fun j => L.β (g j)) =
      (frameInitialIdeal FT.w g).map (MvPolynomial.map (residueQuotMap L.β)) := by
    rw [hI', hI, Ideal.map_span, ← Set.range_comp]
    rfl
  have key := (eSet_map_of_injective (residueQuotMap L.β)
    (residueQuotMap_injective _) (frameInitialIdeal FT.w g) hhom).2
    (fun c hc b hcb => (mul_eq_zero.mp hcb).resolve_left
      ((map_ne_zero_iff _ (residueQuotMap_injective _)).mpr hc))
  unfold frameESet
  rw [hmap]
  exact key

end RegularFrame

end Lemma20Reduction


/-! ### Lemma 20 (pp. 254–256), the proof (the auxiliary results are above, the proof uses the
coordinates and the base change of §8 and is placed after them) -/

section Lemma20

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- **Lemma 20 for complete `R` and residually rational `R₁`** (the proof of Lemma 20 after its
first paragraph, pp. 254–256: "Therefore we may assume that `R` and `S` are complete and that `R₁` is
residually rational over `R`.  Let `M` be the maximal ideal of `R` and `k = R/M`. … `ψ_j =
φ_j(W₁, …, W_r) + λ_j` … Therefore the assumption (8) implies that `ψ_j = φ_j(W₁, …, W_r)`. … Hence
(a) is proved. Now, in view of the first assertion of Lemma 18 of §7 … Then (b) follows by the
second assertion of Lemma 18 of §7").  The statement is that of Lemma 20 with "`R₁` residually rational
over `R`" for "residually separable algebraic" and with `R` complete (not used by the argument: the
power series expansion of a frame exists for every `R`).  The residue field isomorphism `κ : k → k₁`
gives the polynomials `P_j` with `φ_j = P_j(Z)`, `ψ_j = (κ P_j)(W)`
(`exists_polynomials_initialForm_of_isResiduallyRational`, in the coordinates of p. 255), and the
`E`-set of `I' = (ψ_j) k₁[W]` is that of `I = (φ_j) k[Z]` transported by the isomorphism `κ`. -/
theorem isNormalizedBy_frameTransform_and_extendsToStandardBase_of_isResiduallyRational [Hironaka.HironakaCitedResults.{u}]
    [IsAdicComplete (maximalIdeal R) R] (J : Ideal R)
    (F : RegularFrame R) {i : ℕ} (f : Fin i → R) (f' : R) (hfJ : ∀ j, f j ∈ J) (hf'J : f' ∈ J)
    (h1 : ExtendsToStandardBase J (Fin.snoc f f' : Fin (i + 1) → R))
    (h2 : ∀ j : Fin i, tauZ R F.z (fun _ : Fin 1 => f j) = 0)
    (h3 : F.IsNormalizedBy f f')
    (P : Ideal R) [P.IsPrime] (h4 : IsPermissibleCenter R J P) (_h5 : F.idealZ ≤ P)
    (h6 : ∀ j : Fin i, Ideal.ordElem P (f j) = nuI R J (j : ℕ).succPNat)
    (h6' : Ideal.ordElem P f' = nuI R J i.succPNat)
    (T : MonoidalTransform R P) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing)
    (x : F.S) (hxP : algebraMap F.S R x ∈ P)
    (_h7 : P.map T.toRing = Ideal.span {T.toRing (algebraMap F.S R x)})
    (FT : F.FrameTransform T) (h7' : FT.x = T.toRing (algebraMap F.S R x))
    (ν : Fin (i + 1) → ℕ) (hν : ∀ j : Fin (i + 1), (ν j : ℕ∞) = nuI R J (j : ℕ).succPNat)
    (g : Fin i → T.ring)
    (hg : ∀ j : Fin i, T.toRing (algebraMap F.S R x) ^ ν j.castSucc * g j = T.toRing (f j))
    (h8 : ∀ j : Fin i, tauZ T.ring FT.w (fun _ : Fin 1 => g j) = 0)
    (h9 : ∀ j : Fin i, Ideal.ordElem (maximalIdeal T.ring) (g j) = nuI R J (j : ℕ).succPNat)
    (g' : T.ring) (hg' : T.toRing (algebraMap F.S R x) ^ ν (Fin.last i) * g' = T.toRing f') :
    FT.toRegularFrame.IsNormalizedBy g g' ∧
      ((∀ j : ℕ+, (j : ℕ) ≤ i + 1 → nuI T.ring (strictTransformIdeal T J) j = nuI R J j) →
        ExtendsToStandardBase (strictTransformIdeal T J)
          (Fin.snoc g g' : Fin (i + 1) → T.ring)) := by
  classical
  -- the orders of `f_j` and `f'`
  obtain ⟨m, gs, him, hgs, hgsf⟩ := h1
  have hord : ∀ j : Fin (i + 1), Ideal.ordElem (maximalIdeal R)
      ((Fin.snoc f f' : Fin (i + 1) → R) j) = ν j := by
    intro j
    have := ordElem_eq_nuI_of_isStandardBase J gs hgs (Fin.castLE him j)
    rw [hgsf] at this
    exact this.trans (hν j).symm
  have hordf : ∀ j : Fin i, Ideal.ordElem (maximalIdeal R) (f j) = ν j.castSucc := fun j => by
    have := hord j.castSucc
    rwa [Fin.snoc_castSucc] at this
  have hordf' : Ideal.ordElem (maximalIdeal R) f' = ν (Fin.last i) := by
    have := hord (Fin.last i)
    rwa [Fin.snoc_last] at this
  -- `x ≠ 0` in `S₁`
  have hPtop : P ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  have hJP : J ≤ P := by
    rcases h4 with h | ⟨-, hJP, -, -⟩
    · exact absurd h hPtop
    · exact hJP
  have hPreg : IsRegularLocalRing (R ⧸ P) := by
    rcases h4 with h | ⟨-, -, hreg, -⟩
    · exact absurd h hPtop
    · exact hreg
  have hf'M : f' ∈ maximalIdeal R := hJP.trans (le_maximalIdeal hPtop) hf'J
  have hν1 : 1 ≤ ν (Fin.last i) := by
    have h1 : ((1 : ℕ) : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) f' :=
      Ideal.le_ordElem (by rwa [pow_one])
    rw [hordf'] at h1
    exact_mod_cast h1
  have hf'0 : f' ≠ 0 := fun h0 => by
    rw [h0, (Ideal.ordElem_eq_top_iff_eq_zero (maximalIdeal.isMaximal R).ne_top).mpr rfl] at hordf'
    exact ENat.top_ne_natCast _ hordf'
  have hg0 : ∀ j : Fin i, FT.x ^ ν j.castSucc * g j = T.toRing (f j) := fun j => by
    rw [h7']; exact hg j
  have hgM : ∀ j : Fin i, Ideal.ordElem (maximalIdeal T.ring) (g j) = ν j.castSucc :=
    fun j => (h9 j).trans (hν j.castSucc).symm
  have hg'0 : FT.x ^ ν (Fin.last i) * g' = T.toRing f' := by rw [h7']; exact hg'
  have hFTx0 : FT.x ≠ 0 := by
    intro h00
    rw [h00, zero_pow (by omega), zero_mul] at hg'0
    exact hf'0 (T.toRing_injective (by rw [← hg'0, map_zero]))
  have hx0 : FT.TS.toRing x ≠ 0 := fun h0 =>
    hFTx0 (by rw [h7', ← FT.beta_toRing x, h0, map_zero])
  -- the initial forms: `φ_j = P_j(Z)`, `ψ_j = (κ P_j)(W)` (p. 255, by the base change and the
  -- coordinates; `exists_polynomials_initialForm_of_isResiduallyRational`)
  have hfP : ∀ j : Fin i, f j ∈ P ^ ν j.castSucc := fun j =>
    Ideal.mem_pow_of_ordElem ((h6 j).trans (hν j.castSucc).symm)
  obtain ⟨Pf, hPh, hPf, hQg⟩ :=
    FT.exists_polynomials_initialForm_of_isResiduallyRational hrat x hxP h7' hFTx0 f g
      (fun j => ν j.castSucc) hfP hordf h2 hg0 hgM h8
  -- part (a)
  have ha : FT.toRegularFrame.IsNormalizedBy g g' := by
    have hE := FT.frameESet_eq_of_polynomials f g (fun j => ν j.castSucc) Pf hPh hPf hQg
    rw [FT.toRegularFrame.isNormalizedBy_iff_expCoeff]
    intro A hA
    have hA' : A ∈ frameESet F.z f := hE ▸ hA
    have hc := (F.isNormalizedBy_iff_expCoeff f f').mp h3 A hA'
    have hdiv := FT.expCoeff_div x h7' f' g' (ν (Fin.last i)) hg'0
      (Finsupp.equivFunOnFinite.symm A)
    rw [hc, map_zero, mul_zero] at hdiv
    exact (mul_eq_zero.mp hdiv).resolve_left (pow_ne_zero _ hx0)
  refine ⟨ha, fun h10 => ?_⟩
  -- the strict transform `J₁` is contained in the maximal ideal `M₁`
  set J₁ := strictTransformIdeal T J with hJ₁
  have hJ₁M : J₁ ≤ maximalIdeal T.ring := by
    have h := h10 1 (by simp)
    rw [(nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen T.ring J₁).1.2,
      (nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen R J).1.2] at h
    have h1le : 1 ≤ Ideal.nu J :=
      ((Ideal.ord_basic _ J J J).2.1).mpr (hJP.trans (le_maximalIdeal hPtop))
    exact ((Ideal.ord_basic _ J₁ J₁ J₁).2.1).mp (by rw [Ideal.nu] at h; rw [h]; exact h1le)
  -- the elements `g_j`, `g'` lie in `J₁`
  have hgJ : ∀ j : Fin i, g j ∈ J₁ := fun j =>
    Ideal.subset_span ⟨FT.x, FT.span_x, f j, hfJ j, ν j.castSucc,
      ((hν j.castSucc).trans (h6 j).symm).le, hg0 j⟩
  have hg'J : g' ∈ J₁ :=
    Ideal.subset_span ⟨FT.x, FT.span_x, f', hf'J, ν (Fin.last i),
      ((hν (Fin.last i)).trans h6'.symm).le, hg'0⟩
  have hinit : ∀ j : Fin i, initialForm (maximalIdeal T.ring) (g j) ∈
      FT.toRegularFrame.assocSubalgebra := fun j =>
    FT.toRegularFrame.initialForm_mem_adjoin_of_tauZ_eq_zero (g j) (h8 j)
  -- the initial forms of `f_1, …, f_i` are successively independent (standard base)
  have hgsf' : ∀ j : Fin i, gs (Fin.castLE (by omega : i ≤ m) j) = f j := fun j => by
    have := hgsf j.castSucc
    rwa [Fin.snoc_castSucc] at this
  have hindf : ∀ k : Fin i, initialForm (maximalIdeal R) (f k) ∉ Ideal.span
      (Set.range fun j : Fin k => initialForm (maximalIdeal R) (f (Fin.castLE k.2.le j))) := by
    intro k hmem
    refine hgs.2.2.2.2 (Fin.castLE (by omega : i ≤ m) k) ?_
    have e2 : (fun j : Fin (Fin.castLE (by omega : i ≤ m) k : ℕ) => initialForm (maximalIdeal R)
        (gs (Fin.castLE (Fin.castLE (by omega : i ≤ m) k).2.le j))) =
        fun j : Fin k => initialForm (maximalIdeal R) (f (Fin.castLE k.2.le j)) := by
      funext j
      rw [← hgsf' (Fin.castLE k.2.le j)]
      rfl
    show initialForm (maximalIdeal R) (gs (Fin.castLE (by omega : i ≤ m) k)) ∈ _
    rw [hgsf' k, e2]
    exact hmem
  -- the initial forms of `g_1, …, g_i` are successively independent
  have hindg : ∀ k : Fin i, initialForm (maximalIdeal T.ring) (g k) ∉ Ideal.span
      (Set.range fun j : Fin k =>
        initialForm (maximalIdeal T.ring) (g (Fin.castLE k.2.le j))) := fun k =>
    FT.initialForm_notMem_span_of_polynomials f g Pf hPf hQg k (hindf k)
  -- `(g_1, …, g_i)` can be extended to a standard base of `J₁`
  have hnuJ₁ : ∀ j : Fin i, (ν j.castSucc : ℕ∞) = nuI T.ring J₁ (j : ℕ).succPNat := fun j =>
    ((hν j.castSucc).trans (h10 (j : ℕ).succPNat (by simp)).symm :)
  have hmono : Monotone fun j : Fin i => ν j.castSucc := by
    intro j j' hjj'
    have := nuI_mono J (show (j : ℕ).succPNat ≤ (j' : ℕ).succPNat from
      PNat.coe_le_coe _ _ |>.mp (by simpa using hjj'))
    exact_mod_cast (hν j.castSucc).trans_le (this.trans_eq (hν j'.castSucc).symm)
  have hext : ExtendsToStandardBase J₁ g :=
    extendsToStandardBase_of_forall_initialForm_notMem_span J₁ g hgJ (fun j => ν j.castSucc)
      hgM hmono hnuJ₁ hindg
  -- Lemma 18 for `(R₁, J₁, (S₁; w), P := M₁)`: `ν_{M₁}(g') ≥ ν_{i+1}`
  have hperm : IsPermissibleCenter T.ring J₁ (maximalIdeal T.ring) :=
    isPermissibleCenter_maximalIdeal_aux J₁ hJ₁M
  have hzM : FT.toRegularFrame.idealZ ≤ maximalIdeal T.ring :=
    FT.toRegularFrame.idealZ_le_maximalIdeal
  obtain ⟨hge, hiff⟩ := ordElem_ge_nuI_of_isNormalizedBy FT.toRegularFrame J₁ g hgJ hext hinit
    g' hg'J ha (maximalIdeal T.ring) hzM hperm fun j => (hgM j).trans (hnuJ₁ j)
  -- Lemma 8: `ν_{M₁}(g') ≤ ν_{i+1}`
  have halg : RingHom.IsResiduallyAlgebraic (R := R) (R' := T.ring) T.toRing := by
    exact RingHom.isResiduallyAlgebraic_of_isResiduallyRational T.toRing hrat
  have hle : Ideal.ordElem (maximalIdeal T.ring) g' ≤ ν (Fin.last i) := by
    have : IsRegularLocalRing (R ⧸ P) := hPreg
    exact ordElem_le_of_pow_mul_eq_toRing P T halg hf'0 hν1
      (h6'.trans (hν (Fin.last i)).symm) hordf' FT.span_x hg'0
  have hg'ne : g' ≠ 0 := fun h0 =>
    hf'0 (T.toRing_injective (by rw [← hg'0, h0, mul_zero, map_zero]))
  have heq : Ideal.ordElem (maximalIdeal T.ring) g' = nuI T.ring J₁ i.succPNat := by
    refine le_antisymm ?_ hge
    calc Ideal.ordElem (maximalIdeal T.ring) g' ≤ (ν (Fin.last i) : ℕ∞) := by exact_mod_cast hle
      _ = nuI R J i.succPNat := hν (Fin.last i)
      _ = nuI T.ring J₁ i.succPNat := (h10 i.succPNat (by simp)).symm
  exact (hiff hg'ne).mp heq


/-- Lemma 20, p. 254: "Let `R` be a regular local ring, `J` an ideal in `R` and
`(S; z₁, …, z_r)` a regular frame in `R`. Let `(f₁, …, f_i, f)` be a system of elements of `J`
such that (1) `(f₁, …, f_i, f)` can be extended to a standard base of `J`, (2) `τ_{(z)}(f_j) = 0`
for `1 ≤ j ≤ i` where `(z) = (z₁, …, z_r)`, and (3) `f` is normalized by `(f₁, …, f_i)` with
respect to `(S; z₁, …, z_r)`. Let `P` be a prime ideal in `R` such that (4) `P` is a permissible
center for `J`, (5) `P ⊇ (z₁, …, z_r)R`, and (6) `ν_P(f_j) = ν^{(j)}(J)` for `1 ≤ j ≤ i` and
`ν_P(f) = ν^{(i+1)}(J)`. Let `R₁` be a monoidal transform of `R` with center `P` which is
residually separable algebraic over `R`, and `J₁` the strict transform of `J` in `R₁`. Suppose we
have an element `x ∈ P ∩ S` such that (7) `PR₁ = (x)R₁` and `(S; z₁, …, z_r)` admits a frame
transform `(S₁; w₁, …, w_r)` in `R₁` with denominator `x` (`w_j = z_j/x` for `1 ≤ j ≤ r`),
(8) `τ_{(w)}(g_j) = 0` for `1 ≤ j ≤ i` where `g_j = x^{-ν_j} f_j` with `ν_j = ν^{(j)}(J)` and
`(w) = (w₁, …, w_r)`, and (9) `ν_{M₁}(g_j) = ν^{(j)}(J)` for `1 ≤ j ≤ i`, where `M₁` denotes the
maximal ideal of `R₁`. Let `g = x^{-ν_{i+1}} f` with `ν_{i+1} = ν^{(i+1)}(J)`. Then we have that
(a) `g` is normalized by `(g₁, …, g_i)` with respect to `(S₁; w₁, …, w_r)`. If we assume, in
addition, that (10) `ν^{(j)}(J₁) = ν^{(j)}(J)` for `1 ≤ j ≤ i + 1`, then we have that
(b) `(g₁, …, g_i, g)` can be extended to a standard base of `J₁`."

(Formalization notes.
* The paper's `f` and `g` are called `f'` and `g'`; `(f₁, …, f_i, f)` is `Fin.snoc f f'` and
  `(g₁, …, g_i, g)` is `Fin.snoc g g'`.
* The integers `ν_j` (`1 ≤ j ≤ i + 1`) are carried by `ν : Fin (i + 1) → ℕ` with
  `hν : ν_j = ν^{(j)}(J)`; this records their finiteness, which is implicit in `x^{-ν_j}`.
* `x ∈ P ∩ S` is `x : F.S` with `algebraMap F.S R x ∈ P`; the frame transform "with denominator
  `x`" of (7) is a frame transform `FT` (`RegularFrame.FrameTransform`) whose denominator is the
  image of `x` in `R₁` (`h7'`), and `(S₁; w₁, …, w_r)` is `FT.toRegularFrame`, `w = FT.w`.
* `g_j = x^{-ν_j} f_j` and `g = x^{-ν_{i+1}} f` are the elements of `R₁` with `x^{ν_j} g_j = f_j`
  and `x^{ν_{i+1}} g = f` (unique, `R₁` being a domain).
* (10) is the hypothesis of the implication which forms the second conclusion (b).
* `[IsLocalHom T.toRing]`, `[IsRegularLocalRing T.ring]` and `[IsDomain R]` are lemmas of §2
  taken as hypotheses (module docstring).
* The hypothesis (5) `P ⊇ (z)R` is used by the reduction (it gives (5) for the base-changed data:
  `P R̃ ⊇ (z) R̃`); in the core (`..._of_isResiduallyRational`) it is not needed once the frame
  transform `FT` is given (it carries `(x)R₁ = PR₁` and `z_j = x w_j`, so `P ⊇ (z)R` is a
  consequence, `FrameTransform.idealZ_le_and_unique`), and its binder is `_h5` there.)

Printed route.  (1) The paper begins with a base change `S → S̃`,
`R → R̃ = S̃{z}`, `R₁ → R̃₁` (p. 254: "all the assumptions (1)–(10) remain valid, and the
conclusions (a) and (b) are replaced by equivalent ones. Therefore we may assume that `R` and `S`
are complete and that `R₁` is residually rational over `R`").  This is carried out: `S̃` is the
complete regular local ring with separably closed residue field of `CompleteSepClosedExtension`,
`R̃ = S̃⟦z⟧` (`RegularFrame.baseChange`), `R̃₁` the canonical lift of `R₁` (`BaseChangeLift`,
residually rational by `BaseChangeLift.isResiduallyRational`), the frame transform is lifted
(`FrameTransform.exists_baseChange`), and the hypotheses (1)–(10) are verified for the lifted data
(`tauZ_baseChangeHom`, `isNormalizedBy_baseChangeHom`, `extendsToStandardBase_baseChangeHom`,
`ordElem_map_ideal_of_mapsRSOP`, `nuI_map_eq_of_mapsRSOP`,
`BaseChangeLift.nuI_strictTransformIdeal`, `tauZ_map`).  The conclusions (a) and (b) of the lifted lemma are shown to imply those of the
original one ("replaced by equivalent ones"): this needs the canonical homomorphism `γ : S₁ → S̃₁`
of the coefficient rings of the two frame transforms (`FrameTransform.exists_gamma`:
`β̃ ∘ γ = β_L ∘ β`), with which the expansion coefficients correspond,
`c_A(β_L h) = γ(c_A(h))` (`FrameTransform.expCoeff_lift`), the `E`-sets correspond
(`FrameTransform.frameESet_lift`), so that `γ` injective gives (a); and (b) is
`extendsToStandardBase_of_map` (initial forms are successively independent since their images
are).  (2) For complete `R` and residually rational `R₁` the proof is the paper's
(`isNormalizedBy_frameTransform_and_extendsToStandardBase_of_isResiduallyRational`): in the
coordinates of `R`, `R₁` (p. 255: "Let `Z_j` … Then `gr_M(R) = k[Z, X, X_j, Y]` …
`gr_{M₁}(R₁) = k[W, X, U, Y]`": `exists_coordinates_spans`, `exists_models_zI`), "By (9),
`ψ_j = φ_j(W₁, …, W_r) + λ_j` where `λ_j ∈ (X, Y₁, …, Y_s) gr_{M₁}(R₁)` (see the proof of Lemma 14
of §5)" is `forms_correspond` (Lemma K for `(x, y)R₁` and a lowest-degree argument), and (8) puts
`ψ_j` in `k[W]`, so that `λ_j = 0` (`exists_polynomials_initialForm_of_isResiduallyRational`); the
coefficients `d_A = c_A x^{|A|-ν}` and the vanishing `d_A = 0` for `A ∈ E` are
`FrameTransform.expCoeff_div`; "this is enough for that we have the same `E`-set" is
`FrameTransform.frameESet_eq_of_polynomials` (the extension `k → k₁` is an isomorphism, so the
`E`-sets of `I` and `I'` correspond under it; the general form of Remark 1 is not needed here).
(3) The last paragraph (Lemma 18 for `P = M₁`, Lemma 8) is as printed, with its hypotheses verified
(below).

The `E`-set comparison between `R₁` and `R̃₁` in step (1) is Remark 1 of §7 for the residue field
extension `k₁ → k̃₁` (`FrameTransform.frameESet_lift`, `eSet_map_of_injective`).  The paper does
not mention it: it is hidden in its unargued sentence "the conclusions (a) and (b) are replaced by
equivalent ones" (the paper's reduced case has `k = k₁`, where it is not needed).  Without it the
comparison of (a) for `R₁` and for `R̃₁` does not go through, since the `E`-sets are taken with
respect to different residue fields; it is therefore part of the gap filled below.

Deviation from the paper (gap filled): the paper does not say how its
reduction acts on the objects of the argument.  Lean proves: the hypotheses (1)–(10) hold for the
lifted data; the canonical map `γ : S₁ → S̃₁` exists (`β̃ ∘ γ = β_L ∘ β`: both are ring
homomorphisms `S₁ → R̃₁` which agree on `S`, and every element of `S₁ ⊆ Frac S` is a quotient of elements of `S`);
the expansion coefficients and the `E`-sets are compatible with it.  Completeness of `R̃` is not
used by the argument of step (2) (the expansion map of a frame exists for every `R`).

Deviation from the paper (gap filled): in the last step the paper invokes Lemma 18 of §7 for
`(R₁, J₁, (S₁; w), P = M₁)` without checking its hypotheses.  They are proved here: (i) `J₁ ⊆ M₁`
and `M₁` is a permissible center for `J₁` (from (10) for `j = 1`: `ν(J₁) = ν(J) ≥ 1`); (ii)
`g_j ∈ J₁`, `g ∈ J₁` (definition of the strict transform, with (6)); (iii)
`ν_{M₁}(g_j) = ν^{(j)}(J₁)` (from (9) and (10)); (iv) the first hypothesis of Lemma 18, that
`(g₁, …, g_i)` can be extended to a standard base of `J₁`, which the paper does not mention: the
initial forms `ψ_j = φ_j(W)` are successively independent because the `φ_j` are (a standard base
begins with `(f₁, …, f_i, f)`; retraction `gr_{M₁}(R₁) → k₁[W]` and descent of ideal membership
`FrameTransform.initialForm_notMem_span_of_polynomials`), and `(g₁, …, g_i)` then extends to a
standard base by repeated application of `extendsToStandardBase_snoc`
(`extendsToStandardBase_of_forall_initialForm_notMem_span`); (v) `g ≠ 0` (from (1)), needed for the
second assertion of Lemma 18 as corrected.  Finally Lemma 8 of §3, stated for ideals, is applied to
the principal ideal `(f)`, whose weak transform is `(g)`, to get `ν_{M₁}(g) ≤ ν_{i+1}`
(`ordElem_le_of_pow_mul_eq_toRing`): its hypotheses are `R/P` regular (from (4)),
`ν_P(f) = ν_M(f)` (from (6) and (1)) and `R₁` residually algebraic over `R` (from residual
rationality). -/
@[blueprint "lem:III.20"
  (statement := /-- Let $R$ be a regular local ring, $J$ an ideal in $R$ and
    $(S;z_1,\dots,z_r)$ a regular frame in $R$ (\cref{def:III.9}). Let $(f_1,\dots,f_i,f)$ be a
    system of elements of $J$ such that
    \begin{enumerate}
      \item[(1)] $(f_1,\dots,f_i,f)$ can be extended to a standard base of $J$
        (\cref{def:III.7-extends-standard-base}),
      \item[(2)] $\tau_{(z)}(f_j)=0$ for $1\le j\le i$ where $(z)=(z_1,\dots,z_r)$
        (\cref{def:III.10-star}), and
      \item[(3)] $f$ is normalized by $(f_1,\dots,f_i)$ with respect to $(S;z_1,\dots,z_r)$
        (\cref{def:III.9}).
    \end{enumerate}
    Let $P$ be a prime ideal in $R$ such that
    \begin{enumerate}
      \item[(4)] $P$ is a permissible center for $J$ (\cref{def:III.8}),
      \item[(5)] $P\supseteq(z_1,\dots,z_r)R$, and
      \item[(6)] $\nu_P(f_j)=\nu^{(j)}(J)$ for $1\le j\le i$ and $\nu_P(f)=\nu^{(i+1)}(J)$
        (\cref{def:III.1}).
    \end{enumerate}
    Let $R_1$ be a monoidal transform of $R$ with center $P$
    (\cref{def:III.2-monoidal-transform}) which is residually separable algebraic over $R$,
    and $J_1$ the strict transform of $J$ in $R_1$ (\cref{def:III.5-strict}). Suppose we have
    an element $x\in P\cap S$ such that
    \begin{enumerate}
      \item[(7)] $PR_1=(x)R_1$ and $(S;z_1,\dots,z_r)$ admits a frame transform
        $(S_1;w_1,\dots,w_r)$ in $R_1$ with denominator $x$ ($w_j=z_j/x$ for $1\le j\le r$)
        (\cref{def:III.8-frame-transform}),
      \item[(8)] $\tau_{(w)}(g_j)=0$ for $1\le j\le i$ where $g_j=x^{-\nu_j}f_j$ with
        $\nu_j=\nu^{(j)}(J)$ and $(w)=(w_1,\dots,w_r)$, and
      \item[(9)] $\nu_{M_1}(g_j)=\nu^{(j)}(J)$ for $1\le j\le i$, where $M_1$ denotes the
        maximal ideal of $R_1$.
    \end{enumerate}
    Let $g=x^{-\nu_{i+1}}f$ with $\nu_{i+1}=\nu^{(i+1)}(J)$. Then we have that
    \begin{enumerate}
      \item[(a)] $g$ is normalized by $(g_1,\dots,g_i)$ with respect to $(S_1;w_1,\dots,w_r)$.
    \end{enumerate}
    If we assume, in addition, that
    \begin{enumerate}
      \item[(10)] $\nu^{(j)}(J_1)=\nu^{(j)}(J)$ for $1\le j\le i+1$,
    \end{enumerate}
    then we have that
    \begin{enumerate}
      \item[(b)] $(g_1,\dots,g_i,g)$ can be extended to a standard base of $J_1$.
    \end{enumerate}
    (Lemma 20, p.~254.)

    (Formalization note: $x\in P\cap S$ is an element of $S$ whose image in $R$ lies in $P$;
    the frame transform with denominator $x$ is a frame transform in the sense of
    \cref{def:III.8-admits-frame-transform} whose denominator is the image of $x$ in $R_1$;
    $x^{-\nu}h$ is the element $y$ of $R_1$ with $x^\nu y=h$; the integers $\nu_j$ are carried
    by a function with $\nu_j=\nu^{(j)}(J)$, which records their finiteness; that $R\to R_1$ is
    local and that $R_1$ is a regular local ring are lemmas of \S2 taken as hypotheses.) -/)
  (proof := /-- Let $S\to\tilde S$ be any local homomorphism such that a regular system of
    parameters of $S$ is transformed into such a system of parameters of $\tilde S$ and that
    the residue field of $\tilde S$ is separable algebraic over that of $\tilde S$ [sic; read:
    over that of $S$]. Then $S\to\tilde S$ induces in a canonical manner a local homomorphism
    $R\to\tilde S\{z_1,\dots,z_r\}$ which also has the same properties as $S\to\tilde S$. If
    we replace $S$ by $\tilde S$, $R$ by $\tilde R=\tilde S\{z_1,\dots,z_r\}$, and $P$ and $J$
    by their extensions in $\tilde R$, and $R_1$ by a monoidal transform $\tilde R_1$ of
    $\tilde R$ with center $P\tilde R$ which admits a canonical local homomorphism
    $R_1\to\tilde R_1$, all the assumptions (1)--(10) remain valid, and the conclusions (a)
    and (b) are replaced by equivalent ones. Therefore we may assume that $R$ and $S$ are
    complete and that $R_1$ is residually rational over $R$. Let $M$ be the maximal ideal of
    $R$ and $k=R/M$. Let $(Z)=(Z_1,\dots,Z_r)$ be the system of initial forms of
    $(z_1,\dots,z_r)$ in $\operatorname{gr}_M(R)$. Let $\varphi_j$ be the initial form of
    $f_j$ in $\operatorname{gr}_M(R)$, which by (2) belongs to the $k$-subalgebra $k[Z]$ of
    $\operatorname{gr}_M(R)$ for $1\le j\le i$. Let $I=(\varphi_1,\dots,\varphi_i)k[Z]$, and
    $E$ the $E$-set of $I$ with respect to $(k;Z_1,\dots,Z_r)$. By (3), in the power series
    expansion
    $$f=\sum_{A\in\mathbb Z^r_0}c_Az^A\qquad\text{with }c_A\in S,$$
    we have $c_A=0$ for all $A\in E$. Then we have
    $$g=\sum_{A\in\mathbb Z^r_0}d_Aw^A$$
    with $d_A=c_Ax^{|A|-\nu_{i+1}}\in S_1$. Hence $d_A=0$ for all $A\in E$. Hence, to prove
    (a), we have only to show that, if $\psi_j$ is the initial form of $g_j$ in
    $\operatorname{gr}_{M_1}(R_1)$ where $M_1$ denotes the maximal ideal of $R_1$ and if
    $I'=(\psi_1,\dots,\psi_i)k[W]$, then $E$ is also the $E$-set of $I'$ with respect to
    $(k,W_1,\dots,W_r)$, where $(W_1,\dots,W_r)$ is the system of initial forms of
    $(w_1,\dots,w_r)$ in $\operatorname{gr}_{M_1}(R_1)$. We have assumed that $R_1$ is
    residually rational over $R$, hence, $S_1$ is so over $S$. Hence we can find a minimal base
    $(x,x_1,\dots,x_t)$ of $P\cap S$ such that $x_j/x$ is a non-unit of $S_1$ for
    $1\le j\le t$. Then we can extend $(x,x_1,\dots,x_t)$ to a regular system of parameters
    $(x,x_1,\dots,x_t,y_1,\dots,y_s)$ of $S$, so that
    $(z_1,\dots,z_r,x,x_1,\dots,x_t,y_1,\dots,y_s)$ is a regular system of parameters of $R$
    and that
    $$(w_1,\dots,w_r,x,u_1,\dots,u_t,y_1,\dots,y_s)$$
    is a regular system of parameters of $R_1$, where $u_j=x_j/x$ for $1\le j\le t$. (See
    (7).) Let $Z_j$ (resp.\ $X$, resp.\ $X_j$, resp.\ $Y_j$) be the initial form of $z_j$
    (resp.\ $x$, resp.\ $x_j$, resp.\ $y_j$) in $\operatorname{gr}_M(R)$. Then
    $$\operatorname{gr}_M(R)=k[Z_1,\dots,Z_r,X,X_1,\dots,X_t,Y_1,\dots,Y_s].$$
    Let $W_j$ (resp.\ $X$, resp.\ $U_j$, resp.\ $Y_j$) be the initial form of $w_j$ (resp.\
    $x$, resp.\ $u_j$, resp.\ $y_j$) in $\operatorname{gr}_{M_1}(R_1)$. Then
    $$\operatorname{gr}_{M_1}(R_1)=k[W_1,\dots,W_r,X,U_1,\dots,U_t,Y_1,\dots,Y_s].$$
    By (9), we have
    $$\psi_j=\varphi_j(W_1,\dots,W_r)+\lambda_j\qquad\text{for }1\le j\le i$$
    where $\lambda_j\in(X,Y_1,\dots,Y_s)\operatorname{gr}_{M_1}(R_1)$. (See the proof of
    Lemma~14 of \S5, \cref{lem:III.14}.) Therefore the assumption (8) implies that
    $$\psi_j=\varphi_j(W_1,\dots,W_r)\qquad\text{for }1\le j\le i.$$
    This is enough for that we have the same $E$-set of $I$ with respect to
    $(k;Z_1,\dots,Z_r)$ as that of $I'$ with respect to $(k;W_1,\dots,W_r)$. Hence (a) is
    proved. Now, in view of the first assertion of Lemma~18 of \S7 (\cref{lem:III.18}) (for
    the case in which $P=$ the maximal ideal $M_1$ of $R_1$), (a) and (10) imply
    $\nu_{M_1}(g)\ge\nu_{i+1}$. But, since $\nu_M(f)=\nu_{i+1}$, this implies
    $\nu_{M_1}(g)=\nu_{i+1}$. (See Lemma~8 of \S3, \cref{lem:III.8}.) Then (b) follows by the
    second assertion of Lemma~18 of \S7. \qed

    \textbf{Formalization: the printed route.} The base change
    $S\to\tilde S$, $R\to\tilde R=\tilde S\{z\}$, $R_1\to\tilde R_1$ is carried out ($\tilde S$
    complete with separably closed residue field, $\tilde R_1$ the canonical lift of $R_1$,
    residually rational, with the lifted frame transform); the assumptions (1)--(10) are verified
    for the lifted data, and the conclusions (a) and (b) for $\tilde R_1$ imply those for $R_1$
    (``replaced by equivalent ones''): there is a canonical homomorphism
    $\gamma\colon S_1\to\tilde S_1$ of the coefficient rings of the two frame transforms (two
    homomorphisms $S_1\to\tilde R_1$ that agree on $S$ agree, since every element of $S_1\subseteq
    \operatorname{Frac}S$ is a quotient of elements of $S$), the expansion coefficients correspond,
    $c_A(\beta_L h)=\gamma(c_A(h))$, the $E$-sets correspond (Remark~1 \cref{rem:III.7-1} for
    $k_1\to\tilde k_1$; the paper does not mention it, its reduced case has $k=k_1$), and the
    initial forms of $g_j$ are successively independent because their images are. For complete
    $R$ and residually rational $R_1$ the proof is the printed one: the
    coordinates, $\psi_j=\varphi_j(W_1,\dots,W_r)+\lambda_j$ with
    $\lambda_j\in(X,Y_1,\dots,Y_s)\operatorname{gr}_{M_1}(R_1)$, and $\lambda_j=0$ by (8);
    $k=k_1$, so the $E$-sets of $I$ and $I'$ correspond under the isomorphism $k\to k_1$.
    Completeness is not used (the expansion map exists for every regular frame).

    \textbf{Deviation from the paper (gap filled).} The hypotheses of Lemma~18 for
    $(R_1,J_1,(S_1;w_1,\dots,w_r),P=M_1)$ are verified: $J_1\subseteq M_1$ and $M_1$ is a
    permissible center for $J_1$ (from (10) for $j=1$), $g_j,g\in J_1$,
    $\nu_{M_1}(g_j)=\nu^{(j)}(J_1)$, and, not mentioned in the paper, that $(g_1,\dots,g_i)$ can be
    extended to a standard base of $J_1$: the initial forms $\psi_j=\varphi_j(W)$ are successively
    independent because the $\varphi_j$ are (retraction $\operatorname{gr}_{M_1}(R_1)\to k_1[W]$,
    $k\cong k_1$), so $(g_1,\dots,g_i)$ extends to a standard base. Also
    $g\ne0$ (from (1)) is needed for the second assertion of Lemma~18 as corrected, and Lemma~8
    (stated for ideals) is applied to the principal ideal $(f)$, whose weak transform is $(g)$. -/)
  (latexEnv := "lemma")]
theorem isNormalizedBy_frameTransform_and_extendsToStandardBase [Hironaka.HironakaCitedResults.{u}] (J : Ideal R)
    (F : RegularFrame R) {i : ℕ} (f : Fin i → R) (f' : R) (hfJ : ∀ j, f j ∈ J) (hf'J : f' ∈ J)
    (h1 : ExtendsToStandardBase J (Fin.snoc f f' : Fin (i + 1) → R))
    (h2 : ∀ j : Fin i, tauZ R F.z (fun _ : Fin 1 => f j) = 0)
    (h3 : F.IsNormalizedBy f f')
    (P : Ideal R) [P.IsPrime] (h4 : IsPermissibleCenter R J P) (h5 : F.idealZ ≤ P)
    (h6 : ∀ j : Fin i, Ideal.ordElem P (f j) = nuI R J (j : ℕ).succPNat)
    (h6' : Ideal.ordElem P f' = nuI R J i.succPNat)
    (T : MonoidalTransform R P) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing)
    (x : F.S) (hxP : algebraMap F.S R x ∈ P)
    (h7 : P.map T.toRing = Ideal.span {T.toRing (algebraMap F.S R x)})
    (FT : F.FrameTransform T) (h7' : FT.x = T.toRing (algebraMap F.S R x))
    (ν : Fin (i + 1) → ℕ) (hν : ∀ j : Fin (i + 1), (ν j : ℕ∞) = nuI R J (j : ℕ).succPNat)
    (g : Fin i → T.ring)
    (hg : ∀ j : Fin i, T.toRing (algebraMap F.S R x) ^ ν j.castSucc * g j = T.toRing (f j))
    (h8 : ∀ j : Fin i, tauZ T.ring FT.w (fun _ : Fin 1 => g j) = 0)
    (h9 : ∀ j : Fin i, Ideal.ordElem (maximalIdeal T.ring) (g j) = nuI R J (j : ℕ).succPNat)
    (g' : T.ring) (hg' : T.toRing (algebraMap F.S R x) ^ ν (Fin.last i) * g' = T.toRing f') :
    FT.toRegularFrame.IsNormalizedBy g g' ∧
      ((∀ j : ℕ+, (j : ℕ) ≤ i + 1 → nuI T.ring (strictTransformIdeal T J) j = nuI R J j) →
        ExtendsToStandardBase (strictTransformIdeal T J)
          (Fin.snoc g g' : Fin (i + 1) → T.ring)) := by
  classical
  obtain ⟨E⟩ := CompleteSepClosedExtension.nonempty F.S
  set α := F.baseChangeHom E.hom with hαdef
  have hα : RingHom.MapsRSOP α := F.mapsRSOP_baseChangeHom E.hom E.mapsRSOP
  have hsepα : RingHom.IsResiduallySeparableAlgebraic α :=
    F.isResiduallySeparableAlgebraic_baseChangeHom E.hom E.isResiduallySeparableAlgebraic
  have hsepα' := hsepα.isResiduallySeparable
  have hJP : J ≤ P := by
    rcases h4 with hPtop | ⟨-, hJP, -, -⟩
    · exact absurd hPtop (Ideal.IsPrime.ne_top ‹P.IsPrime›)
    · exact hJP
  have hreg : IsRegularLocalRing (R ⧸ P) := by
    rcases h4 with hPtop | ⟨-, -, hreg, -⟩
    · exact absurd hPtop (Ideal.IsPrime.ne_top ‹P.IsPrime›)
    · exact hreg
  obtain ⟨L⟩ := BaseChangeLift.nonempty hα T
  obtain ⟨hPp, hPq⟩ := RingHom.MapsRSOP.isPrime_map_and_isRegularLocalRing_quotient hα
    (inferInstance : P.IsPrime) hreg
  have := hPp
  have := hPq
  have := L.isRegularLocalRing hα
  have := L.isLocalHom_toRing
  have hβ := L.mapsRSOP_β hα hsepα
  have _ : IsSepClosed (ResidueField E.ring) := E.isSepClosed
  have _ : IsAdicComplete (maximalIdeal E.ring) E.ring := E.isAdicComplete
  have _ : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin F.r) E.ring))
      (MvPowerSeries (Fin F.r) E.ring) := F.isAdicComplete_baseChange (S' := E.ring)
  have hrat := L.isResiduallyRational hα (F.isSepClosed_residueField_baseChange (S' := E.ring))
    hsep
  obtain ⟨FT', hFT'x, hFT'w⟩ := RegularFrame.FrameTransform.exists_baseChange E.mapsRSOP L FT x
    hxP h7 h7'
  have hFT'w' : FT'.w = fun j => L.β (FT.w j) := funext hFT'w
  have hνnu : ∀ j : ℕ+, nuI (MvPowerSeries (Fin F.r) E.ring) (J.map α) j = nuI R J j :=
    fun j => (nuI_map_eq_of_mapsRSOP α hα J j).symm
  have hf1 : ∀ j, initialForm (maximalIdeal R) (f j) ∈ Set.range (frameAlgHom F.z) := fun j =>
    F.initialForm_mem_range_frameAlgHom_of_tauZ_eq_zero (f j) (h2 j)
  have hxcomm : ∀ s : F.S, L.T'.toRing (algebraMap E.ring (MvPowerSeries (Fin F.r) E.ring)
      (E.hom s)) = L.β (T.toRing (algebraMap F.S R s)) := fun s =>
    L.toRing_algebraMap_baseChange s
  -- Lemma 20 for the complete `R̃` and the residually rational `R̃₁`
  have key := isNormalizedBy_frameTransform_and_extendsToStandardBase_of_isResiduallyRational
    (J.map α) (F.baseChange E.ring) (fun j => α (f j)) (α f')
    (fun j => Ideal.mem_map_of_mem _ (hfJ j)) (Ideal.mem_map_of_mem _ hf'J)
    (by
      have h := F.extendsToStandardBase_baseChangeHom E.mapsRSOP J _ h1
      convert h using 1
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [hαdef])
    (fun j => by
      have := F.tauZ_baseChangeHom E.mapsRSOP E.isResiduallySeparableAlgebraic
        (fun _ : Fin 1 => f j)
      exact this.trans (h2 j))
    (F.isNormalizedBy_baseChangeHom E.mapsRSOP f hf1 f' h3)
    (P.map α) ((Hironaka.isPermissibleCenter_map_iff α hα J P hJP).2.2.2.mp h4)
    (by
      rw [RegularFrame.idealZ, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, ← F.baseChangeHom_z' E.hom j]
      exact Ideal.mem_map_of_mem _ (h5 (Ideal.subset_span ⟨j, rfl⟩)))
    (fun j => by rw [ordElem_map_ideal_of_mapsRSOP α hα P, h6 j, hνnu])
    (by rw [ordElem_map_ideal_of_mapsRSOP α hα P, h6', hνnu])
    L.T' hrat (E.hom x) (F.algebraMap_mem_map_baseChangeHom x hxP)
    (L.map_eq_span_baseChange x h7) FT' hFT'x ν (fun j => by rw [hν j, hνnu])
    (fun j => L.β (g j))
    (fun j => by
      show L.T'.toRing (algebraMap E.ring (MvPowerSeries (Fin F.r) E.ring) (E.hom x)) ^
        ν j.castSucc * L.β (g j) = L.T'.toRing (α (f j))
      rw [hxcomm, ← map_pow, ← map_mul, hg j, L.toRing_baseChangeHom])
    (fun j => by
      rw [hFT'w']
      have := tauZ_map L.β hβ (L.isResiduallySeparableAlgebraic_β hα hsepα).isResiduallySeparable
        FT.w (fun _ : Fin 1 => g j)
      exact this.trans (h8 j))
    (fun j => by rw [ordElem_map_of_mapsRSOP L.β hβ, h9 j, hνnu])
    (L.β g') (by
      show L.T'.toRing (algebraMap E.ring (MvPowerSeries (Fin F.r) E.ring) (E.hom x)) ^
        ν (Fin.last i) * L.β g' = L.T'.toRing (α f')
      rw [hxcomm, ← map_pow, ← map_mul, hg', L.toRing_baseChangeHom])
  obtain ⟨hnorm, hext⟩ := key
  -- the conclusions for `R₁` follow from those for `R̃₁`
  obtain ⟨γ, hγ⟩ := FT.exists_gamma (RingHom.MapsRSOP.injective E.hom E.mapsRSOP) L FT'
  have hβinj : Function.Injective FT.β := fun s t h =>
    FT.quot_bijective.1 (by rw [RingHom.comp_apply, RingHom.comp_apply, h])
  have hγinj : Function.Injective γ := fun s t h =>
    hβinj (L.injective_β hα (by rw [← hγ, ← hγ, h]))
  refine ⟨?_, fun h10 => ?_⟩
  · -- (a)
    have hginit : ∀ j, initialForm (maximalIdeal T.ring) (g j) ∈
        Set.range (frameAlgHom FT.w) := fun j =>
      FT.toRegularFrame.initialForm_mem_range_frameAlgHom_of_tauZ_eq_zero (g j) (h8 j)
    have hE := FT.frameESet_lift L hβ FT' hFT'w g hginit
    rw [FT.toRegularFrame.isNormalizedBy_iff_expCoeff]
    have hnorm' := (FT'.toRegularFrame.isNormalizedBy_iff_expCoeff _ _).mp hnorm
    intro A hA
    have h1' := hnorm' A (hE ▸ hA)
    have h2 := FT.expCoeff_lift L FT' γ hγ hFT'w g' (Finsupp.equivFunOnFinite.symm A)
    exact hγinj ((h2.symm.trans h1').trans (map_zero γ).symm)
  · -- (b)
    have hg0 : ∀ j : Fin i, FT.x ^ ν j.castSucc * g j = T.toRing (f j) := fun j => by
      rw [h7']; exact hg j
    have hgJ : ∀ j : Fin i, g j ∈ strictTransformIdeal T J := fun j =>
      Ideal.subset_span ⟨FT.x, FT.span_x, f j, hfJ j, ν j.castSucc,
        ((hν j.castSucc).trans (h6 j).symm).le, hg0 j⟩
    have hg'J : g' ∈ strictTransformIdeal T J :=
      Ideal.subset_span ⟨FT.x, FT.span_x, f', hf'J, ν (Fin.last i),
        ((hν (Fin.last i)).trans h6'.symm).le, by rw [h7']; exact hg'⟩
    have h10' : ∀ j : ℕ+, (j : ℕ) ≤ i + 1 →
        nuI L.T'.ring (strictTransformIdeal L.T' (J.map α)) j =
          nuI (MvPowerSeries (Fin F.r) E.ring) (J.map α) j := fun j hj => by
      rw [L.nuI_strictTransformIdeal hα hsepα J hJP j, h10 j hj, hνnu]
    have hext' := hext h10'
    rw [L.strictTransformIdeal_map hα J hJP] at hext'
    refine extendsToStandardBase_of_map L.β hβ (strictTransformIdeal T J)
      (Fin.snoc g g' : Fin (i + 1) → T.ring) (fun j => ?_) ?_
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hg'J
      · simpa using hgJ j
    · convert hext' using 1
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp


end Lemma20

section CoreMain

open MvPolynomial
open scoped Classical

attribute [local instance] RegularFrame.isDomain_S
attribute [local instance] Ideal.Quotient.field

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

omit [IsRegularLocalRing R] [IsDomain R] in
theorem ordElem_le_of_le_of_ordElem {I I' : Ideal R} (hII' : I ≤ I') {e : R} {n : ℕ}
    (h : Ideal.ordElem I' e = n) : Ideal.ordElem I e ≤ n := by
  refine Ideal.ordElem_le_of_notMem (m := n) fun hmem => ?_
  have h1 : e ∈ I' ^ (n + 1) := Ideal.pow_right_mono hII' (n + 1) hmem
  have h2 := Ideal.le_ordElem h1
  rw [h] at h2
  exact absurd (by exact_mod_cast h2 : n + 1 ≤ n) (by omega)

/-- **Lemma 21 for complete `R` and residually rational `R₁`** (the proof of Lemma 21, p. 256,
begins "As in the proof of Lemma 20, we may assume that `S` and `R` are complete, and that `R₁` is
residually rational over `R`"): the core of the proof, pp. 256–258, along the printed route.

* The regular systems of parameters `(z, x_k, x, y)` of `R` and `(w, u, x, y)` of `R₁` of p. 256
  (`RegularFrame.FrameTransform.exists_coordinates`), the identifications `gr_M(R) = k[Z, X, Y]`,
  `gr_{M₁}(R₁) = k[W, U, X, Y]` (`gradedSemiModel`, semilinear because `k` and `k₁` are only
  identified through the residual rationality of `R₁`) and the comparison of the initial forms of
  `f_{i+j}` and `g_{i+j} = x^{-ν} f_{i+j}` (`forms_correspond`; `exists_models`).
* The group `f_{i+1}, …, f_{i+p}` of p. 256 (`RegularFrame.exists_normalized_group`, from Lemma 17;
  `f_{i+1} = f'`), Lemma 18 (`ν_P(f_{i+j}) = μ^{(a)}(J)`, `ordElem_ge_nuI_of_isNormalizedBy`),
  Lemma 20 for each `f_{i+j}` (`isNormalizedBy_frameTransform_and_extendsToStandardBase`) and
  Lemma 19 for the `g_{i+j}` on the `R₁` side
  (`RegularFrame.initialForm_mem_adjoin_tauSubmodule_sup`).
* "`T_a` must contain `Z_1, …, Z_r`, by (1), (2) and (11)" (p. 256): `hZTa`, proved first, before the
  claim `T_a ⊆ ⟨Z, X_1, …, X_t⟩` (which is `hT₀U` in `core_assembly_printed`).
* Lemma 19 on the `R`-side, "`φ ∈ k[Z_1, …, Z_r, X_1, …, X_τ]`" (p. 257): `hφG`.
* "`T*` contains `W₁, …, W_r`" (`hWle`).
* The choice of the coordinates, "we could choose the system `(x_1, …, x_t)` in such a way that …
  `T_a` is generated by `Z_1, …, Z_r, X_1, …, X_τ`" and "We may assume that
  `φ ∈ k[Z_1, …, Z_r, X_1, …, X_τ̄]`", the forms `L_k`, the isomorphism `T*_a → T_a`, "zero is the
  only element in the intersection of the algebra `k[W, U_1 + L_1, …]` and of the ideal
  `(X, Y_1, …, Y_s) gr_{M₁}(R₁)`. Therefore we must have `ψ = φ(W_1, …, W_r, U_1 + L_1, …,
  U_τ̄ + L_τ̄)`" and "This shows that `τ_{(w)}(g) = τ_{(z)}(f)`": `core_instantiate_printed`
  (`core_assembly_printed`, `exists_blockAut_adapted`, `core_adapted_poly`; `Compat/TauZAdapted.lean`).

Deviation from the paper (gaps filled).
(i) "`T_a` must contain `Z₁, …, Z_r`, by (1), (2) and (11)" and "`T*` contains `W₁, …, W_r` … by
(8) and (b)" use that the space `T` of Definition 10* does not grow when the system `(f₁, …, f_i)`
is completed to the `f₁, …, f_{i+p}`.  This is false for arbitrary systems (`φ₁ = X(X+Y)`,
`φ₂ = X+Y`); for initial segments of a standard base it is
`isTauZSubmodule_prefix_of_isTauSubmodule`, proved here (via Lemma 15's decomposition
`AssocGraded.exists_proj_eq_add_of_mem_span`).  (ii) "Any permutation of the `p` elements
preserves these properties": Lemmas 19 and 20 are applied to each `f_{i+j}` separately; that
`(f₁, …, f_i, f_{i+j})` can be extended to a standard base is obtained from
`extendsToStandardBase_snoc`.  That replacing members of a standard base by `G_j - Σ h_{jl} f_l`
(Lemma 17) gives again a standard base (`isStandardBase_replace`) is not argued in the paper.
(iii) The choice of the system `(x₁, …, x_t)` is carried out on the polynomial pictures
`gr_M(R) = k[Z, X_1, …, X_t, X, Y]`, `gr_{M₁}(R₁) = k[W, U, X, Y]`: a `k`-linear transformation of
`(x₁, …, x_t)` changes both identifications by the same `k`-linear change of the variables
`X_j`, `U_j` (the two pictures are composed with it, `SemiModel.comp`); the regular system of
parameters of `R` is not itself replaced.  (iv) The existence of a regular
system of `a`-th `τ`-parameters of `R₁` for `J₁` (to apply Lemma 19) is Lemma 11 for `P = M₁`,
restricted from the `t`-th to the `a`-th system; `a ≤ t(J₁)` and `μ^{(a)}(J₁) = ν^{(i+1)}(J₁)`
follow from (10) (`mu_eq_of_nuI_eq_prefix`).  (v) The number of the linear forms `L_k` is printed
`τ̄` on p. 257; it is `τ = τ^{(a)}(J) - r` (misprint). -/
theorem tauZ_eq_tauZ_frameTransform_of_isAdicComplete [Hironaka.HironakaCitedResults.{u}] [IsAdicComplete (maximalIdeal R) R]
    (J : Ideal R) (F : RegularFrame R) {i : ℕ} (f : Fin i → R)
    (f' : R) (hfJ : ∀ j, f j ∈ J) (hf'J : f' ∈ J)
    (h1 : ExtendsToStandardBase J (Fin.snoc f f' : Fin (i + 1) → R))
    (h2 : ∀ j : Fin i, tauZ R F.z (fun _ : Fin 1 => f j) = 0)
    (h3 : F.IsNormalizedBy f f')
    (P : Ideal R) [P.IsPrime] (h4 : IsPermissibleCenter R J P) (h5 : F.idealZ ≤ P)
    (h6 : ∀ j : Fin i, Ideal.ordElem P (f j) = nuI R J (j : ℕ).succPNat)
    (h6' : Ideal.ordElem P f' = nuI R J i.succPNat)
    (T : MonoidalTransform R P) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing)
    (x : F.S) (hxP : algebraMap F.S R x ∈ P)
    (h7 : P.map T.toRing = Ideal.span {T.toRing (algebraMap F.S R x)})
    (FT : F.FrameTransform T) (h7' : FT.x = T.toRing (algebraMap F.S R x))
    (ν : Fin (i + 1) → ℕ) (hν : ∀ j : Fin (i + 1), (ν j : ℕ∞) = nuI R J (j : ℕ).succPNat)
    (g : Fin i → T.ring)
    (hg : ∀ j : Fin i, T.toRing (algebraMap F.S R x) ^ ν j.castSucc * g j = T.toRing (f j))
    (h8 : ∀ j : Fin i, tauZ T.ring FT.w (fun _ : Fin 1 => g j) = 0)
    (h9 : ∀ j : Fin i, Ideal.ordElem (maximalIdeal T.ring) (g j) = nuI R J (j : ℕ).succPNat)
    (g' : T.ring) (hg' : T.toRing (algebraMap F.S R x) ^ ν (Fin.last i) * g' = T.toRing f')
    (h10 : ∀ j : ℕ+, (j : ℕ) ≤ i + 1 → nuI T.ring (strictTransformIdeal T J) j = nuI R J j)
    (a : ℕ) (ha : 1 ≤ a) (hat : a ≤ t R J) (hμ : (mu R J a : ℕ∞) = nuI R J i.succPNat)
    (h11 : tauZ R (![] : Fin 0 → R) f = F.r)
    (h12 : tau T.ring (strictTransformIdeal T J) a = tau R J a) :
    tauZ R F.z (fun _ : Fin 1 => f') = tauZ T.ring FT.w (fun _ : Fin 1 => g') := by
  classical
  have hdom1 : IsDomain T.ring := Transforms.isDomain_of_isRegularLocalRing _
  have hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing :=
    RingHom.isResiduallySeparableAlgebraic_of_residueField_surjective hrat
  have hPtop : P ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  have hJP : J ≤ P := by
    rcases h4 with h | ⟨-, hJP, -, -⟩
    · exact absurd h hPtop
    · exact hJP
  have hPreg : IsRegularLocalRing (R ⧸ P) := by
    rcases h4 with h | ⟨-, -, hreg, -⟩
    · exact absurd h hPtop
    · exact hreg
  have hPM : P ≤ maximalIdeal R := le_maximalIdeal hPtop
  have hJM : J ≤ maximalIdeal R := hJP.trans hPM
  -- the orders of `f_j` and `f'`
  have hord : ∀ j : Fin (i + 1), Ideal.ordElem (maximalIdeal R)
      ((Fin.snoc f f' : Fin (i + 1) → R) j) = ν j := by
    obtain ⟨m, gs, him, hgs, hgsf⟩ := h1
    intro j
    have := ordElem_eq_nuI_of_isStandardBase J gs hgs (Fin.castLE him j)
    rw [hgsf] at this
    exact this.trans (hν j).symm
  have hordf : ∀ j : Fin i, Ideal.ordElem (maximalIdeal R) (f j) = ν j.castSucc := fun j => by
    have := hord j.castSucc
    rwa [Fin.snoc_castSucc] at this
  have hordf' : Ideal.ordElem (maximalIdeal R) f' = ν (Fin.last i) := by
    have := hord (Fin.last i)
    rwa [Fin.snoc_last] at this
  have hν1 : 1 ≤ ν (Fin.last i) := by
    have h1 : ((1 : ℕ) : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) f' :=
      Ideal.le_ordElem (by rw [pow_one]; exact hJM hf'J)
    rw [hordf'] at h1
    exact_mod_cast h1
  have hf'0 : f' ≠ 0 := fun h0 => by
    rw [h0, (Ideal.ordElem_eq_top_iff_eq_zero (maximalIdeal.isMaximal R).ne_top).mpr rfl] at hordf'
    exact ENat.top_ne_natCast _ hordf'
  have hg0 : ∀ j : Fin i, FT.x ^ ν j.castSucc * g j = T.toRing (f j) := fun j => by
    rw [h7']; exact hg j
  have hg'0 : FT.x ^ ν (Fin.last i) * g' = T.toRing f' := by rw [h7']; exact hg'
  have hFTx0 : FT.x ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega), zero_mul] at hg'0
    exact hf'0 (T.toRing_injective (by rw [← hg'0, map_zero]))
  have hcancel : ∀ (n : ℕ) (b c : T.ring), FT.x ^ n * b = FT.x ^ n * c → b = c :=
    fun n b c h => mul_left_cancel₀ (pow_ne_zero n hFTx0) h
  -- the strict transform
  set J₁ := strictTransformIdeal T J with hJ₁
  have hJ₁M : J₁ ≤ maximalIdeal T.ring := by
    have h := h10 1 (by simp)
    rw [(nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen T.ring J₁).1.2,
      (nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen R J).1.2] at h
    have h1le : 1 ≤ Ideal.nu J := ((Ideal.ord_basic _ J J J).2.1).mpr hJM
    exact ((Ideal.ord_basic _ J₁ J₁ J₁).2.1).mp (by rw [Ideal.nu] at h; rw [h]; exact h1le)
  have hextf : ExtendsToStandardBase J f := by
    obtain ⟨m, gs, him, hgs, hgsf⟩ := h1
    exact ⟨m, gs, by omega, hgs, fun j => by
      have := hgsf j.castSucc
      rwa [Fin.snoc_castSucc] at this⟩
  have hinit : ∀ j, initialForm (maximalIdeal R) (f j) ∈ F.assocSubalgebra := fun j =>
    F.initialForm_mem_adjoin_of_tauZ_eq_zero (f j) (h2 j)
  have hmonoν : ∀ j : Fin (i + 1), ν j ≤ ν (Fin.last i) := fun j => by
    have := nuI_mono J (show (j : ℕ).succPNat ≤ i.succPNat from
      PNat.coe_le_coe _ _ |>.mp (by simpa using Nat.lt_succ_iff.mp j.2))
    exact_mod_cast (hν j).trans_le (this.trans_eq (hν (Fin.last i)).symm)
  -- the elements `g_j` and `g'` lie in `J₁`
  have hν_P : ∀ j : Fin i, (ν j.castSucc : ℕ∞) ≤ Ideal.ordElem P (f j) := fun j =>
    ((hν j.castSucc).trans (h6 j).symm).le
  -- Lemma 20 for an arbitrary member `e` of the group
  have hel : ∀ e : R, e ∈ J → ExtendsToStandardBase J (Fin.snoc f e : Fin (i + 1) → R) →
      F.IsNormalizedBy f e → Ideal.ordElem (maximalIdeal R) e = ν (Fin.last i) →
      Ideal.ordElem P e = ν (Fin.last i) ∧
      ∃ ge : T.ring, FT.x ^ ν (Fin.last i) * ge = T.toRing e ∧
        FT.toRegularFrame.IsNormalizedBy g ge ∧
        ((∀ j : ℕ+, (j : ℕ) ≤ i + 1 → nuI T.ring J₁ j = nuI R J j) →
          ExtendsToStandardBase J₁ (Fin.snoc g ge : Fin (i + 1) → T.ring)) ∧
        ge ∈ J₁ := by
    intro e heJ he1 he3 heord
    have hPe_ge : nuI R J i.succPNat ≤ Ideal.ordElem P e :=
      (ordElem_ge_nuI_of_isNormalizedBy F J f hfJ hextf hinit e heJ he3 P h5 h4 h6).1
    have hPe_le : Ideal.ordElem P e ≤ ν (Fin.last i) := ordElem_le_of_le_of_ordElem hPM heord
    have hPe : Ideal.ordElem P e = ν (Fin.last i) := by
      refine le_antisymm hPe_le ?_
      rw [hν (Fin.last i)]
      exact hPe_ge
    refine ⟨hPe, ?_⟩
    have hePow : e ∈ P ^ ν (Fin.last i) := Ideal.mem_pow_of_ordElem hPe
    have hmem : T.toRing e ∈ Ideal.span {FT.x ^ ν (Fin.last i)} := by
      have := Ideal.mem_map_of_mem T.toRing hePow
      rwa [Ideal.map_pow, ← FT.span_x, Ideal.span_singleton_pow] at this
    obtain ⟨ge, hge⟩ := Ideal.mem_span_singleton'.mp hmem
    have hge' : FT.x ^ ν (Fin.last i) * ge = T.toRing e := by rw [mul_comm]; exact hge
    have hge'' : T.toRing (algebraMap F.S R x) ^ ν (Fin.last i) * ge = T.toRing e := by
      rw [← h7']; exact hge'
    obtain ⟨hnorm, hext⟩ := isNormalizedBy_frameTransform_and_extendsToStandardBase J F f e hfJ
      heJ he1 h2 he3 P h4 h5 h6 (hPe.trans (hν (Fin.last i))) T hsep x hxP h7 FT h7' ν hν g
      hg h8 h9 ge hge''
    refine ⟨ge, hge', hnorm, hext, ?_⟩
    exact Ideal.subset_span ⟨FT.x, FT.span_x, e, heJ, ν (Fin.last i),
      hPe.ge, hge'⟩
  have hgJ : ∀ j : Fin i, g j ∈ J₁ := fun j =>
    Ideal.subset_span ⟨FT.x, FT.span_x, f j, hfJ j, ν j.castSucc, hν_P j, hg0 j⟩
  -- the group `f_{i+1}, …, f_{i+p}` of the proof (p. 256)
  obtain ⟨m, hi, G, hG, hGf, hGi, hGnorm⟩ := F.exists_normalized_group J f f' h1 hinit h3
  obtain ⟨d0, hd0, hmono0⟩ := hG.2.2.1
  have hordG : ∀ j, Ideal.ordElem (maximalIdeal R) (G j) = d0 j := fun j =>
    ordElem_eq_of_isStandardBase_of_initialForm_mem_homogeneous J G hG d0 hd0 j
  have hmuν : mu R J a = ν (Fin.last i) := by
    have := hμ.trans (hν (Fin.last i)).symm
    exact_mod_cast this
  obtain ⟨N, hNm, hlow, hhigh⟩ := exists_initialSegment_length J G hG (mu R J a)
  have hiN : i < N := by
    by_contra hcon
    have := hhigh ⟨i, hi⟩ (by show N ≤ i; omega)
    rw [hGi, hordf', hmuν] at this
    exact lt_irrefl _ this
  have hdict := isTauSubmodule_iff_isTauZSubmodule_initialSegment J G hG hNm hlow hhigh
  set Gp : Fin N → R := fun j => G (Fin.castLE hNm j) with hGp
  set dN : Fin N → ℕ := fun j => d0 (Fin.castLE hNm j) with hdN
  have hGord : ∀ j, Ideal.ordElem (maximalIdeal R) (Gp j) = dN j := fun j => hordG _
  have hdμ : ∀ j, dN j ≤ mu R J a := fun j => by
    have := hlow (Fin.castLE hNm j) j.2
    rw [hordG] at this
    exact_mod_cast this
  have hGi' : Gp ⟨i, hiN⟩ = f' := hGi
  have hdNi : dN ⟨i, hiN⟩ = ν (Fin.last i) := by
    have := hGord ⟨i, hiN⟩
    rw [hGi', hordf'] at this
    exact_mod_cast this.symm
  have hdNge : ∀ j : Fin N, i ≤ (j : ℕ) → dN j = ν (Fin.last i) := by
    intro j hj
    have h1 : dN ⟨i, hiN⟩ ≤ dN j := hmono0 (Fin.mk_le_mk.mpr hj)
    have h2 := hdμ j
    rw [hmuν] at h2
    omega
  have hdNlt : ∀ (j : Fin N) (hj : (j : ℕ) < i), dN j = ν (Fin.castSucc ⟨j, hj⟩) := by
    intro j hj
    have := hGord j
    have hfj : Gp j = f ⟨j, hj⟩ := hGf ⟨j, hj⟩
    rw [hfj, hordf] at this
    exact_mod_cast this.symm
  set Tau₁ := tauSubmodule T.ring J₁ a with hTau₁
  set Wspan := Submodule.span (T.ring ⧸ maximalIdeal T.ring) (Set.range (frameForm FT.w))
    with hWspan
  obtain ⟨hat₁, hmu₁⟩ := mu_eq_of_nuI_eq_prefix J J₁ h10 ha hat hμ
  have hmu₁' : mu T.ring J₁ a = ν (Fin.last i) := by
    have := hmu₁.trans ((h10 i.succPNat (by simp)).trans (hν (Fin.last i)).symm)
    exact_mod_cast this
  have hex : ∀ j : Fin N, ∃ gj : T.ring, FT.x ^ dN j * gj = T.toRing (Gp j) ∧
      Ideal.ordElem (maximalIdeal T.ring) gj = dN j ∧ Ideal.ordElem P (Gp j) = dN j ∧
      initialForm (maximalIdeal T.ring) gj ∈ Algebra.adjoin (T.ring ⧸ maximalIdeal T.ring)
        ((Tau₁ ⊔ Wspan : Submodule (T.ring ⧸ maximalIdeal T.ring)
          (AssocGraded (maximalIdeal T.ring))) : Set (AssocGraded (maximalIdeal T.ring))) := by
    intro j
    by_cases hj : (j : ℕ) < i
    · have hfj : Gp j = f ⟨j, hj⟩ := hGf ⟨j, hj⟩
      refine ⟨g ⟨j, hj⟩, ?_, ?_, ?_, ?_⟩
      · rw [hdNlt j hj, hfj]
        exact hg0 ⟨j, hj⟩
      · rw [hdNlt j hj]
        exact (h9 ⟨j, hj⟩).trans (hν (Fin.castSucc ⟨j, hj⟩)).symm
      · rw [hdNlt j hj, hfj]
        exact (h6 ⟨j, hj⟩).trans (hν (Fin.castSucc ⟨j, hj⟩)).symm
      · have h1 := FT.toRegularFrame.initialForm_mem_adjoin_of_tauZ_eq_zero (g ⟨j, hj⟩)
          (h8 ⟨j, hj⟩)
        refine Algebra.adjoin_mono ?_ h1
        rintro _ ⟨l, rfl⟩
        exact (le_sup_right : Wspan ≤ Tau₁ ⊔ Wspan) (Submodule.subset_span ⟨l, rfl⟩)
    · have hj' : i ≤ (j : ℕ) := not_lt.mp hj
      have heJ : Gp j ∈ J := hG.1 _
      have hordA : Ideal.ordElem (maximalIdeal R) (Gp j) = ν (Fin.last i) := by
        rw [hGord j, hdNge j hj']
      have hirr : initialForm (maximalIdeal R) (Gp j) ∉ Ideal.span
          (Set.range fun l : Fin i => initialForm (maximalIdeal R) (f l)) := by
        intro hmem
        refine hG.2.2.2.2 (Fin.castLE hNm j) (Ideal.span_mono ?_ hmem)
        rintro _ ⟨l, rfl⟩
        refine ⟨⟨l, ?_⟩, ?_⟩
        · have := l.2
          show (l : ℕ) < (j : ℕ)
          omega
        · show initialForm (maximalIdeal R) (G ⟨l, lt_trans l.2 hi⟩) =
            initialForm (maximalIdeal R) (f l)
          rw [hGf l]
      have he1 : ExtendsToStandardBase J (Fin.snoc f (Gp j) : Fin (i + 1) → R) :=
        extendsToStandardBase_snoc J f (Gp j) hextf heJ (ν (Fin.last i)) hordA
          (fun l => by rw [hordf l]; exact_mod_cast hmonoν l.castSucc) (hν (Fin.last i)).le hirr
      obtain ⟨hPe, ge, hge, hnorm, hext, hgeJ⟩ := hel (Gp j) heJ he1 (hGnorm _ hj') hordA
      have hext10 := hext h10
      have hordge : Ideal.ordElem (maximalIdeal T.ring) ge = ν (Fin.last i) := by
        obtain ⟨m₁, gs₁, him₁, hgs₁, hgsf₁⟩ := hext10
        have := ordElem_eq_nuI_of_isStandardBase J₁ gs₁ hgs₁ (Fin.castLE him₁ (Fin.last i))
        rw [hgsf₁, Fin.snoc_last] at this
        exact this.trans ((h10 _ (by simp)).trans (hν (Fin.last i)).symm)
      refine ⟨ge, by rw [hdNge j hj']; exact hge, by rw [hdNge j hj']; exact hordge,
        by rw [hdNge j hj']; exact hPe, ?_⟩
      exact FT.toRegularFrame.initialForm_mem_adjoin_tauSubmodule_sup J₁ hJ₁M g hgJ
        (fun j => h8 j) ge hgeJ a ha hat₁ hmu₁ hext10 hnorm
  choose gf hgf_rel hgf_ord hgf_P hgf_adj using hex
  -- the first assertion on `T*`: `W₁, …, W_r ∈ T_a(J₁)` (p. 257)
  have hl20 := isNormalizedBy_frameTransform_and_extendsToStandardBase J F f f' hfJ hf'J h1 h2 h3
    P h4 h5 h6 h6' T hsep x hxP h7 FT h7' ν hν g hg h8 h9 g' hg'
  have hext10 := hl20.2 h10
  have hWle : Wspan ≤ Tau₁ := by
    obtain ⟨n, M, M₁, U, Zv, hhom, hhom₁, hZv, hZ, hZ₁, hforms⟩ :=
      exists_models FT hrat x hxP h7' hFTx0
    obtain ⟨m₁, G₁, him₁, hG₁, hG₁g⟩ := hext10
    have hTau := (tauSubmodule_spec T.ring J₁ a ha hat₁).1
    have hG₁j : ∀ j : Fin i, G₁ (Fin.castLE (by omega : i ≤ m₁) j) = g j := fun j => by
      have := hG₁g j.castSucc
      rwa [Fin.snoc_castSucc] at this
    have hlowG : ∀ j : Fin m₁, (j : ℕ) < i →
        Ideal.ordElem (maximalIdeal T.ring) (G₁ j) ≤ (mu T.ring J₁ a : ℕ∞) := by
      intro j hj
      have : G₁ j = g ⟨j, hj⟩ := hG₁j ⟨j, hj⟩
      have h1' : (ν (Fin.castSucc ⟨j, hj⟩) : ℕ∞) ≤ (mu T.ring J₁ a : ℕ∞) := by
        rw [hmu₁']; exact_mod_cast hmonoν _
      rw [this, h9 ⟨j, hj⟩]
      exact (hν (Fin.castSucc ⟨j, hj⟩)).symm.le.trans h1'
    have hprefix := isTauZSubmodule_prefix_of_isTauSubmodule J₁ G₁ hG₁ (m' := i) (by omega)
      hlowG hTau
    have hfam : (fun j : Fin i => G₁ (Fin.castLE (by omega : i ≤ m₁) j)) = g := funext hG₁j
    rw [hfam] at hprefix
    have hTg_le : tauZSubmodule T.ring g ≤ Tau₁ := sInf_le hprefix
    -- `T(g₁, …, g_i) = ⟨W⟩`: (11) gives the rank
    have hWsup : ∀ j : Fin i, M₁.Φ.symm (initialForm (maximalIdeal T.ring) (g j)) ∈
        supported (T.ring ⧸ maximalIdeal T.ring) Zv := by
      intro j
      have h1' := FT.toRegularFrame.initialForm_mem_adjoin_of_tauZ_eq_zero (g j) (h8 j)
      have h2' : initialForm (maximalIdeal T.ring) (g j) ∈ Algebra.adjoin
          (T.ring ⧸ maximalIdeal T.ring) (Wspan : Set (AssocGraded (maximalIdeal T.ring))) := by
        refine Algebra.adjoin_mono ?_ h1'
        rintro _ ⟨l, rfl⟩
        exact Submodule.subset_span ⟨l, rfl⟩
      have h3' := (M₁.mem_adjoin_pull_iff Wspan (M₁.Φ.symm (initialForm (maximalIdeal T.ring)
        (g j)))).mpr (by rw [RingEquiv.apply_symm_apply]; exact h2')
      rw [hWspan, hZ₁] at h3'
      refine Algebra.adjoin_le ?_ h3'
      intro p hp
      have : Submodule.span (T.ring ⧸ maximalIdeal T.ring) (X '' Zv) ≤
          Subalgebra.toSubmodule (supported (T.ring ⧸ maximalIdeal T.ring) Zv) :=
        Submodule.span_le.mpr fun q hq => Algebra.subset_adjoin hq
      exact this hp
    have hq : ∀ j : Fin i, M₁.Φ.symm (initialForm (maximalIdeal T.ring) (g j)) =
        M.Φ.symm (initialForm (maximalIdeal R) (f j)) := by
      intro j
      have hPmem : f j ∈ P ^ ν j.castSucc :=
        Ideal.mem_pow_of_ordElem ((h6 j).trans (hν j.castSucc).symm)
      obtain ⟨hs, hdiff⟩ := hforms (ν j.castSucc) (f j) (g j) hPmem (hordf j)
        ((h9 j).trans (hν j.castSucc).symm) (hg0 j)
      have hsub : M₁.Φ.symm (initialForm (maximalIdeal T.ring) (g j)) -
          M.Φ.symm (initialForm (maximalIdeal R) (f j)) ∈
            supported (T.ring ⧸ maximalIdeal T.ring) U :=
        sub_mem (supported_mono hZv (hWsup j)) hs
      have h0 := (projOut_eq_zero_iff U _).mpr hdiff
      rw [projOut_of_mem_supported U hsub] at h0
      exact sub_eq_zero.mp h0
    have hdeg : ∀ j : Fin i, ∃ d ≤ ν (Fin.last i), initialForm (maximalIdeal R) (f j) ∈
        AssocGraded.homogeneous (maximalIdeal R) d := fun j => by
      refine ⟨ν j.castSucc, hmonoν _, ?_⟩
      rw [initialForm_eq_mk _ (hordf j)]
      exact AssocGraded.mk_mem_homogeneous _ _
    have hrk := tauZSubmodule_finrank_eq_of_models M M₁ hhom hhom₁ f g (ν (Fin.last i)) hdeg hq
    have hr : Module.finrank (R ⧸ maximalIdeal R) (tauZSubmodule R f) = F.r :=
      (tauZ_empty f).symm.trans h11
    obtain ⟨hli, hwo⟩ : LinearIndependent (T.ring ⧸ maximalIdeal T.ring) (frameForm FT.w) ∧
        ∀ l, Ideal.ordElem (maximalIdeal T.ring) (FT.w l) = ((1 : ℕ) : ℕ∞) :=
      linearIndependent_frameForm FT.toRegularFrame.z_injective FT.toRegularFrame.extends_rsop
    have hWrank : Module.finrank (T.ring ⧸ maximalIdeal T.ring) Wspan = F.r := by
      rw [hWspan, finrank_span_eq_card hli, Fintype.card_fin]
    have hWhom : Wspan ≤ AssocGraded.homogeneous (maximalIdeal T.ring) 1 := by
      rw [hWspan, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      show initialForm (maximalIdeal T.ring) (FT.w l) ∈ _
      rw [initialForm_eq_mk _ (hwo l)]
      exact AssocGraded.mk_mem_homogeneous _ _
    have hTgW : tauZSubmodule T.ring g ≤ Wspan := by
      refine tauZSubmodule_le_of_forall_mem_adjoin g Wspan hWhom fun j => ?_
      have h1' := FT.toRegularFrame.initialForm_mem_adjoin_of_tauZ_eq_zero (g j) (h8 j)
      refine Algebra.adjoin_mono ?_ h1'
      rintro _ ⟨l, rfl⟩
      exact Submodule.subset_span ⟨l, rfl⟩
    have hfd : FiniteDimensional (T.ring ⧸ maximalIdeal T.ring) Wspan :=
      FiniteDimensional.span_of_finite _ (Set.finite_range _)
    have heq : tauZSubmodule T.ring g = Wspan :=
      Submodule.eq_of_le_of_finrank_eq hTgW (by rw [hrk, hr, hWrank])
    rw [← heq]
    exact hTg_le
  have hψT : ∀ j, initialForm (maximalIdeal T.ring) (gf j) ∈ Algebra.adjoin
      (T.ring ⧸ maximalIdeal T.ring) (Tau₁ : Set (AssocGraded (maximalIdeal T.ring))) := fun j => by
    have := hgf_adj j
    rwa [sup_eq_left.mpr hWle] at this
  -- "`T_a` must contain `Z_1, …, Z_r`, by (1), (2) and (11)" (p. 256): the first step
  have hZTa : Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z)) ≤
      tauSubmodule R J a := by
    have hTau := (tauSubmodule_spec R J a ha hat).1
    have hprefixR := isTauZSubmodule_prefix_of_isTauSubmodule J G hG (m' := i) hi.le
      (fun j hj => hlow j (lt_trans hj hiN)) hTau
    have hfamR : (fun j : Fin i => G (Fin.castLE hi.le j)) = f := funext fun j => hGf j
    rw [hfamR] at hprefixR
    have hTf_le : tauZSubmodule R f ≤ tauSubmodule R J a := sInf_le hprefixR
    -- `T(f_1, …, f_i) = ⟨Z⟩`: (2) gives `⊆`, and (11) gives the rank
    obtain ⟨hliZ, hwoZ⟩ : LinearIndependent (R ⧸ maximalIdeal R) (frameForm F.z) ∧
        ∀ l, Ideal.ordElem (maximalIdeal R) (F.z l) = ((1 : ℕ) : ℕ∞) :=
      linearIndependent_frameForm F.z_injective F.extends_rsop
    have hZrank : Module.finrank (R ⧸ maximalIdeal R)
        (Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z))) = F.r := by
      rw [finrank_span_eq_card hliZ, Fintype.card_fin]
    have hZhom : Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z)) ≤
        AssocGraded.homogeneous (maximalIdeal R) 1 := by
      rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      show initialForm (maximalIdeal R) (F.z l) ∈ _
      rw [initialForm_eq_mk _ (hwoZ l)]
      exact AssocGraded.mk_mem_homogeneous _ _
    have hTfZ : tauZSubmodule R f ≤
        Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z)) := by
      refine tauZSubmodule_le_of_forall_mem_adjoin f _ hZhom fun j => ?_
      have h1' := F.initialForm_mem_adjoin_of_tauZ_eq_zero (f j) (h2 j)
      refine Algebra.adjoin_mono ?_ h1'
      rintro _ ⟨l, rfl⟩
      exact Submodule.subset_span ⟨l, rfl⟩
    have hrR : Module.finrank (R ⧸ maximalIdeal R) (tauZSubmodule R f) = F.r :=
      (tauZ_empty f).symm.trans h11
    have hfdZ : FiniteDimensional (R ⧸ maximalIdeal R)
        (Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z))) :=
      FiniteDimensional.span_of_finite _ (Set.finite_range _)
    have heqR : tauZSubmodule R f =
        Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z)) :=
      Submodule.eq_of_le_of_finrank_eq hTfZ (by rw [hrR, hZrank])
    rw [← heqR]
    exact hTf_le
  -- Lemma 19 on the `R`-side: "`φ ∈ k[Z_1, …, Z_r, X_1, …, X_τ]`" (p. 257)
  have hφG : initialForm (maximalIdeal R) (Gp ⟨i, hiN⟩) ∈ Algebra.adjoin (R ⧸ maximalIdeal R)
      ((tauSubmodule R J a ⊔ Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z)) :
        Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))) :
          Set (AssocGraded (maximalIdeal R))) := by
    rw [hGi']
    exact F.initialForm_mem_adjoin_tauSubmodule_sup J hJM f hfJ h2 f' hf'J a ha hat hμ h1 h3
  have hfin := core_instantiate_printed FT hrat x hxP h7' hFTx0 J a ha hat hat₁ h12 Gp dN hdict
    hGord hdμ (fun j => Ideal.mem_pow_of_ordElem (hgf_P j)) gf hgf_rel hgf_ord hψT hWle hZTa
    ⟨i, hiN⟩ hφG
  have hgfi : gf ⟨i, hiN⟩ = g' := by
    refine hcancel (dN ⟨i, hiN⟩) _ _ ((hgf_rel ⟨i, hiN⟩).trans ?_)
    rw [hGi', hdNi]
    exact hg'0.symm
  rw [hGi', hgfi] at hfin
  unfold tauZ tauZSubmoduleStar
  rw [hfin]

end CoreMain

section Lemma21

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- Lemma 21, p. 256: "Let the notation and assumptions be as in Lemma 20 (up to the assumption
(10)). Let `a` be the integer such that `μ^{(a)}(J) = ν^{(i+1)}(J)` and assume, in addition,
that (11) `τ(f₁, …, f_i) = r`, and (12) `τ^{(a)}(J₁) = τ^{(a)}(J)`. Then we conclude
(c) `τ_{(z)}(f) = τ_{(w)}(g)`."

(Formalization notes.
* "Up to the assumption (10)" is read as "through the assumption (10)": all the hypotheses
  (1)–(10) of Lemma 20 are assumed (`h1`–`h10`), since the proof uses "(10) and (b)".
* `a` is taken with `1 ≤ a ≤ t(J)`, the range in which `μ^{(a)}(J)` is defined (Definition 6;
  `mu R J a` has junk values outside it).
* `τ(f₁, …, f_i)` is `τ_{(z)}(f₁, …, f_i)` for the empty system `(z)` (Definition 10*), i.e.
  `tauZ R ![] f`; `τ_{(z)}(f)` and `τ_{(w)}(g)` are those of the one-element systems `(f)`, `(g)`.
* Notation and encoding as in Lemma 20 (`isNormalizedBy_frameTransform_and_extendsToStandardBase`):
  the paper's `f`, `g` are `f'`, `g'`.)

Printed route.  The proof begins "As in the proof of Lemma 20, we may assume that `S` and `R` are
complete, and that `R₁` is residually rational over `R`" (p. 254: "Let `S → S̃` be any local
homomorphism such that a regular system of parameters of `S` is transformed into such a system of
parameters of `S̃` and that the residue field of `S̃` is separable algebraic over that of `S`. Then
`S → S̃` induces in a canonical manner a local homomorphism `R → S̃{z₁, …, z_r}` which also has the
same properties as `S → S̃`. If we replace `S` by `S̃`, `R` by `R̃ = S̃{z₁, …, z_r}`, and `P` and
`J` by their extensions in `R̃`, and `R₁` by a monoidal transform `R̃₁` of `R̃` with center `PR̃`
which admits a canonical local homomorphism `R₁ → R̃₁`, all the assumptions (1)–(10) remain valid,
and the conclusions (a) and (b) are replaced by equivalent ones. Therefore we may assume that `R`
and `S` are complete and that `R₁` is residually rational over `R`").  This reduction is carried
out here, with `S̃` the complete regular local ring with separably closed residue field of
`CompleteSepClosedExtension` (`Compat/CompleteRationalBaseChange.lean`), `R̃ = S̃⟦z⟧`
(`RegularFrame.baseChangeHom`, `Compat/CompleteRationalFrameBaseChange.lean`), `R̃₁` the canonical
lift `BaseChangeLift` of `R₁` and the lifted frame transform `FrameTransform.exists_baseChange`:
the proof of the theorem below only verifies that the hypotheses (1)–(12) are preserved
(Deviation, gap filled: the paper says "all the assumptions remain valid" without verifying
them; they are `tauZ_baseChangeHom`, `isNormalizedBy_baseChangeHom`,
`extendsToStandardBase_baseChangeHom`, `ordElem_map_ideal_of_mapsRSOP`, `nuI_map_eq_of_mapsRSOP`,
`BaseChangeLift.nuI_strictTransformIdeal`, `tau_map_of_mapsRSOP`, `mu_map_of_mapsRSOP`, and the
descent of the conclusion `tauZ_map`) and then applies the case of complete `R`, residually
rational `R₁` (`tauZ_eq_tauZ_frameTransform_of_isAdicComplete`, whose docstring describes the proof
of the rest of the lemma, pp. 256–258, along the printed route and the gaps filled). -/
@[blueprint "lem:III.21"
  (statement := /-- Let the notation and assumptions be as in Lemma~20 (\cref{lem:III.20}) (up
    to the assumption (10)). Let $a$ be the integer such that $\mu^{(a)}(J)=\nu^{(i+1)}(J)$
    and assume, in addition, that
    \begin{enumerate}
      \item[(11)] $\tau(f_1,\dots,f_i)=r$ (\cref{def:III.10-star}), and
      \item[(12)] $\tau^{(a)}(J_1)=\tau^{(a)}(J)$ (\cref{def:III.6}).
    \end{enumerate}
    Then we conclude
    \begin{enumerate}
      \item[(c)] $\tau_{(z)}(f)=\tau_{(w)}(g)$.
    \end{enumerate}
    (Lemma 21, p.~256.) (Formalization note: ``up to the assumption (10)'' is read as
    including (10), which the proof uses together with the conclusion (b) of Lemma~20; $a$ is
    taken with $1\le a\le t(J)$, the range in which $\mu^{(a)}(J)$ is defined;
    $\tau(f_1,\dots,f_i)$ is $\tau_{(z)}(f_1,\dots,f_i)$ for the empty system $(z)$.) -/)
  (proof := /-- As in the proof of Lemma~20 (\cref{lem:III.20}), we may assume that $S$ and $R$
    are complete, and that $R_1$ is residually rational over $R$. Let $M$ (resp.\ $M_1$) be the
    maximal ideal of $R$ (resp.\ $R_1$) and $k=R/M=R_1/M_1$. We choose a regular system of
    parameters of $R$, say
    $$(z_1,\dots,z_r,x,x_1,\dots,x_t,y_1,\dots,y_s),$$
    such that $P\cap S=(x,x_1,\dots,x_t)S$, that $y_j\in S$ for $1\le j\le s$, and that
    $u_j=x_j/x\in M_1$ for $1\le j\le t$. Then
    $$(w_1,\dots,w_r,x,u_1,\dots,u_t,y_1,\dots,y_s)$$
    is a regular system of parameters of $R_1$. Let $Z_j$ (resp.\ $X$, resp.\ $X_j$, resp.\
    $Y_j$) denote the initial form of $z_j$ (resp.\ $x$, resp.\ $x_j$, resp.\ $y_j$) in
    $\operatorname{gr}_M(R)$, so that we have
    $$\operatorname{gr}_M(R)=k[Z_1,\dots,Z_r,X_1,\dots,X_t,X,Y_1,\dots,Y_s].$$
    Let $W_j$ (resp.\ $X$, resp.\ $U_j$, resp.\ $Y_j$) be the initial form of $w_j$ (resp.\
    $x$, resp.\ $u_j$, resp.\ $y_j$) in $\operatorname{gr}_{M_1}(R_1)$, so that we have
    $$\operatorname{gr}_{M_1}(R_1)=k[W_1,\dots,W_r,U_1,\dots,U_t,X,Y_1,\dots,Y_s].$$
    Let $T_a$ denote the $k$-submodule of $\operatorname{gr}^1_M(R)$ which is generated by the
    initial forms of a regular system of $a$th $\tau$-parameters of $R$ for $J$
    (\cref{def:III.7}). $T_a$ must contain $Z_1,\dots,Z_r$, by (1), (2) and (11). We claim that
    $T_a$ is contained in the $k$-submodule of $\operatorname{gr}^1_M(R)$ generated by
    $Z_1,\dots,Z_r,X_1,\dots,X_t$. To prove this, let $p$ be the maximal integer such that
    $\nu^{(i+p)}(J)=\mu^{(a)}(J)$. By means of Lemma~17 of \S7 (\cref{lem:III.17}), we can
    choose elements $f_{i+j}$ $(1\le j\le p)$ of $J$ such that each of the $f_{i+j}$
    $(1\le j\le p)$ is normalized by $(f_1,\dots,f_i)$ with respect to $(S;z_1,\dots,z_r)$
    and that $(f_1,\dots,f_i,f_{i+1},\dots,f_{i+p})$ can be extended to a standard base of
    $J$. Note that any permutation of the $p$ elements $f_{i+1},\dots,f_{i+p}$ preserves these
    properties. By Lemma~18 of \S7 (\cref{lem:III.18}), we have
    $\nu_P(f_{i+j})=\mu^{(a)}(J)$ for $1\le j\le p$. Let
    $\bar\mu=\mu^{(a)}(J)=\nu^{(i+j)}(J)$ $(1\le j\le p)$. By Lemma~20, we have
    $\nu_{M_1}(x^{-\bar\mu}f_{i+j})=\bar\mu$ for $1\le j\le p$. This shows that the initial
    forms of $f_{i+j}$ $(1\le j\le p)$ are contained in $k[Z_1,\dots,Z_r,X_1,\dots,X_t]$. In
    view of (2), it follows that $T_a$ is contained in the $k$-module generated by
    $Z_1,\dots,Z_r,X_1,\dots,X_t$. Now that we have this result, we could choose the system
    $(x_1,\dots,x_t)$ in such a way that for the integer $\tau=\tau^{(a)}(J)-r$
    $(0\le\tau\le t)$, $T_a$ is generated by $Z_1,\dots,Z_r,X_1,\dots,X_\tau$. Let $\varphi$
    (resp.\ $\varphi_j$ for $1\le j\le i$) be the initial form of $f$ (resp.\ $f_j$) in
    $\operatorname{gr}_M(R)$. We have $\varphi_j$ $(1\le j\le i)\in k[Z_1,\dots,Z_r]$ and, by
    Lemma~19 of \S7 (\cref{lem:III.19}), $\varphi\in k[Z_1,\dots,Z_r,X_1,\dots,X_\tau]$. Let
    $\bar\tau=\tau_{(z)}(f)$. We have $0\le\bar\tau\le\tau$. We may assume that
    $\varphi\in k[Z_1,\dots,Z_r,X_1,\dots,X_{\bar\tau}]$. Let $\psi$ (resp.\ $\psi_j$ for
    $1\le j\le i$) be the initial form of $g$ (resp.\ $g_j$) in
    $\operatorname{gr}_{M_1}(R_1)$. Then, by (8) and (9), we have
    $$\psi_j=\varphi_j(W_1,\dots,W_r)\qquad\text{for }1\le j\le i$$
    and, by (10) and (b),
    $$\psi=\varphi(W_1,\dots,W_r,U_1,\dots,U_{\bar\tau})+\lambda,$$
    where $\lambda\in(X,Y_1,\dots,Y_s)\operatorname{gr}_{M_1}(R_1)$. Let $T^*_a$ be the
    $k$-submodule of $\operatorname{gr}^1_{M_1}(R_1)$ generated by the initial forms of a
    regular system of $a$th $\tau$-parameters of $R_1$ for $J_1$. We claim that $T^*_a$
    contains $W_1,\dots,W_r$, and that there exists a system of linear forms in
    $X,Y_1,\dots,Y_s$, say $(L_1,\dots,L_{\bar\tau})$, such that $T^*_a$ is generated by
    $\{W_1,\dots,W_r,U_1+L_1,\dots,U_{\bar\tau}+L_{\bar\tau}\}$. In fact, in view of the
    equalities $\psi_j=\varphi_j(W_1,\dots,W_r)$ for $1\le j\le i$, (11) implies that
    $\tau(g_1,\dots,g_i)=r$. Hence, by (8) and (b), the first assertion on $T^*_a$ follows. To
    prove the second, we take $f_{i+j}$ and $g_{i+j}=x^{-\bar\mu}f_{i+j}$ $(1\le j\le p)$ in the
    same way as above. Let $\varphi_{i+j}$ (resp.\ $\psi_{i+j}$) be the initial form of
    $f_{i+j}$ (resp.\ $g_{i+j}$) in $\operatorname{gr}_M(R)$ (resp.\
    $\operatorname{gr}_{M_1}(R_1)$). Then we have
    $$\psi_{i+j}=\varphi_{i+j}(W_1,\dots,W_r,U_1,\dots,U_{\bar\tau})+\lambda_j,$$
    with $\lambda_j\in(X,Y_1,\dots,Y_s)\operatorname{gr}_{M_1}(R_1)$. By Lemma~20, $g_{i+j}$
    is normalized by $(g_1,\dots,g_i)$ with respect to $(S_1;w_1,\dots,w_r)$ for
    $1\le j\le p$. Hence, by Lemma~19 of \S7, we must have
    $$\psi_{i+j}\in k[T^*_a]\qquad\text{for }1\le j\le p.$$
    In view of the above expression of $\psi_{i+j}$ in terms of $\varphi_{i+j}$, the
    homomorphism $\operatorname{gr}_{M_1}(R_1)\to k[Z_1,\dots,Z_r,X_1,\dots,X_t]$ which maps
    $W_j$ to $Z_j$ $(1\le j\le r)$, $U_j$ to $X_j$ $(1\le j\le t)$, $X\to0$ and $Y_j\to0$
    $(1\le j\le s)$, should induce a surjective homomorphism $T^*_a\to T_a$. But $T^*_a$ has
    the same rank as $T_a$ by (12). This homomorphism $T^*_a\to T_a$ is an isomorphism of
    $k$-modules. The existence of $(L_1,\dots,L_{\bar\tau})$ follows. Now, by Lemma~19 of
    \S7, we have
    $$\psi\in k[T^*_a]=k[W_1,\dots,W_r,U_1+L_1,\dots,U_{\bar\tau}+L_{\bar\tau}].$$
    On the other hand,
    $$\psi-\varphi(W_1,\dots,W_r,U_1+L_1,\dots,U_{\bar\tau}+L_{\bar\tau})
      =\varphi(W_1,\dots,W_r,U_1,\dots,U_{\bar\tau})+\lambda
      -\varphi(W_1,\dots,W_r,U_1+L_1,\dots,U_{\bar\tau}+L_{\bar\tau})
      \in(X,Y_1,\dots,Y_s)\operatorname{gr}_{M_1}(R_1).$$
    It is, however, clear that zero is the only element in the intersection of the algebra
    $k[W_1,\dots,W_r,U_1+L_1,\dots,U_{\bar\tau}+L_{\bar\tau}]$, and of the ideal
    $(X,Y_1,\dots,Y_s)\operatorname{gr}_{M_1}(R_1)$. Therefore we must have
    $$\psi=\varphi(W_1,\dots,W_r,U_1+L_1,\dots,U_{\bar\tau}+L_{\bar\tau}).$$
    This shows that $\tau_{(w)}(g)=\tau_{(z)}(f)=\bar\tau$, i.e., (c). \qed

    \textbf{Formalization: the proof along the printed route; gaps filled.} (1) The base change
    is carried out and ``all the assumptions remain valid'' is verified (see the proof of the
    Lean theorem). (2) ``$T_a$ must contain $Z_1,\dots,Z_r$, by (1), (2) and (11)'' and ``$T^*_a$
    contains $W_1,\dots,W_r$ \dots\ by (8) and (b)'' need that the module $T$ of Definition~10*
    for $(f_1,\dots,f_i)$ is contained in the one for the longer system; this fails for
    arbitrary systems (e.g.\ $\varphi_1=X(X+Y)$, $\varphi_2=X+Y$) but holds for initial segments
    of a standard base, because the initial forms are minimal generators (the degree-$\nu_j$
    part of an element of $\operatorname{gr}(J)\cap k[T]$-combinations lies in
    $\operatorname{gr}(J)\cap k[T]$ plus the ideal of the lower generators, Lemma~15's
    decomposition); this is proved. (3) ``Any permutation of the $p$ elements preserves these
    properties'': Lemmas~19 and~20 are applied to each $f_{i+j}$ separately, and
    $(f_1,\dots,f_i,f_{i+j})$ is extended to a standard base directly; that the replacement of
    the members of a standard base by $G_j-\sum h_{jl}f_l$ (Lemma~17) gives a standard base is
    proved. (4) The choices of the system $(x_1,\dots,x_t)$ (so that $T_a$ is generated by
    $Z_1,\dots,Z_r,X_1,\dots,X_\tau$, and so that $\varphi\in k[Z,X_1,\dots,X_{\bar\tau}]$) are
    made as printed, on the polynomial rings $k[Z,X_1,\dots,X_t,X,Y]=\operatorname{gr}_M(R)$ and
    $k[W,U,X,Y]=\operatorname{gr}_{M_1}(R_1)$: a $k$-linear transformation of $(x_1,\dots,x_t)$ is the
    same $k$-linear change of the variables $X_j$ and $U_j$ (the regular system of parameters of $R$
    itself is not replaced). The forms $L_k$ and the isomorphism $T^*_a\to T_a$ are as printed (the
    homomorphism $\theta$ of p.~257 is a retraction of $k[T^*_a]$ onto $k[T_a]$), and ``zero is the
    only element in the intersection'' is proved through $\theta$, which maps $U_k+L_k$ to $X_k$ and
    the ideal $(X,Y_1,\dots,Y_s)$ to $0$. (5) $k$ and $k_1$ are
    identified through the residual rationality of $R_1$ (a semilinear isomorphism). (6) The
    number of the linear forms $L_k$ printed as $\bar\tau$ is $\tau=\tau^{(a)}(J)-r$ (a
    misprint). -/)
  (latexEnv := "lemma")]
theorem tauZ_eq_tauZ_frameTransform [Hironaka.HironakaCitedResults.{u}] (J : Ideal R) (F : RegularFrame R) {i : ℕ} (f : Fin i → R)
    (f' : R) (hfJ : ∀ j, f j ∈ J) (hf'J : f' ∈ J)
    (h1 : ExtendsToStandardBase J (Fin.snoc f f' : Fin (i + 1) → R))
    (h2 : ∀ j : Fin i, tauZ R F.z (fun _ : Fin 1 => f j) = 0)
    (h3 : F.IsNormalizedBy f f')
    (P : Ideal R) [P.IsPrime] (h4 : IsPermissibleCenter R J P) (h5 : F.idealZ ≤ P)
    (h6 : ∀ j : Fin i, Ideal.ordElem P (f j) = nuI R J (j : ℕ).succPNat)
    (h6' : Ideal.ordElem P f' = nuI R J i.succPNat)
    (T : MonoidalTransform R P) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing)
    (x : F.S) (hxP : algebraMap F.S R x ∈ P)
    (h7 : P.map T.toRing = Ideal.span {T.toRing (algebraMap F.S R x)})
    (FT : F.FrameTransform T) (h7' : FT.x = T.toRing (algebraMap F.S R x))
    (ν : Fin (i + 1) → ℕ) (hν : ∀ j : Fin (i + 1), (ν j : ℕ∞) = nuI R J (j : ℕ).succPNat)
    (g : Fin i → T.ring)
    (hg : ∀ j : Fin i, T.toRing (algebraMap F.S R x) ^ ν j.castSucc * g j = T.toRing (f j))
    (h8 : ∀ j : Fin i, tauZ T.ring FT.w (fun _ : Fin 1 => g j) = 0)
    (h9 : ∀ j : Fin i, Ideal.ordElem (maximalIdeal T.ring) (g j) = nuI R J (j : ℕ).succPNat)
    (g' : T.ring) (hg' : T.toRing (algebraMap F.S R x) ^ ν (Fin.last i) * g' = T.toRing f')
    (h10 : ∀ j : ℕ+, (j : ℕ) ≤ i + 1 → nuI T.ring (strictTransformIdeal T J) j = nuI R J j)
    (a : ℕ) (ha : 1 ≤ a) (hat : a ≤ t R J) (hμ : (mu R J a : ℕ∞) = nuI R J i.succPNat)
    (h11 : tauZ R (![] : Fin 0 → R) f = F.r)
    (h12 : tau T.ring (strictTransformIdeal T J) a = tau R J a) :
    tauZ R F.z (fun _ : Fin 1 => f') = tauZ T.ring FT.w (fun _ : Fin 1 => g') := by
  classical
  obtain ⟨E⟩ := CompleteSepClosedExtension.nonempty F.S
  set α := F.baseChangeHom E.hom with hαdef
  have hα : RingHom.MapsRSOP α := F.mapsRSOP_baseChangeHom E.hom E.mapsRSOP
  have hsepα : RingHom.IsResiduallySeparableAlgebraic α :=
    F.isResiduallySeparableAlgebraic_baseChangeHom E.hom E.isResiduallySeparableAlgebraic
  have hsepα' := hsepα.isResiduallySeparable
  have hJP : J ≤ P := by
    rcases h4 with hPtop | ⟨-, hJP, -, -⟩
    · exact absurd hPtop (Ideal.IsPrime.ne_top ‹P.IsPrime›)
    · exact hJP
  have hreg : IsRegularLocalRing (R ⧸ P) := by
    rcases h4 with hPtop | ⟨-, -, hreg, -⟩
    · exact absurd hPtop (Ideal.IsPrime.ne_top ‹P.IsPrime›)
    · exact hreg
  obtain ⟨L⟩ := BaseChangeLift.nonempty hα T
  obtain ⟨hPp, hPq⟩ := RingHom.MapsRSOP.isPrime_map_and_isRegularLocalRing_quotient hα
    (inferInstance : P.IsPrime) hreg
  have := hPp
  have := hPq
  have := L.isRegularLocalRing hα
  have := L.isLocalHom_toRing
  have hβ := L.mapsRSOP_β hα hsepα
  have hsepβ := (L.isResiduallySeparableAlgebraic_β hα hsepα).isResiduallySeparable
  have _ : IsSepClosed (ResidueField E.ring) := E.isSepClosed
  have _ : IsAdicComplete (maximalIdeal E.ring) E.ring := E.isAdicComplete
  have _ : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin F.r) E.ring))
      (MvPowerSeries (Fin F.r) E.ring) := F.isAdicComplete_baseChange (S' := E.ring)
  have hrat := L.isResiduallyRational hα (F.isSepClosed_residueField_baseChange (S' := E.ring))
    hsep
  obtain ⟨FT', hFT'x, hFT'w⟩ := RegularFrame.FrameTransform.exists_baseChange E.mapsRSOP L FT x
    hxP h7 h7'
  have hFT'w' : FT'.w = fun j => L.β (FT.w j) := funext hFT'w
  have hνnu : ∀ j : ℕ+, nuI (MvPowerSeries (Fin F.r) E.ring) (J.map α) j = nuI R J j :=
    fun j => (nuI_map_eq_of_mapsRSOP α hα J j).symm
  have hf1 : ∀ j, initialForm (maximalIdeal R) (f j) ∈ Set.range (frameAlgHom F.z) := fun j =>
    F.initialForm_mem_range_frameAlgHom_of_tauZ_eq_zero (f j) (h2 j)
  have hxcomm : ∀ s : F.S, L.T'.toRing (algebraMap E.ring (MvPowerSeries (Fin F.r) E.ring)
      (E.hom s)) = L.β (T.toRing (algebraMap F.S R s)) := fun s =>
    L.toRing_algebraMap_baseChange s
  have key := tauZ_eq_tauZ_frameTransform_of_isAdicComplete (J.map α)
    (F.baseChange E.ring) (fun j => α (f j)) (α f')
    (fun j => Ideal.mem_map_of_mem _ (hfJ j)) (Ideal.mem_map_of_mem _ hf'J)
    (by
      have h := F.extendsToStandardBase_baseChangeHom E.mapsRSOP J _ h1
      convert h using 1
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [hαdef])
    (fun j => by
      have := F.tauZ_baseChangeHom E.mapsRSOP E.isResiduallySeparableAlgebraic
        (fun _ : Fin 1 => f j)
      exact this.trans (h2 j))
    (F.isNormalizedBy_baseChangeHom E.mapsRSOP f hf1 f' h3)
    (P.map α) ((Hironaka.isPermissibleCenter_map_iff α hα J P hJP).2.2.2.mp h4)
    (by
      rw [RegularFrame.idealZ, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, ← F.baseChangeHom_z' E.hom j]
      exact Ideal.mem_map_of_mem _ (h5 (Ideal.subset_span ⟨j, rfl⟩)))
    (fun j => by rw [ordElem_map_ideal_of_mapsRSOP α hα P, h6 j, hνnu])
    (by rw [ordElem_map_ideal_of_mapsRSOP α hα P, h6', hνnu])
    L.T' hrat (E.hom x) (F.algebraMap_mem_map_baseChangeHom x hxP)
    (L.map_eq_span_baseChange x h7) FT' hFT'x ν (fun j => by rw [hν j, hνnu])
    (fun j => L.β (g j))
    (fun j => by
      show L.T'.toRing (algebraMap E.ring (MvPowerSeries (Fin F.r) E.ring) (E.hom x)) ^
        ν j.castSucc * L.β (g j) = L.T'.toRing (α (f j))
      rw [hxcomm, ← map_pow, ← map_mul, hg j, L.toRing_baseChangeHom])
    (fun j => by
      rw [hFT'w']
      have := tauZ_map L.β hβ hsepβ FT.w (fun _ : Fin 1 => g j)
      exact this.trans (h8 j))
    (fun j => by rw [ordElem_map_of_mapsRSOP L.β hβ, h9 j, hνnu])
    (L.β g') (by
      show L.T'.toRing (algebraMap E.ring (MvPowerSeries (Fin F.r) E.ring) (E.hom x)) ^
        ν (Fin.last i) * L.β g' = L.T'.toRing (α f')
      rw [hxcomm, ← map_pow, ← map_mul, hg', L.toRing_baseChangeHom])
    (fun j hj => by
      rw [L.nuI_strictTransformIdeal hα hsepα J hJP j, h10 j hj, hνnu])
    a ha (by rw [(tauStar_map α hα hsepα' J).1]; exact hat)
    (by rw [mu_map_of_mapsRSOP α hα, hμ, hνnu])
    ((F.tauZ_empty_baseChangeHom E.mapsRSOP E.isResiduallySeparableAlgebraic f).trans h11)
    (by
      rw [L.strictTransformIdeal_map hα J hJP,
        tau_map_of_mapsRSOP L.β hβ hsepβ _ a ha, h12,
        tau_map_of_mapsRSOP α hα hsepα' J a ha])
  have e1 := F.tauZ_baseChangeHom E.mapsRSOP E.isResiduallySeparableAlgebraic
    (fun _ : Fin 1 => f')
  have e2 := tauZ_map L.β hβ hsepβ FT.w (fun _ : Fin 1 => g')
  rw [hFT'w'] at key
  exact e1.symm.trans (key.trans e2)

end Lemma21

/-! ### Footnote 11 (p. 259): normalized standard bases over a complete `R` -/

section Footnote11

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Footnote 11, p. 259 (to "For the existence, see Lemmas 17 and 19 of §7" in the proof of
Proposition 2): "We can thus prove the existence of a normalized standard base of `J` with
respect to any regular τ-frame of `R` for `J`, when `R` is complete."

(Formalization note: "`R` is complete" is `IsAdicComplete (maximalIdeal R) R`; the footnote's
remark "`S` is complete and `R` is the formal power series ring `S{z₁, …, z_r}`" is part of its
proof.)

Deviation from the paper (gap filled): the footnote's proof is followed (induction on `i`, Lemma 17
for the `h_p`, Lemma 19 for the normalization of `f^{i+1}`), but it states three things without
proof.  (1) "`S` is complete and `R` is the formal power series ring `S{z₁, …, z_r}`": Lean proves
that the power series expansion of the frame is a ring isomorphism `R ≅ S{z₁, …, z_r}` for `R`
complete for `M` (`RegularFrame.exists_isExpansion_bijective`; `R` is complete for `(z)R ⊆ M`) and
transports Lemma 17, stated for `S{z₁, …, z_r}`, along it, together with the orders, the associated
subalgebras and the `E`-sets (`RegularFrame.exists_isNormalizedBy_sub_sum`).  (2) "It is clear from
the above properties of the `h_p` that `(f¹, …, f^i, f^{i+1})` can be extended to a standard
base": proved (`ordElem_sub_sum_eq_and_initialForm_notMem`: `ν_M(f^{i+1}) = ν^{(i+1)}(J)` and
its initial form is not in `(φ₁, …, φ_i)`; then `extendsToStandardBase_snoc`).  (3) the use of
Lemma 19 needs `τ_{(z)}(f_j) = 0` (from `φ_j ∈ k[Z]`, `RegularFrame.tauZ_eq_zero_of_initialForm_mem`)
and a regular system of `a`-th `τ`-parameters (`μ^{(a)}(J) = ν^{(i+1)}(J)`) consisting of members of
`z` (`RegularFrame.IsRegularTauFrame.exists_isRegularSystemOfTauParameters`).  Finally the
induction stops when `i` reaches the length of a standard base (all standard bases of `J` have the
same length, `length_eq_of_isStandardBase`). -/
@[blueprint "lem:III.8-normalized-standard-base-exists"
  (statement := /-- Let $R$ be a complete regular local ring, $J$ an ideal in $R$ and
    $(S;z_1,\dots,z_r)$ a regular $\tau$-frame of $R$ for $J$ (\cref{def:III.10}). Then there
    exists a normalized standard base of $J$ with respect to $(S;z_1,\dots,z_r)$
    (\cref{def:III.9-normalized-standard-base}). (Footnote 11, p.~259: ``We can thus prove the
    existence of a normalized standard base of $J$ with respect to any regular $\tau$-frame of
    $R$ for $J$, when $R$ is complete.'') -/)
  (proof := /-- (Footnote 11, p.~259.) $S$ is complete and $R$ is the formal power series ring
    $S\{z_1,\dots,z_r\}$. Let $(f_1,\dots,f_i)$ be a system of elements of $J$ which can be
    extended to a standard base of $J$ and which is normalized with respect to
    $(S;z_1,\dots,z_r)$ (cf.\ Definition~9~(3), \cref{def:III.9}). Take $g$ to be any element
    of $J$ such that $(f_1,\dots,f_i,g)$ [printed: $(f_1,\dots,f_r,g)$] can be extended to a
    standard base of $J$. Then, by Lemma~17 (\cref{lem:III.17}), we can find a system of
    elements of $R$, say $(h_1,\dots,h_i)$, such that $\nu_M(h_p)\ge\nu_{i+1}-\nu_p$
    $(1\le p\le i)$ and that $g-\sum_ph_pf_p$ (call it $f_{i+1}$) is normalized by
    $(f_1,\dots,f_i)$ with respect to $(S;z_1,\dots,z_r)$. Since $(S;z_1,\dots,z_r)$ is a
    regular $\tau$-frame of $R$ for $J$, Lemma~19 (\cref{lem:III.19}) implies that
    $(f_1,\dots,f_i,f_{i+1})$ is normalized with respect to $(S;z_1,\dots,z_r)$. It is clear
    from the above properties of the $h_p$ that $(f_1,\dots,f_i,f_{i+1})$ can be extended to a
    standard base of $J$. We can thus prove the existence of a normalized standard base of $J$
    with respect to any regular $\tau$-frame of $R$ for $J$, when $R$ is complete.

    \textbf{Deviation from the paper (gap filled).} The footnote asserts without proof that $R$
    is the formal power series ring $S\{z_1,\dots,z_r\}$: the power series expansion of the frame
    is an isomorphism for $R$ complete (the kernel lies in every power of $(z)R$, whose Krull
    intersection is $0$; a power series is the image of the limit of its truncations), and
    Lemma~17, stated for $S\{z_1,\dots,z_r\}$, is transported along it. The claim that
    $(f_1,\dots,f_i,f_{i+1})$ can be extended to a standard base is proved: $\nu_M(f_{i+1})
    =\nu^{(i+1)}(J)$ and its initial form is not in $(\varphi_1,\dots,\varphi_i)\operatorname{gr}_M(R)$
    since it differs from that of $g$ by an element of this ideal. Lemma~19 is applied with
    $\tau_{(z)}(f_j)=0$ (because $\varphi_j\in k[Z]$) and the $a$-th $\tau$-parameters taken among
    the $z_j$. -/)
  (latexEnv := "lemma")]
theorem exists_isNormalizedStandardBase_of_isAdicComplete [IsAdicComplete (maximalIdeal R) R]
    (J : Ideal R) (F : RegularFrame R) (hF : F.IsRegularTauFrame J) :
    ∃ (m : ℕ) (f : Fin m → R), F.IsNormalizedStandardBase J f :=
  F.exists_isNormalizedStandardBase J hF

end Footnote11


section NormalizedStandardBaseTransform

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

set_option linter.unusedVariables false in
/-- **`(g₁, …, g_m)` is a normalized standard base of `J₁`** (proof of Proposition 2, p. 259: "Let
`g_j = x^{-ν_j} f_j` […]. Then, in view of Lemmas 20 and 21, we see that `(g₁, …, g_m)` is again a
normalized standard base of `J₁` with respect to `(S₁; z₁/x, …, z_r/x)`").  The induction on `i`:
Lemma 20 gives that `g_{i+1}` is normalized by `(g₁, …, g_i)` and that `(g₁, …, g_{i+1})` extends to
a standard base of `J₁`; `ν_{M₁}(g_{i+1}) = ν_{i+1}` is then the `(i+1)`-st character of that
standard base; and the initial form of `g_{i+1}` lies in the associated subalgebra of
`(S₁; z/x)` by Lemma 19 for `(R₁, J₁, (S₁; z/x))`.

Deviation from the paper (gap in the paper repaired): for the last point the paper uses
Lemma 21 (c), `τ_{(w)}(g) = τ_{(z)}(f)`, whose hypothesis (11), `τ(f₁, …, f_i) = r`, does not hold
in general (e.g. `i = 0`); the assertion needed ((8) for the next step, that the initial form of
`g_{i+1}` lies in `k[W_1, …, W_r]`, i.e. Definition 9 (3) (i)) is Lemma 19 applied to `J₁` and the
regular `τ`-frame `(S₁; w)` of `R₁`. -/
theorem isNormalizedStandardBase_strictTransform_of_frameTransform [Hironaka.HironakaCitedResults.{u}] (J : Ideal R)
    (F : RegularFrame R) (Q : Ideal R) [Q.IsPrime] (hQperm : IsPermissibleCenter R J Q)
    (hzQ : F.idealZ ≤ Q) (T : MonoidalTransform R Q) [IsLocalHom T.toRing]
    [IsRegularLocalRing T.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing)
    (x : F.S) (hxQ : algebraMap F.S R x ∈ Q)
    (hx : Q.map T.toRing = Ideal.span {T.toRing (algebraMap F.S R x)})
    (FT : F.FrameTransform T) (hFTx : FT.x = T.toRing (algebraMap F.S R x))
    (hnu : nuStar T.ring (strictTransformIdeal T J) = nuStar R J)
    (hF₁ : FT.toRegularFrame.IsRegularTauFrame (strictTransformIdeal T J))
    {m : ℕ} (f : Fin m → R) (hf : F.IsNormalizedStandardBase J f)
    (hfQ : ∀ j : Fin m, Ideal.ordElem Q (f j) = nuI R J (j : ℕ).succPNat)
    (ν : Fin m → ℕ) (hν : ∀ j, (ν j : ℕ∞) = nuI R J (j : ℕ).succPNat)
    (g : Fin m → T.ring)
    (hg : ∀ j, T.toRing (algebraMap F.S R x) ^ ν j * g j = T.toRing (f j)) :
    FT.toRegularFrame.IsNormalizedStandardBase (strictTransformIdeal T J) g := by
  classical
  set J₁ := strictTransformIdeal T J with hJ₁
  set x₁ := T.toRing (algebraMap F.S R x) with hx₁
  have hnuI : ∀ i, nuI T.ring J₁ i = nuI R J i := fun i => congrFun (toLex.injective hnu) i
  have hg_mem : ∀ j, g j ∈ J₁ := fun j =>
    Ideal.subset_span ⟨x₁, hx.symm, f j, hf.1.1 j, ν j, ((hν j).trans (hfQ j).symm).le, hg j⟩
  -- the induction
  have key : ∀ n : ℕ, ∀ l : Fin m, (l : ℕ) = n →
      Ideal.ordElem (maximalIdeal T.ring) (g l) = nuI R J (l : ℕ).succPNat ∧
      initialForm (maximalIdeal T.ring) (g l) ∈ FT.toRegularFrame.assocSubalgebra ∧
      FT.toRegularFrame.IsNormalizedBy (fun j : Fin (l : ℕ) => g (Fin.castLE l.2.le j)) (g l) ∧
      ExtendsToStandardBase J₁ (Fin.snoc (fun j : Fin (l : ℕ) => g (Fin.castLE l.2.le j)) (g l) :
        Fin ((l : ℕ) + 1) → T.ring) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro l hl
    have hpre := fun j : Fin (l : ℕ) => ih (j : ℕ) (hl ▸ j.2) (Fin.castLE l.2.le j) rfl
    -- the data for Lemma 20
    set ν' : Fin ((l : ℕ) + 1) → ℕ := fun j => ν (Fin.castLE (Nat.succ_le_of_lt l.2) j) with hν'
    have hν'cast : ∀ j : Fin (l : ℕ), ν' j.castSucc = ν (Fin.castLE l.2.le j) := fun j =>
      congrArg ν (Fin.ext rfl)
    have hν'last : ν' (Fin.last (l : ℕ)) = ν l := congrArg ν (Fin.ext rfl)
    have h1 : ExtendsToStandardBase J (Fin.snoc (fun j : Fin (l : ℕ) => f (Fin.castLE l.2.le j))
        (f l) : Fin ((l : ℕ) + 1) → R) := by
      refine ⟨m, f, Nat.succ_le_of_lt l.2, hf.1, fun j => ?_⟩
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact congrArg f (Fin.ext rfl)
      | cast j => rw [Fin.snoc_castSucc]; exact congrArg f (Fin.ext rfl)
    have h2 : ∀ j : Fin (l : ℕ), tauZ R F.z (fun _ : Fin 1 => f (Fin.castLE l.2.le j)) = 0 :=
      fun j => F.tauZ_eq_zero_of_initialForm_mem _ (hf.2.1 _)
    have h8 : ∀ j : Fin (l : ℕ), tauZ T.ring FT.w
        (fun _ : Fin 1 => g (Fin.castLE l.2.le j)) = 0 := fun j =>
      FT.toRegularFrame.tauZ_eq_zero_of_initialForm_mem _ (hpre j).2.1
    have h9 : ∀ j : Fin (l : ℕ), Ideal.ordElem (maximalIdeal T.ring) (g (Fin.castLE l.2.le j)) =
        nuI R J (j : ℕ).succPNat := fun j => (hpre j).1
    obtain ⟨hN, hE⟩ := isNormalizedBy_frameTransform_and_extendsToStandardBase J F
      (fun j : Fin (l : ℕ) => f (Fin.castLE l.2.le j)) (f l) (fun j => hf.1.1 _) (hf.1.1 l)
      h1 h2 (hf.2.2 l) Q hQperm hzQ (fun j => hfQ _) (hfQ l) T hsep x hxQ hx FT hFTx ν'
      (fun j => hν _) (fun j : Fin (l : ℕ) => g (Fin.castLE l.2.le j))
      (fun j => by rw [hν'cast]; exact hg _) h8 h9 (g l) (by rw [hν'last]; exact hg l)
    have hE' := hE (fun j _ => hnuI j)
    refine ⟨?_, ?_, hN, hE'⟩
    · -- `ν_{M₁}(g_l)` is the `(l+1)`-st character of the standard base extending `(g₁, …, g_{l+1})`
      obtain ⟨m₂, G, him, hG, hGf⟩ := hE'
      have hk := ordElem_eq_nuI_of_isStandardBase J₁ G hG (Fin.castLE him (Fin.last (l : ℕ)))
      rw [hGf (Fin.last (l : ℕ)), Fin.snoc_last, hnuI] at hk
      exact hk
    · -- Definition 9 (3) (i), from Lemma 19 for `(R₁, J₁, (S₁; w))`
      exact FT.toRegularFrame.initialForm_mem_assocSubalgebra_of_isNormalizedBy J₁ hF₁
        (fun j : Fin (l : ℕ) => g (Fin.castLE l.2.le j)) (fun j => hg_mem _)
        (fun j => (hpre j).2.1) (g l) (hg_mem l) hE' hN
  have hA : ∀ l, Ideal.ordElem (maximalIdeal T.ring) (g l) = nuI R J (l : ℕ).succPNat :=
    fun l => (key l l rfl).1
  have hB : ∀ l, initialForm (maximalIdeal T.ring) (g l) ∈ FT.toRegularFrame.assocSubalgebra :=
    fun l => (key l l rfl).2.1
  have hN : ∀ l : Fin m, FT.toRegularFrame.IsNormalizedBy
      (fun j : Fin (l : ℕ) => g (Fin.castLE l.2.le j)) (g l) := fun l => (key l l rfl).2.2.1
  -- `g` is a standard base of `J₁`
  refine ⟨?_, hB, hN⟩
  obtain ⟨m₀, hm⟩ : ∃ m₀, m = m₀ + 1 ∨ m = 0 := by
    cases m with
    | zero => exact ⟨0, Or.inr rfl⟩
    | succ m₀ => exact ⟨m₀, Or.inl rfl⟩
  rcases hm with rfl | rfl
  · have hext := (key m₀ ⟨m₀, Nat.lt_succ_self _⟩ rfl).2.2.2
    have hfun : (Fin.snoc (fun j : Fin m₀ => g (Fin.castLE (Nat.lt_succ_self m₀).le j))
        (g ⟨m₀, Nat.lt_succ_self _⟩) : Fin (m₀ + 1) → T.ring) = g := by
      funext j
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact congrArg g (Fin.ext rfl)
      | cast j => rw [Fin.snoc_castSucc]; exact congrArg g (Fin.ext rfl)
    rw [hfun] at hext
    obtain ⟨m₂, G, him, hG, hGf⟩ := hext
    have hlen : m₂ = m₀ + 1 := (length_eq_of_nuI_eq hG hf.1 (fun i => hnuI i)).trans rfl
    subst hlen
    have : g = G := funext fun j => by rw [← hGf j]; rfl
    rw [this]
    exact hG
  · -- `m = 0`
    obtain ⟨m₂, G, hG⟩ := exists_isStandardBase J₁
    have : m₂ = 0 := (length_eq_of_nuI_eq hG hf.1 (fun i => hnuI i))
    subst this
    have : g = G := funext fun j => j.elim0
    rw [this]
    exact hG

end NormalizedStandardBaseTransform

section Proposition2Reduced

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- **Proposition 2 for a complete `R` and a residually rational `R₁`** (pp. 258–259, after "We may
assume that `R` is complete, and that `R₁` is residually rational over `R`"), proved along the
printed proof.  The steps are those of the paper: (1) a regular `τ`-frame `(S; z₁, …, z_r)` of `R`
for `J` which admits a frame transform `(S₁; z₁/x, …, z_r/x)` in `R₁` with denominator `x ∈ S`,
which is a regular `τ`-frame of `R₁` for `J₁`, with `z_j/x ∈ P₁`
(`exists_tauParameters_mem_prime`, `exists_regularFrame_of_extendsToRSOP_insert`,
`admitsFrameTransform_iff`); (2) a normalized standard base `(f_j)` of `J` with respect to
`(S; z)` (footnote 11, `exists_isNormalizedStandardBase_of_isAdicComplete`) and
`g_j = x^{-ν_j} f_j`; (3) `(g_j)` is a normalized standard base of `J₁` with respect to
`(S₁; z/x)` (Lemmas 20 and 19, `isNormalizedStandardBase_strictTransform_of_frameTransform`);
(4) Theorem 6 for `R₁`, `ν_{P₁}(g_j) = ν_j`; (5) `R_P = (R₁)_{P₁}` and `ν_{PR_P} = ν_P`, so
`ν_P(f_j) = ν_j`; (6) Theorem 6 (or Definition 8 (ii)**) for `P`.

Cited results: Cohen's coefficient field in equal characteristic (p. 258, "Then `R` is a formal
power series ring over a field, by Cohen's structure theorem",
`exists_residue_comp_eq_id_of_isAdicComplete_of_ringChar_eq`) and the two cited leaves of
Lemma 18 (Serre, Cohen).

Step (1) follows the printed text, as successive steps (`exists_tauParameters_mem_prime`): (a) a
minimal base `(x, z₁, …, z_t)` of `Q` with `(x)R₁ = QR₁` and `z_i/x ∈ M₁` (the coordinates of the
transform), and Lemma 14: "the initial forms of the `h_j` in `gr_M(R)` must belong to the
`(R/M)`-subalgebra of `gr_M(R)` generated by the initial forms of the `z_i`", so that the
`τ`-submodules lie in `⟨[z₁], …, [z_t]⟩`; (b) "by applying a suitable `k`-linear transformation to
the system `(z₁, …, z_t)`, we can assume `(z₁, …, z_r)` `(r ≤ t)` to be a regular system of
`τ`-parameters of `R` for `J`"; (c) "we can choose the above `(z₁, …, z_r)` in such a way that the
transform `(S₁; z₁/x, …, z_r/x)` is a regular `τ`-frame of `R₁` for `J₁` (See the proof of
Lemma 16)"; (d) "we can choose it in such a way that `z_j/x ∈ P₁` for all `j` (See Lemma 11)".
Gaps filled: "it is then easily seen" (b); "(See the proof of Lemma 16)" (c), the kernel of `ρ` on
`gr¹_{M₁}(R₁)` being `⟨[x], [y_j]⟩`; and "(See Lemma 11)" (d), which does not by itself give that
the `τ`-parameters of `R₁` lying in `P₁` are the quotients `z_j/x` of elements `z_j ∈ P`: the pair
of step (c) is adjusted by elements of `M²` and `M₁²` into a pair `(z_j, z_j/x)` with `z_j ∈ P`,
using that `P₁ ⊆ (q/x)R₁` for a minimal base `(q)` of `P`.  The frame `(S; z)` with `x ∈ S` is that
of the paper (`S = k{…}` for the coefficient field `k = σ(R/M)`,
`exists_regularFrame_of_extendsToRSOP_insert`), and the frame transform with denominator exactly
`x` is obtained from `admitsFrameTransform_iff` (p. 254, a gap of the paper that is filled) by
rescaling the denominator by a unit.

Deviation from the paper (gap in the paper repaired) in step (3): the paper writes "in view of
Lemmas 20 and 21 we see that `(g₁, …, g_m)` is again a normalized standard base of `J₁`".
Lemma 21 (c) is applied to obtain the initial form of `g_{i+1}` in `k[W₁, …, W_r]`
(Definition 9 (3) (i)), but its hypothesis (11), `τ(f₁, …, f_i) = r`, does not hold in general
(for `i = 0`, `τ(∅) = 0`).  Lean takes Definition 9 (3) (i) for `g_{i+1}` from Lemma 19 applied to
`J₁` and the regular `τ`-frame `(S₁; z/x)` of `R₁`
(`initialForm_mem_assocSubalgebra_of_isNormalizedBy`),
which is available because `(g₁, …, g_{i+1})` extends to a standard base of `J₁` and `g_{i+1}` is
normalized by `(g₁, …, g_i)` (Lemma 20).  Lemma 21 is not used.

Further details the paper leaves tacit and Lean proves: that `ν_Q(f_j) = ν_j` makes `g_j` exist
(`f_j ∈ Q^{ν_j}`, `QR₁ = (x)R₁`); that `(g_j)` has the length `m` of a standard base of `J₁`
(`length_eq_of_nuI_eq`); that `R_P = (R₁)_{P₁}`, i.e. `R_P → (R₁)_{P₁}` is bijective for a
monoidal transform with centre `Q` and `x ∉ P`
(`MonoidalTransform.localRingHom_bijective_of_notMem`);
that `ν_{P₁} ≥ ν` implies `ν_P ≥ ν` (`MonoidalTransform.le_ordElem_of_le_ordElem_toRing`); and the
case `J = (0)` (`t(J) = 0`), which the paper excludes tacitly. -/
@[blueprint "prop:III.8-2-complete"
  (statement := /-- Let $R$ be a complete regular local ring which has the same characteristic as
    its residue field, $J$ an ideal and $P$, $Q$ prime ideals of $R$ with $Q\supset P\supseteq J$,
    $Q\ne P$, $R/P$ regular, $Q$ a permissible center for $J$. Let $R_1$ be a monoidal transform
    of $R$ with center $Q$ which is residually separable algebraic and residually rational over
    $R$, $J_1$ the strict transform of $J$ in $R_1$, $P_1$ a prime ideal of $R_1$ with
    $P_1\cap R=P$. If $\nu^*(J_1)=\nu^*(J)$ and $P_1$ is a permissible center for $J_1$, then $P$ is
    a permissible center for $J$. (Proposition 2, p.~258, case of a complete $R$ and a residually
    rational $R_1$.) -/)
  (proof := /-- If $J=(0)$ there is nothing to prove. Otherwise, by
    \cref{lem:III.8-2-tau-parameters}
    there are $x_0\in Q\smallsetminus P$ with $QR_1=(x_0)R_1$ and $z_1,\dots,z_r\in P$ with
    $z_j/x_0\in P_1$ such that $(z_j)$ is a regular system of $\tau$-parameters of $R$ for $J$,
    $(z_j/x_0)$ is one of $R_1$ for $J_1$, and $(z_1,\dots,z_r,x_0)$ can be extended to a regular
    system of parameters of $R$. By Cohen's structure theorem, $R=k\{z_1,\dots,z_r,x_0,y_1,\dots,
    y_s\}$, and $S=k\{x_0,y_1,\dots,y_s\}$ gives a regular $\tau$-frame $(S;z_1,\dots,z_r)$ of $R$
    for $J$ with $x_0\in S$, which admits a frame transform $(S_1;z_1/x_0,\dots,z_r/x_0)$ in $R_1$
    with denominator $x_0$ (\cref{lem:III.8-frame-transform-criterion}), a regular $\tau$-frame of
    $R_1$ for $J_1$. Let $(f_1,\dots,f_m)$ be a normalized standard base of $J$ with respect to
    $(S;z)$ (\cref{lem:III.8-normalized-standard-base-exists}), $\nu_j=\nu^{(j)}(J)$; by
    Theorem~6 (\cref{thm:III.6}) $\nu_Q(f_j)=\nu_j$, so $g_j=x_0^{-\nu_j}f_j$ exists. By
    Lemma~20 (\cref{lem:III.20}) and Lemma~19 (\cref{lem:III.19}) for $(R_1,J_1,(S_1;z/x_0))$,
    $(g_1,\dots,g_m)$ is a normalized standard base of $J_1$ with respect to $(S_1;z/x_0)$. By
    Theorem~6 for $R_1$, $\nu_{P_1}(g_j)=\nu_j$. As $x_0$ is a unit in $R_P=(R_1)_{P_1}$,
    $\nu_{PR_P}(f_j)=\nu_j$, hence $\nu_P(f_j)=\nu_j$ as $R/P$ is regular, and $P$ is a permissible
    center for $J$ (\cref{lem:III.8-equivalents}).

    \textbf{Gaps in the paper filled and repaired.} The choice of the $\tau$-frame follows the
    printed text, steps (a)--(d) of \cref{lem:III.8-2-tau-parameters}; the gaps filled there are
    ``it is then easily seen \dots a suitable $k$-linear transformation'' (b), ``(See the proof of
    Lemma 16)'' (c) and ``(See Lemma 11)'' (d), which does not by itself give that the
    $\tau$-parameters of $R_1$ in $P_1$ are the quotients $z_j/x$ of elements of $P$. The paper uses
    Lemma~21 (c) for Definition~9 (3) (i) of $g_{i+1}$, whose hypothesis (11) fails in general; Lean
    uses Lemma~19 for $(R_1,J_1,(S_1;z/x_0))$ instead (gap in the paper repaired). -/)
  (latexEnv := "proposition")]
theorem isPermissibleCenter_of_nuStar_strictTransform_eq_of_isAdicComplete [Hironaka.HironakaCitedResults.{u}]
    [IsAdicComplete (maximalIdeal R) R] (hchar : ringChar R = ringChar (ResidueField R))
    (J P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P ≤ Q) (hJP : J ≤ P) (hQP : Q ≠ P)
    [IsRegularLocalRing (R ⧸ P)] (hQperm : IsPermissibleCenter R J Q)
    (T : MonoidalTransform R Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing)
    (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing)
    (P₁ : Ideal T.ring) [P₁.IsPrime] (hP₁ : P₁.comap T.toRing = P)
    (hnu : nuStar T.ring (strictTransformIdeal T J) = nuStar R J)
    (hperm₁ : IsPermissibleCenter T.ring (strictTransformIdeal T J) P₁) :
    IsPermissibleCenter R J P := by
  classical
  set J₁ := strictTransformIdeal T J with hJ₁
  have hJQ : J ≤ Q := hJP.trans hPQ
  obtain ⟨-, -, hQreg, -⟩ := hQperm.resolve_left (Ideal.IsPrime.ne_top inferInstance)
  have _ : IsRegularLocalRing (R ⧸ Q) := hQreg
  by_cases ht0 : t R J = 0
  · exact isPermissibleCenter_of_t_eq_zero J P hJP ht0
  have ht0' : 0 < t R J := Nat.pos_of_ne_zero ht0
  obtain ⟨hJ₁P₁, hP₁reg, -⟩ : J₁ ≤ P₁ ∧ IsRegularLocalRing (T.ring ⧸ P₁) ∧
      IsNormallyFlatAlongIdeal (P₁.map (Ideal.Quotient.mk J₁)) := by
    rcases hperm₁ with h | ⟨-, h1, h2, h3⟩
    · exact absurd h (Ideal.IsPrime.ne_top inferInstance)
    · exact ⟨h1, h2, h3⟩
  have _ : IsRegularLocalRing (T.ring ⧸ P₁) := hP₁reg
  -- "Then `R` is a formal power series ring over a field, by Cohen's structure theorem" (p. 258):
  -- the coefficient field `k = σ(R/M)`
  obtain ⟨σ, hσ⟩ := exists_residue_comp_eq_id_of_isAdicComplete_of_ringChar_eq R hchar
  have hσ' : ∀ a, Ideal.Quotient.mk (maximalIdeal R) (σ a) = a := fun a =>
    RingHom.congr_fun hσ a
  -- the choice of the `τ`-parameters (p. 258–259): steps (a)–(d)
  obtain ⟨x₀, z, w, hx₀Q, hx₀P, hxspan, hzP, hzw, hwP₁, hzinj, hext, ⟨hzmax, hzτ⟩, hr, hwmax,
    hwτ⟩ := exists_tauParameters_mem_prime σ hσ' J P Q hPQ hJP hQP hQperm T hrat P₁ hP₁ hnu
      hperm₁ ht0'
  -- the regular `τ`-frame `(S; z₁, …, z_r)` of `R`, with `x₀` in `S`
  have hx₀z : x₀ ∉ Finset.image z Finset.univ := by
    intro h
    obtain ⟨l, -, hl⟩ := Finset.mem_image.mp h
    exact hx₀P (hl ▸ hzP l)
  obtain ⟨F, hFr, hFz, s, hs⟩ :=
    exists_regularFrame_of_extendsToRSOP_insert σ hσ hzinj x₀ hx₀z hext
  have hFz' : ∀ j : Fin F.r, F.z j = z (Fin.cast hFr j) := fun j => by
    have := hFz (Fin.cast hFr j)
    rwa [show Fin.cast hFr.symm (Fin.cast hFr j) = j from Fin.ext rfl] at this
  have hFzP : ∀ j, F.z j ∈ P := fun j => by rw [hFz']; exact hzP _
  have hzQ : F.idealZ ≤ Q := Ideal.span_le.mpr (by
    rintro _ ⟨j, rfl⟩
    exact hPQ (hFzP j))
  have hFτ : F.IsRegularTauFrame J := by
    refine ⟨hFr.symm, fun j => F.mem_maximalIdeal_z j, ?_⟩
    have hfun : (fun i : Fin (tau R J (t R J)) =>
        (⟨F.z (Fin.cast hFr.symm i), F.mem_maximalIdeal_z _⟩ : maximalIdeal R)) =
        fun l => ⟨z l, hzmax l⟩ := funext fun i => Subtype.ext (hFz i)
    rw [hfun]
    exact hzτ
  -- the frame transform with denominator `x = x₀`
  have hxQ : algebraMap F.S R s ∈ Q := by rw [hs]; exact hx₀Q
  have hxspan' : Q.map T.toRing = Ideal.span {T.toRing (algebraMap F.S R s)} := by
    rw [hs]; exact hxspan
  have hw' : ∀ j : Fin F.r,
      T.toRing (algebraMap F.S R s) * w (Fin.cast hFr j) = T.toRing (F.z j) := by
    intro j
    rw [hs, hFz']
    exact hzw _
  have hwnu : ∀ j : Fin F.r, ¬ IsUnit (w (Fin.cast hFr j)) := fun j hu =>
    (Ideal.IsPrime.ne_top (inferInstance : P₁.IsPrime))
      (Ideal.eq_top_of_isUnit_mem P₁ (hwP₁ _) hu)
  obtain ⟨FT, hFTx⟩ := RegularFrame.exists_frameTransform_denominator_eq (F := F) (T := T) s hxQ
    hxspan' hw' hwnu
  have hx₁0 : T.toRing (algebraMap F.S R s) ≠ 0 := fun h0 => hx₀P (by
    have : x₀ = 0 := T.toRing_injective (by rw [← hs, h0, map_zero])
    rw [this]; exact zero_mem _)
  have hFTw : ∀ j, FT.w j = w (Fin.cast hFr j) := fun j =>
    mul_left_cancel₀ hx₁0 (by
      have h := FT.mul_w j
      rw [hFTx] at h
      rw [h, hw'])
  -- `(S₁; z/x)` is a regular `τ`-frame of `R₁` for `J₁`
  have hzF : ∀ j : Fin FT.toRegularFrame.r, FT.toRegularFrame.z j = w (Fin.cast hFr j) :=
    fun j => hFTw j
  have hzFmax : ∀ j : Fin FT.toRegularFrame.r, FT.toRegularFrame.z j ∈ maximalIdeal T.ring :=
    fun j => (hzF j).symm ▸ hwmax _
  have hF₁ : FT.toRegularFrame.IsRegularTauFrame J₁ := by
    refine ⟨hr.trans hFr.symm, hzFmax, ?_⟩
    have hfun : (fun i : Fin (tau T.ring J₁ (t T.ring J₁)) =>
          (⟨FT.toRegularFrame.z (Fin.cast (hr.trans hFr.symm) i), hzFmax _⟩ :
            maximalIdeal T.ring)) =
          fun i => ⟨w (Fin.cast hr i), hwmax _⟩ :=
      funext fun i => Subtype.ext ((hzF _).trans (congrArg w (Fin.ext rfl)))
    rw [hfun]
    exact hwτ
  -- a normalized standard base `(f₁, …, f_m)` of `J` (footnote 11)
  obtain ⟨m, f, hf⟩ := exists_isNormalizedStandardBase_of_isAdicComplete J F hFτ
  have hJtop : J ≠ ⊤ := ne_top_of_le_ne_top (Ideal.IsPrime.ne_top inferInstance) hJP
  -- Theorem 6 for `R`: `ν_Q(f_j) = ν_j`
  have hfQ : ∀ j : Fin m, Ideal.ordElem Q (f j) = nuI R J (j : ℕ).succPNat :=
    (isPermissibleCenter_iff_ordElem_eq_nuI F J hJtop f hf Q hQreg hzQ).mp hQperm
  have hftop : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) ≠ ⊤ := by
    intro j htop
    apply hf.1.2.2.2.2 j
    dsimp only
    rw [show initialForm (maximalIdeal R) (f j) = 0 by rw [initialForm, dite_eq_left htop]]
    exact zero_mem _
  let ν : Fin m → ℕ := fun j => (Ideal.ordElem (maximalIdeal R) (f j)).toNat
  have hν : ∀ j : Fin m, (ν j : ℕ∞) = nuI R J (j : ℕ).succPNat := fun j =>
    (ENat.natCast_toNat (hftop j)).trans (ordElem_eq_nuI_of_isStandardBase J f hf.1 j)
  -- `g_j = x^{-ν_j} f_j`
  have hex : ∀ j : Fin m, ∃ c : T.ring,
      T.toRing (algebraMap F.S R s) ^ ν j * c = T.toRing (f j) := by
    intro j
    have hmem : f j ∈ Q ^ ν j := Ideal.mem_pow_of_ordElem ((hfQ j).trans (hν j).symm)
    have h1 : T.toRing (f j) ∈ Ideal.span {T.toRing (algebraMap F.S R s) ^ ν j} := by
      rw [← Ideal.span_singleton_pow, ← hxspan', ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hmem
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
    exact ⟨c, by rw [mul_comm]; exact hc⟩
  choose g hg using hex
  -- Lemmas 20 and 19: `(g_j)` is a normalized standard base of `J₁` with respect to `(S₁; z/x)`
  have hgnorm := isNormalizedStandardBase_strictTransform_of_frameTransform J F Q hQperm hzQ T hsep
    s hxQ hxspan' FT hFTx hnu hF₁ f hf hfQ ν hν g hg
  -- Theorem 6 for `R₁`: `ν_{P₁}(g_j) = ν_j`
  have hJ₁top : J₁ ≠ ⊤ := ne_top_of_le_ne_top (Ideal.IsPrime.ne_top inferInstance) hJ₁P₁
  have hzP₁ : FT.toRegularFrame.idealZ ≤ P₁ := Ideal.span_le.mpr (by
    rintro _ ⟨j, rfl⟩
    exact (hzF j).symm ▸ hwP₁ _)
  have hgP₁ : ∀ j : Fin m, Ideal.ordElem P₁ (g j) = nuI T.ring J₁ (j : ℕ).succPNat :=
    (isPermissibleCenter_iff_ordElem_eq_nuI FT.toRegularFrame J₁ hJ₁top g hgnorm P₁ hP₁reg
      hzP₁).mp hperm₁
  have hnuI : ∀ i, nuI T.ring J₁ i = nuI R J i := fun i => congrFun (toLex.injective hnu) i
  -- `T.x ∉ P`
  have hxP : T.x ∉ P := by
    intro hxP
    have h1 : T.xR ∈ P₁ := by
      show T.toRing T.x ∈ P₁
      rw [← Ideal.mem_comap, hP₁]; exact hxP
    have h2 : T.toRing (algebraMap F.S R s) ∈ Ideal.span {T.xR} := by
      rw [T.span_xR_eq_map]
      exact Ideal.mem_map_of_mem _ hxQ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h2
    have h3 : T.toRing (algebraMap F.S R s) ∈ P₁ := by
      rw [← hc]; exact Ideal.mul_mem_left _ _ h1
    have h4 : x₀ ∈ P₁.comap T.toRing := by
      rw [Ideal.mem_comap, ← hs]; exact h3
    exact hx₀P (hP₁ ▸ h4)
  -- `ν_P(f_j) = ν_j` (p. 259: "`x` is a unit in `R_P = (R₁)_{P₁}`")
  have hfP : ∀ j : Fin m, Ideal.ordElem P (f j) = nuI R J (j : ℕ).succPNat := by
    intro j
    refine le_antisymm ?_ ?_
    · rw [← ordElem_eq_nuI_of_isStandardBase J f hf.1 j]
      exact Ideal.ordElem_mono (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) _
    · rw [← hν j]
      refine T.le_ordElem_of_le_ordElem_toRing P P₁ hP₁ hxP (f j) _ ?_
      have hgj : g j ∈ P₁ ^ ν j :=
        Ideal.mem_pow_of_ordElem ((hgP₁ j).trans ((hnuI _).trans (hν j).symm))
      rw [← hg j]
      exact Ideal.le_ordElem (Ideal.mul_mem_left _ _ hgj)
  -- `P` is a permissible center for `J`: condition (ii)** of Definition 8
  refine Or.inr ⟨inferInstance, hJP, inferInstance, ?_⟩
  have h13 : IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)) ↔
      ∃ (m : ℕ) (f : Fin m → R), IsStandardBase R J f ∧
        ∀ j : Fin m, Ideal.ordElem P (f j) = nuI R J ((j : ℕ).succPNat) :=
    (isPermissibleCenter_tfae R J P hJP).out 1 3
  exact h13.mpr ⟨m, f, hf.1, hfP⟩

end Proposition2Reduced

/-! ### Proposition 2 (pp. 258–259) -/

section Proposition2

/-- Proposition 2, p. 258: "Let `R` be a regular local ring which has the same characteristic as
its residue field. Let `J` be an ideal in `R` and `P`, `Q` prime ideals in `R` such that
(i) `Q ⊃ P ⊇ J` and `Q ≠ P`, (ii) `R/P` is regular, and (iii) `Q` is a permissible center for
`J`. Let `R₁` be a monoidal transform of `R` with center `Q` which is residually separable
algebraic over `R`, and `J₁` the strict transform of `J` in `R₁`. Suppose we have a prime ideal
`P₁` in `R₁` such that `P₁ ∩ R = P`. If `ν*(J₁) = ν*(J)` and `P₁` is a permissible center for
`J₁`, then `P` is a permissible center for `J`."

(Formalization notes.
* "`R` has the same characteristic as its residue field" is
  `ringChar R = ringChar (ResidueField R)` (see the module docstring: Mathlib has no named notion
  of equal characteristic).
* (i) is `P ≤ Q`, `J ≤ P` and `Q ≠ P`; `P₁ ∩ R = P` is `P₁.comap T.toRing = P`.
* `[IsLocalHom T.toRing]`, `[IsRegularLocalRing T.ring]` and `[IsDomain R]` are lemmas of §2
  taken as hypotheses.)

The proof is the paper's: "We may assume that `R` is complete, and that `R₁` is residually
rational over `R`" is `proposition2_of_complete_residuallyRational`
(`Hironaka/Compat/CompleteRationalBaseChange.lean`), and the rest of the proof of pp. 258–259 is
`isPermissibleCenter_of_nuStar_strictTransform_eq_of_isAdicComplete` (the case of a complete `R`
and a residually rational `R₁`), whose docstring records the deviations from the paper and the
gaps filled; the cited results used are Cohen's coefficient field in equal characteristic
(`exists_residue_comp_eq_id_of_isAdicComplete_of_ringChar_eq`) and the leaves of Lemma 18. -/
@[blueprint "prop:III.8-2"
  (statement := /-- Let $R$ be a regular local ring which has the same characteristic as its
    residue field. Let $J$ be an ideal in $R$ and $P$, $Q$ prime ideals in $R$ such that
    \begin{enumerate}
      \item[(i)] $Q\supset P\supseteq J$ and $Q\ne P$,
      \item[(ii)] $R/P$ is regular, and
      \item[(iii)] $Q$ is a permissible center for $J$ (\cref{def:III.8}).
    \end{enumerate}
    Let $R_1$ be a monoidal transform of $R$ with center $Q$
    (\cref{def:III.2-monoidal-transform}) which is residually separable algebraic over $R$,
    and $J_1$ the strict transform of $J$ in $R_1$ (\cref{def:III.5-strict}). Suppose we have a
    prime ideal $P_1$ in $R_1$ such that $P_1\cap R=P$. If $\nu^*(J_1)=\nu^*(J)$
    (\cref{def:III.2}) and $P_1$ is a permissible center for $J_1$, then $P$ is a permissible
    center for $J$. (Proposition 2, p.~258.)

    (Formalization note: ``$R$ has the same characteristic as its residue field'' is
    $\operatorname{char}R=\operatorname{char}(R/M)$, Mathlib having no named notion of equal
    characteristic; $P_1\cap R$ is the preimage of $P_1$ under $R\to R_1$; that $R\to R_1$ is
    local and that $R_1$ is a regular local ring are lemmas of \S2 taken as hypotheses.) -/)
  (proof := /-- We may assume that $R$ is complete, and that $R_1$ is residually rational over
    $R$. Then $R$ is a formal power series ring over a field, by Cohen's structure theorem.
    Since $\nu^*(J_1)=\nu^*(J)$, there can be found a regular $\tau$-frame
    $(S;z_1,\dots,z_r)$ of $R$ for $J$ (\cref{def:III.10}), which admits a frame transform
    $(S_1;z_1/x,\dots,z_r/x)$ in the monoidal transform $R_1$ with denominator $x\in S$
    (\cref{def:III.8-frame-transform}). In fact, let us choose a minimal base
    $(x,z_1,\dots,z_t)$ of $Q$, where $t=\dim(R_Q)-1$, such that $(x)R_1=QR_1$ and all the
    $z_i/x$ $(1\le i\le t)$ are contained in the maximal ideal of $R_1$. Let $(y_1,\dots,y_s)$
    be a system of elements of $R$ such that $(x,z_1,\dots,z_t,y_1,\dots,y_s)$ is a regular
    system of parameters of $R$. We have a subfield $k$ of $R$ such that
    $R=k\{x,z_1,\dots,z_t,y_1,\dots,y_s\}$. By Lemma~14, \S5 (\cref{lem:III.14}), we have a
    standard base $(h_1,\dots,h_m)$ of $J$ such that, if $\nu_j=\nu_M(h_j)=\nu^{(j)}(J)$, then
    $\nu_Q(h_j)=\nu_j$ and $\nu_{M_1}(x^{-\nu_j}h_j)=\nu_j$ for all $j$ $(1\le j\le m)$, where
    $M$ (resp.\ $M_1$) denotes the maximal ideal of $R$ (resp.\ $R_1$). Therefore, the initial
    forms of the $h_j$ in $\operatorname{gr}_M(R)$ must belong to the $(R/M)$-subalgebra of
    $\operatorname{gr}_M(R)$ generated by the initial forms of the $z_i$ $(1\le i\le t)$. It
    is then easily seen that, by applying a suitable $k$-linear transformation to the system
    $(z_1,\dots,z_t)$, we can assume $(z_1,\dots,z_r)$ $(r\le t)$ to be a regular system of
    $\tau$-parameters of $R$ for $J$ (\cref{def:III.7}). Let
    $S=k\{z_{r+1},\dots,z_t,x,y_1,\dots,y_s\}$. Then $(S;z_1,\dots,z_r)$ is a regular
    $\tau$-frame of $R$ for $J$ having the required property as above. Moreover, by
    Proposition~1, \S5 (\cref{prop:III.5-1}), we have $\tau^*(J_1)=\tau^*(J)$, and therefore
    we can choose the above $(z_1,\dots,z_r)$ in such a way that the transform
    $(S_1;z_1/x,\dots,z_r/x)$ is a regular $\tau$-frame of $R_1$ for $J_1$. (See the proof of
    Lemma~16, \S5, \cref{lem:III.16}.) By the assumption that $P_1$ is a permissible center
    for $J_1$, we can choose it in such a way that $z_j/x\in P_1$ for all $j$ $(1\le j\le r)$.
    (See Lemma~11, \S4, \cref{lem:III.11}.) Now, let $(f_1,\dots,f_m)$ be a normalized
    standard base of $J$ with respect to $(S;z_1,\dots,z_r)$
    (\cref{def:III.9-normalized-standard-base}). (For the existence, see Lemmas~17 and~19 of
    \S7, \cref{lem:III.17}, \cref{lem:III.19}, and footnote~11,
    \cref{lem:III.8-normalized-standard-base-exists}.) Let $g_j=x^{-\nu_j}f_j$ with
    $\nu_j=\nu^{(j)}(J)$ for $1\le j\le m$. Then, in view of Lemmas~20 and~21
    (\cref{lem:III.20}, \cref{lem:III.21}), we see that $(g_1,\dots,g_m)$ is again a
    normalized standard base of $J_1$ with respect to $(S_1;z_1/x,\dots,z_r/x)$. By
    Theorem~6, \S7 (\cref{thm:III.6}), we conclude that $\nu_{P_1}(g_j)=\nu_j$ for all $j$
    $(1\le j\le m)$. However, $x$ is a unit in $R_P=(R_1)_{P_1}$, and therefore
    $\nu_{PR_P}(f_j)=\nu_j$ for all $j$ $(1\le j\le m)$ which implies $\nu_P(f_j)=\nu_j$ for
    all $j$ $(1\le j\le m)$ by the assumption (ii). It follows that $P$ is a permissible
    center for $J$. \qed

    \textbf{Gaps filled and repaired.} The reduction ``We may assume that $R$ is complete, and that
    $R_1$ is residually rational over $R$'' is
    \texttt{proposition2\_of\_complete\_residuallyRational}, and the rest is
    \cref{prop:III.8-2-complete}, which follows the printed text. The gaps filled are ``it is then
    easily seen \dots a suitable $k$-linear transformation'', ``(See the proof of Lemma 16)'' and
    ``(See Lemma 11)'' (alone not sufficient, see \cref{lem:III.8-2-tau-parameters}); $J=(0)$, the
    existence of $g_j$, $R_P=(R_1)_{P_1}$ and the passage from $\nu_{P_1}$ to $\nu_P$ are proved.
    The use of Lemma~21 (c) for the initial forms of the $g_j$ is replaced by Lemma~19 for
    $(R_1,J_1,(S_1;z/x))$, as its hypothesis (11) fails in general (gap in the paper repaired). -/)
  (latexEnv := "proposition")]
theorem isPermissibleCenter_of_nuStar_strictTransform_eq [Hironaka.HironakaCitedResults.{u}] (R : Type u) [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] (hchar : ringChar R = ringChar (ResidueField R))
    (J P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P ≤ Q) (hJP : J ≤ P) (hQP : Q ≠ P)
    [IsRegularLocalRing (R ⧸ P)] (hQperm : IsPermissibleCenter R J Q)
    (T : MonoidalTransform R Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing)
    (P₁ : Ideal T.ring) [P₁.IsPrime] (hP₁ : P₁.comap T.toRing = P)
    (hnu : nuStar T.ring (strictTransformIdeal T J) = nuStar R J)
    (hperm₁ : IsPermissibleCenter T.ring (strictTransformIdeal T J) P₁) :
    IsPermissibleCenter R J P :=
  proposition2_of_complete_residuallyRational
    (fun _R _ _ _ _ hchar J P Q _ _ hPQ hJP hQP _ hQperm T _ _ hsep hrat P₁ _ hP₁ hnu hperm₁ =>
      isPermissibleCenter_of_nuStar_strictTransform_eq_of_isAdicComplete hchar J P Q hPQ hJP hQP
        hQperm T hsep hrat P₁ hP₁ hnu hperm₁)
    R hchar J P Q hPQ hJP hQP hQperm T hsep P₁ hP₁ hnu hperm₁

end Proposition2

/-! ### Corollary 1 of Proposition 2 (pp. 259–260) -/

section Corollary1

/-- Corollary 1, p. 259: "Let `R` be a regular local ring whose residue field is a perfect field
of the same characteristic as that of `R`. Let `J` be an ideal in `R`, and `P`, `Q` prime ideals
in `R` such that (i) `Q ⊃ P ⊇ J` and `Q ≠ P`, and (ii) both `R/P` and `R/Q` are regular. Let
`(f₁, …, f_m)` be a system of elements of `J` such that, `M` denoting the maximal ideal in `R`,
(iii) `ν_M(f_j) = ν_Q(f_j)` for all `j` (`1 ≤ j ≤ m`), and (iv) the initial forms of `f_j` in
`gr_M(R)` generate the ideal `gr_M(J, R)`. Let `R₁` be any monoidal transform of `R` with center
`Q`, `M₁` the maximal ideal of `R₁`, and `J₁` the strict transform of `J` in `R₁`, such that
(v) there exists a prime ideal `P₁` in `R₁` with `P₁ ∩ R = P`, and (vi) `ν_{M₁}(f_j x^{-ν_j}) = ν_j`
where `ν_j = ν_Q(f_j)` (`1 ≤ j ≤ m`) and `x` is an element of `Q` such that `(x)R₁ = QR₁`. If `P₁`
is a permissible center for `J₁`, then `P` is a permissible center for `J`."

(Formalization notes.
* "residue field … a perfect field of the same characteristic as that of `R`" is
  `[PerfectField (ResidueField R)]` together with `ringChar (ResidueField R) = ringChar R`.
* (v) and (vi) are data: the prime `P₁` with `P₁.comap T.toRing = P`, the element `x ∈ Q` with
  `QR₁ = (x)R₁`, the integers `ν_j` with `ν_j = ν_Q(f_j)` (which records their finiteness), and
  the elements `g_j = f_j x^{-ν_j}` of `R₁` (`x^{ν_j} g_j = f_j`) with `ν_{M₁}(g_j) = ν_j`.  The
  conclusion is for this `P₁`.
* No residual assumption is made on `R₁` ("any monoidal transform"), as in the paper.)

Cited (footnote 12, p. 260, "cf. Zariski [29]"): the singular locus of `Spec(Ā)`, `Ā` of finite type
over a perfect field, is closed (`isClosed_compl_regularLocus_of_finiteType`,
`Hironaka/Compat/RegularClosedPoint.lean`; `IsHironakaBase.isClosed_singularLocus` is not usable,
as `IsHironakaBase.of_field` needs characteristic zero).  This is the only leaf the proof uses
besides Proposition 2 itself.

Deviation from the paper (gap filled): everything in the proof except the last sentence is carried
out in `exists_transform_of_perfectField_residueField`
(`Hironaka/Compat/PermissibleCenterBlowdown.lean`).  (a) "nowhere dense" and the existence of a
maximal ideal `N'` with `A_{N'}/NA_{N'}` regular are derived from the cited closedness (the generic
point is regular, closed points are dense).  (b) "The assumption (vi) is equivalent to saying that
`ν_H(g_j) = ν_j`. It follows, by Theorem 5, …": Theorem 5 needs `ν_{M₁'}(g_j) = ν_j`, which follows
from `ν_H ≤ ν_{M₁'}` and Lemma 8 of §3 (`ν_{M₁'}(g_j) ≤ ν_M(f_j)`), and `ν_H(g_j) = ν_{M₁}(g_j)`
needs the regularity of `R₁'/H` (`ν_H = ν_{HR_H}`).  (c) "a suitable subsystem (suitably
reordered) of `(g_1, …, g_m)` is a standard base of `J₁'`" is `exists_isStandardBase_comp` applied
to `(f_j)` (hypothesis (iv)).  (d) "`R₁ = (R₁')_H`, `J₁ = (J₁')R₁`, `P₁ = (P₁')R₁`" and the passage
from `P₁` to `P₁'` by Theorem 3 of Ch. II involve the identification of `(R₁'/J₁')_{H/J₁'}` with
`R₁/J₁` (`isNormallyFlatAlongIdeal_of_localizationEquiv`); the regularity of `R₁'/P₁'` ("it is
clear because it is a monoidal transform of `R/P` with center `Q/P`") is proved.  (e) The algebra
`A` is the chart `R[T.x⁻¹Q]` of the given transform `T` (so `R₁ = A_N`, with `x := T.x`), not
`R[x₁/x, …, x_r/x]` for the element `x` of (vi); this is harmless, hypothesis (vi) being
invariant under a unit factor.  Proposition 2
(`isPermissibleCenter_of_nuStar_strictTransform_eq`) is used as stated. -/
@[blueprint "cor:III.prop2-1"
  (statement := /-- Let $R$ be a regular local ring whose residue field is a perfect field of
    the same characteristic as that of $R$. Let $J$ be an ideal in $R$, and $P$, $Q$ prime
    ideals in $R$ such that
    \begin{enumerate}
      \item[(i)] $Q\supset P\supseteq J$ and $Q\ne P$, and
      \item[(ii)] both $R/P$ and $R/Q$ are regular.
    \end{enumerate}
    Let $(f_1,\dots,f_m)$ be a system of elements of $J$ such that, $M$ denoting the maximal
    ideal in $R$,
    \begin{enumerate}
      \item[(iii)] $\nu_M(f_j)=\nu_Q(f_j)$ for all $j$ $(1\le j\le m)$, and
      \item[(iv)] the initial forms of $f_j$ in $\operatorname{gr}_M(R)$ generate the ideal
        $\operatorname{gr}_M(J,R)$.
    \end{enumerate}
    Let $R_1$ be any monoidal transform of $R$ with center $Q$
    (\cref{def:III.2-monoidal-transform}), $M_1$ the maximal ideal of $R_1$, and $J_1$ the
    strict transform of $J$ in $R_1$ (\cref{def:III.5-strict}), such that
    \begin{enumerate}
      \item[(v)] there exists a prime ideal $P_1$ in $R_1$ with $P_1\cap R=P$, and
      \item[(vi)] $\nu_{M_1}(f_jx^{-\nu_j})=\nu_j$ where $\nu_j=\nu_Q(f_j)$ $(1\le j\le m)$ and
        $x$ is an element of $Q$ such that $(x)R_1=QR_1$.
    \end{enumerate}
    If $P_1$ is a permissible center for $J_1$ (\cref{def:III.8}), then $P$ is a permissible
    center for $J$. (Corollary 1, p.~259.)

    (Formalization note: ``of the same characteristic'' is
    $\operatorname{char}(R/M)=\operatorname{char}R$; $x$, the $\nu_j$ and the elements
    $f_jx^{-\nu_j}$ of $R_1$ are data satisfying (vi); that $R\to R_1$ is local and that
    $R_1$ is a regular local ring are lemmas of \S2 taken as hypotheses.) -/)
  (proof := /-- We first remark that $Q$ is a permissible center for $J$ by (ii), (iii) and
    (iv). Let us choose an element $x$ of $Q$ in such a way as in (vi). We then take a minimal
    base $(x,x_1,\dots,x_r)$ of the prime ideal $Q$. Let $A=R[x_1/x,\dots,x_r/x]$. Then there
    exists a prime ideal $N$ in $A$ such that $R_1=A_N$. We have $N\cap R=M$, and therefore
    $\bar A=A/N$ is an algebra of finite type over the residue field of $R$. We then know that
    the singular locus of $\operatorname{Spec}(\bar A)$ is a nowhere dense closed subset
    (footnote~12: ``cf.\ Zariski [29].''). Therefore we can find a maximal ideal $N'$ in $A$
    such that $N'$ contains $N$ and that $A_{N'}/NA_{N'}$ is regular. Let $R_1'=A_{N'}$. Then
    $R_1'$ is a monoidal transform of $R$ with center $Q$ such that $R_1'$ is residually
    algebraic (hence, separable algebraic) over $R$, and that there exists a prime ideal $H$
    in $R_1'$ such that $R_1=(R_1')_H$. Moreover, we have that $R_1'/H$ is regular. Let $J_1'$
    be the strict transform of $J$ in $R_1'$. We have $(x)R_1'=QR_1'$ and hence, if
    $g_j=f_jx^{-\nu_j}$ $(1\le j\le m)$, these $g_j$ are elements of $J_1'$. The assumption
    (vi) is equivalent to saying that $\nu_H(g_j)=\nu_j$ for all $j$. It follows, by
    Theorem~5, \S6 (\cref{thm:III.5}), that $\nu^*(J)=\nu^*(J_1')$, that a suitable subsystem
    (suitably reordered) of $(g_1,\dots,g_m)$ is a standard base of $J_1'$, and that $H$ is a
    permissible center for $J_1'$. We have $R_1=(R_1')_H$, $J_1=(J_1')R_1$ and
    $P_1=(P_1')R_1$ with $P_1'=P_1\cap R_1'$ [the printed text omits the primes:
    ``$P_1=(P_1)R_1$ with $P_1=P_1\cap R_1'$'']. Therefore, by Theorem~3, \S3, Ch.~II
    (\cref{thm:II.3-3}), if $P_1$ is a permissible center for $J_1$, then $P_1'$ is a
    permissible center for $J_1'$. (It should be noted that the regularity of $R_1'/P_1'$ is
    clear because it is a monoidal transform of $R/P$ with center $Q/P$.) This implies, by
    Proposition~2 (\cref{prop:III.8-2}), that $P$ is a permissible center for $J$. \qed

    \textbf{Gap in the paper filled.} The Lean proof is \cref{lem:III.8-cor1-reduction} followed by
    Proposition~2. (a) ``nowhere dense'' and the existence of $N'$ with $A_{N'}/NA_{N'}$ regular are
    derived from the cited closedness of the singular locus
    (\cref{lem:III.8-singular-locus-closed}, \cref{lem:III.8-cor1-closed-point}): the generic
    point of $\bar A$ is regular and the closed points are dense. (b) Theorem~5 needs
    $\nu_{M_1'}(g_j)=\nu_j$, not $\nu_H(g_j)=\nu_j$; it follows from $\nu_H\le\nu_{M_1'}$ and
    Lemma~8 (\cref{lem:III.8-cor1-lemma8}), and $\nu_H(g_j)=\nu_{M_1}(g_j)$ uses that $R_1'/H$ is
    regular. (c) The subsystem of $(g_1,\dots,g_m)$ that is a standard base is obtained from
    the standard base contained in $(f_1,\dots,f_m)$. (d) The identification of
    $(R_1'/J_1')_{H/J_1'}$ with $R_1/J_1$ for the use of Theorem~3, Ch.~II
    (\cref{lem:III.8-cor1-descent}), and the regularity of $R_1'/P_1'$ are proved. (e) The algebra
    $A$ is the chart $R[T.x^{-1}Q]$ of the given transform. -/)
  (latexEnv := "corollary")]
theorem isPermissibleCenter_of_perfectField_residueField [Hironaka.HironakaCitedResults.{u}] (R : Type u) [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] [PerfectField (ResidueField R)]
    (hchar : ringChar (ResidueField R) = ringChar R)
    (J P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P ≤ Q) (hJP : J ≤ P) (hQP : Q ≠ P)
    [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)]
    {m : ℕ} (f : Fin m → R) (hfJ : ∀ j, f j ∈ J)
    (hiii : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = Ideal.ordElem Q (f j))
    (hiv : Ideal.span (Set.range fun j => initialForm (maximalIdeal R) (f j)) =
      grIdeal (maximalIdeal R) J)
    (T : MonoidalTransform R Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (P₁ : Ideal T.ring) [P₁.IsPrime] (hv : P₁.comap T.toRing = P)
    (x : R) (_hxQ : x ∈ Q) (hx : Q.map T.toRing = Ideal.span {T.toRing x})
    (ν : Fin m → ℕ) (hν : ∀ j, (ν j : ℕ∞) = Ideal.ordElem Q (f j))
    (g : Fin m → T.ring) (hg : ∀ j, T.toRing x ^ ν j * g j = T.toRing (f j))
    (hvi : ∀ j, Ideal.ordElem (maximalIdeal T.ring) (g j) = (ν j : ℕ∞))
    (hperm₁ : IsPermissibleCenter T.ring (strictTransformIdeal T J) P₁) :
    IsPermissibleCenter R J P := by
  classical
  have hJQ : J ≤ Q := hJP.trans hPQ
  -- "We first remark that `Q` is a permissible center for `J` by (ii), (iii) and (iv)."
  have hQperm : IsPermissibleCenter R J Q := by
    refine Or.inr ⟨inferInstance, hJQ, inferInstance, ?_⟩
    have h12 : IsNormallyFlatAlongIdeal (Q.map (Ideal.Quotient.mk J)) ↔
        HasInitialFormSystem J Q (maximalIdeal R) :=
      (isPermissibleCenter_tfae R J Q hJQ).out 1 2
    exact h12.mpr ⟨m, f, hfJ, hiii, hiv⟩
  -- the monoidal transform `R₁'` at a closed point with regular reduction, and `P₁' = P₁ ∩ R₁'`
  obtain ⟨T', hloc, hreg, hsep, P₁', hP₁', hcomap, hnu, hperm⟩ :=
    exists_transform_of_perfectField_residueField J P Q hPQ hJP hQP f hfJ hiii hiv T P₁ hv x hx ν
      hν g hg hvi hperm₁
  -- "This implies, by Proposition 2, that `P` is a permissible center for `J`."
  exact isPermissibleCenter_of_nuStar_strictTransform_eq R hchar.symm J P Q hPQ hJP hQP hQperm T'
    hsep P₁' hcomap hnu hperm

end Corollary1

/-! ### Corollary 2 of Proposition 2 (pp. 260–261) -/

section Corollary2

/-- Corollary 2, p. 260: "Let `R` be a regular local ring and `M` the maximal ideal in `R`. Let
us assume that the residue field `R/M` has characteristic zero. Let `Q` be a prime ideal in `R`,
and `J` an ideal in `R` such that `Q ⊇ J`. Suppose we have a system of elements `(g₁, …, g_m)`
of `J` such that (i) the initial forms of `g_j` (`1 ≤ j ≤ m`) in `gr_M(R)` generate the ideal
`gr_M(J, R)`, and (ii) `ν_M(g_j) = ν_{QR_Q}(g_j)` for all `j` (`1 ≤ j ≤ m`). Let `P` be a prime
ideal in `R` such that `Q ⊇ P ⊇ J` and that `R/P` is regular. If `gr_{PR_Q}(R_Q/JR_Q)` is flat
over `R_Q/PR_Q`, then `gr_P(R/J)` is flat over `R/P`."

(Formalization notes.
* "`R/M` has characteristic zero" is `[CharZero (ResidueField R)]`, as in Corollary 3 (c) of
  Theorem 5.
* "a system of elements `(g₁, …, g_m)` of `J` such that (i), (ii)" is
  `IsLocallyAdaptedSystem R Q J g` (`Hironaka/Ch3/Stability.lean`): these are literally the
  hypotheses (i), (ii) of Corollary 3 of Theorem 5, whose assertions (b), (c) the proof invokes.
* "`gr_{PR_Q}(R_Q/JR_Q)` is flat over `R_Q/PR_Q`" and "`gr_P(R/J)` is flat over `R/P`" are
  `IsNormallyFlatAlongIdeal` of the image of `PR_Q` in `R_Q/JR_Q`, resp. of `P` in `R/J`
  (Definition 1 of Ch. 0, as in condition (ii) of Definition 8; equivalent to flatness of the
  associated graded ring for the noetherian local rings `R_Q/JR_Q` and `R/J`).)

The proof is the printed one, carried out in `Hironaka/Compat/NormalFlatnessLocalization.lean` with
Proposition 2 as a hypothesis (`Proposition2Statement`), which is supplied here.  The passage to the
completion (`corollary2Dim_of_complete`): `Q̂` is a minimal prime of `QR̂` with
`dim(R̂/Q̂) = dim(R/Q)` (`Q̂ ∩ R = Q`; "We can assume that `dim(R̂/Q̂) = dim(R/Q)`" uses the cited
fact
`ringKrullDim_adicCompletion_quotient_eq` of `Hironaka/Compat/DimensionFacts.lean`, footnote 3,
p. 116), and the passage from `R̂` back to `R` is Lemma 9, §3, Ch. II for the faithfully flat map
`R/J → R̂/JR̂` (`isNormallyFlatAlongIdeal_map_iff`).  The induction on `dim(R/Q)`
(`corollary2Dim`, `corollary2DimComplete_of_forall_lt`): `R/Q` regular is the base case; for
`dim(R/Q) = 1` the dimension-one case; for `dim(R/Q) > 1` a prime `Q' ⊇ Q` with `dim(R/Q') = 1`
(`exists_prime_adjacent_maximalIdeal_of_ringKrullDim_quotient_eq`), (i), (ii) for `R_{Q'}` by
Corollary 3 (c), the induction assumption for `R_{Q'}`
(`isNormallyFlatAlongIdeal_localization_of_le`)
and then the dimension-one case for `Q'`.

The dimension-one case follows the printed text (`isNormallyFlatAlongIdeal_of_dimensionLEOne`): "Let
us take a monoidal transform `R₁` of `R` with center `M` which is residually algebraic over `R` and
such that there exists a prime ideal `Q₁` in `R₁` with `Q₁ ∩ R = Q`" is an arbitrary such pair; the
argument uses only these properties.  Gaps filled: that such a pair exists
(`exists_monoidalTransform_curveImage_lt`), and "the process cannot be repeated infinitely many
times" (for every such pair `φ(R₁)` is again a localization of `φ(R₁) ∩ W` and the submodule
`φ(R) ∩ W` of the integral closure `W` of `R/Q` strictly increases,
`exists_ringHom_curveImage_lt_of_comap_eq`).  The prime `P₁` with `P₁ ∩ R = P` ("if `P₁` is the
prime ideal in `R₁` with `P₁ ∩ R = P`"), the regularity of `R₁/P₁`, `R_Q = (R₁)_{Q₁}`,
`PR_Q = P₁(R₁)_{Q₁}`, `JR_Q = J₁(R₁)_{Q₁}`, `ν*(J₁) = ν*(J)`, and that `M` is a permissible center
for `J` (hypotheses of Proposition 2) are proved. -/
@[blueprint "cor:III.prop2-2"
  (statement := /-- Let $R$ be a regular local ring and $M$ the maximal ideal in $R$. Let us
    assume that the residue field $R/M$ has characteristic zero. Let $Q$ be a prime ideal in
    $R$, and $J$ an ideal in $R$ such that $Q\supseteq J$. Suppose we have a system of elements
    $(g_1,\dots,g_m)$ of $J$ such that
    \begin{enumerate}
      \item[(i)] the initial forms of $g_j$ $(1\le j\le m)$ in $\operatorname{gr}_M(R)$
        generate the ideal $\operatorname{gr}_M(J,R)$, and
      \item[(ii)] $\nu_M(g_j)=\nu_{QR_Q}(g_j)$ for all $j$ $(1\le j\le m)$.
    \end{enumerate}
    Let $P$ be a prime ideal in $R$ such that $Q\supseteq P\supseteq J$ and that $R/P$ is
    regular. If $\operatorname{gr}_{PR_Q}(R_Q/JR_Q)$ is flat over $R_Q/PR_Q$, then
    $\operatorname{gr}_P(R/J)$ is flat over $R/P$. (Corollary 2, p.~260.)

    (Formalization note: (i) and (ii) are the hypotheses of Corollary~3 of Theorem~5
    (\cref{cor:III.thm5-3a}); the flatness of $\operatorname{gr}$ is encoded, as in
    \cref{def:III.8}, by the normal flatness of Ch.~0 (\cref{def:normally-flat-ideal}), which
    is equivalent to it for the noetherian local rings $R_Q/JR_Q$ and $R/J$.) -/)
  (proof := /-- Let $\hat R$ be the completion of $R$, and $\hat P=P\hat R$. We see that
    $\hat P$ is a prime ideal in $\hat R$ such that $\hat R/\hat P$ is regular. Let $\hat Q$ be
    a minimal prime ideal associated with $Q\hat R$, i.e., $\hat Q\cap R=Q$ and
    $Q\hat R_{\hat Q}$ is primary to the maximal ideal. We have
    $\nu_{\hat Q\hat R_{\hat Q}}(g_j)\ge\nu_{QR_Q}(g_j)$, and $\nu_{\hat M}(g_j)=\nu_M(g_j)$
    where $\hat M=M\hat R$ which is the maximal ideal of $\hat R$. Therefore, by Theorem~1,
    \S3 (\cref{thm:III.1}), (ii) implies that $\nu_{\hat M}(g_j)=\nu_{\hat Q\hat R_{\hat Q}}(g_j)$
    for all $j$. Moreover, it is clear that (i) implies that the initial forms of $g_j$
    $(1\le j\le m)$ in $\operatorname{gr}_{\hat M}(\hat R)$ generate the ideal
    $\operatorname{gr}_{\hat M}(\hat J,\hat R)$, where $\hat J=J\hat R$. (See Lemma~2, \S1,
    \cref{lem:III.2}.) We know that $\hat R_{\hat Q}$ is faithfully flat over $R_Q$. Hence, by
    Lemma~9, \S3, Ch.~II (\cref{lem:II.3-9}), $\operatorname{gr}_{PR_Q}(R_Q/JR_Q)$ is flat
    over $R_Q/PR_Q$ if and only if
    $\operatorname{gr}_{P\hat R_{\hat Q}}(\hat R_{\hat Q}/J\hat R_{\hat Q})$ is flat over
    $\hat R_{\hat Q}/P\hat R_{\hat Q}$. Here we have $P\hat R_{\hat Q}=\hat P\hat R_{\hat Q}$ and
    $J\hat R_{\hat Q}=\hat J\hat R_{\hat Q}$. For the same reason, $\operatorname{gr}_P(R/J)$
    is flat over $R/P$ if and only if $\operatorname{gr}_{\hat P}(\hat R/\hat J)$ is flat over
    $\hat R/\hat P$. We can assume that $\dim(\hat R/\hat Q)=\dim(R/Q)$. Now, the proof of
    Corollary~2 is done by induction on $\dim(R/Q)$. Let us first consider the case of
    $\dim(R/Q)=1$. By the above arguments, we may assume that $R$ is complete. Therefore, the
    integral closure of $R/Q$ in its field of quotients is a finite $R/Q$-module. Let us take
    a monoidal transform $R_1$ of $R$ with center $M$ which is residually algebraic over $R$
    and such that there exists a prime ideal $Q_1$ in $R_1$ with $Q_1\cap R=Q$. Let $J_1$ be
    the strict transform of $J$ in $R_1$. Let $x$ be an element of $M$ such that
    $(x)R_1=MR_1$, and $g_j'=g_jx^{-\nu_j}$ for each $j$, where $\nu_j=\nu_M(g_j)$. Then, by
    Corollary~3~(b) of Theorem~5, \S6 (\cref{cor:III.thm5-3b}), the assumptions (i) and (ii)
    remain valid for $R_1$, $M_1$ ($=$ the maximal ideal of $R_1$), $Q_1$, $J_1$, and the
    system $(g_1',\dots,g_m')$. Moreover, if $P_1$ is the prime ideal in $R_1$ with
    $P_1\cap R=P$, then Proposition~2 (\cref{prop:III.8-2}) shows that the flatness of
    $\operatorname{gr}_P(R/J)$ over $R/P$ follows the same of
    $\operatorname{gr}_{P_1}(R_1/J_1)$ over $R_1/P_1$. (See Corollary~3~(b) of Theorem~5,
    \S6.) Furthermore, $R_Q=(R_1)_{Q_1}$, $JR_Q=J_1(R_1)_{Q_1}$, and $PR_Q=P_1(R_1)_{Q_1}$.
    Therefore, in order to prove the assertion of Corollary~2, we may replace $R$, $J$, $Q$,
    and $P$ by $R_1$, $J_1$, $Q_1$, and $P_1$ respectively. We know that the assertion is
    verified if $R/Q$ is regular, by Theorem~3, \S3, Ch.~II (\cref{thm:II.3-3}), combined with
    Corollary~1 of Theorem~2, \S2, Ch.~II (\cref{cor:II.2-thm2-1}) and therefore, it is also
    done if $R_1/Q_1$ is regular. If $R_1/Q_1$ is not regular, we repeat the same process as
    above. As is easily seen, the process cannot be repeated infinitely many times. Let us
    consider the case of $\dim(R/Q)>1$. We may again assume that $R$ is complete. By the
    dimension assumption, we can find a prime ideal $Q'$ in $R$ such that $Q'$ contains $Q$ and
    $\dim(R/Q')=1$. By Corollary~3~(c) of Theorem~5, \S6 (\cref{cor:III.thm5-3c}), the
    assumptions (i) and (ii) remain valid if we replace $R$, $Q$, $J$, and $M$ by $R_{Q'}$,
    $QR_{Q'}$, $JR_{Q'}$, and $Q'R_{Q'}$, respectively. Therefore, by the induction
    assumption, the flatness of $\operatorname{gr}_{PR_Q}(R_Q/JR_Q)$ over $R_Q/PR_Q$ implies
    the same of $\operatorname{gr}_{PR_{Q'}}(R_{Q'}/JR_{Q'})$ over $R_{Q'}/PR_{Q'}$. By the
    above result for the 1-dimensional case, the flatness of $\operatorname{gr}_P(R/J)$ over
    $R/P$ follows. \qed

    \textbf{Gaps in the paper filled.} The Lean proof is the printed one:
    \cref{lem:III.8-cor2-completion} (the passage to the completion, with $\hat Q$ a minimal
    prime of $Q\hat R$ with $\dim(\hat R/\hat Q)=\dim(R/Q)$, cited in
    \cref{lem:III.8-cor2-completion-dimension}, and descent by Lemma~9, \S3, Ch.~II) and the
    induction on $\dim(R/Q)$ (\cref{lem:III.8-cor2-finite}, \cref{lem:III.8-cor2-adjacent}),
    applied to Proposition~2. In the case $\dim(R/Q)=1$ (\cref{lem:III.8-cor2-curve}) the
    monoidal transform $R_1$ with center $M$, residually algebraic over $R$, and the prime $Q_1$
    are arbitrary (their existence and the termination of the process are
    \cref{cor:III.thm5-3c}, gaps filled); the prime $P_1$ with $P_1\cap R=P$ and the facts $R_Q=(R_1)_{Q_1}$, $PR_Q=P_1(R_1)_{Q_1}$,
    $JR_Q=J_1(R_1)_{Q_1}$, that $R_1/P_1$ is regular and $\nu^*(J_1)=\nu^*(J)$, and that $M$ is a
    permissible center for $J$ (hypotheses of Proposition~2) are proved
    (\cref{lem:III.8-cor2-transform-step}). -/)
  (latexEnv := "corollary")]
theorem isNormallyFlatAlongIdeal_of_localization [Hironaka.HironakaCitedResults.{u}] (R : Type u) [CommRing R]
    [IsRegularLocalRing R] [CharZero (ResidueField R)] (Q J : Ideal R) [Q.IsPrime] (_hJQ : J ≤ Q)
    {m : ℕ} (g : Fin m → R) (hg : IsLocallyAdaptedSystem R Q J g)
    (P : Ideal R) [P.IsPrime] (hPQ : P ≤ Q) (hJP : J ≤ P) [IsRegularLocalRing (R ⧸ P)]
    (hflat : IsNormallyFlatAlongIdeal
      ((P.map (algebraMap R (Localization.AtPrime Q))).map
        (Ideal.Quotient.mk (J.map (algebraMap R (Localization.AtPrime Q)))))) :
    IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)) := by
  exact isNormallyFlatAlongIdeal_of_proposition2 isPermissibleCenter_of_nuStar_strictTransform_eq
    Q J g hg P hJP hPQ inferInstance hflat

end Corollary2

end Hironaka
