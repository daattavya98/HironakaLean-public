/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Architect
public import Hironaka.Ch0.AlgebraicScheme
public import Hironaka.Ch0.Blowup
public import Hironaka.Ch0.Multiplicity
public import Hironaka.Ch0.NormalFlatness
public import Hironaka.Statements

/-!
# Ch. 0 §4 (pp. 133–138): the facts (A), (B), (C), Question (D), the theorem of B. Levi-Zariski, the character of
singularities and Question (D*)

This module states, without proofs, the parts of Ch. 0 §4 that are neither definitions already in the project
(multiplicity, equi-multiplicity, normal flatness: `Hironaka/Ch0/Multiplicity.lean`,
`Hironaka/Ch0/NormalFlatness.lean`) nor (I), (II) and Main Theorem I* (`Hironaka/Ch0/NormalFlatnessCriteria.lean`,
`Hironaka/Ch4/MainTheoremIZero.lean`).  Every statement is a `def … : Prop` (as `FundamentalTheorem.I₁` and
`ImplicationA` are): nothing here is proved, nothing is assumed, and no hypothesis of any other declaration refers to
these statements.  The analytic case of every statement is not formalized.

The printed text of Question (D) and of the paragraph that follows it, read from the page image (the statements of
(A), (B), (C), the theorem of B. Levi-Zariski, (I), the character of singularities and Question (D*) are quoted in the
docstrings of their declarations):

> Question (D).  Let `X` be the same as in (B), `W` a quasi-compact (or compact) set of points of `X`, and `d` the
> maximum of the multiplicities of `X` at the points in `W`, say `d > 1`.  We ask if there exists a finite succession
> of monoidal transformations `f_i : X_{i+1} → X_i` with centers `D_i` in `X_i`, say `0 ≦ i < r` and `X_0 = X`, such
> that (i) `D_i` is non-singular, and `X_i` is equi-multiple along `D_i` with multiplicity `≧ d` within a
> neighborhood of the preimage of `W` in `X_i`, for all `i`, and (ii) if `f` denotes the composition of the `f_i`,
> `X_r` has multiplicities `< d` at all points of `f⁻¹(W)`?  (p. 134)

> In the case of an algebraic `B`-scheme `X`, the role played by `W` is irrelevant to the question, and we take `W`
> to be the set of all points of `X`.  An affirmative answer to the question (D) can be obtained from the main
> theorem I in the strong form, with (a), (b), and (c) in the case of algebraic `B`-schemes with fields `B` of
> characteristic zero, and it seems quite plausible in general.  Obviously, if the answer to (D) is affirmative,
> then the resolution of singularities in the form of the main theorem I follows.  (p. 134)

The facts (A), (B), (C) are stated "One can prove" with no proof and no reference, and the paper defers the
proofs of Ch. 0 (footnote 2, p. 114): they are not proved here.

Encodings common to all statements of this module:

* "algebraic `B`-scheme with a field `B`" is a scheme `X` with a morphism `pX : X ⟶ Spec B`, `B : Type u` a field,
  `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` (a scheme is separated, p. 118; of finite type, pp. 118,
  162), as in `MainTheorem.Ch0.I` and the fact (*) of p. 141 (`RationalApplication.exists_finite_system_domain_precomp_eq`);
  `B` is any field in (A), (B), (C), (D) ("with a field `B`", no characteristic assumed) and a field of characteristic
  zero where the paper says so;
* "algebraic subscheme" is a `Subscheme X` (a closed subscheme, an ideal sheaf; `Hironaka/Statements.lean`); the
  points of it are `Subscheme.pts`;
* "the multiplicity of `X` at `x`" is `Scheme.multAt` and "equi-multiple along `D`" is `Subscheme.IsEquimultipleAlong`
  (`Hironaka/Ch0/Multiplicity.lean`); "simple" is `Scheme.IsSimpleAt`; "non-singular" is `Subscheme.IsNonsingular`;
  "the monoidal transformation of `X` with center `D`" is any `t : MonoidalTransformation X D` (they are unique up to
  isomorphism over `X`, p. 166);
* the analytic `K`-spaces of the paper are not formalized, so each "analytic subspace or algebraic subscheme" is
  read as the algebraic alternative.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u v

namespace Hironaka

namespace EquimultiplicityQuestions

/-! ### The facts (A), (B), (C) (p. 134) -/

/-- **(A) of p. 134** ("One can prove"; stated without proof or citation; not proved here): for an irreducible
algebraic `B`-scheme `X` with a field `B` and each integer `d` there is an algebraic subscheme `S_d` of `X` whose
points are exactly the points at which the multiplicity of `X` is `≧ d`.

> (A) If `X` is either an analytic `K`-space or an algebraic `B`-scheme, irreducible and with a field `B`, then for
> each integer `d` there exists an analytic subspace or an algebraic subscheme `S_d` of `X`, respectively, such that
> `x` is a point of `S_d` if and only if the multiplicity of `X` at `x` is greater than or equal to `d`.  (p. 134)

Formalization notes (encoding): `S_d` is a `Subscheme X`; "for each integer `d`" is `d : ℤ`, the inequality being
`d ≤ (X.multAt x : ℤ)` (for `d ≤ 1` the locus is all of `X`).  The analytic alternative is not formalized.

Stated without proof (p. 134, "One can prove"; no reference); proofs of Ch. 0 are deferred by the paper (footnote 2,
p. 114); not proved here.  Its truth was not checked here. -/
@[blueprint "prop:0.4-A"
  (statement := /-- Let $X$ be an irreducible algebraic $B$-scheme, $B$ a field. Then for each integer $d$ there
    exists an algebraic subscheme $S_d$ of $X$ such that $x$ is a point of $S_d$ if and only if the multiplicity of
    $X$ at $x$ is greater than or equal to $d$. (Ch.~0 \S4 (A), p.~134: ``One can prove'', analytic case omitted.)
    Formalization note (encoding): an algebraic $B$-scheme is separated and of finite type over the field $B$
    (pp.~118, 162); $d$ is an arbitrary integer. Not proved here: stated without proof (p.~134), proofs of Ch.~0
    deferred by the paper (footnote~2, p.~114). -/)
  (latexEnv := "proposition")]
def ExistsMultiplicityLocus : Prop :=
  ∀ (B : Type u) [Field B] {X : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType pX] [QuasiCompact pX] [IsSeparated pX] [IrreducibleSpace X] (d : ℤ),
    ∃ S : Subscheme X, ∀ x : X, x ∈ S.pts ↔ d ≤ (X.multAt x : ℤ)

/-- **(B) of p. 134** ("One can prove"; stated without proof or citation; not proved here): for a reduced and
irreducible algebraic `B`-scheme `X`, a non-singular subscheme `D` along which `X` is equi-multiple and the monoidal
transformation `f : X' → X` with center `D`, the multiplicity of `X'` at every `x'` is at most that of `X` at `f(x')`.

> (B) Let `X` be as above, and assume that `X` is reduced and irreducible.  Let `D` be a non-singular analytic
> subspace or algebraic subscheme of `X`, respectively, along which `X` is equi-multiple.  Let `f : X' → X` be the
> monoidal transformation of `X` with center `D`.  Then for every point `x'` of `X'` the multiplicity of `X'` at `x'`
> is at most equal to that of `X` at `f(x')`.  (p. 134)

Formalization notes (encoding): the multiplicity of `X'` is `Scheme.multAt` of `t.X'`; "the monoidal transformation"
is every `t : MonoidalTransformation X D`.  The analytic alternative is not formalized.

Stated without proof (p. 134, "One can prove"; no reference); proofs of Ch. 0 are deferred by the paper (footnote 2,
p. 114); not proved here.  Its truth was not checked here. -/
@[blueprint "prop:0.4-B"
  (statement := /-- Let $X$ be a reduced and irreducible algebraic $B$-scheme, $B$ a field. Let $D$ be a non-singular
    algebraic subscheme of $X$ along which $X$ is equi-multiple, and let $f\colon X'\to X$ be the monoidal
    transformation of $X$ with center $D$. Then for every point $x'$ of $X'$ the multiplicity of $X'$ at $x'$ is at
    most equal to that of $X$ at $f(x')$. (Ch.~0 \S4 (B), p.~134: ``One can prove'', analytic case omitted.) Not
    proved here: stated without proof (p.~134), proofs of Ch.~0 deferred by the paper (footnote~2, p.~114). -/)
  (latexEnv := "proposition")]
def MultiplicityNotIncreasing : Prop :=
  ∀ (B : Type u) [Field B] {X : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType pX] [QuasiCompact pX] [IsSeparated pX] [AlgebraicGeometry.IsReduced X]
    [IrreducibleSpace X] (D : Subscheme X), D.IsNonsingular → D.IsEquimultipleAlong →
    ∀ t : MonoidalTransformation X D, ∀ x' : t.X', t.X'.multAt x' ≤ X.multAt (t.f x')

/-- **(C) of p. 134** ("One can prove"; stated without proof or citation; not proved here): for `X` as in (B), a
point `x` of `X` is simple if and only if the multiplicity of `X` at `x` is one.

> (C) Let `X` be the same as in (B).  Then a point `x` of `X` is simple if and only if the multiplicity of `X` at `x`
> is equal to one.  (p. 134)

Formalization notes (encoding): "simple" is `Scheme.IsSimpleAt` (the local ring is regular, footnote 29).  The
analytic alternative is not formalized.

Stated without proof (p. 134, "One can prove"; no reference); proofs of Ch. 0 are deferred by the paper (footnote 2,
p. 114); not proved here.  Its truth was not checked here. -/
@[blueprint "prop:0.4-C"
  (statement := /-- Let $X$ be a reduced and irreducible algebraic $B$-scheme, $B$ a field. Then a point $x$ of $X$
    is simple if and only if the multiplicity of $X$ at $x$ is equal to one. (Ch.~0 \S4 (C), p.~134: ``One can
    prove'', analytic case omitted.) Not proved here: stated without proof (p.~134), proofs of Ch.~0 deferred by the
    paper (footnote~2, p.~114). -/)
  (latexEnv := "proposition")]
def IsSimpleIffMultiplicityEqOne : Prop :=
  ∀ (B : Type u) [Field B] {X : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType pX] [QuasiCompact pX] [IsSeparated pX] [AlgebraicGeometry.IsReduced X]
    [IrreducibleSpace X] (x : X), X.IsSimpleAt x ↔ X.multAt x = 1

/-! ### Question (D) (p. 134) -/

end EquimultiplicityQuestions

namespace MonoidalSuccession

/-- The properties (i) and (ii) of Question (D) for a succession `{f_i : X_{i+1} → X_i}` with centers `D_i` and a
number `d`, in the case `W` = all points of `X`: (i) every center `D_i` is non-singular, `X_i` is equi-multiple along
`D_i`, and the multiplicity of `X_i` at the points of `D_i` is `≧ d`; (ii) `X_r` has multiplicities `< d` at all of its
points.  The data `X_i` are carried along the succession, as in `IsMainIStar` and `IsStrongResolution`.

Formalization note (encoding): the preimage of `W` in `X_i` is all of `X_i` and so is every neighborhood of it, so
"within a neighborhood of the preimage of `W` in `X_i`" imposes nothing more than the condition on the points of the
center; the points of `f⁻¹(W)` are all the points of `X_r`. -/
def IsQuestionDSteps (d : ℕ) : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, Y, nil _ => ∀ y : Y, Y.multAt y < d
  | X, _, cons B _ rest =>
      B.IsNonsingular ∧ B.IsEquimultipleAlong ∧ (∀ x ∈ B.pts, d ≤ X.multAt x) ∧ rest.IsQuestionDSteps d

end MonoidalSuccession

namespace EquimultiplicityQuestions

/-- Question (D) (p. 134) for algebraic `B`-schemes over the field `B`, with `W` the set of all points: for `X` reduced
and irreducible and `d > 1` the maximum of the multiplicities of `X`, is there a finite succession of monoidal
transformations satisfying (i) and (ii) (`IsQuestionDSteps`)?  This definition says that the answer is affirmative for
the field `B`. -/
def QuestionDAt (B : Type u) [Field B] : Prop :=
  ∀ {X : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType pX] [QuasiCompact pX] [IsSeparated pX] [AlgebraicGeometry.IsReduced X]
    [IrreducibleSpace X] (d : ℕ), 1 < d → (∀ x : X, X.multAt x ≤ d) → (∃ x : X, X.multAt x = d) →
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsQuestionDSteps d

/-- **Question (D) of p. 134**, for all algebraic `B`-schemes with a field `B`: the property that the question has an
affirmative answer.

Formalization notes (encoding): `W` is the set of all points of `X`, as the paper says for algebraic `B`-schemes
("the role played by `W` is irrelevant to the question, and we take `W` to be the set of all points of `X`"); it is
quasi-compact since `X` is; "`d` the maximum of the multiplicities of `X` at the points in `W`" is the hypothesis that
`d` bounds every multiplicity and is attained (so a scheme without a maximum is not in the question); the question
is posed for `X` "the same as in (B)": reduced, irreducible, over a field `B` of any characteristic; the analytic
case (with `W` quasi-compact or compact) is not formalized.  (i) and (ii) are `IsQuestionDSteps`.

A question is a `Prop` meaning "the answer is affirmative" (the paper does not say that it is).  Question, not
proved here. -/
@[blueprint "def:0.4-question-D"
  (statement := /-- \textbf{Question (D).} Let $X$ be a reduced and irreducible algebraic $B$-scheme, $B$ a field,
    and $d$ the maximum of the multiplicities of $X$ at its points, say $d>1$ ($W$ is the set of all points of $X$).
    Does there exist a finite succession of monoidal transformations $f_i\colon X_{i+1}\to X_i$ with centers $D_i$
    in $X_i$, $0\le i<r$, $X_0=X$, such that (i) $D_i$ is non-singular and $X_i$ is equi-multiple along $D_i$ with
    multiplicity $\ge d$ for all $i$, and (ii) $X_r$ has multiplicities $<d$ at all its points? (Ch.~0 \S4, p.~134.)
    Formalization note (encoding): the \emph{affirmative answer} is stated, for all fields $B$; $W$ is the set of all
    points, as the paper says for algebraic $B$-schemes. Question: not proved here. -/)
  (latexEnv := "definition")]
def QuestionD : Prop :=
  ∀ (B : Type u) [Field B], QuestionDAt B

/-- **An affirmative answer to Question (D) in characteristic zero** (p. 134): "An affirmative answer to the question
(D) can be obtained from the main theorem I in the strong form, with (a), (b), and (c) in the case of algebraic
`B`-schemes with fields `B` of characteristic zero, and it seems quite plausible in general."

Formalization note (encoding): the statement is `QuestionDAt B` for every field `B` of characteristic zero.  The words
"it seems quite plausible in general" are an opinion of the author, not a claim: they are not a separate statement
(the general case is `QuestionD`).

The paper names its input (Main Theorem I in the strong form, with (a), (b), and (c)) and prints no further argument;
not proved here. -/
@[blueprint "thm:0.4-question-D-affirmative"
  (statement := /-- For algebraic $B$-schemes with fields $B$ of characteristic zero, the answer to Question (D) is
    affirmative. (Ch.~0 \S4, p.~134: ``An affirmative answer to the question (D) can be obtained from the main
    theorem I in the strong form, with (a), (b), and (c) in the case of algebraic $B$-schemes with fields $B$ of
    characteristic zero, and it seems quite plausible in general.'') Not proved here: the paper names the strong
    form of Main Theorem~I as its input but gives no argument. -/)
  (latexEnv := "theorem")]
def QuestionDCharZero : Prop :=
  ∀ (B : Type u) [Field B] [CharZero B], QuestionDAt B

/-- **The resolution of singularities in the form of Main Theorem I follows from the answer to (D)** (p. 134):
"Obviously, if the answer to (D) is affirmative, then the resolution of singularities in the form of the main theorem I
follows."

Formalization notes (encoding): "the answer to (D) is affirmative" is `QuestionD`; "the main theorem I" is its
statement of p. 132 for a reduced and irreducible algebraic `B`-scheme `X` with `B` a field of characteristic zero:
there is a subscheme `D` whose points are the singular locus (the points where `X` is not simple) such that the
monoidal transformation with center `D` has a non-singular source (as `MainTheorem.Ch0.I`, here with the printed
separatedness).  (The hypothesis `QuestionDCharZero` would give a stronger implication; the printed hypothesis is the
answer to (D) in general.)

Stated without argument ("Obviously", p. 134); not proved here. -/
@[blueprint "thm:0.4-question-D-implies-main-I"
  (statement := /-- If the answer to Question (D) is affirmative, then Main Theorem~I follows. (Ch.~0 \S4, p.~134:
    ``Obviously, if the answer to (D) is affirmative, then the resolution of singularities in the form of the main
    theorem I follows.'') Formalization note (encoding): Main Theorem~I is its printed statement for a reduced and
    irreducible algebraic $B$-scheme, $B$ a field of characteristic zero. Not proved here: stated without argument
    (``Obviously'', p.~134). -/)
  (latexEnv := "theorem")]
def QuestionDImpliesMainI : Prop :=
  QuestionD.{u} →
    ∀ (B : Type u) [Field B] [CharZero B] {X : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of B))
      [LocallyOfFiniteType pX] [QuasiCompact pX] [IsSeparated pX] [AlgebraicGeometry.IsReduced X]
      [IrreducibleSpace X],
      ∃ D : Subscheme X, D.pts = {x | ¬ X.IsSimpleAt x} ∧ ∀ t : MonoidalTransformation X D,
        t.X'.IsNonsingular


/-! ### The special case of pp. 134–135: `d`-fold curves and the theorem of B. Levi-Zariski -/

/-- `S_d`, the set of the points of `Z` at which the multiplicity of `Z` is `≧ d` (the points of the subscheme `S_d` of
(A)). -/
def dFoldLocus (Z : Scheme.{u}) (d : ℕ) : Set Z := {z | d ≤ Z.multAt z}

/-- **`d`-fold curves of `Z`** (p. 135): the irreducible and reduced subschemes of dimension one of which `S_d` is a
finite union.

Formalization notes (encoding): the paper says "`S_d` is a finite union of irreducible and reduced algebraic
subschemes of dimension one and points.  Let us call them `d`-fold curves and isolated `d`-fold points of `X`
respectively."  A finite union can be written in many ways; "(b) at most two of the `d`-fold curves pass through each
point" only makes sense for the irredundant one, so the `d`-fold curves are read as the irreducible components of
`S_d` of dimension one, with the reduced structure: a reduced subscheme `C` of `Z` of dimension one whose set of
points is a maximal irreducible subset of `S_d` (`dFoldLocus`).  This reading is recorded as an encoding. -/
@[blueprint "def:0.4-d-fold"
  (statement := /-- Let $Z$ be an algebraic scheme and $d$ an integer. A \emph{$d$-fold curve} of $Z$ is a reduced
    subscheme $C$ of $Z$ of dimension one whose points form an irreducible component of the set $S_d$ of the points
    of $Z$ at which the multiplicity is $\ge d$. An \emph{isolated $d$-fold point} of $Z$ is a point $z$ such that
    $\{z\}$ is an irreducible component of $S_d$. (Ch.~0 \S4, p.~135: ``Let us call them $d$-fold curves and isolated
    $d$-fold points of $X$ respectively.'') Formalization note (encoding): the paper's ``finite union of irreducible
    and reduced subschemes of dimension one and points'' is read as the decomposition into irreducible components,
    the only one for which ``at most two of the $d$-fold curves pass through each point'' is meaningful. -/)
  (latexEnv := "definition")]
def IsDFoldCurve (Z : Scheme.{u}) (d : ℕ) (C : Subscheme Z) : Prop :=
  AlgebraicGeometry.IsReduced C.toScheme ∧ C.toScheme.dim = 1 ∧
    Maximal (fun T : Set Z => IsIrreducible T ∧ T ⊆ dFoldLocus Z d) C.pts

/-- **Isolated `d`-fold points of `Z`** (p. 135): the points `z` such that `{z}` is an irreducible component of `S_d`
(see `IsDFoldCurve` for the encoding).  The corresponding center of a monoidal transformation is a reduced subscheme
whose set of points is `{z}`. -/
def IsIsolatedDFoldPoint (Z : Scheme.{u}) (d : ℕ) (z : Z) : Prop :=
  Maximal (fun T : Set Z => IsIrreducible T ∧ T ⊆ dFoldLocus Z d) {z}

/-- A subscheme `B` of `Z` is the reduced point `z`: its set of points is `{z}` and it is reduced. -/
def IsReducedPointAt {Z : Scheme.{u}} (B : Subscheme Z) (z : Z) : Prop :=
  AlgebraicGeometry.IsReduced B.toScheme ∧ B.pts = {z}

/-- The centers allowed in the step (2) of Zariski's process (p. 135: "we take either an isolated `d`-fold point or an
irreducible `d`-fold curve, which is non-singular, and we apply the monoidal transformation with it as center"): a
`d`-fold curve, or the reduced point at an isolated `d`-fold point.  (The `d`-fold curves of `IsDFoldCurve` are
irreducible and reduced; their non-singularity is the property (a) of the situation `IsTame`, not a hypothesis of the
choice.) -/
def IsDFoldCenter (Z : Scheme.{u}) (d : ℕ) (B : Subscheme Z) : Prop :=
  IsDFoldCurve Z d B ∨ ∃ z, IsIsolatedDFoldPoint Z d z ∧ IsReducedPointAt B z

/-- Two subschemes `C₁`, `C₂` of `Z` *cross transversally at `z`* (p. 135, (c): "any two of the `d`-fold curves
passing through a point have transversal crossing at the point"): both pass through `z` and the sum of their ideals in
the local ring `O_{Z,z}` is the maximal ideal, i.e. their scheme-theoretic intersection is the reduced point `z`
(equivalently, for two non-singular curves, their tangent lines in the tangent space of `Z` at `z` are distinct).

Formalization note (encoding): the paper does not define "transversal crossing"; this is the standard meaning for two
non-singular curves through a point, read in `Z` itself (it is the same as in any non-singular ambient scheme `Y ⊇ Z`
in which both curves lie, since the ideal of `Z` in `Y` is contained in both ideals).  Recorded as an encoding. -/
def CrossTransversallyAt {Z : Scheme.{u}} (C₁ C₂ : Subscheme Z) (z : Z) : Prop :=
  z ∈ C₁.pts ∧ z ∈ C₂.pts ∧
    C₁.stalkIdeal z ⊔ C₂.stalkIdeal z = IsLocalRing.maximalIdeal (Z.presheaf.stalk z)

/-- **The situation established in (1) of Zariski's process** (p. 135): (a) each of the `d`-fold curves is
non-singular; (b) at most two of the `d`-fold curves pass through each point; (c) any two of the `d`-fold curves
passing through a point have transversal crossing at the point.

Formalization notes (encoding): "two of the `d`-fold curves" are two distinct ones, distinct meaning with different sets
of points (they are reduced, hence determined by them); (b) bounds the number of sets of points of `d`-fold curves
containing the point; "transversal crossing" is `CrossTransversallyAt`. -/
def IsTame (Z : Scheme.{u}) (d : ℕ) : Prop :=
  (∀ C : Subscheme Z, IsDFoldCurve Z d C → C.IsNonsingular) ∧
  (∀ z : Z, {T : Set Z | ∃ C : Subscheme Z, IsDFoldCurve Z d C ∧ C.pts = T ∧ z ∈ T}.encard ≤ 2) ∧
  (∀ C₁ C₂ : Subscheme Z, IsDFoldCurve Z d C₁ → IsDFoldCurve Z d C₂ → C₁.pts ≠ C₂.pts →
    ∀ z ∈ C₁.pts ∩ C₂.pts, CrossTransversallyAt C₁ C₂ z)

/-- The setting of pp. 134–135: `Y` a non-singular algebraic `B`-scheme of dimension 3 (`B` a field of characteristic
zero), `X` an irreducible and reduced algebraic subscheme of dimension 2 of `Y`, and `d > 1` the maximum of the
multiplicities of `X` at its points.  ("The maximum" is the hypothesis that `d` bounds the multiplicities of `X` and is
attained.)  The ambient scheme `Y` enters only through these hypotheses; the statements below speak about the scheme
`X.toScheme`. -/
def IsSurfaceInThreefold {Y : Scheme.{u}} (X : Subscheme Y) (d : ℕ) : Prop :=
  Y.IsNonsingular ∧ Y.dim = 3 ∧ AlgebraicGeometry.IsReduced X.toScheme ∧ IrreducibleSpace X.toScheme ∧
    X.toScheme.dim = 2 ∧ 1 < d ∧ (∀ x : X.toScheme, X.toScheme.multAt x ≤ d) ∧
    ∃ x : X.toScheme, X.toScheme.multAt x = d

/-- **`S_d` is a finite union of irreducible and reduced subschemes of dimension one and points** (p. 134–135):
"Let `Y` be a non-singular algebraic `B`-scheme of dim 3, with a field `B` of characteristic zero, and `X` an
irreducible and reduced algebraic subscheme of dim 2 of `Y`.  Let `d` be the maximum of the multiplicities of `X` at
its points.  We assume `d > 1`.  Then `S_d` is a finite union of irreducible and reduced algebraic subschemes of
dimension one and points."

Formalization notes (encoding): `S_d` is the set `dFoldLocus X.toScheme d`; "points" are irreducible reduced
subschemes of dimension zero.

Stated without argument or citation (pp. 134–135, "Then `S_d` is …"; it is not derived from (A) in the text); not
proved here.  Its truth was not checked here. -/
@[blueprint "prop:0.4-d-fold-locus"
  (statement := /-- Let $Y$ be a non-singular algebraic $B$-scheme of dimension~$3$, with a field $B$ of
    characteristic zero, and $X$ an irreducible and reduced algebraic subscheme of dimension~$2$ of $Y$. Let $d$ be
    the maximum of the multiplicities of $X$ at its points; we assume $d>1$. Then $S_d$ is a finite union of
    irreducible and reduced algebraic subschemes of dimension one and points. (Ch.~0 \S4, pp.~134--135.) Not proved
    here: stated without argument or citation. -/)
  (latexEnv := "proposition")]
def DFoldLocusIsFiniteUnion : Prop :=
  ∀ (B : Type u) [Field B] [CharZero B] {Y : Scheme.{u}} (pY : Y ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType pY] [QuasiCompact pY] [IsSeparated pY] (X : Subscheme Y) (d : ℕ),
    IsSurfaceInThreefold X d →
    ∃ (n : ℕ) (C : Fin n → Subscheme X.toScheme),
      (∀ j, AlgebraicGeometry.IsReduced (C j).toScheme ∧ IrreducibleSpace (C j).toScheme ∧
        ((C j).toScheme.dim = 1 ∨ (C j).toScheme.dim = 0)) ∧
      (⋃ j, (C j).pts) = dFoldLocus X.toScheme d

/-- **A "finite sequence of monoidal transformations whose centers are points on `d`-fold curves"** (p. 135, (1)):
every center of the succession is a reduced point lying on a `d`-fold curve of the current scheme.  The data `X_i` are
carried along the succession. -/
def _root_.Hironaka.MonoidalSuccession.HasCentersOnDFoldCurves (d : ℕ) : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, _, MonoidalSuccession.nil _ => True
  | X, _, MonoidalSuccession.cons B _ rest =>
      (∃ z : X, IsReducedPointAt B z ∧ ∃ C : Subscheme X, IsDFoldCurve X d C ∧ z ∈ C.pts) ∧
        rest.HasCentersOnDFoldCurves d

/-- The steps (2) of Zariski's process (p. 135): every center of the succession is allowed in the sense of
`IsDFoldCenter` for the current scheme. -/
def _root_.Hironaka.MonoidalSuccession.HasDFoldSteps (d : ℕ) : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, _, MonoidalSuccession.nil _ => True
  | X, _, MonoidalSuccession.cons B _ rest => IsDFoldCenter X d B ∧ rest.HasDFoldSteps d

/-- `f : X' ⟶ X` is a monoidal transformation of `X` with center `B` (p. 166), as a proposition: the conditions (i)
and (ii) of `MonoidalTransformation` for the morphism `f`.  (The structure `MonoidalTransformation` bundles `X'` and
`f` with these two conditions.) -/
def IsMonoidalWith {X' X : Scheme.{u}} (f : X' ⟶ X) (B : Subscheme X) : Prop :=
  (Subscheme.totalTransform f B).IsInvertibleIdeal ∧
    ∀ (X'' : Scheme.{u}) (f' : X'' ⟶ X), (Subscheme.totalTransform f' B).IsInvertibleIdeal →
      ∃! h : X'' ⟶ X', h ≫ f = f'

/-- An infinite sequence of monoidal transformations `{f_i : X_{i+1} → X_i}` with centers `D_i` in `X_i`,
`i = 0, 1, 2, …` (pp. 135, 137).  Formalization note (encoding): the sequence of schemes `X_i` and morphisms `f_i`
with `f_i` a monoidal transformation with center `D_i` (`IsMonoidalWith`), stated without equalities between the
`X_{i+1}` and the blown-up schemes of the `f_i`. -/
structure MonoidalSequence where
  /-- The schemes `X_i`. -/
  X : ℕ → Scheme.{u}
  /-- The centers `D_i` in `X_i`. -/
  D : ∀ i, Subscheme (X i)
  /-- The morphisms `f_i : X_{i+1} → X_i`. -/
  f : ∀ i, X (i + 1) ⟶ X i
  /-- `f_i` is the monoidal transformation of `X_i` with center `D_i`. -/
  isMonoidal : ∀ i, IsMonoidalWith (f i) (D i)

/-- **(1) of Zariski's form of the answer to (D)** (p. 135): "First, applying a finite number of monoidal
transformations whose centers are points on `d`-fold curves, we can establish the situation in which: (a) each of the
`d`-fold curve is non-singular; (b) at most two of the `d`-fold curves pass through each point; and (c) any two of the
`d`-fold curves passing through a point have transversal crossing at the point."

Formalization notes (encoding): in the setting of pp. 134–135 (`IsSurfaceInThreefold`) there is a finite succession of
monoidal transformations of `X` (the scheme `X.toScheme`; the transformations are those of `X` with center in `X_i`, as
in Question (D)) with centers reduced points on `d`-fold curves of the current scheme, ending in a scheme in the
situation `IsTame`.  The `d`-fold curves of the transformed scheme are those of `IsDFoldCurve` for the same `d`.

Cited: attributed to Zariski by the sentence "O. Zariski answered (D) explicitly in the following form" (p. 135); the
reference [27, §17, Part III] is printed after (2) and covers "this result".  Not proved here.  Its truth was not
checked here. -/
@[blueprint "thm:0.4-levi-zariski-1"
  (statement := /-- In the setting of pp.~134--135 ($Y$ a non-singular algebraic $B$-scheme of dimension~$3$, $B$ a
    field of characteristic zero, $X$ an irreducible and reduced subscheme of dimension~$2$ of $Y$, $d>1$ the maximum
    of the multiplicities of $X$): applying a finite number of monoidal transformations whose centers are points on
    $d$-fold curves we can establish the situation in which (a) each of the $d$-fold curves is non-singular, (b) at
    most two of the $d$-fold curves pass through each point, and (c) any two of the $d$-fold curves passing through a
    point have transversal crossing at the point. (Ch.~0 \S4, p.~135, (1); Zariski [27, \S17, Part III].)
    Formalization note (encoding): the transformations are those of $X$ itself, as in Question (D), and
    ``transversal crossing'' is the sum of the ideals of the two curves being the maximal ideal of the local ring.
    Not proved here: cited (Zariski). -/)
  (latexEnv := "theorem")]
def LeviZariskiEstablish : Prop :=
  ∀ (B : Type u) [Field B] [CharZero B] {Y : Scheme.{u}} (pY : Y ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType pY] [QuasiCompact pY] [IsSeparated pY] (X : Subscheme Y) (d : ℕ),
    IsSurfaceInThreefold X d →
    ∃ (Z : Scheme.{u}) (s : MonoidalSuccession X.toScheme Z), s.HasCentersOnDFoldCurves d ∧ IsTame Z d

/-- **"There exists a unique shortest process of doing this"** (p. 135, the parenthetical remark after (1)): among the
finite successions of monoidal transformations whose centers are points on `d`-fold curves and which establish the
situation `IsTame`, there is a shortest length `r`, and the end of any two of length `r` are isomorphic over `X`.

Formalization notes (encoding): "unique" is read as the uniqueness of the resulting morphism `X_r → X`, up to an
isomorphism over `X`: two successions that blow up disjoint centers in the other order are different successions with
the same end, so uniqueness of the sequence of centers could not hold.  "Shortest" is the number of monoidal
transformations (`MonoidalSuccession.length`).  Recorded as an encoding.

Cited (Zariski [27, §17, Part III]; the parenthesis is part of the sentence quoted for (1)); not proved here.  Its
truth was not checked here. -/
@[blueprint "thm:0.4-levi-zariski-shortest"
  (statement := /-- In the process of (1) there exists a unique shortest process of establishing the situation (a),
    (b), (c): there is a minimal number $r$ of monoidal transformations with centers points on $d$-fold curves that
    establish it, and the resulting schemes $X_r$ of any two such successions of length $r$ are isomorphic over $X$.
    (Ch.~0 \S4, p.~135: ``(There exists a unique shortest process of doing this.)'') Formalization note (encoding):
    uniqueness is that of the morphism $X_r\to X$ up to isomorphism over $X$. Not proved here: cited (Zariski). -/)
  (latexEnv := "theorem")]
def LeviZariskiShortestUnique : Prop :=
  ∀ (B : Type u) [Field B] [CharZero B] {Y : Scheme.{u}} (pY : Y ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType pY] [QuasiCompact pY] [IsSeparated pY] (X : Subscheme Y) (d : ℕ),
    IsSurfaceInThreefold X d →
    ∃ r : ℕ,
      (∃ (Z : Scheme.{u}) (s : MonoidalSuccession X.toScheme Z),
        s.length = r ∧ s.HasCentersOnDFoldCurves d ∧ IsTame Z d) ∧
      (∀ (Z : Scheme.{u}) (s : MonoidalSuccession X.toScheme Z),
        s.HasCentersOnDFoldCurves d → IsTame Z d → r ≤ s.length) ∧
      ∀ (Z Z' : Scheme.{u}) (s : MonoidalSuccession X.toScheme Z) (s' : MonoidalSuccession X.toScheme Z'),
        s.length = r → s.HasCentersOnDFoldCurves d → IsTame Z d →
        s'.length = r → s'.HasCentersOnDFoldCurves d → IsTame Z' d →
        ∃ e : Z ≅ Z', e.hom ≫ s'.composite = s.composite

/-- **(2) and the theorem of Zariski that the process terminates** (p. 135): "(2) After (1) is achieved, we take
either an isolated `d`-fold point or an irreducible `d`-fold curve, which is non-singular, and we apply the monoidal
transformation with it as center.  (Here we have an arbitrary choice out of a finite number of possibilities.)
Zariski proved that the process of (2) can be repeated, without affecting the situation established in (1), until the
transform of `X` has neither `d`-fold curve nor isolated `d`-fold point, and that, as is of the most importance, the
process of (2) cannot be repeated infinitely many times.  (See [27, §17, Part III].)"

Formalization notes (encoding): after any succession of (1) (centers points on `d`-fold curves ending in the situation
`IsTame`): (i) every succession of steps (2) (`HasDFoldSteps`: each center a `d`-fold curve or an isolated `d`-fold
point of the current scheme) ends in a scheme in the situation `IsTame` ("without affecting the situation established
in (1)"); (ii) every such succession can be continued by steps (2) to a scheme with neither a `d`-fold curve nor an
isolated `d`-fold point ("until the transform of `X` has neither …"); (iii) there is no infinite sequence of
monoidal transformations (`MonoidalSequence`) starting at the end of (1), each with center as in (2) ("cannot be
repeated infinitely many times").  The "finite number of possibilities" of the choice follows from the finiteness of
`S_d` (`DFoldLocusIsFiniteUnion`) and is not a separate statement.

Cited (Zariski [27, §17, Part III], "(See [27, §17, Part III].)"); not proved here.  Its truth was not checked here. -/
@[blueprint "thm:0.4-levi-zariski-2"
  (statement := /-- In the setting of pp.~134--135, after (1) is achieved, the process of (2) (applying the
    monoidal transformation with center an isolated $d$-fold point or an irreducible $d$-fold curve, which is
    non-singular) can be repeated, without affecting the situation established in (1), until the transform of $X$ has
    neither $d$-fold curve nor isolated $d$-fold point, and the process of (2) cannot be repeated infinitely many
    times. (Ch.~0 \S4, p.~135: ``Zariski proved \dots (See [27, \S17, Part III].)'') Formalization note
    (encoding): the three assertions are stated for every succession of (2) after any succession of (1), and for
    infinite sequences of (2). Not proved here: cited (Zariski). -/)
  (latexEnv := "theorem")]
def LeviZariskiRepeat : Prop :=
  ∀ (B : Type u) [Field B] [CharZero B] {Y : Scheme.{u}} (pY : Y ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType pY] [QuasiCompact pY] [IsSeparated pY] (X : Subscheme Y) (d : ℕ),
    IsSurfaceInThreefold X d →
    ∀ (Z₁ : Scheme.{u}) (s₁ : MonoidalSuccession X.toScheme Z₁),
      s₁.HasCentersOnDFoldCurves d → IsTame Z₁ d →
      (∀ (Z₂ : Scheme.{u}) (s₂ : MonoidalSuccession Z₁ Z₂), s₂.HasDFoldSteps d → IsTame Z₂ d) ∧
      (∀ (Z₂ : Scheme.{u}) (s₂ : MonoidalSuccession Z₁ Z₂), s₂.HasDFoldSteps d →
        ∃ (Z₃ : Scheme.{u}) (s₃ : MonoidalSuccession Z₂ Z₃), s₃.HasDFoldSteps d ∧
          (∀ C : Subscheme Z₃, ¬ IsDFoldCurve Z₃ d C) ∧ ∀ z : Z₃, ¬ IsIsolatedDFoldPoint Z₃ d z) ∧
      ¬ ∃ σ : MonoidalSequence.{u}, σ.X 0 = Z₁ ∧ ∀ i, IsDFoldCenter (σ.X i) d (σ.D i)

/-- **The theorem of B. Levi-Zariski** (p. 135): "We shall refer to this result as *theorem of B. Levi-Zariski*": the
answer (1), (2) of Zariski to Question (D) in the special case, with its termination.  It is the conjunction of
`LeviZariskiEstablish` ((1)) and `LeviZariskiRepeat` ((2) and the termination); the parenthetical "unique shortest
process" is `LeviZariskiShortestUnique`.  (1) and (2) are the form in which Zariski answered (D) for such `X` ("O. Zariski
answered (D) explicitly in the following form", p. 135); that sentence is `LeviZariskiAnswersD`.

Cited (Zariski [27, §17, Part III]); not proved here. -/
@[blueprint "thm:0.4-levi-zariski"
  (statement := /-- \textbf{Theorem of B.~Levi-Zariski.} In the setting of pp.~134--135: (1) applying a finite number
    of monoidal transformations whose centers are points on $d$-fold curves we can establish the situation (a), (b),
    (c); (2) after (1) is achieved, the process of taking an isolated $d$-fold point or an irreducible $d$-fold curve
    as center can be repeated without affecting (1) until the transform has neither, and cannot be repeated
    infinitely many times. (Ch.~0 \S4, p.~135: ``We shall refer to this result as theorem of B.~Levi-Zariski.'')
    The parenthesis ``(There exists a unique shortest process of doing this.)'' is the separate statement
    \cref{thm:0.4-levi-zariski-shortest}. Not proved here: cited (Zariski [27, \S17, Part III]). -/)
  (latexEnv := "theorem")]
def LeviZariski : Prop :=
  LeviZariskiEstablish.{u} ∧ LeviZariskiRepeat.{u}

/-- **Zariski's answer to (D) for the special `X`** (pp. 134–135): "we shall point out that this idea leads to a
canonical (but not unique) resolution process in a certain special case" (p. 134); "Following Levi's idea, and making
precise certain points which were left ambiguous, O. Zariski answered (D) explicitly in the following form:" (p. 135),
followed by (1), (2) (`LeviZariski`).

Formalization notes (encoding): in the setting of pp. 134–135 (`IsSurfaceInThreefold`, with `d > 1` the maximum of
the multiplicities of the scheme `X.toScheme`, `W` all points as in Question (D)) there is a finite succession of
monoidal transformations of `X.toScheme` satisfying (i) and (ii) of Question (D) (`MonoidalSuccession.IsQuestionDSteps`).
The words "canonical (but not unique)" are a description of the process of (1), (2) (the arbitrary choice in (2)) and are
not a separate statement.

Cited (Zariski [27, §17, Part III]; the sentence says that Zariski answered (D)); not proved here.  Its truth was not
checked here. -/
@[blueprint "thm:0.4-levi-zariski-answers-D"
  (statement := /-- In the setting of pp.~134--135 ($Y$ a non-singular algebraic $B$-scheme of dimension~$3$, $B$ a
    field of characteristic zero, $X$ an irreducible and reduced subscheme of dimension~$2$ of $Y$, $d>1$ the maximum
    of the multiplicities of $X$), Question (D) has an affirmative answer: there is a finite succession of monoidal
    transformations of $X$ satisfying (i) and (ii) of Question (D) (with $W$ the set of all points). (Ch.~0 \S4,
    pp.~134--135: ``this idea leads to a canonical (but not unique) resolution process in a certain special case'';
    ``O.~Zariski answered (D) explicitly in the following form''; Zariski [27, \S17, Part III].) Not proved here:
    cited (Zariski). -/)
  (latexEnv := "theorem")]
def LeviZariskiAnswersD : Prop :=
  ∀ (B : Type u) [Field B] [CharZero B] {Y : Scheme.{u}} (pY : Y ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType pY] [QuasiCompact pY] [IsSeparated pY] (X : Subscheme Y) (d : ℕ),
    IsSurfaceInThreefold X d →
    ∃ (Z : Scheme.{u}) (s : MonoidalSuccession X.toScheme Z), s.IsQuestionDSteps d

/-! ### "But not in general" (p. 136) -/

/-- **The converse of (I) is not true in general** (p. 136): "The converse is true if `X` is imbedded in a non-singular
algebraic `B`-scheme, or analytic `K`-space, `Y` such that the sheaf of ideals of `X` on `Y` is everywhere locally
principal; but not in general."

Formalization notes (encoding): "the converse" of (I) is "if `X` is equi-multiple along `D` then `X` is normally flat
along `D`", for a non-singular subscheme `D` of an algebraic scheme `X` (the hypotheses of the printed (I), as in
`EquimultipleOfNormallyFlatAsPrinted`); "not in general" is the negation of that implication for all `X` and `D`.
`X` ranges over the algebraic schemes in the sense of `IsAlgebraicScheme` (Ch. I: of finite type over a base of the
class 𝔅, not required to be separated), as in the formalized (I), not over the separated algebraic `B`-schemes of the
paper: a deviation to a more general class, so the negation is slightly weaker than the printed one.  The
part "true if … locally principal" is `Subscheme.isNormallyFlatAlong_of_isEquimultipleAlong` and its printed form.

Stated without proof or example (p. 136, "but not in general"); not proved here.  Its truth was not checked here. -/
@[blueprint "prop:0.4-I-converse-not-general"
  (statement := /-- The converse of (I) is not true in general: there are an algebraic scheme $X$ (in the sense of Ch.~I, not necessarily separated) and a non-singular
    subscheme $D$ of $X$ along which $X$ is equi-multiple but not normally flat. (Ch.~0 \S4 (I), p.~136: ``The
    converse is true if $X$ is imbedded in a non-singular algebraic $B$-scheme \dots\ such that the sheaf of ideals
    of $X$ on $Y$ is everywhere locally principal; but not in general.'') Not proved here: stated without proof or
    example (p.~136). -/)
  (latexEnv := "proposition")]
def ConverseOfIFailsInGeneral : Prop :=
  ¬ ∀ (X : Scheme.{u}) [IsAlgebraicScheme X] (D : Subscheme X), D.IsNonsingular → D.IsEquimultipleAlong →
    D.IsNormallyFlatAlong


/-! ### The character of singularities (pp. 136–137) -/

/-- **The class `𝒞` of triples `(x, X, Y)`** (p. 137): "consider the class of all the triples `(x, X, Y)` of
non-singular algebraic `B`-schemes `Y`, subschemes `X` of `Y`, and points `x` of `X`.  Let us denote the class by `C`."

Formalization notes (encoding): `B` is a field (a `B`-scheme is algebraic if its structure morphism is locally of finite
type, quasi-compact and separated); the point `x` is a point of the scheme `X.toScheme`, whose image in `Y` is
`X.ι x`.  The paper does not say what `B` is in this passage; the fields of Ch. 0 §4 are used. -/
@[blueprint "def:0.4-character-class"
  (statement := /-- The class $\mathcal C$ of all triples $(x,X,Y)$ of non-singular algebraic $B$-schemes $Y$,
    subschemes $X$ of $Y$, and points $x$ of $X$. (Ch.~0 \S4, p.~137.) Formalization note (encoding): $B$ is a field;
    $x$ is a point of the scheme $X$. -/)
  (latexEnv := "definition")]
structure CharacterTriple (B : Type u) [Field B] where
  /-- The ambient non-singular scheme `Y`. -/
  Y : Scheme.{u}
  /-- The structure morphism of `Y`. -/
  pY : Y ⟶ Spec (CommRingCat.of B)
  /-- `Y` is an algebraic `B`-scheme. -/
  isAlgebraic : LocallyOfFiniteType pY ∧ QuasiCompact pY ∧ IsSeparated pY
  /-- `Y` is non-singular. -/
  isNonsingular : Y.IsNonsingular
  /-- The subscheme `X` of `Y`. -/
  X : Subscheme Y
  /-- The point `x` of `X`. -/
  x : X.toScheme

/-- **An embedding of a scheme `Z` into a non-singular algebraic `B`-scheme** (the data "`Y ⊃ X`" of pp. 137–138): a
non-singular algebraic `B`-scheme `Y`, a subscheme `XS` of `Y` and an isomorphism `Z ≅ XS`. -/
structure Ambient (B : Type u) [Field B] (Z : Scheme.{u}) where
  /-- The ambient non-singular scheme `Y`. -/
  Y : Scheme.{u}
  /-- The structure morphism of `Y`. -/
  pY : Y ⟶ Spec (CommRingCat.of B)
  /-- `Y` is an algebraic `B`-scheme. -/
  isAlgebraic : LocallyOfFiniteType pY ∧ QuasiCompact pY ∧ IsSeparated pY
  /-- `Y` is non-singular. -/
  isNonsingular : Y.IsNonsingular
  /-- The subscheme of `Y` that `Z` is identified with. -/
  XS : Subscheme Y
  /-- The identification of `Z` with the subscheme. -/
  e : Z ≅ XS.toScheme

/-- The triple `(x, X, Y)` of an embedding `Z ≅ X ⊆ Y` and a point `z` of `Z`. -/
noncomputable def Ambient.triple {B : Type u} [Field B] {Z : Scheme.{u}} (A : Ambient B Z) (z : Z) : CharacterTriple B :=
  ⟨A.Y, A.pY, A.isAlgebraic, A.isNonsingular, A.XS, A.e.hom.base z⟩

/-- **`f` extends to the monoidal transformation `Y' → Y` with center `D`** (pp. 137–138): `A` embeds `Z` into `Y`,
`A'` embeds `Z'` into `Y'`, `f : Z' → Z`, `C` is a subscheme of `Z`; there is a morphism `g : Y' → Y` over `B` which is
the monoidal transformation of `Y` with center `C` (regarded as a subscheme of `Y` through `Z ≅ X ⊆ Y`) and which
restricts to `f`: `Z' ≅ X' ⊆ Y'`, `X ⊆ Y` and `f` form a commutative square with `g`. -/
def Ambient.IsExtensionOf {B : Type u} [Field B] {Z Z' : Scheme.{u}} (A : Ambient B Z) (C : Subscheme Z)
    (f : Z' ⟶ Z) (A' : Ambient B Z') : Prop :=
  ∃ g : A'.Y ⟶ A.Y, g ≫ A.pY = A'.pY ∧ IsMonoidalWith g (C.ι ≫ A.e.hom ≫ A.XS.ι).ker ∧
    A'.e.hom ≫ A'.XS.ι ≫ g = f ≫ A.e.hom ≫ A.XS.ι

section Character

variable {B : Type u} [Field B] {P : Type v} [PartialOrder P]

/-- **A character of singularities is essentially independent of the ambient non-singular space** (p. 137): "`s_x(X/Y')`
for a different `Y'` is obtained by knowing only the value `s_x(X/Y)` and the integer `dim(O_{Y',x}) − dim(O_{Y,x})`,
where `dim` denotes the Krull dimension."

Formalization notes (encoding): there is a function `G` of the value and of the integer such that, for two triples
with the same scheme `X` (an isomorphism of the schemes `X`, over `B`, taking `x` to `x'`), `s(x', X, Y')` is `G` of
`s(x, X, Y)` and of the difference of the Krull dimensions (as natural numbers; the local rings are noetherian)
of `O_{Y',x}` and `O_{Y,x}`. -/
def IsAmbientIndependent (s : CharacterTriple B → P) : Prop :=
  ∃ G : P → ℤ → P, ∀ t t' : CharacterTriple B, ∀ φ : t.X.toScheme ≅ t'.X.toScheme,
    φ.hom ≫ t'.X.ι ≫ t'.pY = t.X.ι ≫ t.pY → φ.hom.base t.x = t'.x →
    s t' = G (s t) ((dimNat (t'.Y.presheaf.stalk (t'.X.ι.base t'.x)) : ℤ) -
      (dimNat (t.Y.presheaf.stalk (t.X.ι.base t.x)) : ℤ))

/-- **A character of singularities is of local nature** (p. 137): "`s_x(X/Y)` is of local nature in the sense that it is
uniquely determined by the local rings `O_{Y,x}` and `O_{X,x}`."

Formalization notes (encoding): `O_{X,x}` is the quotient of `O_{Y,x}` by the ideal of `X`, so the two local rings
together with the map between them are the pair (`O_{Y,x}`, ideal of `X`): two triples whose pairs are
isomorphic (a ring isomorphism of the stalks of `Y` carrying the ideal of `X` onto that of `X'`) have the same
character. -/
def IsLocalNature (s : CharacterTriple B → P) : Prop :=
  ∀ t t' : CharacterTriple B,
    ∀ e : t.Y.presheaf.stalk (t.X.ι.base t.x) ≃+* t'.Y.presheaf.stalk (t'.X.ι.base t'.x),
    (t.X.stalkIdeal (t.X.ι.base t.x)).map e = t'.X.stalkIdeal (t'.X.ι.base t'.x) → s t = s t'

/-- **A character of singularities** (p. 137): "A character of singularities that we shall seek to define and to use is
a function, say `s_x(X/Y)` in symbol, defined for all `(x, X, Y) ∈ C`, and having the values `s_x(X/Y)` in an ordered
(or semi-ordered) set. … The character `s_x(X/Y)` is a measurement of the singularities of `X` at the point `x` of `X`
and is essentially independent of the ambient non-singular space `Y` in the sense that … Moreover, `s_x(X/Y)` is of
local nature in the sense that it is uniquely determined by the local rings `O_{Y,x}` and `O_{X,x}`."

Formalization notes (encoding): a character is a function `s` on the triples of `CharacterTriple` with values in a
partially ordered set `P` ("semi-ordered"; an ordered set is a particular case) which is `IsAmbientIndependent` and
`IsLocalNature`.  "A measurement of the singularities of `X` at `x`" has no mathematical content and is not
formalized.  The two "in the sense that" clauses are the definitions of the two properties.

Definition of the paper (p. 137; the character is "sought to define", it is not defined in Ch. 0). -/
@[blueprint "def:0.4-character"
  (statement := /-- A \emph{character of singularities} is a function $s_x(X/Y)$ defined for all $(x,X,Y)\in\mathcal
    C$ with values in an ordered (or semi-ordered) set, such that: $s_x(X/Y')$ for a different $Y'$ is obtained by
    knowing only the value $s_x(X/Y)$ and the integer $\dim(\mathcal O_{Y',x})-\dim(\mathcal O_{Y,x})$ (essentially
    independent of the ambient non-singular space), and $s_x(X/Y)$ is uniquely determined by the local rings
    $\mathcal O_{Y,x}$ and $\mathcal O_{X,x}$ (of local nature). (Ch.~0 \S4, p.~137.) Formalization note
    (encoding): the values lie in a partially ordered set; the two requirements are made precise as stated; ``a
    measurement of the singularities'' is not formalized. -/)
  (latexEnv := "definition")]
def IsCharacter (s : CharacterTriple B → P) : Prop :=
  IsAmbientIndependent s ∧ IsLocalNature s

/-- **Property (1) of a character** (p. 137): "If `D` is a non-singular algebraic subscheme of an algebraic scheme `X`
such that `X` is normally flat along `D`, and if `f : X' → X` is the monoidal transformation of `X` with center `D`,
then we have `s_{x'}(X'/Y') ≦ s_{f(x')}(X/Y)` for all points `x'` of `X'`, where `(Y', Y)` is a [sic] arbitrary pair of
non-singular algebraic `B`-schemes such that `Y' ⊃ X'`, `Y ⊃ X` and `f` can be extended to the monoidal transformation
`Y' → Y` with center `D`."

Formalization notes (encoding): the pairs `Y ⊃ X`, `Y' ⊃ X'` are `Ambient` embeddings `A`, `A'` of the schemes `X`, `X'`;
"`f` can be extended to the monoidal transformation `Y' → Y` with center `D`" is `Ambient.IsExtensionOf`; "a
arbitrary" is the printed article (a misprint for "an", not significant).  The original sentence is the requirement
on a function `s`, so this is a predicate on `s`. -/
@[blueprint "def:0.4-character-1"
  (statement := /-- Property (1) of a character $s$: if $D$ is a non-singular algebraic subscheme of an algebraic
    scheme $X$ such that $X$ is normally flat along $D$, and $f\colon X'\to X$ is the monoidal transformation of $X$
    with center $D$, then $s_{x'}(X'/Y')\le s_{f(x')}(X/Y)$ for all points $x'$ of $X'$, where $(Y',Y)$ is an
    arbitrary pair of non-singular algebraic $B$-schemes such that $Y'\supset X'$, $Y\supset X$ and $f$ can be
    extended to the monoidal transformation $Y'\to Y$ with center $D$. (Ch.~0 \S4, p.~137.) -/)
  (latexEnv := "definition")]
def HasProperty1 (s : CharacterTriple B → P) : Prop :=
  ∀ {Z : Scheme.{u}} (A : Ambient B Z) (D : Subscheme Z), D.IsNonsingular → D.IsNormallyFlatAlong →
    ∀ (t : MonoidalTransformation Z D) (A' : Ambient B t.X'), A.IsExtensionOf D t.f A' →
      ∀ z' : t.X', s (A'.triple z') ≤ s (A.triple (t.f.base z'))

/-- **Property (2) of a character** (p. 137): "Suppose there is given an infinite sequence of monoidal transformations
`{f_i : X_{i+1} → X_i}` (`i = 0, 1 2, ⋯`) with centers `D_i` in `X_i` such that `D_i` is non-singular and that `X_i` is
normally flat along `D_i` for all `i`, and also an infinite sequence of points `{x_i}` with `x_i ∈ X_i` such that
`f_i(x_{i+1}) = x_i` for all `i`.  Then there exists an integer `r` such that for all `i ≧ r`, `s_{x_i}(X_i/Y_i) =
s_{x_r}(X_r/Y_r)`, where `{Y_i}` is any sequence of non-singular algebraic `B`-schemes such that `Y_i ⊃ X_i` and `f_i`
can be extended to the monoidal transformation `Y_{i+1} → Y_i` with center `D_i` for all `i`."  (p. 137)

Formalization notes (encoding): the infinite sequence is a `MonoidalSequence`; the sequence `{Y_i}` with the embeddings
is a family `A i` of `Ambient` embeddings of the `X_i` with `(A i).IsExtensionOf (D i) (f i) (A (i+1))`.  Reading of the
order of the quantifiers (recorded as an encoding to confirm): the integer `r` is chosen after the sequences
`{f_i}`, `{x_i}` and before `{Y_i}`, as in the printed order ("there exists an integer `r` such that …, where `{Y_i}`
is any sequence"), so `r` does not depend on `{Y_i}`. -/
@[blueprint "def:0.4-character-2"
  (statement := /-- Property (2) of a character $s$: suppose given an infinite sequence of monoidal transformations
    $\{f_i\colon X_{i+1}\to X_i\}$ with centers $D_i$ in $X_i$ such that $D_i$ is non-singular and $X_i$ is normally
    flat along $D_i$ for all $i$, and an infinite sequence of points $x_i\in X_i$ with $f_i(x_{i+1})=x_i$. Then
    there exists an integer $r$ such that for all $i\ge r$, $s_{x_i}(X_i/Y_i)=s_{x_r}(X_r/Y_r)$, where $\{Y_i\}$ is
    any sequence of non-singular algebraic $B$-schemes such that $Y_i\supset X_i$ and $f_i$ can be extended to the
    monoidal transformation $Y_{i+1}\to Y_i$ with center $D_i$ for all $i$. (Ch.~0 \S4, p.~137.) Formalization
    note (encoding): $r$ is chosen before $\{Y_i\}$, as in the printed order. -/)
  (latexEnv := "definition")]
def HasProperty2 (s : CharacterTriple B → P) : Prop :=
  ∀ σ : MonoidalSequence.{u}, (∀ i, (σ.D i).IsNonsingular ∧ (σ.D i).IsNormallyFlatAlong) →
    ∀ x : ∀ i, σ.X i, (∀ i, (σ.f i).base (x (i + 1)) = x i) →
      ∃ r : ℕ, ∀ A : ∀ i, Ambient B (σ.X i), (∀ i, (A i).IsExtensionOf (σ.D i) (σ.f i) (A (i + 1))) →
        ∀ i, r ≤ i → s ((A i).triple (x i)) = s ((A r).triple (x r))

end Character

/-! ### Question (D*) (pp. 137–138) -/

/-- The condition (a) of Question (D*): for a succession `{f_i : X_{i+1} → X_i}` with centers `D_i`, every `D_i` is
non-singular and `X_i` is normally flat along `D_i`. -/
def _root_.Hironaka.MonoidalSuccession.IsNonsingularNormallyFlatSteps :
    {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, _, MonoidalSuccession.nil _ => True
  | _, _, MonoidalSuccession.cons B _ rest => B.IsNonsingular ∧ B.IsNormallyFlatAlong ∧
      rest.IsNonsingularNormallyFlatSteps

/-- The condition (b) of Question (D*) for a character `s`, the value `v = s_x(X'_0/Y'_0)`, a succession
`{f_i : X_{i+1} → X_i}` with centers `D_i`, the open subset `X'_i = U ⊆ X_i` with an embedding `A` into a non-singular
algebraic `B`-scheme `Y'_i`, and the set `pts` of the points of `X_i` which are mapped to `x`: for every choice of
embeddings of the later `X'_j` (with `X'_{j+1} = f_j⁻¹(X'_j)`, so that `f_j` induces the monoidal transformation
`f'_j : X'_{j+1} → X'_j` with center `D_j ∩ X'_j`, and `f'_j` extends to the monoidal transformation
`Y'_{j+1} → Y'_j` with center `D_j ∩ X'_j`), at the end `s_{x_r}(X'_r/Y'_r) < v` for the points `x_r` of `X_r` over `x`.
The data are carried along the succession, as in `IsMainIIZero`. -/
def _root_.Hironaka.MonoidalSuccession.CharacterDrops {B : Type u} [Field B] {P : Type v} [PartialOrder P]
    (s : CharacterTriple B → P) (v : P) :
    {X Y : Scheme.{u}} → MonoidalSuccession X Y → (U : X.Opens) → Ambient B U.toScheme → Set X → Prop
  | _, _, MonoidalSuccession.nil _, U, A, pts => ∀ z ∈ pts, ∀ hz : z ∈ U, s (A.triple ⟨z, hz⟩) < v
  | _, _, MonoidalSuccession.cons C t rest, U, A, pts =>
      ∀ A' : Ambient B (t.f ⁻¹ᵁ U).toScheme,
        A.IsExtensionOf (Subscheme.totalTransform U.ι C) (t.f ∣_ U) A' →
          rest.CharacterDrops s v (t.f ⁻¹ᵁ U) A' (t.f.base ⁻¹' pts)

/-- **Question (D\*) of pp. 137–138** for a given character `s` (with the properties (1), (2) of p. 137): "Let `X` be
an algebraic `B`-scheme.  We denote by `red(X)` the associated reduced scheme of `X`, i.e., the reduced subscheme of
`X` which contains all the points of `X`.  Let `x` be a point of `X` such that either it is a multiple point of
`red(X)` or `X` is not normally flat along `red(X)` at `x`.  Let `X'_0` be the restriction of `X` to an open
neighborhood of `x`, and `Y'_0` a non-singular algebraic `B`-scheme containing `X'_0` as a subscheme.  We then ask if
there exists a finite succession of monoidal transformations `{f_i : X_{i+1} → X_i}` `(0 ≦ i < r)` with centers `D_i`
in `X_i` such that (a) `D_i` is non-singular and `X_i` is normally flat along `D_i` for all `i`; and (b) … then we have
`s_{x_r}(X'_r/Y'_r) < s_x(X'_0/Y'_0)` for all points `x_r` of `X_r` which are mapped to the point `x`."  (pp. 137–138;
the omitted part of (b) says: "if `X'_i` is the restriction of `X_i` to a suitable open subset such that `f_i` induces
the monoidal transformation `f'_i : X'_{i+1} → X'_i` with center `D_i ∩ X'_i` for all `i`, and if `Y'_i` is a
non-singular algebraic `B`-scheme containing `X'_i` such that `f'_i` can be extended to the monoidal transformation
`Y'_{i+1} → Y'_i` with center `D_i ∩ X'_i` for all `i`".)

Formalization notes (encoding): the question is for the algebraic `B`-schemes `X` over a field `B` (separated and of
finite type), with `x`, `U = X'_0` (`Scheme.Opens`, containing `x`) and the embedding `Y'_0` (`Ambient`) given first and
the succession chosen afterwards, as in the text; "`x` is a multiple point of `red(X)`" is `¬ (red ⊥).IsSimpleAt x` and
"`X` is not normally flat along `red(X)` at `x`" is `¬ (red ⊥).IsNormallyFlatAlongAt x` (equivalent, as `X` is the
subscheme `⊥` of itself, to the predicate `IsNormallyFlatAlongAt'` used in `IsMainIStar`; not proved here); (a) is `IsNonsingularNormallyFlatSteps`; in (b) the "suitable open subset" is
`X'_{i+1} = f_i⁻¹(X'_i)`, the only open subset for which `f_i` induces a monoidal transformation with center
`D_i ∩ X'_i`, and (b) is `CharacterDrops`.  The statement is the property that the answer is affirmative for the
character `s`; the paper asks it "once we have found `s_x(X/Y)` having the above properties (1) and (2)" and does not
say that the answer is affirmative, so the properties are not hypotheses here (they are `IsCharacter`, `HasProperty1`,
`HasProperty2`).

A question is a `Prop` meaning "the answer is affirmative".  Question, not proved here. -/
@[blueprint "def:0.4-question-D-star"
  (statement := /-- \textbf{Question (D$^*$).} Let $s$ be a character of singularities (the paper poses the question once $s$ has
    the properties (1), (2)). Let $X$ be an algebraic $B$-scheme, $x$ a point of $X$ such that either it is a multiple point of
    $\operatorname{red}(X)$ or $X$ is not normally flat along $\operatorname{red}(X)$ at $x$, $X'_0$ the restriction
    of $X$ to an open neighborhood of $x$ and $Y'_0$ a non-singular algebraic $B$-scheme containing $X'_0$. Does there
    exist a finite succession of monoidal transformations $f_i\colon X_{i+1}\to X_i$ with centers $D_i$ in $X_i$,
    $0\le i<r$, such that (a) $D_i$ is non-singular and $X_i$ is normally flat along $D_i$ for all $i$, and (b) if
    $X'_i$ is the restriction of $X_i$ to a suitable open subset such that $f_i$ induces the monoidal transformation
    $f'_i$ with center $D_i\cap X'_i$, and $Y'_i\supset X'_i$ are non-singular algebraic $B$-schemes such that $f'_i$
    extends to the monoidal transformation $Y'_{i+1}\to Y'_i$ with center $D_i\cap X'_i$, then
    $s_{x_r}(X'_r/Y'_r)<s_x(X'_0/Y'_0)$ for all points $x_r$ of $X_r$ mapped to $x$? (Ch.~0 \S4, pp.~137--138.)
    Formalization note (encoding): the \emph{affirmative answer} is stated for an arbitrary function $s$ on the
    triples of $\mathcal C$; the properties (1), (2) are not hypotheses (they are \texttt{IsCharacter},
    \texttt{HasProperty1}, \texttt{HasProperty2}); the suitable open subsets are the preimages
    $X'_{i+1}=f_i^{-1}(X'_i)$. Question: not proved here. -/)
  (latexEnv := "definition")]
def QuestionDStar {P : Type v} [PartialOrder P] (B : Type u) [Field B] (s : CharacterTriple B → P) : Prop :=
  ∀ {X : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType pX] [QuasiCompact pX] [IsSeparated pX] (x : X),
    (¬ (Subscheme.red (⊥ : Subscheme X)).IsSimpleAt x ∨
      ¬ (Subscheme.red (⊥ : Subscheme X)).IsNormallyFlatAlongAt x) →
    ∀ (U : X.Opens) (hx : x ∈ U) (A₀ : Ambient B U.toScheme),
      ∃ (Z : Scheme.{u}) (σ : MonoidalSuccession X Z), σ.IsNonsingularNormallyFlatSteps ∧
        σ.CharacterDrops s (s (A₀.triple ⟨x, hx⟩)) U A₀ {x}

/-! ### Main Theorem I\* is stronger than the strong form (p. 138) -/

/-- **Main Theorem I\* is "obviously stronger" than Main Theorem I in the strong form** (p. 138): "At any rate, the
above abstract arguments indicate the most basic principle by which we can prove the following theorem which is
obviously stronger than main theorem I in the strong form with (a), (b), and (c) stated in the previous section:"
(followed by Main Theorem I\*).

Formalization notes (encoding): the implication between the two theorems, for the algebraic `B`-schemes over fields `B`
of characteristic zero (separated and of finite type): Main Theorem I\* for all `X` (a succession with
`MonoidalSuccession.IsMainIStar`) implies the strong form of Main Theorem I for all reduced and irreducible `X` (a
succession with `MonoidalSuccession.IsStrongResolution`).  Both theorems are formalized (`thm:0.4-main-I-star`,
`thm:0.3-main-I-strong`); the implication between them is not, and the paper gives no argument for it ("obviously").

Stated without argument ("obviously stronger", p. 138); not proved here. -/
@[blueprint "thm:0.4-main-I-star-stronger"
  (statement := /-- Main Theorem~I$^*$ is stronger than Main Theorem~I in the strong form: if Main Theorem~I$^*$ holds
    for all algebraic $B$-schemes, $B$ a field of characteristic zero, then the strong form of Main Theorem~I holds for
    all reduced and irreducible ones. (Ch.~0 \S4, p.~138: ``the following theorem which is obviously stronger than
    main theorem I in the strong form with (a), (b), and (c) stated in the previous section''.) Not proved here:
    stated without argument (``obviously''). -/)
  (latexEnv := "theorem")]
def MainIStarImpliesStrongForm : Prop :=
  (∀ (B : Type u) [Field B] [CharZero B] {X : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of B))
      [LocallyOfFiniteType pX] [QuasiCompact pX] [IsSeparated pX],
      ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainIStar) →
    ∀ (B : Type u) [Field B] [CharZero B] {X : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of B))
      [LocallyOfFiniteType pX] [QuasiCompact pX] [IsSeparated pX] [AlgebraicGeometry.IsReduced X]
      [IrreducibleSpace X],
      ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsStrongResolution

end EquimultiplicityQuestions

end Hironaka
