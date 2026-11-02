/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Architect
public import Hironaka.Compat.BlowupLocalIso
public import Hironaka.Compat.BlowupSingleCenter
public import Hironaka.Compat.MainISystem
public import Hironaka.Ch4.MainTheoremIZero
public import Hironaka.Statements

/-!
# Main Theorem I with a single center, and its weak form (Ch. 0 §3, pp. 132-133)

> MAIN THEOREM I. Let `B` be a field of characteristic zero. If `X` is an algebraic `B`-scheme, say reduced and
> irreducible, then there exists an algebraic subscheme `D` of `X` such that (i) the set of points of `D` is exactly the
> singular locus of `X`, and (ii) if `f : X̃ → X` is the monoidal transformation of `X` with center `D`, then `X̃` is
> non-singular.  (p. 132)
> We see that the complementary open subset of `X` to `D`, say `U`, is dense in the underlying topological space of `X`
> and that `f` induces an isomorphism of `X|f⁻¹(U)` to `X|U`.  By replacing the condition (i) by these conditions on `D`,
> we get main theorem I in the weak form.  (p. 132)

The paper's route (pp. 132-133): Main Theorem I in the strong form gives a succession `X_r → ⋯ → X_0 = X` of
monoidal transformations with non-singular `X_r` whose centers `D_i` contain no simple point of `X_i`; "One can see that,
in general, a morphism obtained by a finite succession of monoidal transformations can be also obtained by a single
monoidal transformation with suitably chosen center" (p. 132, proved in `Compat/BlowupSingleCenter`,
`MonoidalSuccession.exists_monoidalTransformation`).  The paper does not say why the points of that single center are
exactly the singular locus (i); this is the bookkeeping fact `MonoidalSuccession.centerPts_eq_of_isStrongResolution`
proved here: each `f_i` is an isomorphism off its center, and the centers contain only multiple points.

Contents:
* `MonoidalSuccession.IsStrongResolution.isNonsingular` (the last scheme of a strong resolution is non-singular) and
  `MonoidalSuccession.centerPts_eq_of_isStrongResolution` (the bookkeeping fact);
* `MainTheorem.Ch0.I_strong_eq_of_isAlgebraicScheme` (the succession and the single center linked) and its printed form
  `I_strong_eq`;
* `MainTheorem.Ch0.I_of_isAlgebraicScheme` (Main Theorem I) and its printed form `I`;
* `MainTheorem.Ch0.I_isProper_of_isAlgebraicScheme` (the same with `f` proper, cf. (3) of p. 112);
* `MainTheorem.Ch0.I_weak_of_isAlgebraicScheme` (the weak form) and its printed form `I_weak`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

/-! ### Simple points off the center -/

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X}

/-- p. 167 on simple points: off the center the monoidal transformation does not change the local rings, so for
`f(y) ∉ B` the scheme `X'` is simple at `y` iff `X` is simple at `f(y)` (`bijective_stalkMap_of_notMem_pts`). -/
theorem isSimpleAt_iff_of_notMem_pts (t : MonoidalTransformation X B) (y : t.X') (hy : t.f y ∉ B.pts) :
    t.X'.IsSimpleAt y ↔ X.IsSimpleAt (t.f y) := by
  let e := RingEquiv.ofBijective (t.f.stalkMap y).hom (t.bijective_stalkMap_of_notMem_pts y hy)
  constructor
  · intro h
    have : IsRegularLocalRing (t.X'.presheaf.stalk y) := h
    exact IsRegularLocalRing.of_ringEquiv e.symm
  · intro h
    have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := h
    exact IsRegularLocalRing.of_ringEquiv e

/-- p. 167: a point off the center is the image of a point of `X'` (`f` induces an isomorphism of `X' − f⁻¹(B)` onto
`X − B`, `isIso_morphismRestrict_complOpens`). -/
theorem exists_eq_of_notMem_pts (t : MonoidalTransformation X B) {x : X} (hx : x ∉ B.pts) :
    ∃ y : t.X', t.f y = x := by
  have := t.isIso_morphismRestrict_complOpens
  obtain ⟨z, hz⟩ := (t.f ∣_ complOpens B).homeomorph.surjective ⟨x, hx⟩
  refine ⟨z.1, ?_⟩
  rw [← morphismRestrict_base_coe]
  exact congrArg Subtype.val hz

end MonoidalTransformation

/-! ### The bookkeeping fact: the centers lie over the singular locus -/

namespace MonoidalSuccession

/-- The last scheme `X_r = X̃` of a succession satisfying the strong form is non-singular. -/
theorem IsStrongResolution.isNonsingular {X Y : Scheme.{u}} {s : MonoidalSuccession X Y}
    (hs : s.IsStrongResolution) : Y.IsNonsingular := by
  induction s with
  | nil X => exact hs
  | cons B t rest ih => exact ih hs.2.2.2

/-- The bookkeeping fact behind (i) of Main Theorem I (p. 132): for a succession `{f_i : X_{i+1} → X_i}` satisfying the
strong form (centers `D_i` without simple points of `X_i`, `X_r` non-singular), the points of `X = X_0` lying under some
center (`centerPts`, the points of the single center of p. 133) are exactly the multiple points of `X`.

Gap filled (not printed): the paper passes from the strong form to (i) without comment.  Proof by induction on the
length: a point of `D_0` is multiple by (b); off `D_0` the transformation `f_0` is an isomorphism
(`isIso_morphismRestrict_complOpens`), so a point `x ∉ D_0` is `f_0(x_1)` with the same local ring, and `x` is multiple iff
`x_1` is, iff (induction) `x_1` lies under a later center; a point `f_0(x_1)` with `x_1` multiple is either in `D_0` or
has the local ring of `x_1`.  For the empty succession `X` is non-singular. -/
@[blueprint "lem:0.3-center-pts-singular"
  (statement := /-- Let $\{f_i\colon X_{i+1}\to X_i\}_{0\le i<r}$, $X_0=X$, be a finite succession of monoidal
    transformations with centers $D_i$ such that (b) $D_i$ contains no simple point of $X_i$ for $0\le i<r$, and $X_r$
    is non-singular. Then $\bigcup_i(f_0\circ\cdots\circ f_{i-1})(D_i)$ is exactly the singular locus of $X$.
    \textbf{Gap in the paper filled.} Not printed; it is the step from the strong form to (i) of Main Theorem I
    (p.~132). -/)
  (proof := /-- Induction on $r$. For $r=0$, $X$ is non-singular and the union is empty. For $r>0$ the induction
    hypothesis says that the union $S_1$ of the images in $X_1$ of the later centers is the singular locus of $X_1$, and
    the union for $X$ is $D_0\cup f_0(S_1)$. The points of $D_0$ are multiple by (b). Off $D_0$, $f_0$ induces an
    isomorphism of $X_1-f_0^{-1}(D_0)$ onto $X-D_0$ (\cref{compat:blowup-local-iso-open}), so every $x\notin D_0$ is
    $f_0(x_1)$ with $\mathcal O_{X,x}\cong\mathcal O_{X_1,x_1}$ (\cref{compat:blowup-local-iso-stalk}): $x$ is multiple
    iff $x_1$ is, iff $x_1\in S_1$. -/)
  (proofUses := ["thm:0.3-main-I-strong", "compat:blowup-local-iso-open", "compat:blowup-local-iso-stalk",
    "prop:0.3-single-center"])
  (latexEnv := "lemma")]
theorem centerPts_eq_of_isStrongResolution {X Y : Scheme.{u}} (s : MonoidalSuccession X Y)
    (hs : s.IsStrongResolution) : s.centerPts = {x | ¬ X.IsSimpleAt x} := by
  induction s with
  | nil X =>
    ext x
    simp only [centerPts_nil, Set.mem_empty_iff_false, Set.mem_ofPred_eq, false_iff, not_not]
    exact hs x
  | cons B t rest ih =>
    obtain ⟨-, hb, -, hrest⟩ := hs
    rw [centerPts_cons, ih hrest]
    ext x
    simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro (hx | ⟨y, hy, rfl⟩)
      · exact hb x hx
      · intro hsx
        by_cases hyB : t.f y ∈ B.pts
        · exact hb _ hyB hsx
        · exact hy ((t.isSimpleAt_iff_of_notMem_pts y hyB).mpr hsx)
    · intro hx
      by_cases hxB : x ∈ B.pts
      · exact Or.inl hxB
      · obtain ⟨y, rfl⟩ := t.exists_eq_of_notMem_pts hxB
        exact Or.inr ⟨y, fun h => hx ((t.isSimpleAt_iff_of_notMem_pts y hxB).mp h), rfl⟩

end MonoidalSuccession

/-! ### Density of the simple points -/

/-- `X` is simple at `x` as soon as the subscheme `⊥ = X` is (converse of `Subscheme.isSimpleAt_bot_of_isSimpleAt`). -/
theorem Subscheme.isSimpleAt_of_isSimpleAt_bot {X : Scheme.{u}} {x : X} (h : (⊥ : Subscheme X).IsSimpleAt x) :
    X.IsSimpleAt x := by
  have : IsRegularLocalRing (X.presheaf.stalk x ⧸ (⊥ : Subscheme X).stalkIdeal x) := h.2
  rw [Subscheme.stalkIdeal_bot_eq] at this
  exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot (X.presheaf.stalk x))

/-- p. 172: "the set of simple points of a reduced algebraic scheme is open and dense": the simple points are dense.
Every point specializes from a simple point (the generic point of an irreducible component through it,
`Subscheme.exists_specializes_isMainResolvedAt` for `V_0 = W = X`). -/
theorem dense_setOf_isSimpleAt (X : Scheme.{u}) [IsAlgebraicScheme X] [AlgebraicGeometry.IsReduced X] :
    Dense {x : X | X.IsSimpleAt x} := by
  intro x
  have hx : x ∈ (⊥ : Subscheme X).pts :=
    Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr (by rw [Subscheme.stalkIdeal_bot_eq]; exact bot_ne_top)
  obtain ⟨η, hηx, hη, -⟩ := Subscheme.exists_specializes_isMainResolvedAt
    (mainSystem (X := X) (Fin.elim0 : Fin 0 → Subscheme X)) ⊥ Subscheme.isReduced_bot_of_isReduced
    (fun j => by rw [mainSystem_elim0_eq_bot j]; exact fun _ => le_rfl) hx
  have hηS : ({η} : Set X) ⊆ {y : X | X.IsSimpleAt y} :=
    Set.singleton_subset_iff.mpr (Subscheme.isSimpleAt_of_isSimpleAt_bot hη)
  exact closure_mono hηS (specializes_iff_mem_closure.mp hηx)

/-! ### The statements -/

namespace MainTheorem.Ch0

/-- **Main Theorem I in the strong form, linked with the single center** (pp. 132-133): the succession of the strong
form ("The morphism `f` is obtained by a finite succession of monoidal transformations", p. 132) composes to a single
monoidal transformation `t` with center `D` (up to an isomorphism `e` over `X`), and the points of `D` are the singular
locus of `X`.

Gap filled: the composition is the p. 133 "we can see" (`MonoidalSuccession.exists_monoidalTransformation`); the
identification of the points of `D` with the singular locus is not printed
(`MonoidalSuccession.centerPts_eq_of_isStrongResolution`). -/
theorem I_strong_eq_of_isAlgebraicScheme [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X] [AlgebraicGeometry.IsReduced X] :
    ∃ (D : Subscheme X) (Y : Scheme.{u}) (s : MonoidalSuccession X Y) (t : MonoidalTransformation X D)
      (e : Y ≅ t.X'), s.IsStrongResolution ∧ D.pts = {x | ¬ X.IsSimpleAt x} ∧ e.hom ≫ t.f = s.composite := by
  obtain ⟨Y, s, hs⟩ := I_strong_of_isAlgebraicScheme X
  obtain ⟨D, t, e, he, hD⟩ := s.exists_monoidalTransformation_of_isAlgebraicScheme
  exact ⟨D, Y, s, t, e, hs, hD.trans (s.centerPts_eq_of_isStrongResolution hs), he⟩

/-- `I_strong_eq_of_isAlgebraicScheme` as printed (p. 132): `X` an algebraic `B`-scheme (not necessarily separated: the
statement is more general than the printed one), `B` a field of characteristic zero, reduced and irreducible (the
irreducibility is not used). -/
theorem I_strong_eq [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p] [QuasiCompact p] [AlgebraicGeometry.IsReduced X] [IrreducibleSpace X] :
    ∃ (D : Subscheme X) (Y : Scheme.{u}) (s : MonoidalSuccession X Y) (t : MonoidalTransformation X D)
      (e : Y ≅ t.X'), s.IsStrongResolution ∧ D.pts = {x | ¬ X.IsSimpleAt x} ∧ e.hom ≫ t.f = s.composite := by
  have := IsAlgebraicScheme.of_field p
  exact I_strong_eq_of_isAlgebraicScheme X

/-- **Main Theorem I** (p. 132), for every reduced algebraic scheme (p. 151).

Formalization notes (encoding): "the singular locus of `X`" is the set of points at which `X` is not simple; "the
monoidal transformation of `X` with center `D`" is any `t : MonoidalTransformation X D` (they exist, the cited
`MonoidalTransformation.exists_isProper`, and are isomorphic over `X`, `MonoidalTransformation.unique_up_to_iso`); `D`
is a closed subscheme of the algebraic scheme `X`, hence algebraic.

Deviation from the paper (gap filled): the paper derives (i), (ii) from the strong form and p. 133 ("One can see that, in
general, a morphism obtained by a finite succession of monoidal transformations can be also obtained by a single
monoidal transformation with suitably chosen center"), without saying why the points of the single center are the
singular locus.  Both are proved: `MonoidalSuccession.exists_monoidalTransformation` and
`MonoidalSuccession.centerPts_eq_of_isStrongResolution`. -/
@[blueprint "thm:0.3-main-I"
  (statement := /-- Let $X$ be a reduced algebraic scheme. Then there exists an algebraic subscheme $D$ of $X$ such that
    (i) the set of points of $D$ is exactly the singular locus of $X$, and (ii) if $f\colon\tilde X\to X$ is the
    monoidal transformation of $X$ with center $D$, then $\tilde X$ is non-singular. (Main theorem I, p.~132: ``Let $B$
    be a field of characteristic zero. If $X$ is an algebraic $B$-scheme, say reduced and irreducible, then there exists
    an algebraic subscheme $D$ of $X$ such that (i) the set of points of $D$ is exactly the singular locus of $X$, and
    (ii) if $f\colon\tilde X\to X$ is the monoidal transformation of $X$ with center $D$, then $\tilde X$ is
    non-singular.'' Valid over any base ring of the class $\mathfrak B$ by p.~151; the irreducibility is not used.) -/)
  (proof := /-- By the strong form (\cref{thm:0.3-main-I-strong}) there is a succession
    $\{f_i\colon X_{i+1}\to X_i\}_{0\le i<r}$, $X_0=X$, with centers $D_i$ containing no simple point of $X_i$ and with
    $X_r$ non-singular. By \cref{prop:0.3-single-center} the composite $f_0\circ\cdots\circ f_{r-1}$ is, up to an
    isomorphism over $X$, the monoidal transformation of $X$ with a center $D$ whose points are
    $\bigcup_i(f_0\circ\cdots\circ f_{i-1})(D_i)$, which is the singular locus of $X$ (\cref{lem:0.3-center-pts-singular});
    this is (i). Every monoidal transformation of $X$ with center $D$ is isomorphic over $X$ to this one
    (\cref{lem:monoidal-transformation-unique}), hence to $X_r$, which is non-singular; this is (ii).
    \textbf{Gap in the paper filled.} The single center is the p.~133 ``One can see'' (\cref{prop:0.3-single-center});
    the identification (i) of its points with the singular locus is not printed. -/)
  (proofUses := ["thm:0.3-main-I-strong", "prop:0.3-single-center", "lem:0.3-center-pts-singular",
    "lem:monoidal-transformation-unique"])
  (latexEnv := "theorem")]
theorem I_of_isAlgebraicScheme [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X] [AlgebraicGeometry.IsReduced X] :
    ∃ D : Subscheme X, D.pts = {x | ¬ X.IsSimpleAt x} ∧ ∀ t : MonoidalTransformation X D, t.X'.IsNonsingular := by
  obtain ⟨D, Y, s, t₀, e, hs, hD, -⟩ := I_strong_eq_of_isAlgebraicScheme X
  refine ⟨D, hD, fun t => ?_⟩
  obtain ⟨e', -, -⟩ := t₀.unique_up_to_iso t
  exact CD.isNonsingular_of_iso (e ≪≫ e').symm hs.isNonsingular

/-- **Main Theorem I**, as printed (p. 132): `X` an algebraic `B`-scheme (not necessarily separated: the statement is
more general than the printed one), `B` a field of characteristic zero, reduced and irreducible.  (A field of
characteristic zero belongs to `𝔅`, `(a)` of p. 161, so this is `I_of_isAlgebraicScheme`; the irreducibility is not
used.) -/
theorem I [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p] [QuasiCompact p] [AlgebraicGeometry.IsReduced X] [IrreducibleSpace X] :
    ∃ D : Subscheme X, D.pts = {x | ¬ X.IsSimpleAt x} ∧ ∀ t : MonoidalTransformation X D, t.X'.IsNonsingular := by
  have := IsAlgebraicScheme.of_field p
  exact I_of_isAlgebraicScheme X

/-- Main Theorem I (p. 132) with the morphism `f` proper, the condition (3) of the resolution problem of p. 112 ("(3) `f`
is proper in the sense of Grothendieck. (See §5, Ch. II, [6].)"), which the printed statement leaves implicit:
every monoidal transformation of an algebraic scheme is proper (`MonoidalTransformation.isProper`). -/
theorem I_isProper_of_isAlgebraicScheme [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X] [AlgebraicGeometry.IsReduced X] :
    ∃ D : Subscheme X, D.pts = {x | ¬ X.IsSimpleAt x} ∧
      ∀ t : MonoidalTransformation X D, t.X'.IsNonsingular ∧ IsProper t.f := by
  have := IsAlgebraicScheme.isNoetherian X
  obtain ⟨D, hD, h⟩ := I_of_isAlgebraicScheme X
  exact ⟨D, hD, fun t => ⟨h t, t.isProper⟩⟩

/-- **Main Theorem I in the weak form** (p. 132), for every reduced algebraic scheme: there is a subscheme `D` whose
complement `U` is dense, such that the monoidal transformation `f : X̃ → X` with center `D` has `X̃` non-singular and
induces an isomorphism of `f⁻¹(U)` onto `U`.

Formalization notes (encoding): `U = X − D` is `MonoidalTransformation.complOpens D`; "`f` induces an isomorphism of
`X|f⁻¹(U)` to `X|U`" is `IsIso (t.f ∣_ complOpens D)`.

Deviation from the paper (gap filled): "We see" (p. 132), no proof.  The same `D` as in Main Theorem I works: its
complement is the set of simple points, dense by p. 172 ("the set of simple points of a reduced algebraic scheme is open
and dense"; every point specializes from the generic point of a component, where the local ring is a field), and every
monoidal transformation is an isomorphism off its center (p. 167, `isIso_morphismRestrict_complOpens`). -/
@[blueprint "thm:0.3-main-I-weak"
  (statement := /-- Let $X$ be a reduced algebraic scheme. Then there exists an algebraic subscheme $D$ of $X$ such that
    the complementary open subset $U$ of $X$ to $D$ is dense in $X$, and, if $f\colon\tilde X\to X$ is the monoidal
    transformation of $X$ with center $D$, then $f$ induces an isomorphism of $\tilde X|f^{-1}(U)$ to $X|U$ and
    $\tilde X$ is non-singular. (Main theorem I in the weak form, p.~132: ``We see that the complementary open subset of
    $X$ to $D$, say $U$, is dense in the underlying topological space of $X$ and that $f$ induces an isomorphism of
    $X|f^{-1}(U)$ to $X|U$. By replacing the condition (i) by these conditions on $D$, we get main theorem I in the
    weak form.'') -/)
  (proof := /-- Take $D$ as in \cref{thm:0.3-main-I}. Its complement is the set of simple points of $X$. Every point
    of $X$ is a specialization of the generic point of an irreducible component through it, where the local ring of the
    reduced $X$ is a field, hence regular (\cref{lem:I.3-resolved-generization}); so the simple points are dense
    (p.~172: ``the set of simple points of a reduced algebraic scheme is open and dense''). Every monoidal
    transformation with center $D$ induces an isomorphism of $\tilde X-f^{-1}(D)$ onto $X-D$
    (\cref{compat:blowup-local-iso-open}), and $\tilde X$ is non-singular by \cref{thm:0.3-main-I}.
    \textbf{Gap in the paper filled.} The paper says ``We see'' and gives no proof. -/)
  (proofUses := ["thm:0.3-main-I", "lem:I.3-resolved-generization", "compat:blowup-local-iso-open"])
  (latexEnv := "theorem")]
theorem I_weak_of_isAlgebraicScheme [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X] [AlgebraicGeometry.IsReduced X] :
    ∃ D : Subscheme X, Dense D.ptsᶜ ∧ ∀ t : MonoidalTransformation X D,
      t.X'.IsNonsingular ∧ IsIso (t.f ∣_ MonoidalTransformation.complOpens D) := by
  obtain ⟨D, hD, h⟩ := I_of_isAlgebraicScheme X
  refine ⟨D, ?_, fun t => ⟨h t, t.isIso_morphismRestrict_complOpens⟩⟩
  rw [hD, Set.compl_ofPred]
  simpa only [not_not] using dense_setOf_isSimpleAt X

/-- **Main Theorem I in the weak form**, as printed (p. 132): `X` an algebraic `B`-scheme (not necessarily separated:
the statement is more general than the printed one), `B` a field of characteristic zero, reduced and irreducible (the
irreducibility is not used). -/
theorem I_weak [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p] [QuasiCompact p] [AlgebraicGeometry.IsReduced X] [IrreducibleSpace X] :
    ∃ D : Subscheme X, Dense D.ptsᶜ ∧ ∀ t : MonoidalTransformation X D,
      t.X'.IsNonsingular ∧ IsIso (t.f ∣_ MonoidalTransformation.complOpens D) := by
  have := IsAlgebraicScheme.of_field p
  exact I_weak_of_isAlgebraicScheme X

end MainTheorem.Ch0

end Hironaka
