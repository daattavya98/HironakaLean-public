/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import Architect
public import Hironaka.Ch4.MainTheoremII
public import Hironaka.Ch4.MainTheoremIZero
public import Hironaka.Compat.BlowupLocalIso
public import Hironaka.Compat.ComponentStalk
public import Hironaka.Compat.TrivializingSystem
public import Hironaka.Compat.WeakTransformProduct
public import Hironaka.Statements

/-!
# Ch. 0 §5 (p. 146): Corollary 3 of Main Theorem II, the simplification of an algebraic boundary

> **Corollary 3.**  Let `X` be the same as in main theorem II.  Let `W` be an algebraic subscheme of `X` which is
> nowhere dense in `X`.  Then there exists a finite succession of monoidal transformations `f_i : X_{i+1} → X_i`
> with non-singular centers `D_i`, where `0 ≦ i < r` and `X₀ = X`, such that: (i) `X_r` is non-singular; (ii) if
> `f̄_i` denotes the composition of the `f_j` for `0 ≦ j < i`, `D_i` is contained in `f̄_i⁻¹(W)` for all `i`; and
> (iii) the associated reduced scheme `red(f̄_r⁻¹(W))` of `f̄_r⁻¹(W)` is defined by an invertible sheaf of ideals on
> `X_r` and has only normal crossings. …  In view of main theorem I in the strong form, this assumption of Corollary 2
> may be replaced, without affecting the conclusion, by the weaker one that singular locus of `X` is contained in
> `W`.  (p. 146)

The paper calls Corollary 3 an "immediate but important consequence of main theorem II" and prints no derivation.  The
proof here uses main theorem II in the form II(N) of Ch. I §3 (p. 176),
whose last property `J_r = O_{X_r}` is exactly what is needed (the Ch. 0 form, with `ν(J_{r,y}) < d`, would have to be
iterated over `d`):

* `W` is a coherent sheaf of non-zero ideals: on an algebraic scheme a nowhere dense subscheme has non-zero stalks
  (`Subscheme.stalkIdeal_ne_bot_of_isNowhereDense`: the generic point of an irreducible component would lie in `W`);
* Main Theorem II(N) of Ch. I §3 (`mainTheorem_II`) for `J = W` and `E = ∅` gives a succession with `J_r = O_{X_r}`;
  along it `f̄_i⁻¹(W)` has the points of `J_i ∪ E_i` (Remark 2: `f_i⁻¹(J_i) = J_{i+1} · P^{d_i}` with `d_i ≥ 1`),
  so `D_i ⊆ V(J_i) ⊆ f̄_i⁻¹(W)` (ii), and at the end `red(f̄_r⁻¹(W)) = E_r`, which has only normal crossings
  (`MonoidalSuccession.isBoundarySimplification_of_isMainSuccession`);
* the invertibility in (iii): the Lean predicate `HasOnlyNormalCrossings` does not contain the standing hypothesis of
  Definition 2 ("Assume that the sheaf of ideals of `E` on `X` is invertible (or, equivalently, `E` is everywhere of
  codimension one on `X`)", p. 141); a reduced subscheme with only normal crossings has, at every point, the product of
  some members of a regular system of parameters as local generator, so it is invertible and everywhere of codimension
  one (`Subscheme.isInvertibleIdeal_of_hasOnlyNormalCrossings`).

The last sentence ("In view of main theorem I in the strong form ...") is
`MainTheorem.Ch0.exists_isBoundarySimplification_of_singularLocus_subset`: the strong form
(`MainTheorem.Ch0.I_strong_of_isAlgebraicScheme`) is applied first; its centers contain no simple point, so they lie
over the singular locus, hence in the total transforms of `W`; the total transform of `W` stays nowhere dense; then
Corollary 3 is applied to the non-singular `X_m`, and the two successions are concatenated.  The hypothesis that `X` is
reduced is tacit in the paper: main theorem I in the strong form is stated for reduced `X` (p. 132).

Slips in the paper: "this assumption of Corollary 2" means Corollary 3 (the non-singularity of `X` is an
assumption of Corollary 3); the reducedness of `X` in the last sentence is tacit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

/-! ### Nowhere dense subschemes and normal crossings -/

namespace Subscheme

variable {X : Scheme.{u}}

/-- On an algebraic scheme a subscheme `W` which is nowhere dense in `X` is a coherent sheaf of non-zero ideals: every
stalk `W_x` is a non-zero ideal.  If `W_x = 0`, then `W_η = 0` at the generic point `η` of an irreducible component
through `x`, so `η ∈ W` and the component lies in `W`; but a component of a noetherian space contains a non-empty open
set.

Gap filled: used tacitly when Main Theorem II is applied to `W` in Corollary 3 (p. 146). -/
@[blueprint "lem:0.3-nowhere-dense-nonzero"
  (statement := /-- Let $X$ be an algebraic scheme and $W$ a subscheme of $X$ which is nowhere dense in $X$. Then
    $W_x\ne0$ for every point $x$ of $X$, i.e.\ $W$ is a coherent sheaf of non-zero ideals.
    \textbf{Gap in the paper filled.} Used without comment in Corollary~3 (p.~146). -/)
  (proof := /-- Let $Z$ be an irreducible component of $X$ through $x$ and $\eta$ its generic point. If $W_x=0$ then
    $W_\eta$, the image of $W_x$ under $\mathcal O_{X,x}\to\mathcal O_{X,\eta}$, is $0$, so $\eta\in W$ and $Z\subseteq
    W$ ($W$ is closed). An irreducible component of the noetherian space $X$ contains a non-empty open subset of $X$,
    which contradicts the nowhere density of $W$. -/)
  (latexEnv := "lemma")]
theorem stalkIdeal_ne_bot_of_isNowhereDense [IsAlgebraicScheme X] {W : Subscheme X}
    (hW : IsNowhereDense W.pts) (x : X) : W.stalkIdeal x ≠ ⊥ := by
  intro hx
  have := IsAlgebraicScheme.noetherianSpace X
  have hirr : _root_.IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
  have hη : closure {hirr.genericPoint} = irreducibleComponent x := by
    rw [hirr.isGenericPoint_genericPoint_closure.def, hcl.closure_eq]
  have hηx : hirr.genericPoint ⤳ x :=
    specializes_iff_mem_closure.mpr (by rw [hη]; exact mem_irreducibleComponent)
  have hWcl : IsClosed W.pts := W.support.isClosed
  have hηW : hirr.genericPoint ∈ W.pts := by
    rw [mem_pts_iff_stalkIdeal_ne_top, stalkIdeal_eq_map_stalkSpecializes W hηx, hx, Ideal.map_bot]
    exact bot_ne_top
  have hsub : irreducibleComponent x ⊆ W.pts := by
    rw [← hη]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηW) hWcl
  obtain ⟨o, ho, hne, hoZ⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _
    (irreducibleComponent_mem_irreducibleComponents x)
  have hint : interior W.pts = ∅ := hWcl.isNowhereDense_iff.mp hW
  have ho' : o ⊆ interior W.pts := interior_maximal (hoZ.trans hsub) ho
  rw [hint] at ho'
  exact hne.ne_empty (Set.subset_empty_iff.mp ho')

/-- The local form of a reduced subscheme with only normal crossings (Definition 2, p. 141): at every point `x` the
ideal `E_x` is generated by the product of some members of a regular system of parameters of `O_{X,x}`. -/
theorem exists_stalkIdeal_eq_span_prod_of_hasOnlyNormalCrossings (hX : X.IsNonsingular) {E : Subscheme X}
    (hE : E.IsReduced) (hnc : E.HasOnlyNormalCrossings) (x : X) :
    ∃ K : Finset (X.presheaf.stalk x), ExtendsToRSOP _ K ∧ E.stalkIdeal x = Ideal.span {∏ k ∈ K, k} := by
  obtain ⟨z, hz, ⟨K, hKz, hK⟩, -⟩ := (hasOnlyNormalCrossingsWithAt_iff hE (hX x)).mp (hnc x)
  exact ⟨K, ⟨z, hKz, hz⟩, hK⟩

/-- A reduced subscheme `E` with only normal crossings on a non-singular scheme is everywhere of codimension one
(Definition 2, p. 141: "Assume that the sheaf of ideals of `E` on `X` is invertible (or, equivalently, `E` is everywhere
of codimension one on `X`)"; the Lean predicate `HasOnlyNormalCrossings` does not build in this standing hypothesis,
and here it is recovered from the normal crossings: the local generator is a product of `k ≥ 1` members of a regular
system of parameters, whose ideal has height one). -/
theorem isEverywhereCodimOne_of_hasOnlyNormalCrossings (hX : X.IsNonsingular) {E : Subscheme X}
    (hE : E.IsReduced) (hnc : E.HasOnlyNormalCrossings) : E.IsEverywhereCodimOne :=
  DatumTransform.isEverywhereCodimOne_of_forall_stalk hX
    (exists_stalkIdeal_eq_span_prod_of_hasOnlyNormalCrossings hX hE hnc)

/-- **A reduced subscheme with only normal crossings is defined by an invertible sheaf of ideals** (needed for (iii) of
Corollary 3, p. 146): at every point the ideal is generated by a product of members of a regular system of parameters,
a non-zero element of the domain `O_{X,x}`.

Deviation from the paper (encoding): Definition 2 (p. 141) assumes the invertibility before it defines normal crossings
("Assume that the sheaf of ideals of `E` on `X` is invertible (or, equivalently, `E` is everywhere of codimension one on
`X`)"), so for the paper "has only normal crossings" contains the invertibility; the Lean predicate
`HasOnlyNormalCrossings` does not, and this lemma supplies it. -/
@[blueprint "lem:0.3-normal-crossings-invertible"
  (statement := /-- Let $X$ be a non-singular scheme and $E$ a reduced subscheme of $X$ which has only normal crossings
    in the sense of the local condition of \cref{def:0.2-normal-crossings}. Then the sheaf of ideals of $E$ is
    invertible, and $E$ is everywhere of codimension one.
    Formalization note (encoding): Definition~2 (p.~141) assumes that the sheaf of ideals of $E$ is invertible (``or,
    equivalently, $E$ is everywhere of codimension one on $X$'') before it defines normal crossings; the Lean predicate
    does not contain this standing hypothesis, and the lemma recovers it, as needed for (iii) of Corollary~3. -/)
  (proof := /-- At a point $x$ choose a regular system of parameters $(z_1,\dots,z_n)$ of $\mathcal O_{X,x}$ such that
    the ideal of each component of $E$ through $x$ is generated by one of the $z_i$. Since $E$ is reduced, $E_x$ is the
    intersection of these prime ideals, generated by the product of the corresponding $z_i$; this product is non-zero in
    the domain $\mathcal O_{X,x}$, and its ideal has height one when it is proper. A local generator which is a
    non-zero-divisor spreads to an affine neighbourhood. -/)
  (proofUses := ["def:0.2-normal-crossings"])
  (latexEnv := "lemma")]
theorem isInvertibleIdeal_of_hasOnlyNormalCrossings (hX : X.IsNonsingular) {E : Subscheme X}
    [IsLocallyNoetherian X] (hE : E.IsReduced) (hnc : E.HasOnlyNormalCrossings) : E.IsInvertibleIdeal := by
  refine Subscheme.isInvertibleIdeal_of_forall_stalkIdeal_eq_span E fun x => ?_
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk x)
  obtain ⟨K, hK, hEK⟩ := exists_stalkIdeal_eq_span_prod_of_hasOnlyNormalCrossings hX hE hnc x
  exact ⟨_, hEK, mem_nonZeroDivisors_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun k hk => hK.ne_zero hk)⟩

end Subscheme

/-! ### The properties (ii) and (iii) of Corollary 3 -/

namespace MonoidalSuccession

variable {X Y Z : Scheme.{u}}

/-- The total transform by a succession `f̄ = f₀ ∘ ⋯` starting with `f₀`: `f̄⁻¹(W) = f̄'⁻¹(f₀⁻¹(W))`. -/
theorem totalTransform_cons (B : Subscheme X) (t : MonoidalTransformation X B) (rest : MonoidalSuccession t.X' Y)
    (W : Subscheme X) :
    (cons B t rest).totalTransform W = rest.totalTransform (Subscheme.totalTransform t.f W) := by
  simp only [MonoidalSuccession.totalTransform, composite_cons, Subscheme.totalTransform_comp]

/-- The total transform by a concatenation of successions. -/
theorem totalTransform_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z) (W : Subscheme X) :
    (s.append s').totalTransform W = s'.totalTransform (s.totalTransform W) := by
  simp only [MonoidalSuccession.totalTransform, composite_append, Subscheme.totalTransform_comp]



/-- (ii) for a concatenation: the centers of `s` followed by those of `s'` (for `f̄⁻¹(W)`, `f̄` the composite of `s`). -/
theorem hasNonsingularCentersIn_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z)
    (W : Subscheme X) (hs : s.HasNonsingularCentersIn W)
    (hs' : s'.HasNonsingularCentersIn (s.totalTransform W)) : (s.append s').HasNonsingularCentersIn W := by
  induction s with
  | nil X =>
    rw [totalTransform_nil] at hs'
    exact hs'
  | cons B t rest ih =>
    rw [totalTransform_cons] at hs'
    exact ⟨hs.1, hs.2.1, ih s' _ hs.2.2 hs'⟩

/-- Corollary 3's conclusion for a concatenation: if the centers of `s` are non-singular and contained in the total
transforms of `W`, and `s'` simplifies `f̄⁻¹(W)` (`f̄` the composite of `s`), then `s` followed by `s'` simplifies `W`. -/
theorem isBoundarySimplification_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z)
    (W : Subscheme X) (hs : s.HasNonsingularCentersIn W)
    (hs' : s'.IsBoundarySimplification (s.totalTransform W)) : (s.append s').IsBoundarySimplification W := by
  refine ⟨hasNonsingularCentersIn_append s s' W hs hs'.1, ?_⟩
  rw [totalTransform_append]
  exact hs'.2

/-- **From Main Theorem II(N) to Corollary 3** (p. 146): along a succession with the properties (1)–(4) of Main
Theorem II(N) for `J` and a reduced `E`, the total transforms `W_i` of a subscheme `W` with the points of `J ∪ E` keep
the points of `J_i ∪ E_i`; so the centers `B_i ⊆ V(J_i)` (where `ν(J_i) = d_i ≥ 1`) lie in `W_i`, and at the end
`J_r = O`, so that `red(W_r) = E_r`, which has only normal crossings and is invertible
(`Subscheme.isInvertibleIdeal_of_hasOnlyNormalCrossings`).  The last scheme is non-singular.

The step: by Remark 2 (p. 214) `f_i⁻¹(J_i) = J_{i+1}·P^{d_i}`, `d_i ≥ 1`, so `f_i⁻¹(V(J_i)) = V(J_{i+1}) ∪ f_i⁻¹(B_i)`
(`Subscheme.pts_preimage_eq_pts_weakTransform_union`), and `E_{i+1} = red(f_i⁻¹(E_i ∪ B_i))` has the points of
`f_i⁻¹(E_i) ∪ f_i⁻¹(B_i)`.

Gap filled: the paper calls Corollary 3 an "immediate but important consequence of main theorem II" and prints no
derivation. -/
@[blueprint "lem:0.3-boundary-simplification-main-II"
  (statement := /-- Let $X$ be a non-singular algebraic scheme, $J$ a coherent sheaf of non-zero ideals, $E$ a reduced
    subscheme, and $\{f_i\colon X_{i+1}\to X_i\}_{0\le i<r}$ a succession with the properties (1)--(4) of Main
    Theorem~II($N$) (\cref{thm:I.3-main-II}) for $J$ and $E$. Let $W$ be a subscheme of $X$ whose points are those of
    $V(J)\cup E$. Then $X_r$ is non-singular, the centers $B_i$ are non-singular and contained in $\bar f_i^{-1}(W)$,
    and $\operatorname{red}(\bar f_r^{-1}(W))$ is defined by an invertible sheaf of ideals and has only normal
    crossings.
    \textbf{Gap in the paper filled.} The paper calls Corollary~3 an ``immediate but important consequence of main
    theorem~II'' and prints no derivation. -/)
  (proof := /-- Induction on $r$, with $W_i=\bar f_i^{-1}(W)$ and the invariant: $W_i$ has the points of
    $V(J_i)\cup E_i$. By (2), $\nu(J_{iz})=d_i\ge1$ on $B_i$, so $B_i\subseteq V(J_i)\subseteq W_i$; $B_i$ is
    non-singular, hence reduced, so it is contained in $W_i$ as a subscheme. By Remark~2 (\cref{rem:III.2-2}),
    $f_i^{-1}(J_i)=J_{i+1}P^{d_i}$ with $P$ the ideal of $f_i^{-1}(B_i)$, so $f_i^{-1}(V(J_i))=V(J_{i+1})\cup
    f_i^{-1}(B_i)$, while $E_{i+1}=\operatorname{red}(f_i^{-1}(E_i\cup B_i))$ has the points of
    $f_i^{-1}(E_i)\cup f_i^{-1}(B_i)$; the invariant passes to $i+1$. At the end $J_r=\mathcal O_{X_r}$, so
    $\operatorname{red}(W_r)$ and $E_r$ are reduced with the same points, hence equal; $E_r$ has only normal crossings by
    (4) and is invertible by \cref{lem:0.3-normal-crossings-invertible}. -/)
  (proofUses := ["thm:I.3-main-II", "rem:III.2-2", "lem:0.3-normal-crossings-invertible"])
  (latexEnv := "lemma")]
theorem isBoundarySimplification_of_isMainSuccession [Hironaka.HironakaCitedResults.{u}] (s : MonoidalSuccession X Y) :
    IsAlgebraicScheme X → X.IsNonsingular → ∀ (J E W : Subscheme X), s.IsMainSuccession J E →
      E.IsReduced → (∀ x, J.stalkIdeal x ≠ ⊥) → W.pts = J.pts ∪ E.pts →
        Y.IsNonsingular ∧ s.IsBoundarySimplification W := by
  induction s with
  | nil X =>
    intro hXa hX J E W hs hE _ hW
    obtain ⟨hnc, hJ⟩ := hs
    have hJpts : J.pts = ∅ := by
      rw [hJ]
      exact Subscheme.pts_empty
    have hWE : Subscheme.red W = E := by
      refine Subscheme.eq_of_pts_eq_of_isReduced (Subscheme.isReduced_red W) hE ?_
      change W.pts = E.pts
      rw [hW, hJpts, Set.empty_union]
    have := IsAlgebraicScheme.isNoetherian X
    refine ⟨hX, trivial, ?_⟩
    rw [totalTransform_nil, hWE]
    exact ⟨Subscheme.isInvertibleIdeal_of_hasOnlyNormalCrossings hX hE hnc, hnc⟩
  | cons B t rest ih =>
    intro hXa hX J E W hs hE hJ hW
    obtain ⟨hB, ⟨d, hd, -, hBd⟩, -, hrest⟩ := hs
    have hX' : t.X'.IsNonsingular :=
      (t.isNonsingular_and_isNonsingular_exceptional hX hB.isNonsingular).1
    have h1 : ∀ z ∈ B.pts, 1 ≤ Ideal.nu (J.stalkIdeal z) := fun z hz => by
      rw [hBd z hz]
      exact_mod_cast hd
    have hBJ : B.pts ⊆ J.pts := fun z hz =>
      Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr ((J.one_le_nu_stalkIdeal_iff z).mp (h1 z hz))
    have hW' : (Subscheme.totalTransform t.f W).pts =
        (Subscheme.weakTransform t J).pts ∪
          Subscheme.pts (Subscheme.totalTransform t.f (E.union B)).radical := by
      rw [Subscheme.pts_totalTransform_eq_preimage, hW, Set.preimage_union,
        Subscheme.pts_preimage_eq_pts_weakTransform_union hX hB t J hJ h1,
        pts_radical_totalTransform_union, Set.preimage_union]
      ext y
      simp only [Set.mem_union]
      tauto
    obtain ⟨hY, hrest'⟩ := ih (t.isAlgebraicScheme) hX' (Subscheme.weakTransform t J) _
      (Subscheme.totalTransform t.f W) hrest (Subscheme.isReduced_red _)
      (Subscheme.stalkIdeal_weakTransform_ne_bot hX t hJ) hW'
    refine ⟨hY, ⟨hB.isNonsingular, Subscheme.isContainedIn_of_pts_subset hB.isReduced ?_, hrest'.1⟩, ?_⟩
    · rw [hW]
      exact hBJ.trans Set.subset_union_left
    · rw [totalTransform_cons]
      exact hrest'.2

end MonoidalSuccession

/-! ### Corollary 3 -/

namespace MainTheorem.Ch0

/-- Corollary 3 for a subscheme `W` given as a coherent sheaf of non-zero ideals (every stalk `W_x ≠ 0`), on a
non-singular algebraic scheme: Main Theorem II(N) (`mainTheorem_II`) for `J = W` and `E₀ = ∅`, then
`isBoundarySimplification_of_isMainSuccession`.  The empty scheme is trivial. -/
theorem exists_isBoundarySimplification_of_stalkIdeal_ne_bot [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) (W : Subscheme X) (hW : ∀ x, W.stalkIdeal x ≠ ⊥) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), Y.IsNonsingular ∧ s.IsBoundarySimplification W := by
  by_cases hne : Nonempty X
  · obtain ⟨N, hN⟩ := IsAlgebraicScheme.exists_nat_dim_eq X
    obtain ⟨Y, s, hs⟩ := mainTheorem_II.{u} N X inferInstance hX hN W hW Subscheme.empty
      Subscheme.isReduced_empty Subscheme.isEverywhereCodimOne_empty (Subscheme.hasOnlyNormalCrossings_empty hX)
    exact ⟨Y, s, s.isBoundarySimplification_of_isMainSuccession inferInstance hX W _ W hs
      Subscheme.isReduced_empty hW (by rw [Subscheme.pts_empty, Set.union_empty])⟩
  · exact ⟨X, MonoidalSuccession.nil X, hX, trivial, fun x => (hne ⟨x⟩).elim, fun x => (hne ⟨x⟩).elim⟩

/-- **Corollary 3 of Main Theorem II** (p. 146), the simplification of an algebraic boundary, for an algebraic scheme.

Formalization notes (encoding): "an algebraic subscheme `W` of `X`" is a closed subscheme (`Subscheme X`, a coherent
sheaf of ideals); "nowhere dense" refers to its points; the succession is a `MonoidalSuccession X Y` with `Y = X_r`;
(i) is `Y.IsNonsingular`; the non-singularity of the centers, (ii) and (iii) are
`MonoidalSuccession.IsBoundarySimplification`, with `f̄_i⁻¹(W)` the total transform.  The statement is for algebraic
schemes (p. 151); the printed form (`B` a field of characteristic zero) is `exists_isBoundarySimplification`.

Gap filled: the paper calls it an "immediate but important consequence of main theorem II" and prints no derivation.
Main Theorem II is used in the form II(N) of Ch. I §3 (p. 176), whose (4) `J_r = O_{X_r}` gives (iii) at once (the
Ch. 0 form would be iterated over `d`).  Proof: `W` has non-zero stalks
(`Subscheme.stalkIdeal_ne_bot_of_isNowhereDense`); Main Theorem II(N) for `J = W`, `E₀ = ∅` and
`MonoidalSuccession.isBoundarySimplification_of_isMainSuccession`.  The invertibility in (iii) is not part of the Lean
normal crossings predicate and is proved (`Subscheme.isInvertibleIdeal_of_hasOnlyNormalCrossings`). -/
@[blueprint "cor:0.3-boundary-simplification"
  (statement := /-- \textbf{Corollary 3.} Let $X$ be the same as in main theorem II (a non-singular algebraic scheme).
    Let $W$ be an algebraic subscheme of $X$ which is nowhere dense in $X$. Then there exists a finite succession of
    monoidal transformations $f_i\colon X_{i+1}\to X_i$ with non-singular centers $D_i$, where $0\le i<r$ and $X_0=X$,
    such that: (i) $X_r$ is non-singular; (ii) if $\bar f_i$ denotes the composition of the $f_j$ for $0\le j<i$, $D_i$
    is contained in $\bar f_i^{-1}(W)$ for all $i$; and (iii) the associated reduced scheme
    $\operatorname{red}(\bar f_r^{-1}(W))$ of $\bar f_r^{-1}(W)$ is defined by an invertible sheaf of ideals on $X_r$
    and has only normal crossings. (p.~146.)
    Formalization note (encoding): $W$ is a closed subscheme (a coherent sheaf of ideals) and $\bar f_i^{-1}(W)$ its
    total transform; the statement is for algebraic schemes (p.~151). -/)
  (proof := /-- The paper calls Corollary~3 an ``immediate but important consequence of main theorem~II'' and prints
    no derivation. $W$ is a coherent sheaf of non-zero ideals
    (\cref{lem:0.3-nowhere-dense-nonzero}). Apply main theorem~II in the form II($N$) of Ch.~I~\S3 (\cref{thm:I.3-main-II}, whose (4) gives
    $J_r=\mathcal O_{X_r}$; the form of Ch.~0 would be iterated over $d$) to $J=W$ and $E=\emptyset$
    (reduced, everywhere of codimension one and with only normal crossings, vacuously), and read (i)--(iii) off its
    properties (1)--(4) (\cref{lem:0.3-boundary-simplification-main-II}). If $X$ is empty, $r=0$.
    \textbf{Gap in the paper filled.} No derivation is printed; the invertibility in (iii) is
    \cref{lem:0.3-normal-crossings-invertible}. -/)
  (proofUses := ["thm:I.3-main-II", "lem:0.3-nowhere-dense-nonzero", "lem:0.3-boundary-simplification-main-II",
    "lem:0.3-normal-crossings-invertible"])
  (latexEnv := "corollary")]
theorem exists_isBoundarySimplification_of_isNonsingular [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) (W : Subscheme X) (hW : IsNowhereDense W.pts) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), Y.IsNonsingular ∧ s.IsBoundarySimplification W :=
  exists_isBoundarySimplification_of_stalkIdeal_ne_bot X hX W (Subscheme.stalkIdeal_ne_bot_of_isNowhereDense hW)

/-- **Corollary 3 of Main Theorem II**, printed form (p. 146): `X` a non-singular algebraic `B`-scheme, `B` a field of
characteristic zero, i.e. a scheme with a morphism `p` of finite type to `Spec B` (not necessarily separated: the
statement is more general than the printed one). -/
theorem exists_isBoundarySimplification [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType p] [QuasiCompact p] (hX : X.IsNonsingular)
    (W : Subscheme X) (hW : IsNowhereDense W.pts) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), Y.IsNonsingular ∧ s.IsBoundarySimplification W := by
  have := IsAlgebraicScheme.of_field p
  exact exists_isBoundarySimplification_of_isNonsingular X hX W hW

end MainTheorem.Ch0

/-! ### The last sentence of Corollary 3: the singular locus contained in `W` -/

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X}

/-- p. 167: off the center a monoidal transformation does not change the local rings, so `X'` is simple at `y` when
`X` is simple at `f(y) ∉ B` (`bijective_stalkMap_of_notMem_pts`). -/
theorem isSimpleAt_of_isSimpleAt_of_notMem_pts (t : MonoidalTransformation X B) {y : t.X'}
    (hy : t.f y ∉ B.pts) (h : X.IsSimpleAt (t.f y)) : t.X'.IsSimpleAt y := by
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := h
  exact IsRegularLocalRing.of_ringEquiv
    (RingEquiv.ofBijective (t.f.stalkMap y).hom (t.bijective_stalkMap_of_notMem_pts y hy))

/-- The inverse image of a set with empty interior by a monoidal transformation has empty interior: off the exceptional
subscheme `f` is an open embedding (p. 167, `isIso_morphismRestrict_complOpens`), and the exceptional subscheme, defined
by an invertible sheaf of ideals, has empty interior (`interior_pts_exceptional`). -/
theorem interior_preimage_eq_empty (t : MonoidalTransformation X B) [IsAlgebraicScheme t.X'] {S : Set X}
    (hS : interior S = ∅) : interior (t.f.base ⁻¹' S) = ∅ := by
  have := t.isIso_morphismRestrict_complOpens
  have hopen : IsOpenImmersion ((t.f ⁻¹ᵁ complOpens B).ι ≫ t.f) := by
    rw [← morphismRestrict_ι t.f (complOpens B)]
    infer_instance
  set g := (t.f ⁻¹ᵁ complOpens B).ι ≫ t.f with hg
  set O := interior (t.f.base ⁻¹' S) with hO
  have himg : g.base '' ((t.f ⁻¹ᵁ complOpens B).ι.base ⁻¹' O) ⊆ interior S := by
    refine interior_maximal ?_ (g.isOpenEmbedding.isOpenMap _
      (isOpen_interior.preimage (t.f ⁻¹ᵁ complOpens B).ι.base.hom.continuous))
    rintro _ ⟨w, hw, rfl⟩
    have := interior_subset hw
    simpa [hg] using this
  rw [hS, Set.subset_empty_iff, Set.image_eq_empty] at himg
  have hOE : O ⊆ t.exceptional.pts := by
    intro y hy
    rw [pts_exceptional]
    by_contra hyB
    obtain ⟨w, hw⟩ : y ∈ Set.range (t.f ⁻¹ᵁ complOpens B).ι.base := by
      rw [Scheme.Opens.range_ι]
      exact hyB
    have hmem : w ∈ (t.f ⁻¹ᵁ complOpens B).ι.base ⁻¹' O := show _ ∈ O from hw ▸ hy
    rw [himg] at hmem
    exact hmem
  have := t.interior_pts_exceptional
  exact Set.subset_empty_iff.mp (this ▸ interior_maximal hOE isOpen_interior)

end MonoidalTransformation

namespace MonoidalSuccession

variable {X Y : Scheme.{u}}

/-- The inverse image of a set with empty interior by a succession of monoidal transformations of an algebraic scheme
has empty interior (`MonoidalTransformation.interior_preimage_eq_empty` at every step). -/
theorem interior_preimage_composite_eq_empty [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme X] (s : MonoidalSuccession X Y) {S : Set X}
    (hS : interior S = ∅) : interior (s.composite.base ⁻¹' S) = ∅ := by
  revert ‹IsAlgebraicScheme X›
  induction s with
  | nil X =>
    intro _
    simpa using hS
  | cons B t rest ih =>
    intro _
    have := t.isAlgebraicScheme
    rw [composite_cons, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    exact ih (t.interior_preimage_eq_empty hS)

/-- The last scheme of a succession with the strong form of Main Theorem I is non-singular. -/
theorem isNonsingular_of_isStrongResolution (s : MonoidalSuccession X Y) (hs : s.IsStrongResolution) :
    Y.IsNonsingular := by
  induction s with
  | nil X => exact hs
  | cons B t rest ih => exact ih hs.2.2.2

/-- The centers of a succession with the strong form of Main Theorem I (pp. 132–133) are non-singular and lie in the
total transforms of every subscheme `W` containing the singular locus of `X`: a center `D_i` contains no simple point
of `X_i` by (b), and a point of `X_{i+1}` over a simple point of `X_i` off `D_i` is simple (p. 167), so the singular
locus of `X_i` lies over that of `X`.

Gap filled: the paper passes over this in "In view of main theorem I in the strong form" (p. 146). -/
@[blueprint "lem:0.3-strong-form-centers-in-boundary"
  (statement := /-- Let $\{f_i\colon X_{i+1}\to X_i\}_{0\le i<r}$ be a succession of monoidal transformations with the
    properties (a) and (b) of main theorem I in the strong form (\cref{thm:0.3-main-I-strong}), and $W$ a subscheme of
    $X=X_0$ containing the singular locus of $X$. Then every center $D_i$ is non-singular and contained in
    $\bar f_i^{-1}(W)$.
    \textbf{Gap in the paper filled.} Used without comment in the last sentence of Corollary~3 (p.~146). -/)
  (proof := /-- Induction on $r$, with the invariant: the singular locus of $X_i$ lies in $\bar f_i^{-1}(W)$. By (b)
    $D_i$ lies in the singular locus of $X_i$; it is non-singular, hence reduced, hence contained in $\bar f_i^{-1}(W)$.
    If $y\in X_{i+1}$ is a singular point, either $f_i(y)\in D_i$, or $\mathcal O_{X_i,f_i(y)}\cong\mathcal
    O_{X_{i+1},y}$ (\cref{compat:blowup-local-iso-stalk}) and $f_i(y)$ is singular; in both cases $f_i(y)\in\bar
    f_i^{-1}(W)$. -/)
  (proofUses := ["thm:0.3-main-I-strong", "compat:blowup-local-iso-stalk"])
  (latexEnv := "lemma")]
theorem hasNonsingularCentersIn_of_isStrongResolution (s : MonoidalSuccession X Y) (hs : s.IsStrongResolution)
    (W : Subscheme X) (hW : {x | ¬ X.IsSimpleAt x} ⊆ W.pts) : s.HasNonsingularCentersIn W := by
  induction s with
  | nil X => trivial
  | cons B t rest ih =>
    obtain ⟨hB, hb, -, hrest⟩ := hs
    have hBW : B.pts ⊆ W.pts := fun x hx => hW (hb x hx)
    refine ⟨hB, Subscheme.isContainedIn_of_pts_subset (Subscheme.isReduced_of_isNonsingular hB) hBW,
      ih hrest _ fun y hy => ?_⟩
    rw [Subscheme.pts_totalTransform_eq_preimage]
    change t.f y ∈ W.pts
    by_cases hyB : t.f y ∈ B.pts
    · exact hBW hyB
    · exact hW fun h => hy (t.isSimpleAt_of_isSimpleAt_of_notMem_pts hyB h)

end MonoidalSuccession

namespace MainTheorem.Ch0

/-- **Corollary 3, last sentence** (p. 146): "In view of main theorem I in the strong form, this assumption of
Corollary 2 may be replaced, without affecting the conclusion, by the weaker one that singular locus of `X` is contained
in `W`."  For a reduced algebraic scheme `X` and a nowhere dense subscheme `W` containing the singular locus of `X`, the
conclusions (i)–(iii) of Corollary 3 hold.

Formalization notes: "Corollary 2" is a slip for Corollary 3 (the assumption replaced, "`X` is non-singular", is that of
Corollary 3).  The hypothesis that `X` is reduced is tacit in the paper: main theorem I in the strong form, on which the
sentence rests, is stated for reduced `X` (p. 132).  (Under the other hypotheses `X` is reduced at the generic points of
its irreducible components: a non-reduced generic point is a singular point, and its closure, a component, would lie in
the nowhere dense `W`; so the added hypothesis excludes only embedded non-reduced points.)

Gap filled: the sentence is not argued further.  Proof: the strong form (`I_strong_of_isAlgebraicScheme`) gives a succession
with non-singular centers containing no simple points, ending at a non-singular `X_m`; its centers lie in the total
transforms of `W` (`MonoidalSuccession.hasNonsingularCentersIn_of_isStrongResolution`); the total transform of `W` on
`X_m` is nowhere dense (`MonoidalSuccession.interior_preimage_composite_eq_empty`); Corollary 3 for `X_m`
(`exists_isBoundarySimplification_of_isNonsingular`); concatenation (`MonoidalSuccession.append`). -/
@[blueprint "cor:0.3-boundary-simplification-singular"
  (statement := /-- Let $X$ be a reduced algebraic scheme and $W$ an algebraic subscheme of $X$ which is nowhere dense in
    $X$ and contains the singular locus of $X$. Then the conclusions (i)--(iii) of Corollary~3
    (\cref{cor:0.3-boundary-simplification}) hold. (p.~146: ``In view of main theorem I in the strong form, this
    assumption of Corollary 2 may be replaced, without affecting the conclusion, by the weaker one that singular locus
    of $X$ is contained in $W$.'')
    \textbf{Deviation from the paper (statement modified).} ``Corollary 2'' is a slip for Corollary~3. The hypothesis
    that $X$ is reduced is tacit in the paper (main theorem I in the strong form, on which the sentence rests, is for
    reduced $X$, p.~132) and is added. -/)
  (proof := /-- By main theorem I in the strong form (\cref{thm:0.3-main-I-strong}) there is a succession
    $X_m\to\cdots\to X_0=X$ with non-singular centers containing no simple points and $X_m$ non-singular. Its centers
    are contained in the total transforms of $W$ (\cref{lem:0.3-strong-form-centers-in-boundary}). The total transform
    of $W$ on $X_m$ is nowhere dense: off the exceptional subscheme a monoidal transformation is an open embedding
    (\cref{compat:blowup-local-iso-open}), and the exceptional subscheme, being defined by an invertible sheaf of
    ideals, has no interior point. Apply Corollary~3 (\cref{cor:0.3-boundary-simplification}) to $X_m$ and the total
    transform of $W$, and concatenate the two successions.
    \textbf{Gap in the paper filled.} The sentence is not argued further. -/)
  (proofUses := ["thm:0.3-main-I-strong", "lem:0.3-strong-form-centers-in-boundary", "compat:blowup-local-iso-open",
    "cor:0.3-boundary-simplification"])
  (latexEnv := "corollary")]
theorem exists_isBoundarySimplification_of_singularLocus_subset [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X]
    [AlgebraicGeometry.IsReduced X] (W : Subscheme X) (hW : IsNowhereDense W.pts)
    (hsing : {x | ¬ X.IsSimpleAt x} ⊆ W.pts) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), Y.IsNonsingular ∧ s.IsBoundarySimplification W := by
  obtain ⟨X₁, s₁, hs₁⟩ := I_strong_of_isAlgebraicScheme X
  have := s₁.isAlgebraicScheme_target
  have hW₁ : IsNowhereDense (s₁.totalTransform W).pts := by
    have hcl : IsClosed (s₁.totalTransform W).pts := (s₁.totalTransform W).support.isClosed
    refine hcl.isNowhereDense_iff.mpr ?_
    rw [MonoidalSuccession.totalTransform, Subscheme.pts_totalTransform_eq_preimage]
    exact s₁.interior_preimage_composite_eq_empty (W.support.isClosed.isNowhereDense_iff.mp hW)
  obtain ⟨Y, s₂, hY, hs₂⟩ := exists_isBoundarySimplification_of_isNonsingular X₁
    (s₁.isNonsingular_of_isStrongResolution hs₁) _ hW₁
  exact ⟨Y, s₁.append s₂, hY, MonoidalSuccession.isBoundarySimplification_append s₁ s₂ W
    (s₁.hasNonsingularCentersIn_of_isStrongResolution hs₁ W hsing) hs₂⟩

/-- **Corollary 3, last sentence**, printed form (p. 146): `X` a reduced algebraic `B`-scheme (not necessarily
separated: the statement is more general than the printed one), `B` a field of characteristic zero, whose singular locus
is contained in the nowhere dense subscheme `W`. -/
theorem exists_isBoundarySimplification_of_singularLocus_subset_of_field [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType p] [QuasiCompact p]
    [AlgebraicGeometry.IsReduced X] (W : Subscheme X) (hW : IsNowhereDense W.pts)
    (hsing : {x | ¬ X.IsSimpleAt x} ⊆ W.pts) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), Y.IsNonsingular ∧ s.IsBoundarySimplification W := by
  have := IsAlgebraicScheme.of_field p
  exact exists_isBoundarySimplification_of_singularLocus_subset X W hW hsing

end MainTheorem.Ch0

end Hironaka
