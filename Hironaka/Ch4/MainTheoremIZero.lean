/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Architect
public import Hironaka.Compat.ResolutionBookkeeping
public import Hironaka.Compat.MainISystem
public import Hironaka.Compat.CompletionEmbedding
public import Hironaka.Ch4.MainIAmbientDatum
public import Hironaka.Ch4.MainTheoremI
public import Hironaka.Statements

/-!
# Main Theorem I in the strong form and Main Theorem I* (Ch. 0 §3-§4, pp. 132-133, 138)

> We can prove the main theorem I in the strong form as follows: The morphism `f` is obtained by a finite succession of
> monoidal transformations `f_i : X_{i+1} → X_i`, where `0 ≦ i < r`, `X = X₀` and `X̃ = X_r`, which satisfy the following
> conditions: (a) The center of `f_i`, say `D_i`, is non-singular, and (b) `D_i` does not contain any simple point of `X_i`
> for `0 ≦ i < r`.  (p. 132)

> Finally, according to our proof of main theorem I in the strong form, we may impose (and in fact we do) the following
> condition on the monoidal transformations `f_i` in addition to the above (a) and (b): (c) `X_i` is normally flat along
> `D_i` for all `i`, `0 ≦ i < r`.  (p. 133)

> MAIN THEOREM I*. Let `X` be an algebraic `B`-scheme with a field `B` of characteristic zero. Then there exists a finite
> succession of monoidal transformations `{f_i : X_{i+1} → X_i}` with centers `D_i` in `X_i` `(0 ≦ i < r)`, where `X = X₀`,
> such that (a) `D_i` is non-singular; (b) every point of `D_i` is either a multiple point of `red(X_i)`, or such that `X_i`
> is not normally flat along `red(X_i)` at the point; (c) `X_i` is normally flat along `D_i`, for all `i`; and (d) `red(X_r)`
> is non-singular, and `X_r` is normally flat along `red(X_r)`.  (p. 138)

The paper derives neither: p. 112 says that main theorem I* "includes main theorem I in the strong form under the
conditions (a), (b), and (c)", and that "the finest form of the resolution of singularities that we can prove in this work
can be found in main theorem I(n)"; p. 138 calls I* "obviously stronger" than the strong form; p. 151: "main theorems I,
I*, II, stated in the preceding sections, remain verified if the field B is replaced by any local ring belonging to a
certain class of local rings, which we shall specify in the beginning paragraph of Chapter I, and denote by 𝔅".

Contents:
* the predicates `MonoidalSuccession.IsStrongResolution` and `IsMainIStar` for (a), (b), (c) and the last scheme;
* both statements are the case `V₀ = X` (the subscheme `⊥`), `β = 0`, of Main Theorem I(n) (`MainTheorem.I_all`), with
  `W = X` (reduced) for the strong form and `W = red(X)` for I*: condition (2) of I(n), "`B_i` does not contain any
  simple point of `W(i)` at which all the `V_j(i)` (here only `V₀(i) = X_i`) are normally flat along `W(i)`", is (b);
  (3) is (c); (4) is the non-singularity of `X_r` resp. (d); the one unprinted identification is `W(i) = red(X_i)`
  (`MonoidalSuccession.strictTransform_red_bot`, Compat/ResolutionBookkeeping);
* for every algebraic scheme (p. 151), then for an algebraic `B`-scheme with `B` a field of characteristic zero as printed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

/-! ### The scheme itself as a subscheme -/

section Bot

variable {X : Scheme.{u}}

/-- `X` is non-singular as soon as the subscheme `⊥ = X` is. -/
theorem Subscheme.isNonsingular_of_isNonsingular_bot (h : (⊥ : Subscheme X).IsNonsingular) :
    X.IsNonsingular := fun x => by
  have hx : x ∈ (⊥ : Subscheme X).pts :=
    Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr (by rw [Subscheme.stalkIdeal_bot_eq]; exact bot_ne_top)
  have := Subscheme.isRegular_stalk_quot _ h hx
  rw [Subscheme.stalkIdeal_bot_eq] at this
  exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot (X.presheaf.stalk x))

/-- The subscheme `⊥ = X` of a reduced scheme is reduced. -/
theorem Subscheme.isReduced_bot_of_isReduced [AlgebraicGeometry.IsReduced X] : (⊥ : Subscheme X).IsReduced :=
  isReduced_of_isOpenImmersion (⊥ : Subscheme X).ι

/-- The subscheme `⊥ = X` has the dimension of `X`. -/
theorem Subscheme.dim_bot : (⊥ : Subscheme X).dim = X.dim :=
  dim_eq_of_iso (asIso (⊥ : Subscheme X).ι)

/-- `red(X)` has the dimension of `X` (the reduction is a homeomorphism). -/
theorem Subscheme.dim_red_bot : (Subscheme.red (⊥ : Subscheme X)).dim = X.dim := by
  refine dim_eq_of_surjective_closedImmersion (Subscheme.red (⊥ : Subscheme X)).ι ?_
  intro x
  have : x ∈ Set.range (Subscheme.red (⊥ : Subscheme X)).ι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    change x ∈ ((⊥ : Scheme.IdealSheafData X).support : Set X)
    rw [Scheme.IdealSheafData.support_bot]
    trivial
  exact this

end Bot

/-! ### The predicates -/

namespace MonoidalSuccession



end MonoidalSuccession

/-! ### From Main Theorem I(n) with `V₀ = X`, `β = 0` -/

section Unwinding

/-- The system `(V₀) = (⊥)`: all members are `⊥`. -/
theorem mainSystem_elim0_eq_bot {X : Scheme.{u}} (j : Fin (0 + 1)) :
    mainSystem (X := X) (Fin.elim0 : Fin 0 → Subscheme X) j = ⊥ := by
  refine Fin.cases ?_ (fun i => i.elim0) j
  rfl

/-- Main Theorem I(n) for `V₀ = X`, `β = 0`, `W = X` is the strong form of Main Theorem I (pp. 132-133): (1) is (a),
(2) is (b) (a scheme is normally flat along itself at its simple points), (3) is (c), (4) is the non-singularity of
`X_r`.  Induction on the succession; the data stay `V_j(i) = ⊥`, `W(i) = ⊥` (`strictTransform_bot`). -/
theorem MonoidalSuccession.isStrongResolution_of_isMainI [Hironaka.HironakaCitedResults.{u}] {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) :
    IsAlgebraicScheme X → ∀ (V : Fin (0 + 1) → Subscheme X) (W : Subscheme X), (∀ j, V j = ⊥) → W = ⊥ →
      s.IsMain123 V W → s.IsMain4 V W → s.IsStrongResolution := by
  induction s with
  | nil X =>
    intro _ V W _ hW _ h4
    subst hW
    exact Subscheme.isNonsingular_of_isNonsingular_bot h4.1
  | cons B t rest ih =>
    intro hX V W hV hW h123 h4
    subst hW
    obtain ⟨⟨⟨hB, -⟩, h2, h3⟩, hrest⟩ := h123
    have := t.isAlgebraicScheme
    refine ⟨hB.isNonsingular, ?_, ?_, ?_⟩
    · intro x hx hsimple
      refine h2 x hx ⟨Subscheme.isSimpleAt_bot_of_isSimpleAt hsimple, fun j => ?_⟩
      rw [hV j]
      exact Subscheme.isNormallyFlatAlongAt'_bot_of_isSimpleAt hsimple
        (Subscheme.isSimpleAt_bot_of_isSimpleAt hsimple)
    · intro x hx
      have := (h3 x hx).1 0
      rwa [hV 0] at this
    · refine ih inferInstance (fun j => Subscheme.strictTransform t (V j))
        (Subscheme.strictTransform t ⊥) (fun j => ?_)
        (MonoidalTransformation.strictTransform_bot t) hrest h4
      rw [hV j]
      exact MonoidalTransformation.strictTransform_bot t

/-- Main Theorem I(n) for `V₀ = X`, `β = 0`, `W = red(X)` is Main Theorem I* (p. 138): the strict transform of
`red(X)` is `red(X_i)` (`strictTransform_red_bot`), so (2) is (b), (3) is (c), (4) is (d). -/
theorem MonoidalSuccession.isMainIStar_of_isMainI [Hironaka.HironakaCitedResults.{u}] {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) :
    IsAlgebraicScheme X → ∀ (V : Fin (0 + 1) → Subscheme X) (W : Subscheme X), (∀ j, V j = ⊥) →
      W = Subscheme.red (⊥ : Subscheme X) → s.IsMain123 V W → s.IsMain4 V W → s.IsMainIStar := by
  induction s with
  | nil X =>
    intro _ V W hV hW _ h4
    subst hW
    refine ⟨h4.1, fun x hx => ?_⟩
    have h : Subscheme.IsNormallyFlatAlongAt' (V 0) (Subscheme.red (⊥ : Subscheme X)) x := h4.2 0 x hx
    rwa [hV 0] at h
  | cons B t rest ih =>
    intro hX V W hV hW h123 h4
    subst hW
    obtain ⟨⟨⟨hB, -⟩, h2, h3⟩, hrest⟩ := h123
    have := t.isAlgebraicScheme
    refine ⟨hB.isNonsingular, ?_, ?_, ?_⟩
    · intro x hx
      by_cases hsimple : (Subscheme.red (⊥ : Subscheme _)).IsSimpleAt x
      · right
        intro hnf
        exact h2 x hx ⟨hsimple, fun j => by rw [hV j]; exact hnf⟩
      · exact Or.inl hsimple
    · intro x hx
      have := (h3 x hx).1 0
      rwa [hV 0] at this
    · refine ih inferInstance (fun j => Subscheme.strictTransform t (V j))
        (Subscheme.strictTransform t (Subscheme.red ⊥)) (fun j => ?_)
        (MonoidalTransformation.strictTransform_red_bot t) hrest h4
      rw [hV j]
      exact MonoidalTransformation.strictTransform_bot t

end Unwinding

/-! ### The statements -/

namespace MainTheorem.Ch0

/-- **Main Theorem I in the strong form** (pp. 132-133), for every algebraic scheme (p. 151).

Formalization notes (encoding): the succession `{f_i : X_{i+1} → X_i}` is a `MonoidalSuccession X Y` with
`Y = X_r = X̃`; the conditions (a), (b), (c) and the non-singularity of `X̃` are `MonoidalSuccession.IsStrongResolution`;
"`X_i` is normally flat along `D_i`" is `IsNormallyFlatAlongAt' ⊥ D_i` (`X_i` is the subscheme `⊥` of itself).  The link
"the morphism `f` is obtained by" with the single center `D` of Main Theorem I is the unproved "we can see" of p. 133
and is not formalized here.

Deviation from the paper (gap filled): the paper announces this ("We can prove the main theorem I in the strong form as
follows") and derives it nowhere; it is Main Theorem I(n) (`MainTheorem.I_all`) for `V₀ = X`, `β = 0`, `W = X` (reduced):
(1) gives (a), (2) gives (b) because a scheme is normally flat along itself at its simple points, (3) gives (c), and
(4) gives the non-singularity of `X_r`.  The dimension `n = dim X` of `W` is a natural number
(`IsAlgebraicScheme.exists_nat_dim_eq`, p. 163, stated without proof in the paper); the empty scheme is trivial. -/
@[blueprint "thm:0.3-main-I-strong"
  (statement := /-- Let $X$ be a reduced algebraic scheme. Then there exists a finite succession of monoidal
    transformations $f_i\colon X_{i+1}\to X_i$, $0\le i<r$, $X=X_0$, such that (a) the center $D_i$ of $f_i$ is
    non-singular, (b) $D_i$ does not contain any simple point of $X_i$ for $0\le i<r$, (c) $X_i$ is normally flat along
    $D_i$ for all $i$, $0\le i<r$, and $\tilde X=X_r$ is non-singular. (Main theorem I in the strong form,
    pp.~132--133; valid over any base ring of the class $\mathfrak B$ by p.~151.) -/)
  (proof := /-- Apply Main Theorem I($n$) (\cref{thm:I.3-main-I}) with $V_0=X$ (the scheme itself), $\beta=0$ and
    $W=X$, a reduced subscheme of dimension $n=\dim X$ (\cref{lem:I.0-dimension-finite}). Then $W(i)=X_i$ and
    $V_0(i)=X_i$ for all $i$ (a scheme is its own strict transform), so (1) is (a); (2) says that $B_i$ contains no
    simple point of $X_i$ at which $X_i$ is normally flat along $X_i$, and $X_i$ is normally flat along itself at its
    simple points, so (2) is (b); (3) gives (c); and (4) says that $X_r$ is non-singular.
    \textbf{Gap in the paper filled.} The paper does not derive the strong form. -/)
  (proofUses := ["thm:I.3-main-I", "lem:I.0-dimension-finite"])
  (latexEnv := "theorem")]
theorem I_strong_of_isAlgebraicScheme [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X]
    [AlgebraicGeometry.IsReduced X] :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsStrongResolution := by
  by_cases hne : Nonempty X
  · obtain ⟨n, hn⟩ := IsAlgebraicScheme.exists_nat_dim_eq X
    obtain ⟨Y, s, hs⟩ := MainTheorem.I_all.{u} n X 0 Fin.elim0 ⊥ Subscheme.isReduced_bot_of_isReduced
      (by rw [Subscheme.dim_bot, hn]) (fun j => j.elim0)
    exact ⟨Y, s, MonoidalSuccession.isStrongResolution_of_isMainI s inferInstance _ _
      mainSystem_elim0_eq_bot rfl hs.1 hs.2⟩
  · exact ⟨X, MonoidalSuccession.nil X, fun x => (hne ⟨x⟩).elim⟩

/-- **Main Theorem I in the strong form**, as printed (pp. 132–133): `X` an algebraic `B`-scheme (not necessarily
separated: the statement is more general than the printed one), `B` a field of characteristic zero, reduced and
irreducible.  (A field of characteristic zero belongs to `𝔅`, `(a)` of p. 161, so this is
`I_strong_of_isAlgebraicScheme`, the form valid for every `B ∈ 𝔅` by p. 151; the irreducibility is not used.) -/
theorem I_strong [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p] [QuasiCompact p] [AlgebraicGeometry.IsReduced X] [IrreducibleSpace X] :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsStrongResolution :=
  haveI := IsAlgebraicScheme.of_field p
  I_strong_of_isAlgebraicScheme X

/-- **Main Theorem I\*** (p. 138), for every algebraic scheme (p. 151).

Formalization notes (encoding): as for `I_strong_of_isAlgebraicScheme`; `red(X_i)` is `Subscheme.red ⊥`, the nilradical
subscheme of `X_i`; "multiple point of `red(X_i)`" is `¬ Subscheme.IsSimpleAt`; the condition (b) is read with `X_i`:
the printed "`X_r` is not normally flat along `red(X_i)`" is a misprint (`red(X_i)` is a subscheme of `X_i`, not of `X_r`;
cf. (D*), p. 137, and (2) of I(n), p. 174).

Deviation from the paper (gap filled): the paper calls I* "obviously stronger" than the strong form and derives it
nowhere; it is Main Theorem I(n) (`MainTheorem.I_all`) for `V₀ = X`, `β = 0`, `W = red(X)` (reduced, of dimension
`dim X`): (2) of I(n) says that `B_i` contains no simple point of `W(i)` at which `V₀(i) = X_i` is normally flat along
`W(i)`, which is (b) once `W(i) = red(X_i)`; this identification (the strict transform of `red(X_i)` by `f_i` is
`red(X_{i+1})`, `MonoidalTransformation.strictTransform_red_bot`) is not printed; (3) is (c), (4) is (d). -/
@[blueprint "thm:0.4-main-I-star"
  (statement := /-- Let $X$ be an algebraic scheme. Then there exists a finite succession of monoidal transformations
    $\{f_i\colon X_{i+1}\to X_i\}$ with centers $D_i$ in $X_i$ $(0\le i<r)$, $X=X_0$, such that (a) $D_i$ is
    non-singular; (b) every point of $D_i$ is either a multiple point of $\operatorname{red}(X_i)$, or such that $X_i$ is
    not normally flat along $\operatorname{red}(X_i)$ at the point; (c) $X_i$ is normally flat along $D_i$, for all $i$;
    and (d) $\operatorname{red}(X_r)$ is non-singular, and $X_r$ is normally flat along $\operatorname{red}(X_r)$.
    (Main theorem I*, p.~138; valid over any base ring of the class $\mathfrak B$ by p.~151.
    Formalization note: the printed ``$X_r$'' in (b) is a misprint for $X_i$.) -/)
  (proof := /-- Apply Main Theorem I($n$) (\cref{thm:I.3-main-I}) with $V_0=X$, $\beta=0$ and $W=\operatorname{red}(X)$,
    a reduced subscheme of dimension $n=\dim X$ (\cref{lem:I.0-dimension-finite}). The strict transform of
    $\operatorname{red}(X_i)$ by $f_i$ is $\operatorname{red}(X_{i+1})$ ($X_{i+1}$ is the scheme-theoretic closure of the
    complement of the exceptional divisor, where $f_i$ is a local isomorphism), so $W(i)=\operatorname{red}(X_i)$ and
    $V_0(i)=X_i$; then (1) is (a), (2) is (b), (3) is (c) and (4) is (d).
    \textbf{Gap in the paper filled.} The paper does not derive I*, and the identification
    $W(i)=\operatorname{red}(X_i)$ is invisible there. -/)
  (proofUses := ["thm:I.3-main-I", "lem:I.0-dimension-finite"])
  (latexEnv := "theorem")]
theorem IStar_of_isAlgebraicScheme [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X] :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainIStar := by
  by_cases hne : Nonempty X
  · obtain ⟨n, hn⟩ := IsAlgebraicScheme.exists_nat_dim_eq X
    obtain ⟨Y, s, hs⟩ := MainTheorem.I_all.{u} n X 0 Fin.elim0 (Subscheme.red ⊥)
      (Subscheme.isReduced_red _) (by rw [Subscheme.dim_red_bot, hn]) (fun j => j.elim0)
    exact ⟨Y, s, MonoidalSuccession.isMainIStar_of_isMainI s inferInstance _ _ mainSystem_elim0_eq_bot
      rfl hs.1 hs.2⟩
  · exact ⟨X, MonoidalSuccession.nil X, fun x => (hne ⟨(Subscheme.red (⊥ : Subscheme X)).ι x⟩).elim,
      fun x _ => (hne ⟨x⟩).elim⟩

/-- **Main Theorem I\***, as printed (p. 138): `X` an algebraic `B`-scheme (not necessarily separated: the statement is
more general than the printed one), `B` a field of characteristic zero. -/
theorem IStar [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p] [QuasiCompact p] :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainIStar :=
  haveI := IsAlgebraicScheme.of_field p
  IStar_of_isAlgebraicScheme X

end MainTheorem.Ch0

end Hironaka
