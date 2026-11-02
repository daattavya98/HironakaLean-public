/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Architect
public import Hironaka.Ch4.MainTheoremIIZero
public import Hironaka.Compat.ExtendSuccessionWeak
public import Hironaka.Compat.TrivializingSystem
public import Hironaka.Compat.WeakTransformProduct
public import Hironaka.Statements

/-!
# Ch. 0 §5 (pp. 143–146): Corollaries 1 and 3 of Main Theorem II

> **Corollary 1.**  Let `X` be a non-singular algebraic `B`-scheme with a field `B` of characteristic zero.  Let
> `(J₁, J₂, ⋯, J_e)` with `e ≧ 1` be a finite system of coherent sheaves of non-zero ideals on `X`.  Then there
> exists a finite succession of monoidal transformations `f_i : X(i + 1) → X(i)` with non-singular irreducible
> centers `D(i)`, where `0 ≦ i < r` and `X(0) = X`, which has the following property: If `J_j(i + 1)` denotes the
> weak transform of `J_j(i)` by `f_i`, where `1 ≦ j ≦ e`, `0 ≦ i < r`, and `J_j(0) = J_j`, then
> (1) `ν(J_j(i)_y)` is a positive constant for the points `y` of `D(i)`, for every pair `(i, j)`; and
> (2) for every point `x` of `X(r)`, we have `J_j(r)_x = O_{X(r),x}` for at least one `j`.  (p. 143)

> **Corollary 3.**  Let `X` be the same as in main theorem II.  Let `W` be an algebraic subscheme of `X` which is
> nowhere dense in `X`.  Then there exists a finite succession of monoidal transformations `f_i : X_{i+1} → X_i`
> with non-singular centers `D_i`, where `0 ≦ i < r` and `X₀ = X`, such that: (i) `X_r` is non-singular; (ii) if
> `f̄_i` denotes the composition of the `f_j` for `0 ≦ j < i`, `D_i` is contained in `f̄_i⁻¹(W)` for all `i`; and
> (iii) the associated reduced scheme `red(f̄_r⁻¹(W))` of `f̄_r⁻¹(W)` is defined by an invertible sheaf of ideals on
> `X_r` and has only normal crossings. …  (p. 146)

Corollary 1 (`MainTheorem.Ch0.exists_isTrivializing_of_isAlgebraicScheme`) is proved along the printed proof
(p. 144): the induction on the maximum `d` of `ν(∏_j J_j)` at the points where no `J_j` is trivial, the closed sets
`T`, `S`, `T − S`, Main Theorem II on `X − S` and the extension of the succession to `X`; the steps are in
`Hironaka/Compat/TrivializingSystem.lean` (every one of them is unprinted: gaps filled).  Corollary 3 is proved in `Hironaka/Ch4/MainTheoremIICorollary3.lean`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

/-! ### Corollary 1: the trivialization of a system of coherent sheaves of ideals -/

namespace MonoidalSuccession

variable {X Y : Scheme.{u}} {e : ℕ}


end MonoidalSuccession

namespace MainTheorem.Ch0

/-- **Corollary 1 of Main Theorem II** (p. 143), the trivialization of a system of coherent sheaves of ideals, for
an algebraic scheme.

Formalization notes (encoding): as for Main Theorem II (`exists_isMainIIZero_of_isAlgebraicScheme`) "a coherent sheaf
of non-zero ideals" is read as in Definition 3: every stalk `(J_j)_x` is a non-zero ideal; the system is
`J : Fin e → Subscheme X`; the hypothesis `1 ≤ e` is printed (and necessary for (2)); "a non-singular irreducible
subscheme" may be empty (the agreement of p. 163).  The statement is for algebraic schemes (p. 151); the printed
form (`B` a field of characteristic zero) is `exists_isTrivializing`.

Proof (pp. 143–144, printed as a sketch): the orders `ν((J_j)_x)` are bounded (`exists_forall_nu_stalkIdeal_le`), so
`ν((∏ J_j)_x) = ∑_j ν((J_j)_x)` is bounded, and the induction on that bound (`exists_isTrivializingSteps_of_le`)
gives the succession.

Deviation from the paper (gaps filled): "Then we can prove that `T`, `S` and `T − S` are all closed", "as is easily
seen", the extension `u_i` of the succession of `X − S` and the induction on `d` are not argued in the paper; see
`Hironaka/Compat/TrivializingSystem.lean`. -/
@[blueprint "cor:0.3-trivialization"
  (statement := /-- \textbf{Corollary 1.} Let $X$ be a non-singular algebraic scheme. Let
    $(J_1,J_2,\dots,J_e)$ with $e\ge1$ be a finite system of coherent sheaves of non-zero ideals on $X$. Then there
    exists a finite succession of monoidal transformations $f_i\colon X(i+1)\to X(i)$ with non-singular irreducible
    centers $D(i)$, where $0\le i<r$ and $X(0)=X$, which has the following property: If $J_j(i+1)$ denotes the weak
    transform of $J_j(i)$ by $f_i$, where $1\le j\le e$, $0\le i<r$, and $J_j(0)=J_j$, then
    (1) $\nu(J_j(i)_y)$ is a positive constant for the points $y$ of $D(i)$, for every pair $(i,j)$; and
    (2) for every point $x$ of $X(r)$, we have $J_j(r)_x=\mathcal O_{X(r),x}$ for at least one $j$. (p.~143.)
    Formalization note (encoding): the sheaves $J_j(i)$ are carried along the succession; a non-singular irreducible
    subscheme may be empty (the agreement of p.~163). -/)
  (proof := /-- As printed (p.~144), by induction on $d$, the maximum of $\nu((\prod_jJ_j)_x)$ for the points $x$
    at which no $J_j$ is trivial (it exists: the orders are bounded on the quasi-compact $X$; if there is no such
    point, $r=0$ will do; $d\ge e\ge1$ otherwise). Let $T=\{x\mid\nu((\prod_jJ_j)_x)\ge d\}$ and $S$ the set of
    the points of $T$ at which some $J_j$ is trivial. $T$ is closed (\cref{cor:III.thm2-1}); $T-S=T\cap\bigcap_j
    V(J_j)$ is closed; $S$ is closed: it is the intersection of $T$ with an open set and is stable under
    specialization, since $\nu((\prod_jJ_j)_x)=\sum_j\nu((J_j)_x)$ and at a specialization outside the open set
    the order would exceed $d$; in a noetherian sober space this makes $S$ the union of the irreducible pieces of $T$
    which meet the open set. On $\bar X=X-S$, $d$ is the maximum of $\nu(\prod_jJ_j)$; apply Main Theorem~II with
    the remark of p.~143 (\cref{thm:0.3-main-II}, \cref{rem:0.3-main-II}) to $\prod_jJ_j$ and $E_0=\emptyset$.
    Along the succession the weak transform of the product is the product of the weak transforms (Remark~2,
    \cref{rem:III.2-2}); on each center $\bar D(i)$ the sum $\sum_j\nu(J_j(i)_y)=d$ is constant and each term is
    upper semicontinuous, hence each term is constant; it is positive by the invariant ``where some $J_j(i)$ is
    trivial, $\nu(\prod_jJ_j(i))<d$'', which passes from $i$ to $i+1$ by (\textbf{B}$^*$) applied to each factor
    (\cref{thm:0.3-B-star}). By (\textbf{B}$^*$) the centers are mapped into $T-S$, so the succession extends to
    $X$ with open immersions $u_i$ (\cref{prop:IV.2-5-extension}; $u_i^{-1}$ of a weak transform is the weak
    transform), property (1) passes to the extension, and over $S$ the extended succession is a local isomorphism.
    At the end, at a point over $S$ some $J_j(r)$ is trivial, and at a point of $u_r(\bar X(r))$ either some
    $J_j(r)$ is trivial or $\nu(\prod_jJ_j(r))<d$ by (iv): $d$ is reduced, and one concludes by induction,
    concatenating the successions.
    \textbf{Gaps in the paper filled.} ``Then we can prove that $T$, $S$ and $T-S$ are all closed'', ``as is easily
    seen'' (the constancy and positivity in (1), the drop of $d$), the extension $u_i$ and the induction on $d$ are
    not argued. -/)
  (proofUses := ["thm:0.3-main-II", "rem:0.3-main-II", "thm:0.3-B-star", "prop:IV.2-5-extension",
    "cor:III.thm2-1", "rem:III.2-2"])
  (latexEnv := "corollary")]
theorem exists_isTrivializing_of_isAlgebraicScheme [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) {e : ℕ} (he : 1 ≤ e) (J : Fin e → Subscheme X)
    (hJ : ∀ j x, (J j).stalkIdeal x ≠ ⊥) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsTrivializing J := by
  choose n hn using fun k => Subscheme.exists_forall_nu_stalkIdeal_le hX (J k) (hJ k)
  obtain ⟨Y, s, h1, h2⟩ := exists_isTrivializingSteps_of_le he (∑ k, n k) X inferInstance hX J hJ
    fun x _ => by
      rw [Subscheme.nu_stalkIdeal_prod hX, Nat.cast_sum]
      exact Finset.sum_le_sum fun k _ => hn k x
  exact ⟨Y, s, h1, h2⟩

/-- **Corollary 1 of Main Theorem II**, printed form (p. 143): `X` a non-singular algebraic `B`-scheme, `B` a field of
characteristic zero, i.e. a scheme with a morphism `p` of finite type to `Spec B` (not necessarily separated: the
statement is more general than the printed one). -/
theorem exists_isTrivializing [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType p] [QuasiCompact p] (hX : X.IsNonsingular)
    {e : ℕ} (he : 1 ≤ e) (J : Fin e → Subscheme X) (hJ : ∀ j x, (J j).stalkIdeal x ≠ ⊥) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsTrivializing J := by
  have := IsAlgebraicScheme.of_field p
  exact exists_isTrivializing_of_isAlgebraicScheme X hX he J hJ

end MainTheorem.Ch0

end Hironaka
