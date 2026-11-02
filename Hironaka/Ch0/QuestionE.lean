/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Architect
public import Hironaka.Ch0.FactStar
public import Hironaka.Ch0.RationalApplication
public import Hironaka.Ch4.MainTheoremIICorollaries
public import Hironaka.Compat.BlowupPreimageDense
public import Hironaka.Compat.CompletionEmbedding
public import Hironaka.Compat.LocalizeSuccession
public import Hironaka.Compat.NowhereDenseCenters
public import Hironaka.Compat.PrimitiveWeakTransform
public import Hironaka.Compat.ResolutionBookkeeping
public import Hironaka.Statements

/-!
# Ch. 0 §5 (pp. 139–144): the elimination of points of indeterminacy, Question (E)

> **Question (E).**  Let `f : X → Y` be any rational application as above.  We assume that `X` is non-singular and that
> `f` is proper.  Let `S₀` be any quasi-compact (resp. compact) subset of the underlying topological space of `X`.  We
> then ask if there exists a finite succession of monoidal transformations `h_i : X_{i+1} → X_i` with centers `D_i` in
> `X_i`, where `0 ≦ i < r` and `X₀ = X`, such that if `S_{i+1} = h_i⁻¹(S_i)` for all `i`, then
> (i) `D_i` is irreducible and has no multiple points within a neighborhood of `S_i` in `X_i`;
> (ii) if `f_i` denotes the composition of `f` and those `h_j` with `j < i`, every point of `D_i` is a point of
> indeterminacy of `f_i`, and
> (iii) the domain of the definition of `f_r` contains `S_r`.  (p. 140)

> For the case of algebraic `B`-schemes, it suffices (and it is most interesting) to ask the question in which `S₀`
> contains all the points of `X` so that (iii) asserts that `f_r` is a morphism.  (p. 140)

> In this paper, we shall find the affirmative answer to the question (E), at least for the case in which `X` and `Y` are
> algebraic `B`-schemes, where `B` is a field of characteristic zero.  …  The sense of the trivialization will be made
> precise, and we shall see that it is a corollary to the main theorem II.  (p. 140)

The answer (`question_E`) follows the printed route: fact (*) (p. 141; `exists_finite_system_domain_precomp_eq`, a cited
leaf) turns the elimination of points of indeterminacy into the trivialization of a finite system of sheaves of ideals,
and Corollary 1 of Main Theorem II (p. 143; `MainTheorem.Ch0.exists_isTrivializing_of_isAlgebraicScheme`) trivializes it.
The steps which the paper leaves out are in this file:
* the system of (*) is replaced by the system `J_i = G_i J_i⁰` of its primitive parts
  (`Subscheme.exists_isInvertibleIdeal_mul_isPrimitive`, proved: used tacitly by the paper);
* along the succession of Corollary 1, `f_i⁻¹(J) = P_i · J_i(i)` with `P_i` invertible and `J_i(i)` the weak transform,
  which stays primitive (`Subscheme.isPrimitive_weakTransform`, proved: used tacitly by the paper), so the sheaves `J'` of (*) are the weak
  transforms, and the domain of `f_i` is the set where some weak transform is trivial;
* (ii) follows from (1) of Corollary 1: `ν(J_j(i)_y) > 0` at the points `y` of `D(i)`; (iii) from (2).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Hironaka

namespace RationalApplication

end RationalApplication

/-! ### The centers of a succession -/

namespace MonoidalSuccession

/-- Every center of the succession is a non-singular irreducible subscheme, or empty (the agreement of p. 163). -/
def HasCenters : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, _, nil _ => True
  | _, _, cons B _ rest => B.IsCenter ∧ rest.HasCenters

variable {X Y : Scheme.{u}}

theorem HasCenters.hasNonsingularCenters {s : MonoidalSuccession X Y} (h : s.HasCenters) :
    s.HasNonsingularCenters := by
  induction s with
  | nil X => trivial
  | cons B t rest ih => exact ⟨h.1.isNonsingular, ih h.2⟩

theorem hasCenters_of_isTrivializingSteps {e : ℕ} (s : MonoidalSuccession X Y) :
    ∀ J : Fin e → Subscheme X, s.IsTrivializingSteps J → s.HasCenters := by
  induction s with
  | nil X => intro _ _; trivial
  | cons B t rest ih => intro J h; exact ⟨h.1, ih _ h.2.2⟩

end MonoidalSuccession

namespace RationalApplication

variable {X Y : Scheme.{u}}


/-- The conclusion of (*) for a system `J` of sheaves of ideals on `X`, as a predicate (the statement of
`exists_finite_system_domain_precomp_eq` after the choice of `d` and `J`). -/
def StarProperty {B : Type u} [Field B] [CharZero B] (pX : X ⟶ Spec (CommRingCat.of B)) (f : X ⤏ Y) {d : ℕ}
    (J : Fin d → Subscheme X) : Prop :=
  ∀ (X' : Scheme.{u}) (pX' : X' ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType pX'] [QuasiCompact pX']
    [IsSeparated pX'] (_ : X'.IsNonsingular) (h : X' ⟶ X) (_ : h ≫ pX = pX') (hh : h.PreimageDense)
    (P J' : Fin d → Subscheme X'),
    (∀ i, (P i).IsInvertibleIdeal ∧ (∀ x, (J' i).stalkIdeal x ≠ ⊥) ∧ Subscheme.IsPrimitive (J' i) ∧
      ∀ x, (Subscheme.totalTransform h (J i)).stalkIdeal x = (P i).stalkIdeal x * (J' i).stalkIdeal x) →
    ((f.precomp h hh).domain : Set X') = {x | ∃ i, (J' i).stalkIdeal x = ⊤}

section Stages

variable {B : Type u} [Field B] [CharZero B] {pX : X ⟶ Spec (CommRingCat.of B)} {f : X ⤏ Y} {d : ℕ}
  {J : Fin d → Subscheme X}

/-- At a stage `a : X₀ ⟶ X` of the succession, with `a⁻¹(J_i) = P_i · J_c(i)`, `P_i` invertible and `J_c(i)` not divisible by
any invertible sheaf of ideals, (*) gives the domain of definition of `f_i = f ∘ a` as the set where some `J_c(i)` is
trivial (the sheaves `J'ᵢ` of (*) are the `J_c(i)`). -/
theorem domain_precomp_eq_of_stage (hstar : StarProperty pX f J) {X₀ : Scheme.{u}}
    (pX₀ : X₀ ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType pX₀] [QuasiCompact pX₀] [IsSeparated pX₀]
    (hX₀ : X₀.IsNonsingular) (a : X₀ ⟶ X) (hpa : a ≫ pX = pX₀) (ha : a.PreimageDense)
    (Jc : Fin d → Subscheme X₀) (hnz : ∀ i x, (Jc i).stalkIdeal x ≠ ⊥) (hprim : ∀ i, Subscheme.IsPrimitive (Jc i))
    (hdec : ∀ i, ∃ P : Subscheme X₀, P.IsInvertibleIdeal ∧
      ∀ x, (Subscheme.totalTransform a (J i)).stalkIdeal x = P.stalkIdeal x * (Jc i).stalkIdeal x) :
    ((f.precomp a ha).domain : Set X₀) = {x | ∃ i, (Jc i).stalkIdeal x = ⊤} :=
  hstar X₀ pX₀ hX₀ a hpa ha (fun i => (hdec i).choose) Jc
    fun i => ⟨(hdec i).choose_spec.1, hnz i, hprim i, (hdec i).choose_spec.2⟩

/-- **The induction along the succession of Corollary 1** (the translation of p. 140): if `a⁻¹(J_i) = P_i · J_c(i)` with `P_i`
invertible and `J_c(i)` non-zero and not divisible by any invertible sheaf of ideals, and the weak transforms `J_c(i)` along
`s` satisfy (1) and (2) of Corollary 1, then `s` eliminates the points of indeterminacy of `f`.  At each step the points of
the center are points of indeterminacy by (*) and (1) (`ν > 0`), and at the end the domain of `f_r` is everything by (*)
and (2). -/
theorem eliminates_of_isTrivializing [Hironaka.HironakaCitedResultsCh0.{u}] (hstar : StarProperty pX f J) :
    ∀ {X₀ X₁ : Scheme.{u}} (s : MonoidalSuccession X₀ X₁)
      (pX₀ : X₀ ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType pX₀] [QuasiCompact pX₀] [IsSeparated pX₀]
      (_ : X₀.IsNonsingular) (a : X₀ ⟶ X) (_ : a ≫ pX = pX₀) (ha : a.PreimageDense)
      (Jc : Fin d → Subscheme X₀) (_ : ∀ i x, (Jc i).stalkIdeal x ≠ ⊥) (_ : ∀ i, Subscheme.IsPrimitive (Jc i))
      (_ : ∀ i, ∃ P : Subscheme X₀, P.IsInvertibleIdeal ∧
        ∀ x, (Subscheme.totalTransform a (J i)).stalkIdeal x = P.stalkIdeal x * (Jc i).stalkIdeal x)
      (_ : s.IsTrivializingSteps Jc)
      (_ : ∀ x : X₁, ∃ j, (s.weakTransformFamily Jc j).stalkIdeal x = ⊤) (S : Set X₀),
      EliminatesIndeterminacy f a ha S s := by
  intro X₀ X₁ s
  induction s with
  | nil X₀ =>
    intro pX₀ _ _ _ hX₀ a hpa ha Jc hnz hprim hdec _ hfin S
    have hdom := domain_precomp_eq_of_stage hstar pX₀ hX₀ a hpa ha Jc hnz hprim hdec
    refine EliminatesIndeterminacy.nil a ha S fun x _ => ?_
    obtain ⟨j, hj⟩ := hfin x
    have hx : x ∈ ((f.precomp a ha).domain : Set X₀) := by
      rw [hdom]
      exact ⟨j, hj⟩
    exact hx
  | @cons X₀ D t Y₁ rest ih =>
    intro pX₀ _ _ _ hX₀ a hpa ha Jc hnz hprim hdec hs hfin S
    obtain ⟨hD, hnu, hrestS⟩ := hs
    have hdom := domain_precomp_eq_of_stage hstar pX₀ hX₀ a hpa ha Jc hnz hprim hdec
    have hAlg : IsAlgebraicScheme X₀ := IsAlgebraicScheme.of_field pX₀
    have := IsAlgebraicScheme.isNoetherian X₀
    have := t.isProper
    have : LocallyOfFiniteType (t.f ≫ pX₀) := inferInstance
    have : QuasiCompact (t.f ≫ pX₀) := inferInstance
    have : IsSeparated (t.f ≫ pX₀) := inferInstance
    have hAlg' : IsAlgebraicScheme t.X' := IsAlgebraicScheme.of_field (t.f ≫ pX₀)
    have ha' : (t.f ≫ a).PreimageDense := Scheme.Hom.PreimageDense.comp t.preimageDense_f ha
    have hX₁ : t.X'.IsNonsingular :=
      (t.isNonsingular_and_isNonsingular_exceptional hX₀ hD.isNonsingular).1
    refine EliminatesIndeterminacy.cons a ha S D t rest (hD.imp id And.right)
      ⟨⊤, fun _ _ => trivial, fun y hy _ => Subscheme.isSimpleAt_of_isNonsingular hD.isNonsingular hy⟩
      ?_ ha' ?_
    · intro y hy hmem
      have hmem' : y ∈ ((f.precomp a ha).domain : Set X₀) := hmem
      rw [hdom] at hmem'
      obtain ⟨i, hi⟩ := hmem'
      obtain ⟨c, hc, hcy⟩ := hnu i
      have h0 := hcy y hy
      rw [hi, Ideal.nu_top_eq_zero] at h0
      exact (Nat.pos_iff_ne_zero.mp hc) (by exact_mod_cast h0.symm)
    · refine ih (t.f ≫ pX₀) hX₁ (t.f ≫ a) (by rw [Category.assoc, hpa]) ha'
        (fun i => Subscheme.weakTransform t (Jc i)) (fun i y => ?_) (fun i => ?_) (fun i => ?_) hrestS hfin
        (t.f ⁻¹' S)
      · exact Subscheme.stalkIdeal_weakTransform_ne_bot hX₀ t (hnz i) y
      · exact Subscheme.isPrimitive_weakTransform hX₀ hD t (hnz i) (hprim i)
      · obtain ⟨P, hP, hPe⟩ := hdec i
        obtain ⟨Q, hQ, hQe⟩ :=
          Subscheme.exists_totalTransform_eq_weakTransform_mul hX₀ hD t (Jc i) (hnz i)
        refine ⟨Subscheme.totalTransform t.f P * Q, (t.isInvertibleIdeal_totalTransform hP).mul hQ,
          fun y => ?_⟩
        have e1 : (Subscheme.totalTransform t.f (Subscheme.totalTransform a (J i))).stalkIdeal y =
            (Subscheme.totalTransform t.f P).stalkIdeal y *
              (Subscheme.totalTransform t.f (Jc i)).stalkIdeal y := by
          rw [stalkIdeal_totalTransform t.f _ y, hPe (t.f y), Ideal.map_mul,
            ← stalkIdeal_totalTransform t.f P y, ← stalkIdeal_totalTransform t.f (Jc i) y]
        rw [Subscheme.totalTransform_comp, e1, hQe, Subscheme.stalkIdeal_mul_eq, Subscheme.stalkIdeal_mul_eq]
        ring

end Stages

/-- The succession of Question (E) together with the information that every center is non-singular irreducible (or
empty): the proof of `question_E`. -/
theorem exists_eliminates_and_hasCenters [Hironaka.HironakaCitedResultsCh0.{u}] {B : Type u} [Field B] [CharZero B] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (CommRingCat.of B)) (pY : Y ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType pX] [QuasiCompact pX] [IsSeparated pX]
    [LocallyOfFiniteType pY] [QuasiCompact pY] [IsSeparated pY]
    (hX : X.IsNonsingular) (f : X ⤏ Y) (hf : f.IsProperApplication pX pY) (S₀ : Set X) :
    ∃ (Xr : Scheme.{u}) (s : MonoidalSuccession X Xr),
      EliminatesIndeterminacy f (𝟙 X) (Scheme.Hom.PreimageDense.id X) S₀ s ∧ s.HasCenters := by
  obtain ⟨d, J, hJ, hstar⟩ := exists_finite_system_domain_precomp_eq pX pY hX f hf
  have hAlg : IsAlgebraicScheme X := IsAlgebraicScheme.of_field pX
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- no sheaf of ideals: the domain of `f` is empty, so `X` is empty
    have hdom := domain_precomp_eq_of_stage hstar pX hX (𝟙 X) (Category.id_comp _)
      (Scheme.Hom.PreimageDense.id X) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
      (fun i => i.elim0)
    have hX0 : IsEmpty X := by
      by_contra hne
      rw [not_isEmpty_iff] at hne
      have hd := (f.precomp (𝟙 X) (Scheme.Hom.PreimageDense.id X)).dense_domain.nonempty
      obtain ⟨x, hx⟩ := hd
      have hx' : x ∈ (((f.precomp (𝟙 X) (Scheme.Hom.PreimageDense.id X)).domain : X.Opens) : Set X) :=
        hx
      rw [hdom] at hx'
      obtain ⟨i, -⟩ := hx'
      exact i.elim0
    exact ⟨X, .nil X, EliminatesIndeterminacy.nil _ _ _ fun x _ => (hX0.false x).elim, trivial⟩
  · choose G K₀ hG hK₀ hK₀nz hGK using fun i =>
      Subscheme.exists_isInvertibleIdeal_mul_isPrimitive hX (J i) (hJ i)
    obtain ⟨Xr, s, hs⟩ :=
      MainTheorem.Ch0.exists_isTrivializing_of_isAlgebraicScheme X hX hd K₀ hK₀nz
    refine ⟨Xr, s, eliminates_of_isTrivializing hstar s pX hX (𝟙 X) (Category.id_comp _)
      (Scheme.Hom.PreimageDense.id X) K₀ hK₀nz hK₀ (fun i => ⟨G i, hG i, fun x => ?_⟩) hs.1 hs.2 S₀,
      MonoidalSuccession.hasCenters_of_isTrivializingSteps s K₀ hs.1⟩
    rw [Subscheme.totalTransform_id, hGK i, Subscheme.stalkIdeal_mul_eq]

/-- **Question (E), answered (p. 140)** for a non-singular algebraic `B`-scheme `X`, `B` a field of characteristic zero, and
a proper rational application `f` of `X` to an algebraic `B`-scheme `Y`: there is a finite succession of monoidal
transformations `h_i : X_{i+1} → X_i` with centers `D_i` such that, with `S_{i+1} = h_i⁻¹(S_i)`, (i) `D_i` is irreducible
and has no multiple points near `S_i`, (ii) every point of `D_i` is a point of indeterminacy of `f_i`, (iii) the domain of
definition of `f_r` contains `S_r`.

Encoding: `B`-schemes are separated (p. 118: "If the diagonal of `X ×_S X` is a closed subscheme, then the `S`-prescheme
`(X, p)` is called an `S`-scheme").

Deviation from the paper (stronger statement): `S₀` is any subset of `X`, not only a quasi-compact one; the printed case is
the special case.

Deviation from the paper (gap filled): "the following corollary of main theorem II is sufficient" (p. 143): the passage
from Corollary 1 to (E) is not printed.  It uses (*) for the decomposition `f_i⁻¹(J_j) = P · J_j(i)`, the facts that every
sheaf of non-zero ideals on a non-singular scheme is an invertible sheaf of ideals times a primitive one and that weak
transforms of primitive ones are primitive (proved in `PrimitiveIdeal.lean`, `PrimitiveWeakTransform.lean`: used tacitly by the paper), and
the induction `eliminates_of_isTrivializing`.  The printed first step "replace `Y` by the graph of `f`" (p. 140) is not
needed, since (*) is stated for `f` itself. -/
@[blueprint "thm:0.5-question-E"
  (statement := /-- \textbf{Question (E), answered.} Let $f\colon X\dashrightarrow Y$ be a proper rational application
    of a non-singular algebraic $\mathbf B$-scheme $X$ to an algebraic $\mathbf B$-scheme $Y$, $\mathbf B$ a field of
    characteristic zero, and $S_0$ a subset of $X$. Then there exists a finite succession of monoidal transformations
    $h_i\colon X_{i+1}\to X_i$ ($0\le i<r$, $X_0=X$) with centers $D_i$ in $X_i$ such that, with $S_{i+1}=h_i^{-1}(S_i)$:
    (i) $D_i$ is irreducible and has no multiple points within a neighbourhood of $S_i$ in $X_i$; (ii) if $f_i$ denotes the
    composition of $f$ and those $h_j$ with $j<i$, every point of $D_i$ is a point of indeterminacy of $f_i$; and
    (iii) the domain of the definition of $f_r$ contains $S_r$. (p.~140.) \textbf{Gap in the paper filled.} The paper
    says that Corollary~1 of Main Theorem~II is sufficient (p.~143); the passage is not printed. Formalization note
    (encoding): $\mathbf B$-schemes are separated (p.~118). Deviation (stronger statement): $S_0$ is any subset of $X$,
    where the paper takes a quasi-compact one. -/)
  (proof := /-- Apply (*) (\cref{thm:0.5-fact-star}) to $f$ and replace the system $(J_i)$ by its primitive parts $J_i^0$
    (\cref{lem:0.5-primitive-decomposition}). Corollary~1 (\cref{cor:0.3-trivialization}) gives a succession which trivializes
    $(J_i^0)$. Along it $f_i^{-1}(J_j)=P\cdot J_j^0(i)$ with $P$ invertible (\cref{thm:0.3-main-II}, the definition of the
    weak transform) and $J_j^0(i)$ the weak transform, primitive (\cref{lem:0.5-weak-transform-primitive}), so by (*) the domain of
    $f_i$ is the set where some $J^0_j(i)$ is trivial. A point $y$ of $D(i)$ has $\nu(J^0_j(i)_y)>0$ for all $j$ by (1), so
    it is a point of indeterminacy; at the end some $J^0_j(r)$ is trivial at each point by (2), so $f_r$ is defined
    everywhere. The centers are non-singular irreducible, so (i) holds. -/)
  (proofUses := ["thm:0.5-fact-star", "lem:0.5-primitive-decomposition", "lem:0.5-weak-transform-primitive",
    "cor:0.3-trivialization"])
  (latexEnv := "theorem")]
theorem question_E [Hironaka.HironakaCitedResultsCh0.{u}] {B : Type u} [Field B] [CharZero B] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (CommRingCat.of B)) (pY : Y ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType pX] [QuasiCompact pX] [IsSeparated pX]
    [LocallyOfFiniteType pY] [QuasiCompact pY] [IsSeparated pY]
    (hX : X.IsNonsingular) (f : X ⤏ Y) (hf : f.IsProperApplication pX pY) (S₀ : Set X) :
    ∃ (Xr : Scheme.{u}) (s : MonoidalSuccession X Xr),
      EliminatesIndeterminacy f (𝟙 X) (Scheme.Hom.PreimageDense.id X) S₀ s := by
  obtain ⟨Xr, s, h, -⟩ := exists_eliminates_and_hasCenters pX pY hX f hf S₀
  exact ⟨Xr, s, h⟩

/-! ### Consequences: nowhere dense centers, the composite, and a morphism -/

namespace EliminatesIndeterminacy

variable {f : X ⤏ Y}

/-- The centers are nowhere dense: every point of `D_i` is a point of indeterminacy, and the domain of `f_i` is dense, so
`D_i` contains no non-empty open set (this is why the compositions `f_i` of p. 139 exist). -/
theorem nowhereDenseCenters {X₀ X₁ : Scheme.{u}} {a : X₀ ⟶ X} {ha : a.PreimageDense} {S : Set X₀}
    {s : MonoidalSuccession X₀ X₁} (h : EliminatesIndeterminacy f a ha S s) : s.NowhereDenseCenters := by
  induction h with
  | nil => trivial
  | cons a ha S D t rest hirr hsimple hind ha' hrest ih =>
    refine ⟨?_, ih⟩
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨y, hyU, hyD⟩ := (f.precomp a ha).dense_domain.inter_open_nonempty (interior D.pts)
      isOpen_interior ⟨x, hx⟩
    exact hind y (interior_subset hyU) hyD

/-- At the end of the succession, the points over `S` lie in the domain of the composition `f ∘ (composite ≫ a)`. -/
theorem exists_mem_domain_composite {X₀ X₁ : Scheme.{u}} {a : X₀ ⟶ X} {ha : a.PreimageDense} {S : Set X₀}
    {s : MonoidalSuccession X₀ X₁} (h : EliminatesIndeterminacy f a ha S s) :
    ∃ hr : (s.composite ≫ a).PreimageDense,
      ∀ x ∈ s.composite ⁻¹' S, x ∈ (f.precomp (s.composite ≫ a) hr).domain := by
  induction h with
  | nil a ha S hS =>
    have e : (MonoidalSuccession.nil _).composite ≫ a = a := by simp
    refine ⟨by rw [e]; exact ha, fun x hx => ?_⟩
    rw [Scheme.RationalMap.precomp_congr f e _ ha]
    exact hS x hx
  | cons a ha S D t rest hirr hsimple hind ha' hrest ih =>
    obtain ⟨hr, hmem⟩ := ih
    have e : (MonoidalSuccession.cons D t rest).composite ≫ a = rest.composite ≫ (t.f ≫ a) := by
      simp
    refine ⟨by rw [e]; exact hr, fun x hx => ?_⟩
    rw [Scheme.RationalMap.precomp_congr f e _ hr]
    exact hmem x hx

end EliminatesIndeterminacy

/-- **Question (E) for an integral source, with the consequences used afterwards** (p. 140; pp. 144–145): for an integral
non-singular algebraic `B`-scheme `X` and a proper rational application `f` of `X` to a separated algebraic `B`-scheme `Y`,
there is a succession of monoidal transformations eliminating the points of indeterminacy of `f` on the whole of `X` such
that `X_r` is integral, every center is non-singular irreducible (or empty) and nowhere dense, the composite `h : X_r → X`
has dense preimages and `f ∘ h` is a morphism `φ : X_r → Y` over `B`.

Encoding: `B`-schemes are separated (p. 118: "If the diagonal of `X ×_S X` is a closed subscheme, then the `S`-prescheme
`(X, p)` is called an `S`-scheme"), so `Y` is a scheme and the morphism `φ` is unique (p. 139).

Deviation from the paper (gap filled): the sentence "so that (iii) asserts that `f_r` is a morphism" (p. 140) and the facts
that `X_r` is integral, the centers nowhere dense and `f ∘ h` over `B` are not argued. -/
@[blueprint "cor:0.5-question-E-integral"
  (statement := /-- In the situation of Question~(E) with $X$ integral, a succession of monoidal transformations
    eliminating the points of indeterminacy of $f$ on the whole of $X$ can be chosen with $X_r$ integral, all centers
    non-singular irreducible (or empty) and nowhere dense, and such that the composite $h\colon X_r\to X$ makes $f\circ h$ a
    morphism $X_r\to Y$ over $\mathbf B$ (``(iii) asserts that $f_r$ is a morphism'', p.~140). \textbf{Gap in the paper
    filled.} -/)
  (proof := /-- By \cref{thm:0.5-question-E} with $S_0=X$ the points of every center are points of indeterminacy, hence the
    centers are nowhere dense (the domain of $f_i$ is dense), so $X_r$ is integral; the domain of $f_r$ is $X_r$, so $f_r$ is a
    morphism ($X_r$ reduced, $Y$ separated), and over $\mathbf B$ because $f$ is. -/)
  (proofUses := ["thm:0.5-question-E"])
  (latexEnv := "corollary")]
theorem question_E_integral [Hironaka.HironakaCitedResultsCh0.{u}] {B : Type u} [Field B] [CharZero B] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (CommRingCat.of B)) (pY : Y ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType pX] [QuasiCompact pX] [IsSeparated pX]
    [LocallyOfFiniteType pY] [QuasiCompact pY] [IsSeparated pY] [IsIntegral X]
    (hX : X.IsNonsingular) (f : X ⤏ Y) (hf : f.IsProperApplication pX pY) :
    ∃ (Xr : Scheme.{u}) (s : MonoidalSuccession X Xr),
      EliminatesIndeterminacy f (𝟙 X) (Scheme.Hom.PreimageDense.id X) Set.univ s ∧ IsIntegral Xr ∧
      s.HasCenters ∧ s.NowhereDenseCenters ∧
      ∃ (hr : s.composite.PreimageDense) (φ : Xr ⟶ Y), φ ≫ pY = s.composite ≫ pX ∧
        φ.toRationalMap = f.precomp s.composite hr := by
  obtain ⟨Xr, s, hE, hC⟩ := exists_eliminates_and_hasCenters pX pY hX f hf Set.univ
  have hnd := hE.nowhereDenseCenters
  have hint : IsIntegral Xr := MonoidalSuccession.isIntegral_of_nowhereDenseCenters s hnd
  obtain ⟨hr', hmem⟩ := hE.exists_mem_domain_composite
  have hr : s.composite.PreimageDense := by simpa using hr'
  have hdom : (f.precomp s.composite hr).domain = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    have := hmem x (Set.mem_univ _)
    rwa [Scheme.RationalMap.precomp_congr f (Category.comp_id s.composite) hr' hr] at this
  have : Y.IsSeparated := by
    refine ⟨?_⟩
    rw [show terminal.from Y = pY ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance
  have hmor := Scheme.RationalMap.isMorphism_iff_domain_eq_top.mpr hdom
  refine ⟨Xr, s, hE, hint, hC, hnd, hr, hmor.toHom, ?_, hmor.toHom_toRationalMap⟩
  -- over the base: both sides define the same rational application of `Xr` to `Spec B`
  refine Scheme.RationalMap.eq_of_toRationalMap_eq ?_
  have h1 : (hmor.toHom ≫ pY).toRationalMap = (hmor.toHom.toRationalMap).compHom pY := by
    rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.Hom.toPartialMap_compHom]
  rw [h1, hmor.toHom_toRationalMap, ← Scheme.RationalMap.precomp_compHom, hf.compHom_eq,
    Scheme.RationalMap.precomp_toRationalMap_hom]

end RationalApplication

end Hironaka
