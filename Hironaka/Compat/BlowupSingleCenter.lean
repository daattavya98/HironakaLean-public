/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Compat.BlowupComposition
public import Hironaka.Compat.BlowupCompositionMain

/-!
# Ch. 0 §3 (pp. 132–133): a finite succession of monoidal transformations is a single monoidal
transformation

p. 132 (end): "One can see that, in general, a morphism obtained by a finite succession of
monoidal transformations can be also obtained by a single monoidal transformation with suitably
chosen center."

The paper sketches the two-step case on p. 133: with `f₀ : X₁ → X₀` (center `D₀`, ideal `J₀`)
and `f₁ : X₂ → X₁` (center `D₁`, ideal `J₁`), "for a sufficiently large integer m there exists a
coherent sheaf of ideals J(m) on X0 such that f0^-1(J(m)) = f0^-1(J0)^m J1"
(`MonoidalTransformation.exists_totalTransform_map_eq`, `Compat/BlowupCompositionMain`), and the
monoidal transformation of `X₀` with center `D'` defined by `J(m) J₀` is `f₀ ∘ f₁` up to a unique
isomorphism (`MonoidalTransformation.comp`, `MonoidalTransformation.existsUnique_iso_comp`,
`Compat/BlowupComposition`).  The general case is left to the reader; it is the induction on the
length of the succession done here.

This file adds
* (P5) the points of the center: `D'.pts = D₀.pts ∪ f₀(D₁.pts)`
  (`MonoidalTransformation.pts_map_exceptional_pow_mul_mul`);
* (P6) `MonoidalSuccession.centerPts` (the union of the images in `X₀` of all the centers), the
  identity monoidal transformation with empty center (`MonoidalTransformation.id`), and the
  theorem `MonoidalSuccession.exists_monoidalTransformation` (with its algebraic-scheme form).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

namespace MonoidalTransformation

variable {X : Scheme.{u}} {D₀ : Subscheme X}

/-- The identity of `X` is a monoidal transformation of `X` with the empty center (p. 168: "B may
be the empty subscheme of X"; by `isIso_of_empty` every such transformation is an
isomorphism). -/
def id (X : Scheme.{u}) : MonoidalTransformation X Subscheme.empty where
  X' := X
  f := 𝟙 X
  invertible := by
    rw [Subscheme.totalTransform_id]
    exact Subscheme.isInvertibleIdeal_empty
  universal _X'' f' _ := ⟨f', Category.comp_id f', fun h hh => (Category.comp_id h).symm.trans hh⟩

/-- The blown-up scheme of `MonoidalTransformation.id X` is `X`. -/
@[simp] theorem id_X' (X : Scheme.{u}) : (MonoidalTransformation.id X).X' = X := rfl

/-- The morphism of `MonoidalTransformation.id X` is `𝟙 X`. -/
@[simp] theorem id_f (X : Scheme.{u}) : (MonoidalTransformation.id X).f = 𝟙 X := rfl

/-- The points of the exceptional subscheme `f⁻¹(B)` are the preimage of the points of `B`. -/
theorem pts_exceptional {B : Subscheme X} (t : MonoidalTransformation X B) :
    t.exceptional.pts = t.f ⁻¹' B.pts := by
  change ((B.comap t.f).support : Set t.X') = _
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- (P5) The points of the center `D'` of p. 133.  Let `f₀ : X₁ → X₀` be a monoidal
transformation of the locally noetherian scheme `X₀` with center `D₀`, `E = f₀⁻¹(D₀)` its
exceptional subscheme, `D₁` a subscheme of `X₁`, and `J(m) := (Eᵐ J₁).map f₀` (the sheaf of ideals
of `exists_totalTransform_map_eq`).  Then the subscheme `D'` defined by `J(m) J₀` has the points
`D₀ ∪ f₀(D₁)`, for every `m`.

Proof: `J(m)` has support the closure of `f₀(supp(Eᵐ J₁))`, which is closed because `f₀` is proper,
hence a closed map (`MonoidalTransformation.isProper`); and
`D₁ ⊆ supp(Eᵐ J₁) ⊆ f₀⁻¹(D₀) ∪ D₁`, while `f₀(f₀⁻¹(D₀)) ⊆ D₀`. -/
theorem pts_map_exceptional_pow_mul_mul [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [IsLocallyNoetherian X]
    (t₀ : MonoidalTransformation X D₀) (D₁ : Subscheme t₀.X') (m : ℕ) :
    Subscheme.pts ((t₀.exceptional ^ m * D₁).map t₀.f * D₀) = D₀.pts ∪ t₀.f '' D₁.pts := by
  have := t₀.isProper
  have hcl : IsClosedMap t₀.f := t₀.f.isClosedMap
  -- the points of `Eᵐ`: empty for `m = 0`, those of `E` otherwise
  have hE : ((t₀.exceptional ^ m).support : Set t₀.X') ⊆ t₀.f ⁻¹' D₀.pts := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [pow_zero]
      exact fun x hx => absurd hx (by simp [show (1 : Subscheme t₀.X') = ⊤ from rfl])
    · rw [Scheme.IdealSheafData.support_pow _ _ hm.ne']
      exact (t₀.pts_exceptional).le
  change (((t₀.exceptional ^ m * D₁).map t₀.f * D₀).support : Set X) = _
  rw [Scheme.IdealSheafData.support_mul, Scheme.IdealSheafData.support_map, Closeds.coe_sup,
    Closeds.coe_closure, (hcl _ (t₀.exceptional ^ m * D₁).support.isClosed).closure_eq,
    Scheme.IdealSheafData.support_mul, Closeds.coe_sup]
  ext x
  simp only [Set.mem_union, Set.mem_image]
  constructor
  · rintro (⟨y, hy | hy, rfl⟩ | hx)
    · exact Or.inl (hE hy)
    · exact Or.inr ⟨y, hy, rfl⟩
    · exact Or.inl hx
  · rintro (hx | ⟨y, hy, rfl⟩)
    · exact Or.inr hx
    · exact Or.inl ⟨y, Or.inr hy, rfl⟩

end MonoidalTransformation

namespace MonoidalSuccession

/-- The points of `X = X₀` lying under some center of a succession: for
`{fᵢ : Xᵢ₊₁ → Xᵢ}` with centers `Bᵢ`, the union of the images `(f₀ ∘ ⋯ ∘ fᵢ₋₁)(Bᵢ)`.  It is
the point set of the single center of `exists_monoidalTransformation`. -/
def centerPts : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Set X
  | _, _, nil _ => ∅
  | _, _, cons B t rest => B.pts ∪ t.f '' rest.centerPts

/-- The empty succession has no centers. -/
@[simp] theorem centerPts_nil (X : Scheme.{u}) : (nil X).centerPts = ∅ := rfl

/-- `centerPts` of `cons B t rest` is `B ∪ t.f(rest.centerPts)`. -/
@[simp] theorem centerPts_cons {X Y : Scheme.{u}} (B : Subscheme X)
    (t : MonoidalTransformation X B) (rest : MonoidalSuccession t.X' Y) :
    (cons B t rest).centerPts = B.pts ∪ t.f '' rest.centerPts := rfl

/-- p. 132: "One can see that, in general, a morphism obtained by a finite succession of
monoidal transformations can be also obtained by a single monoidal transformation with suitably
chosen center."  For a noetherian scheme `X` (every algebraic scheme is,
`IsAlgebraicScheme.isNoetherian`) and a succession `s : X_r → ⋯ → X₀ = X`, there are a subscheme
`D` of `X`, a monoidal transformation `t : X' → X` with center `D` and an isomorphism
`e : X_r ≅ X'` with `t.f ∘ e = s.composite`; moreover the points of `D` are the images in `X` of
the points of the centers (`centerPts`).

Asserted without proof in the paper (gap filled); the two-step case is sketched on p. 133 with
two further "we can see" steps, both proved (`exists_totalTransform_map_eq`,
`existsUnique_iso_comp`).  Proof by induction on the length (the paper's "in general"):
`X₁` is again noetherian, the induction hypothesis gives a single center `D₁` on `X₁` for the rest
of the succession, and the two-step case with `J(m) := (f₀⁻¹(D₀)ᵐ D₁).map f₀` gives the center
`D' = J(m) D₀`, with points `D₀ ∪ f₀(D₁)` (`pts_map_exceptional_pow_mul_mul`).  The empty
succession is the identity, the monoidal transformation with the empty center. -/
@[blueprint "prop:0.3-single-center"
  (statement := /-- Let $X$ be a noetherian scheme (e.g.\ an algebraic scheme) and
    $\{f_i\colon X_{i+1}\to X_i\}_{0\le i<r}$, $X_0=X$, a finite succession of monoidal
    transformations with centers $B_i\subseteq X_i$. Then there exist a subscheme $D$ of $X$ and
    a monoidal transformation $f'\colon X'\to X$ with center $D$, together with an isomorphism
    $e\colon X_r\to X'$ such that $f'\circ e=f_0\circ\cdots\circ f_{r-1}$. Moreover the points of
    $D$ are the points $\bigcup_i (f_0\circ\cdots\circ f_{i-1})(B_i)$. (p.~132: ``One can see
    that, in general, a morphism obtained by a finite succession of monoidal transformations can
    be also obtained by a single monoidal transformation with suitably chosen center.'') -/)
  (proof := /-- Induction on $r$. For $r=0$ take $D=\emptyset$: the identity of $X$ is the
    monoidal transformation with empty center. For $r>0$, $X_1$ is again noetherian ($f_0$ is
    proper, \cref{lem:monoidal-transformation-proper}, hence of finite type and quasi-compact),
    so by induction the succession $X_r\to\cdots\to X_1$ is, up to an isomorphism $e_1$ over
    $X_1$, a single monoidal transformation $f_1$ of $X_1$ with a center $D_1$ whose points are
    $\bigcup_{i\ge1}(f_1\circ\cdots\circ f_{i-1})(B_i)$. Let $J_0$, $J_1$ be the ideals of
    $D_0=B_0$ and $D_1$, and $E=f_0^{-1}(J_0)$. This is the situation of p.~133. By
    \cref{lem:0.2-composition-ideal} there is $m$ with $f_0^{-1}(J(m))=E^mJ_1$ for
    $J(m)=f_{0*}$-image of $E^mJ_1$. The two-step case (p.~133: ``We can then easily see that if
    $f'\colon X'\to X_0$ is the monoidal transformation of $X_0$ with center $D'$, there exists a
    unique isomorphism $h\colon X'\to X_2$ such that $f'=f_0\circ f_1\circ h$'') holds for every
    $J$ with $f_0^{-1}(J)=E^mJ_1$: $(f_0f_1)^{-1}(JJ_0)=f_1^{-1}(E)^{m+1}f_1^{-1}(J_1)$ is
    invertible, and a morphism $g$ with $g^{-1}(JJ_0)$ invertible has $g^{-1}(J_0)$ invertible, so
    factors as $g=f_0g_1$, and then $g_1^{-1}(J_1)$ is invertible, so $g_1=f_1h$; hence
    $f_0\circ f_1$ is itself a monoidal transformation with center $D'$ defined by $J(m)J_0$, and
    every other one is isomorphic to it by a unique isomorphism over $X_0$
    (\cref{lem:monoidal-transformation-unique}). Take $D=D'$ and $e=e_1$. The points of $D'$ are
    $D_0\cup\overline{f_0(\operatorname{supp}E^mJ_1)}=D_0\cup f_0(D_1)$, since $f_0$ is a closed
    map, $D_1\subseteq\operatorname{supp}E^mJ_1\subseteq f_0^{-1}(D_0)\cup D_1$ and
    $f_0(f_0^{-1}(D_0))\subseteq D_0$.
    \textbf{Gap in the paper filled.} The paper asserts the statement (``One can see'') and, for
    two steps, the existence of $J(m)$ (``we can see'') and the isomorphism (``we can then easily
    see''), all without proof or citation; the induction on $r$ is not written out. -/)
  (proofUses := ["lem:0.2-composition-ideal", "lem:monoidal-transformation-proper",
    "lem:monoidal-transformation-unique", "def:succession"])
  (latexEnv := "proposition")]
theorem exists_monoidalTransformation [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {X Y : Scheme.{u}} [IsNoetherian X]
    (s : MonoidalSuccession X Y) :
    ∃ (D : Subscheme X) (t : MonoidalTransformation X D) (e : Y ≅ t.X'),
      e.hom ≫ t.f = s.composite ∧ D.pts = s.centerPts := by
  revert ‹IsNoetherian X›
  induction s with
  | nil X =>
    intro _
    refine ⟨Subscheme.empty, MonoidalTransformation.id X, Iso.refl X, Category.id_comp _, ?_⟩
    change ((⊤ : Subscheme X).support : Set X) = ∅
    rw [Scheme.IdealSheafData.support_top]
    rfl
  | cons B t rest ih =>
    intro _
    have := t.isProper
    have : IsLocallyNoetherian t.X' := LocallyOfFiniteType.isLocallyNoetherian t.f
    have : CompactSpace t.X' := QuasiCompact.compactSpace_of_compactSpace t.f
    have : IsNoetherian t.X' := ⟨⟩
    obtain ⟨D₁, t₁, e₁, he₁, hD₁⟩ := ih
    obtain ⟨m, hm⟩ := t.exists_totalTransform_map_eq D₁
    refine ⟨_, t.comp t₁ (hm m le_rfl), e₁, ?_, ?_⟩
    · change e₁.hom ≫ t₁.f ≫ t.f = rest.composite ≫ t.f
      rw [← Category.assoc, he₁]
    · rw [t.pts_map_exceptional_pow_mul_mul D₁ m, hD₁, centerPts_cons]

/-- `exists_monoidalTransformation` for an algebraic scheme `X` (the setting of p. 132), which is
noetherian by `IsAlgebraicScheme.isNoetherian`. -/
theorem exists_monoidalTransformation_of_isAlgebraicScheme [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {X Y : Scheme.{u}}
    [IsAlgebraicScheme X] (s : MonoidalSuccession X Y) :
    ∃ (D : Subscheme X) (t : MonoidalTransformation X D) (e : Y ≅ t.X'),
      e.hom ≫ t.f = s.composite ∧ D.pts = s.centerPts := by
  have := IsAlgebraicScheme.isNoetherian X
  exact s.exists_monoidalTransformation

end MonoidalSuccession

end Hironaka
