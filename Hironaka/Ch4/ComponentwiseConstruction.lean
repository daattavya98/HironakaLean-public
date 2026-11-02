/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch4.ImplicationsAB
public import Hironaka.Statements

/-!
# Ch. IV §3: the componentwise construction (correction of [g], [h], pp. 298–299)

Lemma (AB.4) (p. 299) asserts that `B̂_s = c_s⁻¹(B_s)` is irreducible whenever `B_s` contains a
point satisfying the conditions (1), (2), (3).  This is false (an error of the paper, Lemma (AB.4) and condition [g], p. 299): `B̂_s` is non-singular, and its irreducible (= connected) components
correspond to the connected components of `B_s ∩ g_s⁻¹(x_0)`.  The paper proves the two
containments of the condition [g] (p. 298), `B̂_s ⊆ X̄_s` and `J̄(s) ⊆ P(B̄'_s)^b`, only at the
point `x̂` over `x`, hence (`lem:IV.AB-4-local`) on the component of `B̂_s` through `x̂`; whether
they hold on the other components is not known (a counterexample to the irreducibility is at
`lem:IV.AB-4-componentwise`).  Since [g] requires them
globally, the first assertion of the printed (AB.4), "`x ∈ X'_s`", and through it the printed proof of
Theorems A* and B* (p. 310), depend on that unproved claim.

This file formalizes the repair of this error (`def:IV.3-construction-componentwise`,
`lem:IV.AB-4-componentwise`): the condition [g] is
applied *componentwise* on the `X̂`-side.  A component `K` of `B̂_s` is *good* (relative to the
current open `X̂*'_s`) if `K ⊆ X̄_s` and `J̄(s) ⊆ P(B̄_s)^b` at the points of `X̄*'_s` over `K`;
the *bad locus* `Bad_s` is the union of the components that are not good (a closed subset of
`B̂_s`), and

* [f*] `X̂*'_0 = X̂_0`;
* [g*]/[h*] `X̂*'_{s+1} = f̂_s⁻¹(X̂*'_s − Bad_s)` and `X̄*'_{s+1} = X̂*'_{s+1} ∩ X̄_{s+1}`.

The paper's [g] and [h] are the cases `Bad_s = ∅` and `Bad_s = B̂_s`.  There is no `X'_s` on the
`X`-side: only `X̂*'_s` and `X̄*'_s` matter for the rest of §3.  `J̄(s)` is unchanged (it does not
depend on `X'_s`, `def:IV.3-construction`).

The repaired Lemma (AB.4) (`lem:IV.AB-4-componentwise`) then holds with the paper's own proof
(pp. 299–302): if `x` satisfies (1), (2), (3), the unique `x̂` over `x` lies in `X̂*'_s`, and if
moreover `x ∈ B_s`, every component of `B̂_s` through `x̂` is good, so `x̂ ∉ Bad_s`.  The only
change to the paper's argument is "the component through `x̂`" in place of "`B̂_s`".

The printed construction (`def:IV.3-construction`) is kept in `Hironaka.Ch4.ImplicationsAB`.  The
facts of pp. 297–298 on the open
subschemes `X̄*'_s` (non-singularity, etc.) are the generic construction facts
`lem:IV.3-construction-facts-generic` applied to the family `removalFamilyStar`.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory

namespace Hironaka

universe u

/-! ## Irreducible components of a subscheme: finiteness and closedness -/

/-- A subscheme of an algebraic scheme has only finitely many irreducible components (the
underlying space is noetherian).  (The same statement is `CD.finite_irreducibleComponents` in
`Hironaka.Ch4.ImplicationsCD`; it belongs in `Hironaka.Compat.ComponentStalk`.) -/
theorem Subscheme.finite_irreducibleComponents {X : Scheme.{u}} [IsAlgebraicScheme X]
    (D : Subscheme X) : D.irreducibleComponents.Finite := by
  have := IsAlgebraicScheme.noetherianSpace X
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible D.support.isClosed
  refine (hSf.image fun u => Subscheme.ofClosed ⟨closure u, isClosed_closure⟩).subset ?_
  rintro C ⟨Z, ⟨⟨hZirr, hZsub⟩, hZmax⟩, rfl⟩
  have hZS : (Z : Set X) ⊆ ⋃₀ S := by
    rw [← hSU]; exact hZsub
  obtain ⟨u, huS, hZu⟩ := (isIrreducible_iff_sUnion_isClosed.mp hZirr) hSf.toFinset
    (fun t ht => hSc t (hSf.mem_toFinset.mp ht))
    (by simpa using hZS)
  have huS' : u ∈ S := hSf.mem_toFinset.mp huS
  have hsub : u ⊆ D.pts := by
    show u ⊆ (D.support : Set X)
    rw [hSU]; exact Set.subset_sUnion_of_mem huS'
  have hle : (⟨u, hSc u huS'⟩ : TopologicalSpace.Closeds X) ≤ Z :=
    hZmax (y := ⟨u, hSc u huS'⟩) ⟨hSi u huS', hsub⟩ hZu
  refine ⟨u, huS', ?_⟩
  have : (⟨closure u, isClosed_closure⟩ : TopologicalSpace.Closeds X) = Z := by
    refine TopologicalSpace.Closeds.ext ?_
    show closure u = (Z : Set X)
    rw [(hSc u huS').closure_eq]
    exact Set.Subset.antisymm hle hZu
  show Subscheme.ofClosed ⟨closure u, isClosed_closure⟩ = Subscheme.ofClosed Z
  rw [this]

/-- The point set of an irreducible component is closed. -/
theorem Subscheme.isClosed_pts_of_mem_irreducibleComponents {X : Scheme.{u}}
    {D C : Subscheme X} (hC : C ∈ D.irreducibleComponents) : IsClosed C.pts := by
  obtain ⟨Z, -, rfl⟩ := hC
  rw [Subscheme.pts_ofClosed]
  exact Z.isClosed

/-- An irreducible component of `D` is contained in `D`. -/
theorem Subscheme.isContainedIn_of_mem_irreducibleComponents {X : Scheme.{u}}
    {D C : Subscheme X} (hC : C ∈ D.irreducibleComponents) : C.IsContainedIn D := by
  obtain ⟨Z, hZ, rfl⟩ := hC
  have hle : D ≤ Subscheme.ofClosed Z :=
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp hZ.1.2
  exact fun U => hle U

namespace AB

/-- The schemes `X̂_s` of the induced succession are algebraic: `X̂_0 = Spec(Ŝ)` is
(`lem:IV.3-xhat0-algebraic`), and monoidal transformations preserve algebraicity. -/
theorem Completion.isAlgebraicScheme_tHat_X [Hironaka.HironakaCitedResults.{u}] {X : Scheme.{u}} {T : Tower X} {x₀ : X}
    (𝒞 : Completion T x₀) (hX : IsAlgebraicScheme X) : ∀ s, IsAlgebraicScheme (𝒞.tHat.X s)
  | 0 => haveI := hX; isAlgebraicScheme_xHat0 X x₀
  | s + 1 => haveI := 𝒞.isAlgebraicScheme_tHat_X hX s
      (𝒞.tHat.monoidalTransformation s).isAlgebraicScheme

namespace Frame

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
  (𝒮 : Frame hS)

/-- The schemes `X̂_s` of the frame are algebraic. -/
theorem isAlgebraicScheme_tHat_X [Hironaka.HironakaCitedResults.{u}] (s : ℕ) : IsAlgebraicScheme (𝒮.tHat.X s) :=
  𝒮.toCompletion.isAlgebraicScheme_tHat_X hS.ambient.1 s

/-! ## Good components and the bad locus -/

/-- A subscheme `K` of `X̂_s` (an irreducible component of `B̂_s`) is *good* relative to an open
`U ⊆ X̂_s` if the two containments of the condition [g] (p. 298) hold on it: `K ⊆ X̄_s`, and
`J̄(s) ⊆ P(B̄_s)^b` at the points of `U ∩ X̄_s` lying over `K`. -/
def IsGoodComponent (s : ℕ) (U : (𝒮.tHat.X s).Opens) (K : Subscheme (𝒮.tHat.X s)) : Prop :=
  K.IsContainedIn (𝒮.xBar s) ∧
    ∀ xb : (𝒮.xBar s).toScheme, (𝒮.xBar s).ι.base xb ∈ U → (𝒮.xBar s).ι.base xb ∈ K.pts →
      (𝒮.jBar s).stalkIdeal xb ≤ ((𝒮.bBarOn s).stalkIdeal xb) ^ 𝒮.b

/-- The *bad locus* of `B̂_s` relative to an open `U ⊆ X̂_s`: the union of the irreducible
components of `B̂_s` that are not good. -/
def badLocus (s : ℕ) (U : (𝒮.tHat.X s).Opens) : Set (𝒮.tHat.X s) :=
  ⋃ K ∈ {K ∈ (𝒮.tHat.B s).irreducibleComponents | ¬ 𝒮.IsGoodComponent s U K}, K.pts

theorem mem_badLocus_iff (s : ℕ) (U : (𝒮.tHat.X s).Opens) (xh : 𝒮.tHat.X s) :
    xh ∈ 𝒮.badLocus s U ↔ ∃ K ∈ (𝒮.tHat.B s).irreducibleComponents,
      ¬ 𝒮.IsGoodComponent s U K ∧ xh ∈ K.pts := by
  rw [badLocus, Set.mem_iUnion₂]
  constructor
  · rintro ⟨K, ⟨hK, hbad⟩, hx⟩
    exact ⟨K, hK, hbad, hx⟩
  · rintro ⟨K, hK, hbad, hx⟩
    exact ⟨K, ⟨hK, hbad⟩, hx⟩

/-- `Bad_s ⊆ B̂_s`. -/
theorem badLocus_subset_pts (s : ℕ) (U : (𝒮.tHat.X s).Opens) :
    𝒮.badLocus s U ⊆ (𝒮.tHat.B s).pts := by
  intro xh hxh
  obtain ⟨K, hK, -, hxK⟩ := (𝒮.mem_badLocus_iff s U xh).mp hxh
  exact Subscheme.pts_subset_of_mem_irreducibleComponents hK hxK

/-- `Bad_s` is closed: a finite union (`X̂_s` is noetherian) of closed sets. -/
theorem isClosed_badLocus [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (U : (𝒮.tHat.X s).Opens) : IsClosed (𝒮.badLocus s U) := by
  have := 𝒮.isAlgebraicScheme_tHat_X s
  exact Set.Finite.isClosed_biUnion
    ((Subscheme.finite_irreducibleComponents (𝒮.tHat.B s)).subset fun K hK => hK.1)
    fun K hK => Subscheme.isClosed_pts_of_mem_irreducibleComponents hK.1

/-- If the containments of [g] hold globally relative to `U` (`B̂_s ⊆ X̄_s`, and
`J̄(s) ⊆ P(B̄_s)^b` at the points of `U ∩ X̄_s`), then no component is bad: `Bad_s = ∅`. -/
theorem badLocus_eq_empty_of_isContainedIn (s : ℕ) (U : (𝒮.tHat.X s).Opens)
    (hcont : (𝒮.tHat.B s).IsContainedIn (𝒮.xBar s))
    (hJ : ∀ xb : (𝒮.xBar s).toScheme, (𝒮.xBar s).ι.base xb ∈ U →
      (𝒮.jBar s).stalkIdeal xb ≤ ((𝒮.bBarOn s).stalkIdeal xb) ^ 𝒮.b) :
    𝒮.badLocus s U = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun xh hxh => ?_
  obtain ⟨K, hK, hKbad, -⟩ := (𝒮.mem_badLocus_iff s U xh).mp hxh
  exact hKbad ⟨(Subscheme.isContainedIn_of_mem_irreducibleComponents hK).trans hcont,
    fun xb hU _ => hJ xb hU⟩

/-- If no component is good, then `Bad_s = B̂_s`. -/
theorem badLocus_eq_pts_of_forall_not_isGoodComponent (s : ℕ) (U : (𝒮.tHat.X s).Opens)
    (h : ∀ K ∈ (𝒮.tHat.B s).irreducibleComponents, ¬ 𝒮.IsGoodComponent s U K) :
    𝒮.badLocus s U = (𝒮.tHat.B s).pts := by
  refine Set.Subset.antisymm (𝒮.badLocus_subset_pts s U) fun xh hxh => ?_
  obtain ⟨K, hK, hxK⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_pts _ hxh
  exact (𝒮.mem_badLocus_iff s U xh).mpr ⟨K, hK, h K hK, hxK⟩

/-! ## The componentwise construction [f*], [g*]/[h*] -/

/-- The open subschemes `X̂*'_s` of the `X̂_s` of the corrected construction, by induction on
`s`: [f*] `X̂*'_0 = X̂_0`; [g*]/[h*] `X̂*'_{s+1} = f̂_s⁻¹(X̂*'_s − Bad_s)`, where `Bad_s` is the
union of the components of `B̂_s` on which the containments of [g] (relative to `X̂*'_s`) fail.

\textbf{Deviation from the paper (construction corrected).} The paper's [g] and [h] (p. 298)
remove either nothing or all of `B̂_s` according as the containments hold on all of `B̂_s` or
not; here only the bad components are removed.  The paper's cases are `Bad_s = ∅` and
`Bad_s = B̂_s` (`badLocus_eq_empty_of_isContainedIn`,
`badLocus_eq_pts_of_forall_not_isGoodComponent`).  No open `X'_s` of `X_s` is formed; `J̄(s)` is
unchanged. -/
@[blueprint "def:IV.3-construction-componentwise"
  (statement := /-- \textbf{Deviation from the paper (construction corrected).} This is NOT the
    paper's construction. Notation as in \cref{def:IV.3-setup}, \cref{def:IV.3-frame},
    \cref{def:IV.3-construction}; $\bar J(s)$ is the sheaf of \cref{def:IV.3-construction}
    (it does not depend on $X_s'$). We define open subschemes $\hat X_s^{*\prime}$ of
    $\hat X_s$ and $\bar X_s^{*\prime}=\hat X_s^{*\prime}\cap\bar X_s$ of $\bar X_s$ by
    induction on $s\ge0$: [f*] $\hat X_0^{*\prime}=\hat X_0$; a component $K$ of $\hat B_s$
    (non-singular, so its irreducible components are its connected components) is \emph{good}
    if $K\subseteq\bar X_s$ and the $b$th power of the sheaf of ideals of $\bar B_s=\hat
    B_s\cap\bar X_s$ contains $\bar J(s)$ at every point of $\bar X_s^{*\prime}$ lying over $K$;
    the \emph{bad locus} $\mathrm{Bad}_s$ is the union of the components of $\hat B_s$ that are
    not good, a closed subset of $\hat B_s$; [g*]/[h*]
    $\hat X_{s+1}^{*\prime}=\hat f_s^{-1}(\hat X_s^{*\prime}-\mathrm{Bad}_s)$ and
    $\bar X_{s+1}^{*\prime}=\hat X_{s+1}^{*\prime}\cap\bar X_{s+1}$.

    The paper (p.~298): ``[g] if $\hat B_s=c_s^{-1}(B_s)$ is contained in $\bar X_s$ and if, at
    the same time, the $b$th power of the sheaf of prime ideals of $\hat B_s$ on $\bar X_s'$
    contains the sheaf of ideals $\bar J(s)$, then we define $X_{s+1}'=f_s^{-1}(X_s')$,
    $\hat X_{s+1}'=\hat f_s^{-1}(\hat X_s')=c_{s+1}^{-1}(X_{s+1}')$ and
    $\bar X_{s+1}'=\bar f_s^{-1}(\bar X_s')=\hat X_{s+1}'\cap\bar X_{s+1}=
    \bar c_{s+1}^{-1}(X_{s+1}')$ \dots; [h] if either one of the conditions in [g] is not
    satisfied, then $X_{s+1}'=f_s^{-1}(X_s'-B_s)=f_s^{-1}(X_s')-E_{\alpha+s+1}(s+1)$,
    $\hat X_{s+1}'=\hat f_s^{-1}(\hat X_s'-\hat B_s)=c_{s+1}^{-1}(X_{s+1}')$ and
    $\bar X_{s+1}'=\bar f_s^{-1}(\bar X_s'-\hat B_s\cap\bar X_s')=\hat X_{s+1}'\cap
    \bar X_{s+1}=\bar c_{s+1}^{-1}(X_{s+1}')$.'' The paper's [g] and [h] are the cases
    $\mathrm{Bad}_s=\emptyset$ and $\mathrm{Bad}_s=\hat B_s$ of [g*]/[h*]. The paper's
    condition [g] requires the containments on all of $\hat B_s$, which Lemma (AB.4) claims by
    the false irreducibility of $\hat B_s$ (\cref{lem:IV.AB-4-componentwise});
    the corrected construction removes only the components on which they fail, and no open
    $X_s'$ of $X_s$ is formed. -/)
  (latexEnv := "definition")]
noncomputable def xHatPrimeStar [Hironaka.HironakaCitedResults.{u}] : ∀ s, (𝒮.tHat.X s).Opens
  | 0 => ⊤
  | s + 1 => 𝒮.tHat.f s ⁻¹ᵁ (xHatPrimeStar s ⊓
      ⟨(𝒮.badLocus s (xHatPrimeStar s))ᶜ, (𝒮.isClosed_badLocus s _).isOpen_compl⟩)

/-- The bad locus `Bad_s` at the stage `s` of the corrected construction, relative to `X̂*'_s`. -/
noncomputable def badLocusStar [Hironaka.HironakaCitedResults.{u}] (s : ℕ) : Set (𝒮.tHat.X s) :=
  𝒮.badLocus s (𝒮.xHatPrimeStar s)

/-- `X̄*'_s = X̂*'_s ∩ X̄_s`, an open subscheme of `X̄_s`. -/
noncomputable def xBarPrimeStar [Hironaka.HironakaCitedResults.{u}] (s : ℕ) : (𝒮.xBar s).toScheme.Opens :=
  (𝒮.xBar s).ι ⁻¹ᵁ 𝒮.xHatPrimeStar s

/-- [g*]/[h*]: `X̂*'_{s+1} = f̂_s⁻¹(X̂*'_s − Bad_s)`. -/
theorem coe_xHatPrimeStar_succ [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    (𝒮.xHatPrimeStar (s + 1) : Set (𝒮.tHat.X (s + 1))) =
      (𝒮.tHat.f s).base ⁻¹' ((𝒮.xHatPrimeStar s : Set (𝒮.tHat.X s)) \ 𝒮.badLocusStar s) := by
  ext yh
  exact Iff.rfl

/-- The corrected construction as an open family with removals (`Frame.RemovalFamily`): the
containments of [g] hold off `Bad_s` by the definition of the good components, the ideal of
`B̂_s` at a point of a component being that of the component (`B̂_s` is non-singular). -/
noncomputable def removalFamilyStar [Hironaka.HironakaCitedResults.{u}] : 𝒮.RemovalFamily where
  U := 𝒮.xHatPrimeStar
  bad := 𝒮.badLocusStar
  bad_subset s := 𝒮.badLocus_subset_pts s _
  coe_U_succ := 𝒮.coe_xHatPrimeStar_succ
  stalkIdeal_xBar_le s xh hxh := by
    obtain ⟨K, hK, hxK⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_pts _ hxh.1
    have hgood : 𝒮.IsGoodComponent s (𝒮.xHatPrimeStar s) K := by
      by_contra hbad
      exact hxh.2 ((𝒮.mem_badLocus_iff s _ xh).mpr ⟨K, hK, hbad, hxK⟩)
    have hBns : (𝒮.tHat.B s).IsNonsingular := 𝒮.isNonsingular_B (hS.ambient.2.1 x₀)
      hS.isNonsingular_X hS.isNonsingular_B s
    rw [← Subscheme.stalkIdeal_eq_of_mem_irreducibleComponents_of_isNonsingular hBns hK hxK]
    exact Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hgood.1 xh
  stalkIdeal_jBar_le s xb hU hB := by
    obtain ⟨K, hK, hxK⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_pts _ hB.1
    have hgood : 𝒮.IsGoodComponent s (𝒮.xHatPrimeStar s) K := by
      by_contra hbad
      exact hB.2 ((𝒮.mem_badLocus_iff s _ _).mpr ⟨K, hK, hbad, hxK⟩)
    exact hgood.2 xb hU hxK

/-- `X̄*'_s` is non-singular (the generic construction facts
`lem:IV.3-construction-facts-generic` for the family `removalFamilyStar`). -/
theorem isSimpleAt_xBar_of_mem_xBarPrimeStar [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (xb : (𝒮.xBar s).toScheme)
    (hxb : xb ∈ 𝒮.xBarPrimeStar s) : (𝒮.xBar s).toScheme.IsSimpleAt xb :=
  (𝒮.removalFamilyStar.isSimpleAt_and_isIrreducible_and_isNonsingCodimOneOn s).1 xb hxb

/-! ## The repaired Lemma (AB.4) -/

/-- The componentwise second assertion of Lemma (AB.4): if `x ∈ B_s` satisfies (1), (2), (3)
and `c_s(x̂) = x`, every irreducible component `K` of `B̂_s` through `x̂` is good relative to
`X̂*'_s`.  This is the paper's argument at `x̂` (pp. 300–302, `lem:IV.AB-4-stalk`) extended to
`K` (`lem:IV.AB-4-local`), with the non-singularity of `X̄*'_s` in place of that of `X̄'_s`. -/
theorem isGoodComponent_of_cond [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (x : T.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s x) (hxB : x ∈ (T.B s).pts)
    (xh : 𝒮.tHat.X s) (hxh : (𝒮.c s).base xh = x) (K : Subscheme (𝒮.tHat.X s))
    (hK : K ∈ (𝒮.tHat.B s).irreducibleComponents) (hxhK : xh ∈ K.pts) :
    𝒮.IsGoodComponent s (𝒮.xHatPrimeStar s) K :=
  ⟨𝒮.isContainedIn_xBar_of_mem_irreducibleComponents s x hx hxB xh hxh K hK hxhK,
    fun xb hU hxbK => 𝒮.jBar_le_pow_of_mem_irreducibleComponents s x hx hxB xh hxh K hK hxhK
      xb (𝒮.isSimpleAt_xBar_of_mem_xBarPrimeStar s xb hU) hxbK⟩

/-- The first assertion of the repaired Lemma (AB.4): if `x` satisfies (1), (2), (3) and
`c_s(x̂) = x`, then `x̂ ∈ X̂*'_s`.  By induction on `s`, as in the paper ("If the first and the
second assertions are verified for certain `s ≥ 0`, then the first assertion for `s + 1` follows
immediately by the definition `X'_{s+1}`. The first assertion is trivially true for `s = 0`",
p. 299): the image `x̂_s = f̂_s(x̂)` lies over `x_s = f_s(x)`, which satisfies (1), (2), (3)
(`Standing.cond_f_of_cond_succ`), so `x̂_s ∈ X̂*'_s`; and `x̂_s ∉ Bad_s`, because `Bad_s ⊆ B̂_s`
and, if `x̂_s ∈ B̂_s`, every component of `B̂_s` through `x̂_s` is good
(`isGoodComponent_of_cond`). -/
theorem mem_xHatPrimeStar_of_cond [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (x : T.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s x) (xh : 𝒮.tHat.X s)
    (hxh : (𝒮.c s).base xh = x) : xh ∈ 𝒮.xHatPrimeStar s := by
  induction s with
  | zero => exact trivial
  | succ s ih =>
    have hc : (𝒮.c s).base ((𝒮.tHat.f s).base xh) = (T.f s).base x := by
      rw [← hxh]
      exact congrArg (fun φ => φ.base xh) (𝒮.c_comm s)
    have hy := hS.cond_f_of_cond_succ s x hx
    have hmem := ih _ hy _ hc
    show (𝒮.tHat.f s).base xh ∈ 𝒮.xHatPrimeStar s ∧
      (𝒮.tHat.f s).base xh ∉ 𝒮.badLocusStar s
    refine ⟨hmem, fun hbad => ?_⟩
    obtain ⟨K, hK, hKbad, hxK⟩ := (𝒮.mem_badLocus_iff s _ _).mp hbad
    have hxB : (T.f s).base x ∈ (T.B s).pts := by
      have h1 := Subscheme.pts_subset_of_mem_irreducibleComponents hK hxK
      rw [𝒮.B_hat s, Subscheme.pts_totalTransform_eq_preimage, Set.mem_preimage, hc] at h1
      exact h1
    exact hKbad (𝒮.isGoodComponent_of_cond s _ hy hxB _ hc K hK hxK)

/-- **Lemma (AB.4), repaired** (p. 299, for the corrected construction
`def:IV.3-construction-componentwise`): if `x ∈ X_s` satisfies the conditions (1), (2), (3)
(`Cond`: (1) `X_s` has dimension `N` at `x`, (2) `g_s(x) = x_0`, (3) `ν*_x` and `τ*_x` of
`(V_1(s), …, V_β(s), W(s)/X_s)` equal `ν*_{x_0}` and `τ*_{x_0}` of `(V_1, …, V_β, W/X)`), then
there is a unique `x̂ ∈ X̂_s` with `c_s(x̂) = x`, and it lies in `X̂*'_s`; if moreover
`x ∈ B_s`, then `B̂_s` is non-singular, every irreducible component `K` of `B̂_s` through `x̂`
is good (`K ⊆ X̄_s`, and `J̄(s) ⊆ P(B̄_s)^b` at the points of `X̄*'_s` over `K`), `x̂ ∉ Bad_s`,
and `B̄_s = B̂_s ∩ X̄_s` is simple at the points of `X̄*'_s` over `K`.

The paper's statement: "If `x` is any point of `X_s` satisfying the conditions (1), (2) and (3),
then `x` is a point of `X'_s`, and there exists a unique point `x̂` of `X̂'_s` such that
`c_s(x̂) = x`. If `B_s` contains at least one point `x` of `X_s` satisfying the conditions (1),
(2) and (3), then `B̂_s = c_s⁻¹(B_s)` is a non-singular irreducible subscheme of `X̄_s` (i.e., a
non-singular irreducible subscheme of `X̂_s` which is contained in `X̄_s`) and the coherent sheaf
of ideals `J̄(s)` is contained in the `b`th power of the coherent sheaf of ideals of `B̄'_s`
(`= B̂_s ∩ X̄'_s`, which is a non-singular irreducible subscheme of `X̄'_s`)."

\textbf{Deviation from the paper (proof corrected).} The paper's proof (pp. 299–302) establishes
the containments at `x̂` and extends them to all of `B̂_s` by the irreducibility of `B̂_s`
("So `B̂_s` is a non-singular irreducible subscheme of `X̂_s`", p. 299; "Since `B̄'_s` is a
non-singular irreducible subscheme of `X̄'_s`, this suffices", p. 301), which is false in
general.  Here they are extended to the component of `B̂_s` through `x̂` instead
(`lem:IV.AB-4-local`), and the first assertion is `x̂ ∈ X̂*'_s` for the corrected construction,
proved by the paper's induction with "`x̂_t ∉ Bad_t`" in place of "the condition [g] holds at
`t`".  The containments on all of `B̂_s` (`B̂_s ⊆ X̄_s`, and `J̄(s)` in the `b`th power of the
ideal of `B̄'_s`) are proved by the paper's argument only near `x̂`; on a component through a point
over `x₀` where `τ*` is larger the paper gives no control, and whether they hold globally is not
known.

\textbf{Counterexample to the irreducibility.}  Over a field of characteristic 0 let `X = 𝔸³` with
coordinates `(u, v, w)`, `ℜ = (∅; W)` (so `α = β = 0`), `N = 3`, `n = 2`, `W = {w(w − g) = 0}` with
`g = v² − u²(1 + u)`, and open restriction `U = W − C`, where `C = {w = g = 0}` is the nodal curve along
which the two smooth sheets `w = 0`, `w = g` of `W` meet; `x₀` is the node.  Take `B₀ = {x₀}`
(permissible) and `B₁ = C'`, the strict transform of `C`.  It is non-singular, lies in `W(1) − U(1)`,
crosses the exceptional divisor `E₁` transversally at its two points `x`, `y` over `x₀`, and `W(1)`
has multiplicity 2 along it (a hypersurface, hence normally flat), so `B₁` is permissible.  At `x` the
local equation of `W(1)` has initial form `w₁²`, so `ν*_x = (2, ∞, …) = ν*_{x₀}` and
`τ^{(1)}_x = 1 = τ^{(1)}_{x₀}`: the point `x` satisfies (1)–(3).  But `C' → C` is the normalization,
a finite morphism, so
`B̂₁ = c₁⁻¹(C') = C' ×_C Spec Ô_{C,x₀} = Spec(Ô_{C',x} × Ô_{C',y})`
has two connected components: `B̂₁` is non-singular but not irreducible.

\textbf{Deviation from the paper (gap filled).} The simplicity of `B̄_s` at the points of `X̄*'_s`
over `K` ("which is a non-singular … subscheme of `X̄'_s`") is derived from `K ⊆ X̄_s` and the
non-singularity of `B̂_s`: `O_{X̄_s}/B̄_s ≅ O_{X̂_s}/K = O_{X̂_s}/B̂_s` at such points
(`Subscheme.exists_quotEquiv_totalTransform`). -/
@[blueprint "lem:IV.AB-4-componentwise"
  (statement := /-- \textbf{Lemma (AB.4), repaired.} Notation as in \cref{def:IV.3-setup},
    \cref{def:IV.3-frame} and \cref{def:IV.3-construction-componentwise}. Let us consider the
    following condition on a point $x$ of $X_s$: (1) $X_s$ has dimension $N$ at $x$, (2)
    $g_s(x)=x_0$, and (3) $\nu^*_x(V_1(s),\dots,V_\beta(s),W(s)/X_s)=
    \nu^*_{x_0}(V_1,\dots,V_\beta,W/X)$ and $\tau^*_x(V_1(s),\dots,V_\beta(s),W(s)/X_s)=
    \tau^*_{x_0}(V_1,\dots,V_\beta,W/X)$ (Formalization note (encoding): condition (3) includes
    that $X_s$ is simple at $x$, where the characters are formed). If $x$ is any point of
    $X_s$ satisfying the conditions (1), (2) and (3), then there exists a unique point $\hat x$
    of $\hat X_s$ such that $c_s(\hat x)=x$, and $\hat x\in\hat X_s^{*\prime}$. If moreover
    $x\in B_s$, then $\hat B_s=c_s^{-1}(B_s)$ is non-singular, every irreducible component $K$
    of $\hat B_s$ through $\hat x$ is good, i.e.\ $K\subseteq\bar X_s$ and $\bar J(s)$ is
    contained in the $b$th power of the sheaf of ideals of $\bar B_s=\hat B_s\cap\bar X_s$ at
    every point of $\bar X_s^{*\prime}$ lying over $K$; $\hat x\notin\mathrm{Bad}_s$; and
    $\bar B_s$ is non-singular at the points of $\bar X_s^{*\prime}$ lying over $K$.

    \textbf{Deviation from the paper (statement corrected).} The printed Lemma (AB.4) (p.~299)
    reads: ``If $x$ is any point of $X_s$ satisfying the conditions (1), (2) and (3), then $x$ is
    a point of $X_s'$, and there exists a unique point $\hat x$ of $\hat X_s'$ such that
    $c_s(\hat x)=x$. If $B_s$ contains at least one point $x$ of $X_s$ satisfying the conditions
    (1), (2) and (3), then $\hat B_s=c_s^{-1}(B_s)$ is a non-singular irreducible subscheme of
    $\bar X_s$ (i.e., a non-singular irreducible subscheme of $\hat X_s$ which is contained in
    $\bar X_s$) and the coherent sheaf of ideals $\bar J(s)$ is contained in the $b$th power of
    the coherent sheaf of ideals of $\bar B_s'$ ($=\hat B_s\cap\bar X_s'$, which is a
    non-singular irreducible subscheme of $\bar X_s'$).'' The irreducibility of $\hat B_s$ is
    false: $\hat B_s=B_s\times_X\operatorname{Spec}\hat S$ is irreducible only when
    $B_s\cap g_s^{-1}(x_0)$ is connected, and there are permissible successions in which it is
    not while $B_s$ contains a point satisfying (1), (2), (3). The containments on all of
    $\hat B_s$ are not proved by the paper's argument, and whether they hold is not known. This
    statement replaces $X_s'$, $\hat X_s'$ by $\hat X_s^{*\prime}$ and ``$\hat B_s$'' by
    ``every component of $\hat B_s$ through $\hat x$''.

    \textbf{Counterexample to the irreducibility.} Over a field of characteristic~$0$ let
    $X=\mathbb A^3$ with coordinates $(u,v,w)$, $\mathfrak R=(\emptyset;W)$ (so
    $\alpha=\beta=0$), $N=3$, $n=2$, $W=\{w(w-g)=0\}$ with $g=v^2-u^2(1+u)$, and open
    restriction $U=W-C$, where $C=\{w=g=0\}$ is the nodal curve along which the two smooth
    sheets $w=0$, $w=g$ of $W$ meet; $x_0$ is the node. Take $B_0=\{x_0\}$ (permissible) and
    $B_1=C'$, the strict transform of $C$. It is non-singular, lies in $W(1)-U(1)$, crosses the
    exceptional divisor $E_1$ transversally at its two points $x,y$ over $x_0$, and $W(1)$ has
    multiplicity $2$ along it (a hypersurface, hence normally flat), so $B_1$ is permissible. At
    $x$ the local equation of $W(1)$ has initial form $w_1^2$, so $\nu^*_x=(2,\infty,\dots)=
    \nu^*_{x_0}$ and $\tau^{(1)}_x=1=\tau^{(1)}_{x_0}$: the point $x$ satisfies (1), (2), (3).
    But $C'\to C$ is the normalization, a finite morphism, so $\hat B_1=c_1^{-1}(C')=
    C'\times_C\operatorname{Spec}\hat{\mathcal O}_{C,x_0}=\operatorname{Spec}(\hat{\mathcal
    O}_{C',x}\times\hat{\mathcal O}_{C',y})$ has two connected components: $\hat B_1$ is
    non-singular but not irreducible. -/)
  (proof := /-- The paper's proof (pp.~299--302). If the first and the second assertions are
    verified for certain $s\ge0$, then the first assertion for $s+1$ follows immediately by the
    definition of $\hat X_{s+1}^{*\prime}$: the image $x_s=f_s(x)$ of $x$ satisfies (1), (2), (3)
    (\cref{lem:IV.3-thm3-consequence}), so $\hat x_s=\hat f_s(\hat x)\in\hat X_s^{*\prime}$,
    and $\hat x_s\notin\mathrm{Bad}_s$ since $\mathrm{Bad}_s\subseteq\hat B_s$ and, if
    $\hat x_s\in\hat B_s$, every component of $\hat B_s$ through $\hat x_s$ is good by the second
    assertion at $s$. The first assertion is trivially true for $s=0$. For the second assertion:
    the non-singularity of $B_s$ implies that of $\hat B_s$ (\cref{lem:IV.3-setup-nonsingular});
    the paper's local computation at $\hat x$ (\cref{lem:IV.AB-4-stalk}: $z_s\in\hat Q_s$ and
    $\bar Q_s^b\supseteq(g_{jki}(s)^{b/i})\bar T_s=\bar J(s)_{\hat x}$) gives, on the component
    $K$ of $\hat B_s$ through $\hat x$, $K\subseteq\bar X_s$ and $\bar J(s)\subseteq P(\bar
    B_s)^b$ at the points of $\bar X_s^{*\prime}$ over $K$ (\cref{lem:IV.AB-4-local}, with the
    non-singularity of $\bar X_s^{*\prime}$, \cref{lem:IV.3-construction-facts-generic}); hence
    every such $K$ is good and $\hat x\notin\mathrm{Bad}_s$; and $\bar B_s$ is non-singular at a
    point $\bar y$ of $\bar X_s^{*\prime}$ over $K$ because the local ring of $\bar B_s$ at
    $\bar y$ is that of $\hat B_s$ at $\iota(\bar y)$ ($K\subseteq\bar X_s$ and the ideal of
    $\hat B_s$ there is that of $K$).

    \textbf{Deviation from the paper (proof corrected).} The paper extends the containments
    from $\hat x$ to all of $\hat B_s$ by the irreducibility of $\hat B_s$ (``So $\hat B_s$ is
    a non-singular irreducible subscheme of $\hat X_s$'', p.~299; ``Since $\bar B_s'$ is a
    non-singular irreducible subscheme of $\bar X_s'$, this suffices'', p.~301), which is false
    in general; here they are extended to the component through $\hat x$ only, and the first
    assertion is proved for the corrected construction with ``$\hat x_t\notin\mathrm{Bad}_t$''
    in place of ``[g] holds at $t$''.

    \textbf{Deviation from the paper (gap filled).} The non-singularity of $\bar B_s$ at the
    points of $\bar X_s^{*\prime}$ over $K$ (``which is a non-singular \dots\ subscheme of
    $\bar X_s'$'') is derived from $K\subseteq\bar X_s$ and the non-singularity of $\hat B_s$. -/)
  (proofUses := ["lem:IV.3-thm3-consequence", "lem:IV.AB-2", "lem:IV.3-setup-nonsingular",
    "lem:IV.AB-4-stalk", "lem:IV.AB-4-local", "lem:IV.3-construction-facts-generic",
    "def:IV.3-construction-componentwise"])
  (latexEnv := "lemma")]
theorem mem_xHatPrimeStar_and_isGoodComponent_of_cond [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (x : T.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s x) :
    (∃! xh : 𝒮.tHat.X s, (𝒮.c s).base xh = x) ∧
    ∀ xh : 𝒮.tHat.X s, (𝒮.c s).base xh = x →
      xh ∈ 𝒮.xHatPrimeStar s ∧
      (x ∈ (T.B s).pts →
        (𝒮.tHat.B s).IsNonsingular ∧
        ∀ K ∈ (𝒮.tHat.B s).irreducibleComponents, xh ∈ K.pts →
          𝒮.IsGoodComponent s (𝒮.xHatPrimeStar s) K ∧ xh ∉ 𝒮.badLocusStar s ∧
          ∀ xb ∈ 𝒮.xBarPrimeStar s, (𝒮.xBar s).ι.base xb ∈ K.pts →
            (𝒮.bBarOn s).IsSimpleAt xb) := by
  refine ⟨𝒮.existsUnique_c_apply_eq (hS.ambient.2.1 x₀) hS.isNonsingular_X hS.isNonsingular_B s x
    hx.2.1, fun xh hxh =>
    ⟨𝒮.mem_xHatPrimeStar_of_cond s x hx xh hxh, fun hxB => ?_⟩⟩
  have hBns : (𝒮.tHat.B s).IsNonsingular := 𝒮.isNonsingular_B (hS.ambient.2.1 x₀)
    hS.isNonsingular_X hS.isNonsingular_B s
  refine ⟨hBns, fun K hK hxhK => ?_⟩
  have hgood := 𝒮.isGoodComponent_of_cond s x hx hxB xh hxh K hK hxhK
  refine ⟨hgood, fun hbad => ?_, fun xb _ hxbK => ?_⟩
  · obtain ⟨K', hK', hK'bad, hxK'⟩ := (𝒮.mem_badLocus_iff s _ xh).mp hbad
    exact hK'bad (𝒮.isGoodComponent_of_cond s x hx hxB xh hxh K' hK' hxK')
  · -- `O_{X̄_s,x̄}/B̄_s ≅ O_{X̂_s,ι(x̄)}/K = O_{X̂_s,ι(x̄)}/B̂_s`, a regular local ring
    have hKeq : K.stalkIdeal ((𝒮.xBar s).ι.base xb) =
        (𝒮.tHat.B s).stalkIdeal ((𝒮.xBar s).ι.base xb) :=
      Subscheme.stalkIdeal_eq_of_mem_irreducibleComponents_of_isNonsingular hBns hK hxbK
    have hmemB : (𝒮.xBar s).ι.base xb ∈ (𝒮.tHat.B s).pts :=
      Subscheme.pts_subset_of_mem_irreducibleComponents hK hxbK
    obtain ⟨τ, -⟩ := Subscheme.exists_quotEquiv_totalTransform (𝒮.xBar s) K hgood.1 xb
    have hDeq : (𝒮.bBarOn s).stalkIdeal xb =
        (Subscheme.totalTransform (𝒮.xBar s).ι K).stalkIdeal xb := by
      show (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s)).stalkIdeal xb = _
      rw [stalkIdeal_totalTransform, stalkIdeal_totalTransform, hKeq]
    have hreg := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hBns hmemB
    rw [← hKeq] at hreg
    refine ⟨?_, ?_⟩
    · show xb ∈ (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s)).pts
      rw [Subscheme.pts_totalTransform_eq_preimage]
      exact hmemB
    · rw [hDeq]
      exact IsRegularLocalRing.of_ringEquiv τ

/-- `x̂ ∉ Bad_s` for the unique point `x̂` over a point `x ∈ B_s` with (1), (2), (3): the form of
the repaired (AB.4) used by the first assertion at the next stage. -/
theorem notMem_badLocusStar_of_cond [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (x : T.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s x) (hxB : x ∈ (T.B s).pts)
    (xh : 𝒮.tHat.X s) (hxh : (𝒮.c s).base xh = x) : xh ∉ 𝒮.badLocusStar s := fun hbad => by
  obtain ⟨K, hK, hKbad, hxK⟩ := (𝒮.mem_badLocus_iff s _ xh).mp hbad
  exact hKbad (𝒮.isGoodComponent_of_cond s x hx hxB xh hxh K hK hxK)

/-! ## The Corollary of Lemma (AB.4) for the corrected construction -/

/-- **Corollary of Lemma (AB.4)** (p. 302) for the corrected construction: if `x` satisfies (1),
(2), (3) (and `x ∈ F(s)` in the closed case), the unique `x̂` over `x` lies in `X̂*'_s` and on
`X̄_s`, and `J̄(s)_x̂ ⊆ m̄^b` in the local ring of `X̄*'_s` at `x̂`.  The printed Corollary has
`X̂'_s` in place of `X̂*'_s`, and speaks of the local ring of `X̄'_s` at `x̂`, which presupposes
`x̂ ∈ X̄_s`; this membership is asserted explicitly.

As printed (p. 302): "we have `g_s(x) = x_0 ∈ W − U`.  Hence, by the condition (3) on `x`, we have
`x ∈ W(s) − U(s)`.  Then we see that the monoidal transformation of `X_s` with center `x` is
permissible for the resolution datum `(ℜ^{N,n}_I(s), U(s))`.  Namely we can take `B_s` to be the
closed point `x` of `X_s`. … Thus the assertions in the Corollary follow Lemma (AB.4) applied to
`B_s = x`."  Lean: `x ∈ W(s)` (`Standing.mem_pts_sys_last_of_cond`); `x` is a closed point of `X_s`
because `X_s` has dimension `N` at `x` (condition (1), `isClosed_singleton_of_dimAt_eq`); the reduced
closed point `{x}` is a permissible center for `ℜ(s)` (`DatumI.Raw.isPermissible_ofClosed_singleton`)
and lies in `F(s)` in the closed case; Lemma (AB.4) for this center is
`Frame.stalkIdeal_xBar_le_and_jBar_le_pow_of_isPermissible` (the proof of (AB.4) uses of `B_s`
only that it is a permissible center for `(ℜ(s), r(s))`; the modified infinite tower with
`B_s = x` is not built).  Then `Q̂ = M̂_s` (the regular system of parameters of `S_s` goes to
one of `Ŝ_s`, Lemma (AB.2)).
\textbf{Gaps filled.} that `x` is a closed point (not said by the paper); that `{x}` is a
permissible center ("Then we see …"); the first assertion is the repaired (AB.4). -/
@[blueprint "cor:IV.AB-4-componentwise"
  (statement := /-- \textbf{Corollary} (of \cref{lem:IV.AB-4-componentwise}). Notation as in
    \cref{def:IV.3-construction-componentwise}. For the case in which
    $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},U)$, if $x$ is any point of $X_s$ satisfying
    the conditions (1), (2) and (3) of Lemma (AB.4), then the unique point $\hat x$ of
    $\hat X_s$ such that $c_s(\hat x)=x$ belongs to $\hat X_s^{*\prime}$ and to $\bar X_s$, and
    the stalk $\bar J(s)_{\hat x}$ is contained in the $b$th power of the maximal ideal of the
    local ring of $\bar X_s^{*\prime}$ at $\hat x$. For the case in which
    $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$, the same is true provided $x\in F(s)$.
    (The Corollary of Lemma (AB.4), p.~302, for the corrected construction.)

    \textbf{Deviation from the paper (statement corrected).} $\hat X_s'$ is replaced by
    $\hat X_s^{*\prime}$. The printed Corollary speaks of the local ring of $\bar X_s'$ at
    $\hat x$, which presupposes $\hat x\in\bar X_s$; this membership is asserted
    explicitly. -/)
  (proof := /-- $\hat x\in\hat X_s^{*\prime}$ by the first assertion of
    \cref{lem:IV.AB-4-componentwise}. For the rest, the paper applies Lemma (AB.4) to the
    succession with $B_s=x$: ``For the case in which
    $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},U)$, we have $g_s(x)=x_0\in W-U$. Hence, by the
    condition (3) on $x$, we have $x\in W(s)-U(s)$. Then we see that the monoidal
    transformation of $X_s$ with center $x$ is permissible for the resolution datum
    $(\mathfrak R^{N,n}_{\mathrm I}(s),U(s))$. Namely we can take $B_s$ to be the closed point
    $x$ of $X_s$'' (p.~302), and likewise for $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$
    provided $x\in F(s)$. In Lean the local computation of \cref{lem:IV.AB-4-stalk} is run at
    $\hat x$ with $\hat Q_s=\hat M_s$, the ideal of the center $x$: $z_s\in\hat M_s$ (so
    $\hat x\in\bar X_s$), $g_{jk}(s)\in\hat M_s^{\nu_{jk}}$ since
    $\nu_{\hat M_s}(g_{jk}(s))=\nu_{jk}$ (\cref{lem:IV.AB-4-frames}), hence
    $g_{jki}(s)\in\hat M_s^i$ and $g_{jki}(s)^{b/i}\in\hat M_s^b$, i.e.\
    $\bar J(s)_{\hat x}=(g_{jki}(s)^{b/i})\bar T_s\subseteq\bar M_s^b$.

    \textbf{Gaps filled.} That $x$ is a closed point of $X_s$ (condition (1): $X_s$ has dimension
    $N$ at $x$ and no point has larger local dimension), and that the monoidal transformation with
    center $x$ is permissible (``Then we see \dots''): $x\in W(s)$ by (3), and the reduced closed
    point is non-singular and irreducible, $(E;V_1,\dots,V_\beta,W;\{x\})$ is a datum, resolved at
    $x$ (the graded pieces are modules over the residue field; $E$ has normal crossings with the
    point, whose ideal is generated by the whole regular system of parameters). The proof of
    \cref{lem:IV.AB-4-stalk} is stated for any permissible center of $\mathfrak R(s)$, since it uses
    $B_s$ only through this; the modified succession with $B_s=x$ is not built. -/)
  (proofUses := ["lem:IV.AB-4-componentwise", "lem:IV.AB-4-frames", "lem:IV.AB-4-stalk"])
  (latexEnv := "corollary")]
theorem exists_mem_xHatPrimeStar_and_jBar_le_maximalIdeal_pow_of_cond [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (x : T.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s x)
    (hF : ∀ F, r = .closed F → x ∈ ((T.pre s).strictTransform F).pts) :
    ∃ xh : 𝒮.tHat.X s, (𝒮.c s).base xh = x ∧ (∀ yh, (𝒮.c s).base yh = x → yh = xh) ∧
      xh ∈ 𝒮.xHatPrimeStar s ∧
      ∃ xb : (𝒮.xBar s).toScheme, xb ∈ 𝒮.xBarPrimeStar s ∧ (𝒮.xBar s).ι.base xb = xh ∧
        (𝒮.jBar s).stalkIdeal xb ≤
          (maximalIdeal ((𝒮.xBar s).toScheme.presheaf.stalk xb)) ^ 𝒮.b := by
  classical
  obtain ⟨xh, hxh, huniq⟩ := 𝒮.existsUnique_c_apply_eq (hS.ambient.2.1 x₀) hS.isNonsingular_X
    hS.isNonsingular_B s x hx.2.1
  have hxhU := 𝒮.mem_xHatPrimeStar_of_cond s x hx xh hxh
  have hx' := hx
  have hF' := hF
  subst hxh
  -- p. 302: "`x` is a point of `X_s` with `g_s(x) = x_0 ∈ W − U`.  Hence, by the condition (3) on
  -- `x`, we have `x ∈ W(s) − U(s)`": `x ∈ W(s)`
  have hXa : IsAlgebraicScheme (T.X s) := hS.isAlgebraicScheme_X s
  have hxW := hS.mem_pts_sys_last_of_cond s _ hx'
  have hW : ((T.pre s).transformI ℜ).W = T.sys ℜ s (Fin.last ℜ.β) := by
    rw [MonoidalSuccession.transformI_W]
    show _ = (T.pre s).strictTransform (datumSystem ℜ (Fin.last ℜ.β))
    simp only [datumSystem, Fin.snoc_last]
  -- "Then we see that the monoidal transformation of `X_s` with center `x` is permissible for the
  -- resolution datum `(ℜ(s), U(s))`.  Namely we can take `B_s` to be the closed point `x` of `X_s`":
  -- `x` is a closed point since `X_s` has dimension `N` at `x` (condition (1)), and the closed point
  -- is a permissible center
  have hcl : IsClosed ({(𝒮.c s).base xh} : Set (T.X s)) :=
    haveI : IsLocallyNoetherian (T.X s) := (IsAlgebraicScheme.isNoetherian _).toIsLocallyNoetherian
    isClosed_singleton_of_dimAt_eq (hS.dimAt_X_le s) hx'.1
  have hℜs : ((T.pre s).transformI ℜ).IsDatum :=
    haveI : IsAlgebraicScheme X := hS.ambient.1
    MonoidalSuccession.transformI_isDatum (T.pre s) hS.ambient.2.1 ℜ hS.isDatum (hS.permissible s).isPermissibleI
  set B' : Subscheme (T.X s) := Subscheme.ofClosed ⟨{(𝒮.c s).base xh}, hcl⟩ with hB'def
  have hB'pts : B'.pts = {(𝒮.c s).base xh} := Subscheme.pts_ofClosed _
  have hB'perm : ((T.pre s).transformI ℜ).IsPermissible B' :=
    DatumI.Raw.isPermissible_ofClosed_singleton (hS.isNonsingular_X s) hℜs hcl (by
      rw [hW]; exact hxW)
  have hBF : ∀ F, r = .closed F → B'.pts ⊆ ((T.pre s).strictTransform F).pts := by
    intro F hr y hy
    rw [hB'pts] at hy
    rw [Set.mem_singleton_iff.mp hy]
    exact hF' F hr
  have hxB : (𝒮.c s).base xh ∈ B'.pts := by rw [hB'pts]; rfl
  -- Lemma (AB.4) applied to `B_s = x`
  obtain ⟨h1, h2⟩ := 𝒮.stalkIdeal_xBar_le_and_jBar_le_pow_of_isPermissible s B' hB'perm hBF xh
    hx' hxB
  -- the ideal of `B̂_s = c_s⁻¹(x)` at `x̂` is the maximal ideal of `Ŝ_s`: the regular system of
  -- parameters of `S_s` goes to one of `Ŝ_s` (Lemma (AB.2))
  have hxh0 : (𝒮.tHat.pre s).composite.base xh = xhat0 X x₀ (hS.ambient.2.1 x₀) :=
    𝒮.composite_tHat_eq_xhat0 (hS.ambient.2.1 x₀) s xh hx'.2.1
  obtain ⟨-, hα, -⟩ := 𝒮.isRegularLocalRing_and_mapsRSOP_stalkMap (hS.ambient.2.1 x₀)
    hS.isNonsingular_X hS.isNonsingular_B s xh hxh0
  have hQmax : (Subscheme.totalTransform (𝒮.c s) B').stalkIdeal xh =
      maximalIdeal ((𝒮.tHat.X s).presheaf.stalk xh) := by
    rw [stalkIdeal_totalTransform, hB'def, stalkIdeal_ofClosed_singleton_eq_maximalIdeal]
    obtain ⟨t, ht, ht', -⟩ := hα
    rw [← ht'.1, ← ht.1, Ideal.map_span, Finset.coe_image]
  -- hence `x̂ ∈ X̄_s`
  have hxhX : xh ∈ (𝒮.xBar s).pts := by
    rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top]
    intro htop
    rw [htop, top_le_iff, hQmax] at h1
    exact (maximalIdeal.isMaximal _).ne_top h1
  obtain ⟨xb, hxb⟩ := Subscheme.exists_ι_eq_of_mem_pts (𝒮.xBar s) hxhX
  subst hxb
  refine ⟨_, rfl, fun yh hyh => huniq yh hyh, hxhU, xb, hxhU, rfl, ?_⟩
  -- "`J̄(s)_x̂ ⊆ Q̄_s^b`", `Q̄_s` the ideal of `B̄_s = x̂` in `X̄_s`: the maximal ideal
  have hmM : (Subscheme.totalTransform (𝒮.xBar s).ι
      (Subscheme.totalTransform (𝒮.c s) B')).stalkIdeal xb =
      maximalIdeal ((𝒮.xBar s).toScheme.presheaf.stalk xb) := by
    rw [stalkIdeal_totalTransform, hQmax,
      IsLocalRing.map_maximalIdeal_of_surjective _ ((𝒮.xBar s).ι.stalkMap_surjective xb)]
  have := h2 xb rfl
  rwa [hmM] at this

/-- A point `x` of `X_s` satisfying (1), (2), (3) of Lemma (AB.4) (and on `F(s)` in the closed case)
gives a point of `X̃ = X̄*'_s` at which `X̃` has dimension `N - 1` (the proviso of p. 308: "We shall be
only interested in the case in which `X̃` has dimension `N - 1`.  This is the case, if there exists
at least one point `x` of `S(ℜ(s))` having the properties (1), (2) and (3) of Lemma (AB.4)"):
the point `x̂_b` of the Corollary of Lemma (AB.4) (`exists_mem_xHatPrimeStar_and_jBar_le_maximalIdeal_pow_of_cond`)
lies on `X̄_s` over `x` and `O_{X̄_s,x̂_b} = O_{X̂_s,x̂}/(z_s)` has dimension `N - 1`
(`Frame.dimAt_xBar_eq_of_cond`). -/
theorem exists_dimAt_xTilde_removalFamilyStar_eq_of_cond [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (x : T.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s x)
    (hF : ∀ F, r = .closed F → x ∈ ((T.pre s).strictTransform F).pts) :
    ∃ xt : 𝒮.removalFamilyStar.xTilde s,
      (𝒮.removalFamilyStar.xTilde s).dimAt xt = ((N - 1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨xh, hcx, -, -, xb, hxb, hι, -⟩ :=
    𝒮.exists_mem_xHatPrimeStar_and_jBar_le_maximalIdeal_pow_of_cond s x hx hF
  have hcx' : (𝒮.c s).base ((𝒮.xBar s).ι.base xb) = x := by rw [hι, hcx]
  exact 𝒮.removalFamilyStar.exists_dimAt_xTilde_eq_of_cond s xb hxb (hcx' ▸ hx)
    (fun F hr => hcx' ▸ hF F hr)

/-- `X̃ = X̄*'_s` is an ambient scheme of dimension `N - 1` when some point `x` of `X_s` satisfies
(1), (2), (3) of Lemma (AB.4) (and lies on `F(s)` in the closed case); see
`Frame.RemovalFamily.isAmbient_xTilde`. -/
theorem isAmbient_xTilde_removalFamilyStar_of_cond [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (x : T.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s x)
    (hF : ∀ F, r = .closed F → x ∈ ((T.pre s).strictTransform F).pts) :
    IsAmbient (𝒮.removalFamilyStar.xTilde s) (N - 1) :=
  𝒮.removalFamilyStar.isAmbient_xTilde s
    (𝒮.exists_dimAt_xTilde_removalFamilyStar_eq_of_cond s x hx hF)

end Frame

end AB

end Hironaka
