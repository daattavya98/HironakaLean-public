/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Architect
public import Hironaka.Ch4.CorollaryLocallyFree
public import Hironaka.Compat.PullbackInvertibleSubsheaf
public import Hironaka.Statements

/-!
# Ch. 0 §5 (pp. 145-146): Corollary 2 of Main Theorem II

> **Corollary 2.**  Let `X` be the same as in the above Corollary 1.  We assume that `X` is irreducible.  Let `F` be a
> locally free sheaf of `O_X`-modules which is coherent.  Then there exists a morphism `f : X' → X` obtained by a
> finite succession of monoidal transformation with non-singular and nowhere dense centers, such that the inverse
> image `f*(F)` contains an invertible subsheaf of `O_{X'}`-modules `L` with a locally free quotient sheaf
> `f*(F)/L`.  (pp. 145-146)

The printed proof (p. 145): "In fact, this follows from the above Corollary 1 of main theorem II.  To see this, we
first remark that any locally free coherent sheaf `F` contains an invertible sheaf of `O_X`-modules `M`.  [...]  Let
`J` be the coherent sheaf of ideals on `X` which is defined as follows: [...] `J_x = (h_1, …, h_r) O_{X,x}`.  To this
sheaf of ideals `J` on `X`, we apply Corollary 1 of main theorem II in which `e = 1`.  We let `f : X' → X` be the
composition of a succession of monoidal transformations which we find according to Corollary 1.  We then obtain an
invertible subsheaf `L` of `f*(F)` such that `f*(M) = f^{-1}(J)L`, where `f*(M)` is viewed as a subsheaf of `f*(F)`
in a natural manner.  We can easily see that `f*(F)/L` is locally free on `X'`."

The proof is formalized in the steps of the printed one:

* `Modules.exists_isInvertible_mono` (`Hironaka/Compat/InvertibleSubsheaf.lean`): `F` contains an invertible `M`;
* `coordSubscheme` (`Hironaka/Compat/CoordinateIdeal.lean`): the sheaf of ideals `J`, independent of the bases;
* `exists_isTrivializing_coordSubscheme` (`Hironaka/Ch4/CorollaryLocallyFree.lean`): Corollary 1 with `e = 1`, with
  nowhere dense centers;
* `isInvertibleIdeal_totalTransform_composite` (`Hironaka/Compat/TotalTransformInvertible.lean`): `f⁻¹(J)` is
  invertible;
* `PullbackDatum` (`Hironaka/Compat/PullbackDatum.lean`): locally `f^♯ h_j = g h'_j` with `(h'_j)` unimodular;
* `pullback_map_app_injective`, `localImageModule` (`Hironaka/Compat/PullbackInvertibleSubsheaf.lean`):
  `f*(M) → f*(F)` is injective on sections and `L` is generated locally by `e = ∑ h'_j f*(c_j)`;
* `isFrame_cokernel` (`Hironaka/Compat/FrameModifications.lean`): `f*(F)/L` is locally free.

**Deviation from the paper (gaps filled, tacit hypotheses).**  The remark "any locally free coherent sheaf contains an
invertible sheaf", the independence of `J` of the bases and its coherence, the injectivity of
`f*(M) → f*(F)`, the invertibility of `f⁻¹(J)` and the form of `L`, "we can easily see that `f*(F)/L` is
locally free", the nowhere density of the centers and the use of Corollary 1 with `e = 1` are not
argued in the paper.  The hypothesis `F ≠ 0` (rank `≥ 1`) is tacit: for `F = 0` the statement is false.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace Opposite
open Hironaka.Scheme.Modules AlgebraicGeometry.Scheme.Modules

namespace Hironaka

universe u

/-- On a non-singular irreducible scheme the local rings are reduced, so the scheme is integral. -/
theorem isIntegral_of_isNonsingular_of_irreducibleSpace (Z : Scheme.{u}) [IrreducibleSpace Z]
    (hZ : Z.IsNonsingular) : IsIntegral Z := by
  have hred : ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x) := fun x => by
    have : IsRegularLocalRing (Z.presheaf.stalk x) := hZ x
    have := isDomain_of_isRegularLocalRing (Z.presheaf.stalk x)
    infer_instance
  have : IsReduced Z := isReduced_of_isReduced_stalk Z
  exact isIntegral_of_irreducibleSpace_of_isReduced Z

namespace MainTheorem.Ch0

/-- **Corollary 2 of Main Theorem II** (pp. 145-146), for an algebraic scheme.

Formalization notes (encoding): "locally free sheaf of `𝒪_X`-modules which is coherent" is Mathlib's
`IsLocallyFree` together with `IsFiniteType` (equivalent to local frames, `hasLocalFrames_iff`); "inverse image" is
`(Scheme.Modules.pullback s.composite).obj F`; "contains an invertible subsheaf `L`" is a monomorphism
`i : L ⟶ f*F` with `IsInvertible L` (locally free of rank one, by one-element frames); "`f*(F)/L` locally free" is
`cokernel i` locally free and of finite type; "irreducible" is `[IrreducibleSpace X]` (so `X` is non-empty);
`¬ IsZero F` is the tacit hypothesis `F ≠ 0` (equivalently rank `≥ 1`).  The statement is for algebraic schemes
(p. 151); the printed form is `exists_isInvertible_subsheaf_pullback`. -/
theorem exists_isInvertible_subsheaf_pullback_of_isAlgebraicScheme [Hironaka.HironakaCitedResultsCh0.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X]
    [IrreducibleSpace X] (hX : X.IsNonsingular) (F : X.Modules) [F.IsLocallyFree] [F.IsFiniteType]
    (hF : ¬ IsZero F) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsNowhereDense ∧
      ∃ (L : Y.Modules) (i : L ⟶ (Scheme.Modules.pullback s.composite).obj F),
        Mono i ∧ IsInvertible L ∧ (cokernel i).IsLocallyFree ∧ (cokernel i).IsFiniteType := by
  classical
  have hXn : IsLocallyNoetherian X := (IsAlgebraicScheme.isNoetherian X).toIsLocallyNoetherian
  have hXi : IsIntegral X := isIntegral_of_isNonsingular_of_irreducibleSpace X hX
  have hFf : HasLocalFrames F := hasLocalFrames_of_isLocallyFree F
  obtain ⟨M, i, hmono, hMinv⟩ := Modules.exists_isInvertible_mono hX hFf hF
  obtain ⟨Y, s, hnd, hs⟩ := exists_isTrivializing_coordSubscheme X hX i hFf hMinv
  have hJne : ∀ x, (coordSubscheme i hFf hMinv).stalkIdeal x ≠ ⊥ := fun x => by
    rw [stalkIdeal_coordSubscheme]
    exact coordStalkIdeal_ne_bot i hFf hMinv x
  obtain ⟨hYa, hYi, hY⟩ := s.isAmbient_of_isTrivializingSteps (le_refl 1) inferInstance inferInstance hX
    (fun _ : Fin 1 => coordSubscheme i hFf hMinv) (fun _ x => hJne x) hs.1
  have hYint : IsIntegral Y := isIntegral_of_isNonsingular_of_irreducibleSpace Y hY
  have hfin : ∀ z, (s.weakTransformFamily (fun _ : Fin 1 => coordSubscheme i hFf hMinv) 0).stalkIdeal z = ⊤ :=
    fun z => by
      obtain ⟨j, hj⟩ := hs.2 z
      rwa [Subsingleton.elim j 0] at hj
  have hinv := s.isInvertibleIdeal_totalTransform_composite inferInstance hX (coordSubscheme i hFf hMinv)
    hJne hs.1 hfin
  let f := s.composite
  have hδ : ∀ y, Nonempty (PullbackDatum f i y) := fun y =>
    PullbackDatum.nonempty f i hFf hMinv hinv y
  have hinj := pullback_map_app_injective hδ
  let U0 : Y.Opens := f ⁻¹ᵁ trivialLocus (coordSubscheme i hFf hMinv)
  have hU0 : Nonempty U0 :=
    ⟨⟨genericPoint Y, genericPoint_mem_preimage_trivialLocus _ f hinv⟩⟩
  have hne : ∀ T : Y.Opens, Nonempty T → Nonempty (T ⊓ U0 : Y.Opens) := fun T hT =>
    nonempty_inf_of_irreducible T U0
  have hgU : ∀ (y : Y) (δ : PullbackDatum f i y) (z : Y) (hz : z ∈ δ.V'), z ∈ U0 →
      IsUnit ((Y.presheaf.germ δ.V' z hz).hom δ.g) := fun y δ z hz hzU =>
    δ.isUnit_germ_g hFf hMinv hz ((mem_trivialLocus_iff _ _).mp hzU)
  let φ := (Scheme.Modules.pullback f).map i
  have hframes : ∀ y : Y, ∃ (V₀ : Y.Opens) (_ : y ∈ V₀) (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
      (c' : ι → Γ((Scheme.Modules.pullback f).obj F, V₀)) (j₀ : ι)
      (ε : Γ(localImageModule φ U0 hinj, V₀)),
      IsFrame ((Scheme.Modules.pullback f).obj F) V₀ c' ∧
      IsFrame (localImageModule φ U0 hinj) V₀ (fun _ : PUnit.{u + 1} => ε) ∧
      (localImageι φ U0 hinj).app V₀ ε = c' j₀ := by
    intro y
    obtain ⟨V₀, hy, c', j₀, ε, h1, h2, h3⟩ := (hδ y).some.exists_frames U0 hne (hgU y (hδ y).some) hinj
    exact ⟨V₀, hy, _, (hδ y).some.fintype, Classical.decEq _, c', j₀, ε, h1, h2, h3⟩
  refine ⟨Y, s, hnd, localImageModule φ U0 hinj, localImageι φ U0 hinj, ?_, ?_, ?_⟩
  · exact Modules.mono_ofSubmoduleι _ _ _ _
  · intro y
    obtain ⟨V₀, hy, ι, _, _, c', j₀, ε, h1, h2, h3⟩ := hframes y
    exact ⟨V₀, hy, ε, h2⟩
  · have : HasLocalFrames (cokernel (localImageι φ U0 hinj)) := by
      intro y
      obtain ⟨V₀, hy, ι, _, _, c', j₀, ε, h1, h2, h3⟩ := hframes y
      exact ⟨V₀, hy, {k // k ≠ j₀}, inferInstance, _, isFrame_cokernel h1 j₀ _ h2 h3⟩
    exact (hasLocalFrames_iff _).mp this

/-- **Corollary 2 of Main Theorem II**, printed form (pp. 145-146): `X` a non-singular irreducible algebraic `B`-scheme
(not necessarily separated: the statement is more general than the printed one), `B` a field of characteristic zero,
`F ≠ 0` a locally free coherent sheaf. -/
@[blueprint "cor:0.5-locally-free"
  (statement := /-- \textbf{Corollary 2.} Let $X$ be a non-singular algebraic scheme which is irreducible. Let $F$
    be a locally free sheaf of $\mathcal O_X$-modules which is coherent (and non-zero). Then there exists a morphism
    $f\colon X'\to X$ obtained by a finite succession of monoidal transformations with non-singular and nowhere dense
    centers, such that the inverse image $f^*(F)$ contains an invertible subsheaf of $\mathcal O_{X'}$-modules $L$
    with a locally free quotient sheaf $f^*(F)/L$. (pp.~145--146.)
    Formalization note (encoding): locally free and coherent is \texttt{IsLocallyFree} with \texttt{IsFiniteType};
    $F\ne0$ is a tacit hypothesis. Deviation from the paper (more general statement): $X$ is not required to be
    separated (the paper's schemes are, p.~118). -/)
  (proof := /-- As printed (p.~145): $F$ contains an invertible subsheaf $M$; let $J_x=(h_1,\dots,h_r)\mathcal
    O_{X,x}$ be the ideal of the coordinates of a generator of $M_x$ in a basis of $F_x$ (independent of the bases);
    apply \cref{cor:0.3-trivialization} with $e=1$ to $J$: $f^{-1}(J)\mathcal O_{X'}$ is then invertible, locally
    generated by $g$ with $f^\sharp h_j=g h'_j$, the $h'_j$ generating the unit ideal, and $L$ is generated by
    $\sum h'_jf^*(c_j)$, which is part of a basis of $f^*(F)$, so $f^*(F)/L$ is locally free.
    \textbf{Gaps in the paper filled.} The existence of $M$ (by the unique factorization of the regular local rings,
    \cref{lem:regular-local-ring-ufd}), the independence and coherence of $J$, the injectivity of $f^*(M)\to
    f^*(F)$, the form of $L$, the nowhere density of the centers and the local freeness of the quotient are not
    argued; $F\ne0$ is tacit. -/)
  (proofUses := ["cor:0.3-trivialization", "lem:regular-local-ring-ufd"])
  (latexEnv := "corollary")]
theorem exists_isInvertible_subsheaf_pullback [Hironaka.HironakaCitedResultsCh0.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType p] [QuasiCompact p] [IrreducibleSpace X]
    (hX : X.IsNonsingular) (F : X.Modules) [F.IsLocallyFree] [F.IsFiniteType] (hF : ¬ IsZero F) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsNowhereDense ∧
      ∃ (L : Y.Modules) (i : L ⟶ (Scheme.Modules.pullback s.composite).obj F),
        Mono i ∧ IsInvertible L ∧ (cokernel i).IsLocallyFree ∧ (cokernel i).IsFiniteType :=
  haveI := IsAlgebraicScheme.of_field p
  exists_isInvertible_subsheaf_pullback_of_isAlgebraicScheme X hX F hF

end MainTheorem.Ch0

end Hironaka
