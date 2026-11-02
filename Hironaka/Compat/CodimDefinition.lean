/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
public import Architect
public import Hironaka.Ch0.AlgebraicScheme
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Compat.ComponentStalk

/-!
# The codimension of a subscheme: the printed definition (Ch. I, p. 163)

> If W is not empty, then we define the codimension of W in V to be the minimum of dim_x(V) for all
> the points x of W. If x is a point of W, then the codimension of W in V at x is defined to be the
> codimension of Spec(O_{W,x}) in Spec(O_{V,x}) where the first spectrum is viewed in a canonical way as
> a subscheme of the second. We can see that the codimension of W in V is equal to the minimum of the
> codimensions of W in V at the points of W, provided W is not empty.  (p. 163)

`Subscheme.codim` (`Hironaka/Ch0/AlgebraicScheme.lean`) is the second characterization, the minimum of
the codimensions `codimAt` at the points of `W`.  The printed definition is `⨅_{x ∈ W} dim_x(V)`, with
`dim_x(V) = dim O_{V,x}` (`Scheme.dimAt`); this file proves that the two agree
(`Subscheme.isLeast_dimAt_codim`), as the paper says "we can see".

Deviation from the paper (gap filled): the paper gives no argument.  Proof: `codim_x(W) = ht(W_x) ≤
dim O_{V,x}` gives `codim W ≤ dim_x(V)` for every `x ∈ W`.  Conversely, `ht(W_x)` is the height of a minimal
prime `q` of `W_x`, which is the ideal at `x` of an irreducible component `C` of `W` through `x`; the
generic point `ξ` of `C` lies in `W` and `O_{V,ξ} = (O_{V,x})_q`, so `dim_ξ(V) = ht q = ht(W_x)`.  No
noetherian hypothesis is needed.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

namespace Subscheme

variable {X : Scheme.{u}}

/-- For `x ∈ W` there is a point `ξ ∈ W` with `dim_ξ(V) = codim_x(W)`: the generic point of an irreducible
component of `W` through `x` whose ideal at `x` is a minimal prime of `W_x` of minimal height. -/
theorem exists_mem_pts_dimAt_eq_codimAt (W : Subscheme X) {x : X} (hx : x ∈ W.pts) :
    ∃ ξ ∈ W.pts, X.dimAt ξ = (W.codimAt x : WithBot ℕ∞) := by
  have hne : W.stalkIdeal x ≠ ⊤ := mem_pts_iff_stalkIdeal_ne_top.mp hx
  -- a minimal prime of `W_x` of minimal height
  have hmin : (W.stalkIdeal x).minimalPrimes.Nonempty := by
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le hle
    exact ⟨q, hq⟩
  obtain ⟨q, hq, hqh⟩ : ∃ q ∈ (W.stalkIdeal x).minimalPrimes, q.height = (W.stalkIdeal x).height := by
    set S : Set ℕ∞ := (fun q : Ideal (X.presheaf.stalk x) => q.height) '' (W.stalkIdeal x).minimalPrimes
      with hS
    have hSne : S.Nonempty := hmin.image _
    have h1 : (W.stalkIdeal x).height = sInf S := by
      rw [Ideal.height_eq_inf_minimalPrimes, hS, sInf_image]
    obtain ⟨q, hq, hqS⟩ := csInf_mem hSne
    exact ⟨q, hq, hqS.trans h1.symm⟩
  obtain ⟨C, hC, hxC, hCq⟩ := exists_mem_irreducibleComponents_of_mem_minimalPrimes W x hq
  obtain ⟨Z, ⟨⟨hZirr, hZW⟩, -⟩, rfl⟩ := hC
  have hCpts : (Subscheme.ofClosed Z).pts = Z := pts_ofClosed Z
  obtain ⟨ξ, hξ⟩ : ∃ ξ, IsGenericPoint ξ (Subscheme.ofClosed Z).pts := by
    rw [hCpts]
    exact QuasiSober.sober hZirr Z.isClosed
  have hprime : ((Subscheme.ofClosed Z).stalkIdeal x).IsPrime := by
    rw [hCq]; exact hq.1.1
  obtain ⟨e⟩ := nonempty_stalk_equiv_localization_of_isGenericPoint (Subscheme.ofClosed Z) hξ hxC
  refine ⟨ξ, hZW (hCpts ▸ hξ.mem), ?_⟩
  show ringKrullDim (X.presheaf.stalk ξ) = _
  rw [ringKrullDim_eq_of_ringEquiv e,
    IsLocalization.AtPrime.ringKrullDim_eq_height ((Subscheme.ofClosed Z).stalkIdeal x)
      (Localization.AtPrime ((Subscheme.ofClosed Z).stalkIdeal x)), hCq, hqh]
  rfl

/-- p. 163: "the codimension of `W` in `V` [is] the minimum of `dim_x(V)` for all the points `x` of `W`",
and "we can see that [it] is equal to the minimum of the codimensions of `W` in `V` at the points of `W`":
for a non-empty `W`, `Subscheme.codim W` is the least of the dimensions `dim_x(V)`, `x ∈ W`.

Deviation from the paper (gap filled): the paper says "we can see". -/
@[blueprint "def:I.0-codimension-printed"
  (statement := /-- Let $W$ be a non-empty subscheme of $V$. Then the minimum of $\dim_x(V)$ for all the
    points $x$ of $W$ exists and equals the minimum of the codimensions of $W$ in $V$ at the points of
    $W$ (\cref{def:I.0-codimension}). (p.~163.)
    \textbf{Gap in the paper filled.} The paper: ``we can see''. -/)
  (proof := /-- For $x\in W$, $\operatorname{codim}_x(W)=\operatorname{ht}(W_x)\le\dim\mathcal O_{V,x}$.
    Conversely $\operatorname{ht}(W_x)$ is the height of a minimal prime $q$ of $W_x$, which is the ideal
    at $x$ of an irreducible component $C$ of $W$ through $x$; the generic point $\xi$ of $C$ lies in $W$
    and $\mathcal O_{V,\xi}=(\mathcal O_{V,x})_q$, so $\dim_\xi(V)=\operatorname{ht}(q)$. -/)
  (latexEnv := "lemma")]
theorem isLeast_dimAt_codim (W : Subscheme X) (hW : W.pts.Nonempty) :
    IsLeast {d : WithBot ℕ∞ | ∃ x ∈ W.pts, X.dimAt x = d} (W.codim : WithBot ℕ∞) := by
  -- `codim W` is attained at some point
  obtain ⟨x₀, hx₀, hx₀c⟩ : ∃ x₀ ∈ W.pts, W.codimAt x₀ = W.codim := by
    set S : Set ℕ∞ := (fun x => W.codimAt x) '' W.pts with hS
    have hSne : S.Nonempty := hW.image _
    have h1 : W.codim = sInf S := by
      rw [codim, hS, sInf_image]
    obtain ⟨x₀, hx₀, hx₀S⟩ := csInf_mem hSne
    exact ⟨x₀, hx₀, hx₀S.trans h1.symm⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨ξ, hξ, hξd⟩ := exists_mem_pts_dimAt_eq_codimAt W hx₀
    exact ⟨ξ, hξ, by rw [hξd, hx₀c]⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hne : W.stalkIdeal x ≠ ⊤ := mem_pts_iff_stalkIdeal_ne_top.mp hx
    calc ((W.codim : ℕ∞) : WithBot ℕ∞) ≤ (W.codimAt x : WithBot ℕ∞) :=
          WithBot.coe_le_coe.mpr (iInf₂_le x hx)
      _ ≤ X.dimAt x := Ideal.height_le_ringKrullDim_of_ne_top hne

end Subscheme

end Hironaka
