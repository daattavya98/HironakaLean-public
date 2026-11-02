/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Architect
public import Hironaka.Compat.RegularLocusFlatDescent
public import Hironaka.Compat.FlatLocalRegularity
public import Hironaka.Compat.AdicCompletionRegular
public import Hironaka.Compat.RingPushoutSquares

/-!
# Compatibility layer: descent along the completion of a flat local extension (property (c))

Footnote 31 (p. 161): "Reduce the proof to the case in which S is complete".  Let `R → R'` be a
flat local homomorphism of noetherian local rings such that `R'` satisfies condition (ii) of the
class 𝔅 (`HasCompletionRegularLocus R'`).  For a finite type `R`-algebra `C`, consider
`Y = C ⊗_R R̂`, `E = R' ⊗_R C` and `X = E ⊗_{R'} R̂'`.  By the flat local map `R̂ → R̂'`
(footnote 3, p. 116, cited as `exists_flat_isLocalHom_adicCompletion_of_flat`), `Y → X` is
faithfully flat (a base change of `R̂ → R̂'`, `X` also being a pushout of `C` and `R̂'` over `R`).
If a prime `q` of `Y` lies over a regular prime of `C` and the primes of `E` over regular primes
of `C` are regular (the hypothesis `H`), a prime `q'` of `X` over `q` is regular by (ii) for `R'`,
hence `q` is regular by descent of regularity along the flat map `Y → X`.
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

noncomputable section

namespace Hironaka

universe u

section Descent

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {R' : Type u} [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Algebra R R']
  [Module.Flat R R'] [IsLocalHom (algebraMap R R')]
  {C : Type u} [CommRing C] [Algebra R C] [Algebra.FiniteType R C]

/-- **Descent along the completion of a flat local extension.**  Let `R → R'` be a flat local
homomorphism of noetherian local rings with `R'` satisfying condition (ii) of p. 161, and `C` a
finite type `R`-algebra such that every prime of `R' ⊗_R C` lying over a regular prime of `C` is
regular (`H`).  Then every prime `q` of `C ⊗_R R̂` over a regular prime of `C` is regular.

Deviation from the paper (gap filled): footnote 31 (p. 161) only says "Reduce the proof to the case
in which S is complete".  This is the descent step of that reduction . -/
@[blueprint "lem:class-A-c-descent-completion"
  (statement := /-- Let $R\to R'$ be a flat local homomorphism of noetherian local rings such that
    $R'$ satisfies condition (ii) of the class $\mathfrak B$, and let $C$ be a finite type
    $R$-algebra such that every prime of $R'\otimes_RC$ lying over a regular prime of $C$ is
    regular. Then every prime of $C\otimes_R\hat R$ lying over a regular prime of $C$ is
    regular. -/)
  (proof := /-- By \cref{lem:completion-flat-local} the induced map $\hat R\to\hat R'$ is a flat
    local, hence faithfully flat, homomorphism. Put $Y=C\otimes_R\hat R$, $E=R'\otimes_RC$ and
    $X=E\otimes_{R'}\hat R'$; then $X$ is also the pushout of $C$ and $\hat R'$ over $R$, hence
    the base change of $\hat R\to\hat R'$ along $\hat R\to Y$, and $Y\to X$ is faithfully flat. A
    prime $q$ of $Y$ lying over a regular prime of $C$ is the contraction of a prime $q'$ of $X$.
    The contraction of $q'$ to $E$ is regular by hypothesis, so $q'$ is regular by condition (ii)
    for $R'$. By descent of regularity along the flat local map $Y_q\to X_{q'}$
    (\cref{lem:regular-descent-flat-local}), $q$ is regular.
    \textbf{Deviation from the paper (gap filled).} Footnote~31 only says ``Reduce the proof to
    the case in which S is complete''. -/)
  (proofUses := ["lem:completion-flat-local", "lem:regular-locus-flat-descent"])
  (latexEnv := "lemma")]
theorem mem_regularLocus_tensor_adicCompletion_of_fibre [Hironaka.Cited.ExistsFlatIsLocalHomAdicCompletionOfFlat.{u}] [Hironaka.Cited.IsRegularLocalRingOfFlatOfIsRegularLocalRing.{u}] (hR' : HasCompletionRegularLocus R')
    (H : ∀ Q : PrimeSpectrum (R' ⊗[R] C),
      PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := C)).toRingHom Q ∈
          regularLocus C → Q ∈ regularLocus (R' ⊗[R] C))
    (q : PrimeSpectrum (C ⊗[R] AdicCompletion (maximalIdeal R) R))
    (hq : PrimeSpectrum.comap (algebraMap C (C ⊗[R] AdicCompletion (maximalIdeal R) R)) q ∈
      regularLocus C) :
    q ∈ regularLocus (C ⊗[R] AdicCompletion (maximalIdeal R) R) := by
  classical
  obtain ⟨φ, hφc, hφflat, hφloc⟩ :=
    exists_flat_isLocalHom_adicCompletion_of_flat (R := R) (R' := R')
  -- the three tensor squares
  have Q2 := IsRingPushout.tensorProduct R R' C
  have Z := IsRingPushout.tensorProduct R' (R' ⊗[R] C) (AdicCompletion (maximalIdeal R') R')
  have Y1 := IsRingPushout.tensorProduct R C (AdicCompletion (maximalIdeal R) R)
  have X1 := IsRingPushout.paste_horiz Q2 Z.flip
  have hw : ((Algebra.TensorProduct.includeLeftRingHom :
        (R' ⊗[R] C) →+* (R' ⊗[R] C) ⊗[R'] AdicCompletion (maximalIdeal R') R').comp
      (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := C)).toRingHom).comp
      (algebraMap R C) =
      ((Algebra.TensorProduct.includeRight (R := R') (A := R' ⊗[R] C)
        (B := AdicCompletion (maximalIdeal R') R')).toRingHom.comp φ).comp
        (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
    ext r
    have h1 := congr($(Q2.comm) r)
    have h2 := congr($(Z.comm) (algebraMap R R' r))
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [← h1, hφc r]
    exact h2
  obtain ⟨ι, hι1, hι2⟩ := Y1.exists_desc _ _ hw
  have e1 : φ.comp (algebraMap R (AdicCompletion (maximalIdeal R) R)) =
      (algebraMap R' (AdicCompletion (maximalIdeal R') R')).comp (algebraMap R R') := by
    exact RingHom.ext fun r => hφc r
  have W : IsRingPushout φ
      (Algebra.TensorProduct.includeRight (R := R) (A := C)
        (B := AdicCompletion (maximalIdeal R) R)).toRingHom
      (Algebra.TensorProduct.includeRight (R := R') (A := R' ⊗[R] C)
        (B := AdicCompletion (maximalIdeal R') R')).toRingHom ι := by
    refine IsRingPushout.of_left (h₁₁ := algebraMap R (AdicCompletion (maximalIdeal R) R))
      (h₂₁ := Algebra.TensorProduct.includeLeftRingHom) ?_ Y1.flip hι2.symm
    rw [e1, hι1]
    exact X1
  have hφff : φ.FaithfullyFlat := by
    algebraize [φ]
    have h1 : IsLocalHom (algebraMap (AdicCompletion (maximalIdeal R) R)
        (AdicCompletion (maximalIdeal R') R')) := by
      rw [RingHom.algebraMap_toAlgebra]
      exact hφloc
    rw [← RingHom.algebraMap_toAlgebra φ, RingHom.faithfullyFlat_algebraMap_iff]
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hι : ι.FaithfullyFlat := W.faithfullyFlat hφff
  obtain ⟨q', hq'⟩ := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hι).2 q
  -- `q'` is regular, by condition (ii) for `R'` and the fibre hypothesis
  have hq'reg : q' ∈ regularLocus ((R' ⊗[R] C) ⊗[R'] AdicCompletion (maximalIdeal R') R') := by
    refine (hR' (R' ⊗[R] C) q').mpr (H _ ?_)
    have hc : PrimeSpectrum.comap (Algebra.TensorProduct.includeRight (R := R) (A := R')
        (B := C)).toRingHom (PrimeSpectrum.comap (algebraMap (R' ⊗[R] C)
          ((R' ⊗[R] C) ⊗[R'] AdicCompletion (maximalIdeal R') R')) q') =
        PrimeSpectrum.comap (algebraMap C (C ⊗[R] AdicCompletion (maximalIdeal R) R)) q := by
      rw [← hq', ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
      congr 1
      exact hι1.symm
    rw [hc]
    exact hq
  -- descent along the flat map `ι`
  have hYfin : (Algebra.TensorProduct.includeRight (R := R) (A := C)
      (B := AdicCompletion (maximalIdeal R) R)).toRingHom.FiniteType :=
    Y1.finiteType (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hYnoeth : IsNoetherianRing (C ⊗[R] AdicCompletion (maximalIdeal R) R) := by
    algebraize [(Algebra.TensorProduct.includeRight (R := R) (A := C)
      (B := AdicCompletion (maximalIdeal R) R)).toRingHom]
    have := isNoetherianRing_adicCompletion_of_isNoetherianRing (maximalIdeal R)
    exact Algebra.FiniteType.isNoetherianRing (AdicCompletion (maximalIdeal R) R) _
  have hιflat : ι.Flat := hι.flat
  algebraize [ι]
  have key := comap_mem_regularLocus_of_mem_regularLocus_of_flat
    (C ⊗[R] AdicCompletion (maximalIdeal R) R) ((R' ⊗[R] C) ⊗[R'] AdicCompletion
      (maximalIdeal R') R') q' hq'reg
  rw [RingHom.algebraMap_toAlgebra, hq'] at key
  exact key

end Descent

end Hironaka
