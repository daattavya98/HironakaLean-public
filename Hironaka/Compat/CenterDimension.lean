/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.DatumPresentation
public import Hironaka.Compat.StrictTransformDim
public import Hironaka.Ch0.NormalFlatness

/-!
# Dimension of the centers `B_s` of the final induction of Theorems A*, B* (pp. 309-310)

Ch. IV, p. 310: "applying Theorem `I₂^{N,n'}` (with `n' < n`) to the resolution datum
`(ℜ^{N,n'}_I(s), U_s)`", `n' = dim B_s`.  The paper does not prove `n' < n` (`n = dim W`).  This file
proves it for an irreducible closed subscheme `B` of the (transformed) principal subscheme `W` in the
two situations of the proof:

* closed case (`ℜ = (ℜ_I, F)`): `B ⊆ W ∩ F` and `W − F` is dense in `W`, so `B` lies in an irreducible
  component of `W` which is not contained in `F`; the inclusion is strict
  (`Subscheme.dim_lt_of_pts_subset_inter_of_subset_closure_diff`);
* open case (`ℜ = (ℜ_I, U)`): `B ⊆ W` is reduced irreducible, `(E; V_1, …, V_β, W; B)` is resolved at
  a point `x` of `B` at which `ℜ` is not resolved (`Subscheme.dim_lt_of_resolvedAt_extendBy_of_not_resolvedAt`):
  if `B` were a component of `W`, `W` would be normally flat along `B` at `x`, hence equal to `B`
  near `x`, and `ℜ` would be resolved at `x`.

The ingredients are `eq_of_isNormallyFlatAlongIdeal_of_mem_minimalPrimes` (a reduced scheme normally
flat along a component through a point coincides with it near the point) and
`Subscheme.dim_lt_of_ssubset_of_mem_irreducibleComponents` (dimension drops strictly from an irreducible
component to a proper irreducible closed subset).
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

section LocalRing

/-- In a noetherian ring, for a radical ideal `J` and a minimal prime `P` of `J`, every element of `P`
is killed modulo `J` by an element outside `P` (`J_P = 0` on `P`): `R_P/J_P` is a field. -/
theorem exists_notMem_mul_mem_of_mem_minimalPrimes {R : Type u} [CommRing R] [IsNoetherianRing R]
    {J P : Ideal R} (hJ : J.IsRadical) (hP : P ∈ J.minimalPrimes) {m : R} (hm : m ∈ P) :
    ∃ s ∉ P, s * m ∈ J := by
  classical
  have hfin : J.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing R J
  have hPprime : P.IsPrime := hP.1.1
  have hother : ∀ Q ∈ (hfin.toFinset.erase P), ∃ a ∈ Q, a ∉ P := by
    intro Q hQ
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hQ
    by_contra hcon
    push Not at hcon
    have hQP : Q ≤ P := fun a ha => hcon a ha
    exact hQ.1 (le_antisymm hQP (hP.2 ⟨hQ.2.1.1, hQ.2.1.2⟩ hQP))
  choose a ha hanP using hother
  let s : R := ∏ Q ∈ (hfin.toFinset.erase P).attach, a Q.1 Q.2
  refine ⟨s, ?_, ?_⟩
  · intro hs
    obtain ⟨Q, -, hQ⟩ := (Ideal.IsPrime.prod_mem_iff).mp hs
    exact hanP Q.1 Q.2 hQ
  · rw [← hJ.radical, ← Ideal.sInf_minimalPrimes]
    refine (Submodule.mem_sInf).mpr fun Q hQ => ?_
    by_cases hQP : Q = P
    · subst hQP
      exact Ideal.mul_mem_left _ _ hm
    · have hQ' : Q ∈ hfin.toFinset.erase P := by
        rw [Finset.mem_erase, Set.Finite.mem_toFinset]; exact ⟨hQP, hQ⟩
      refine Ideal.mul_mem_right _ _ ?_
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun Q' : (hfin.toFinset.erase P) => a Q'.1 Q'.2)
        (Finset.mem_attach _ ⟨Q, hQ'⟩)
      have hs : s = a Q hQ' * c := hc
      rw [hs]
      exact Ideal.mul_mem_right _ _ (ha Q hQ')

/-- A minimal prime `P` of a radical ideal `J` along which `R/J` is normally flat equals `J`, when
`gr^1_{P̄}(R/J) = P̄/P̄²` is a free module over the domain `R/P`, and it is killed
by elements outside `P̄` (`(R/J)_P` is a field), hence it is zero; so `P̄ = P̄²` and `P̄ = 0` by
Nakayama's lemma.  (A reduced scheme which is normally flat along a component through a point
coincides with it near the point.) -/
theorem eq_of_isNormallyFlatAlongIdeal_of_mem_minimalPrimes {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {J P : Ideal R} (hJ : J.IsRadical)
    (hP : P ∈ J.minimalPrimes)
    (hNF : IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J))) : J = P := by
  classical
  have hPprime : P.IsPrime := hP.1.1
  have hJP : J ≤ P := hP.1.2
  set O := R ⧸ J with hO
  set Pb : Ideal O := P.map (Ideal.Quotient.mk J) with hPb
  have hPbprime : Pb.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJP)
  have hJloc : J ≤ maximalIdeal R := hJP.trans (le_maximalIdeal hPprime.ne_top)
  have : IsLocalRing O := isLocalRing_quotient_of_le hJloc
  have hA : IsDomain (O ⧸ Pb) := (Ideal.Quotient.isDomain_iff_prime Pb).mpr hPbprime
  have hTF : Module.IsTorsionFree (O ⧸ Pb) (GrPiece Pb 1) := by
    have := hNF 1
    infer_instance
  -- `P̄/P̄² = 0`
  have hzero : Pb ≤ Pb ^ 2 := by
    intro m hm
    obtain ⟨m', -, rfl⟩ := Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective |>.mp hm
    obtain ⟨t, htP, htm⟩ := exists_notMem_mul_mem_of_mem_minimalPrimes hJ hP
      (show m' ∈ P from by
        obtain ⟨m'', hm'', hmm⟩ := Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective |>.mp hm
        have : m' - m'' ∈ J := by rw [← Ideal.Quotient.eq]; exact hmm.symm
        have h2 : m' = m'' + (m' - m'') := by ring
        rw [h2]; exact Ideal.add_mem _ hm'' (hJP this))
    have hmem : Ideal.Quotient.mk J m' ∈ Pb ^ 1 := by rw [pow_one]; exact hm
    have ht0 : (Ideal.Quotient.mk Pb (Ideal.Quotient.mk J t)) ≠ 0 := by
      intro h0
      rw [Ideal.Quotient.eq_zero_iff_mem] at h0
      have h1 : t ∈ Ideal.comap (Ideal.Quotient.mk J) Pb := h0
      rw [hPb, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hJP] at h1
      exact htP h1
    have hsm : (Ideal.Quotient.mk Pb (Ideal.Quotient.mk J t)) •
        (Submodule.Quotient.mk ⟨Ideal.Quotient.mk J m', hmem⟩ : GrPiece Pb 1) =
        (0 : GrPiece Pb 1) := by
      have h1 : (Ideal.Quotient.mk Pb (Ideal.Quotient.mk J t)) •
          (Submodule.Quotient.mk ⟨Ideal.Quotient.mk J m', hmem⟩ : GrPiece Pb 1) =
          (Ideal.Quotient.mk J t) •
            (Submodule.Quotient.mk ⟨Ideal.Quotient.mk J m', hmem⟩ : GrPiece Pb 1) :=
        IsScalarTower.algebraMap_smul (O ⧸ Pb) _ _
      rw [h1, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      show (Ideal.Quotient.mk J t) * (Ideal.Quotient.mk J m') ∈ Pb ^ (1 + 1)
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr htm]
      exact zero_mem _
    have hg : (Submodule.Quotient.mk ⟨Ideal.Quotient.mk J m', hmem⟩ : GrPiece Pb 1) = 0 := by
      exact (smul_eq_zero.mp hsm).resolve_left ht0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hg
    exact hg
  have hfg : Pb.FG := IsNoetherian.noetherian Pb
  have hle : Pb ≤ Pb • Pb := by rw [smul_eq_mul, ← pow_two]; exact hzero
  have hPbtop : Pb ≠ ⊤ := hPbprime.ne_top
  have hjac : Pb ≤ (⊥ : Ideal O).jacobson :=
    (le_maximalIdeal hPbtop).trans (maximalIdeal_le_jacobson _)
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot Pb Pb hfg hle hjac
  refine le_antisymm hJP (fun p hp => ?_)
  have : Ideal.Quotient.mk J p ∈ Pb := Ideal.mem_map_of_mem _ hp
  rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this
  
end LocalRing

namespace Subscheme

variable {X : Scheme.{u}}

/-- A closed irreducible subset `B` strictly contained in an irreducible component `C` of `D` has
smaller dimension than `D`, when `D` has finite dimension `≤ n`: the generic point of `C` lies strictly
above that of `B` in the specialization order. -/
theorem dim_lt_of_ssubset_of_mem_irreducibleComponents {D C B : Subscheme X}
    (hC : C ∈ D.irreducibleComponents) (hB : _root_.IsIrreducible B.pts) (hlt : B.pts ⊂ C.pts)
    {n : ℕ} (hn : D.dim ≤ n) : B.dim < n := by
  obtain ⟨Z, hZ, rfl⟩ := hC
  rw [pts_ofClosed] at hlt
  have hBcl : IsClosed B.pts := B.support.isClosed
  obtain ⟨ζ, hζ⟩ : ∃ ζ, IsGenericPoint ζ B.pts := QuasiSober.sober hB hBcl
  obtain ⟨γ, hγ⟩ : ∃ γ, IsGenericPoint γ (Z : Set X) := QuasiSober.sober hZ.1.1 Z.isClosed
  have hζB : ζ ∈ B.pts := hζ.mem
  have hγZ : γ ∈ (Z : Set X) := hγ.mem
  have hζlt : ζ < γ := by
    rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    refine ⟨?_, fun h => ?_⟩
    · exact hγ.specializes (hlt.1 hζB)
    · -- `ζ ⤳ γ` would put `γ` in `B`, hence `Z = closure {γ} ⊆ B`
      have hγB : γ ∈ B.pts := by
        rw [← hζ.def]; exact specializes_iff_mem_closure.mp h
      apply hlt.2
      intro z hz
      have : z ∈ closure ({γ} : Set X) := by rw [hγ.def]; exact hz
      exact hBcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hγB) this
  have h1 : Order.height ζ + 1 ≤ Order.height γ := Order.height_add_one_le hζlt
  have h2 : (Order.height γ : WithBot ℕ∞) ≤ n :=
    (StrictDim.height_le_dim D (hZ.1.2 hγZ)).trans hn
  have h2' : Order.height γ ≤ (n : ℕ∞) := by exact_mod_cast h2
  have h3 : Order.height ζ < (n : ℕ∞) := by
    have h4 : Order.height ζ + 1 ≤ (n : ℕ∞) := h1.trans h2'
    exact (ENat.add_one_le_iff' (ENat.natCast_ne_top n)).mp h4
  have h5 : B.dim ≤ Order.height ζ := by
    refine StrictDim.dim_le_of_forall B fun x hx => ?_
    have hx' : ζ ⤳ x := specializes_iff_mem_closure.mpr (by rw [hζ.def]; exact hx)
    have : x ≤ ζ := Scheme.le_iff_specializes.mpr hx'
    exact_mod_cast Order.height_mono this
  exact lt_of_le_of_lt h5 (by exact_mod_cast h3)

/-- An irreducible closed subset of `D` lies in an irreducible component of `D`. -/
theorem exists_mem_irreducibleComponents_pts_subset [NoetherianSpace X] {D B : Subscheme X}
    (hB : _root_.IsIrreducible B.pts) (hBD : B.pts ⊆ D.pts) :
    ∃ C ∈ D.irreducibleComponents, B.pts ⊆ C.pts := by
  have hfin := (finite_irreducibleComponents_of_noetherianSpace D).image fun C : Subscheme X => C.pts
  have hcl : ∀ A ∈ (fun C : Subscheme X => C.pts) '' D.irreducibleComponents, IsClosed A := by
    rintro _ ⟨C, -, rfl⟩
    exact C.support.isClosed
  have hsub : B.pts ⊆ ⋃₀ ((fun C : Subscheme X => C.pts) '' D.irreducibleComponents) := by
    intro y hy
    obtain ⟨C, hC, hyC⟩ := exists_mem_irreducibleComponents_of_mem_pts D (hBD hy)
    exact ⟨C.pts, ⟨C, hC, rfl⟩, hyC⟩
  obtain ⟨A, ⟨C, hC, rfl⟩, hBA⟩ := isIrreducible_subset_of_finite_sUnion hB hfin hcl hsub
  exact ⟨C, hC, hBA⟩

/-- **Closed case of `dim B_s < n`.**  If `W − F` is dense in `W` and the irreducible closed subset
`B` lies in `W ∩ F`, then `dim B < n` for every `n ≥ dim W`: `B` lies in a component of `W`, which is
not contained in `F`, so the inclusion is strict. -/
theorem dim_lt_of_pts_subset_inter_of_subset_closure_diff [NoetherianSpace X]
    {W F B : Subscheme X} (hB : _root_.IsIrreducible B.pts) (hBW : B.pts ⊆ W.pts)
    (hBF : B.pts ⊆ F.pts) (hdense : W.pts ⊆ closure (W.pts \ F.pts)) {n : ℕ} (hn : W.dim ≤ n) :
    B.dim < n := by
  obtain ⟨C, hC, hBC⟩ := exists_mem_irreducibleComponents_pts_subset hB hBW
  refine dim_lt_of_ssubset_of_mem_irreducibleComponents hC hB ⟨hBC, fun hCB => ?_⟩ hn
  exact not_pts_subset_of_mem_irreducibleComponents_of_subset_closure_diff hC hdense
    (hCB.trans hBF)

/-- **Open case of `dim B_s < n`.**  Let `ℜ` be a datum on a non-singular algebraic scheme, `B` a
reduced irreducible subscheme contained in `W`, and `x` a point of `B` at which `(ℜ; B)` (that is,
`(E; V_1, …, V_β, W; B)`) is resolved but `ℜ` is not.  Then `dim B < n` for every `n ≥ dim W`.
Otherwise `B` is an irreducible component of the reduced `W` through `x`, along which `W` is normally
flat at `x`, so `W = B` near `x` (`eq_of_isNormallyFlatAlongIdeal_of_mem_minimalPrimes`), and `ℜ` is
resolved at `x`. -/
theorem dim_lt_of_resolvedAt_extendBy_of_not_resolvedAt [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) {ℜ : DatumI.Raw X} (hℜ : ℜ.IsDatum) {B : Subscheme X}
    (hBred : B.IsReduced) (hBirr : B.IsIrreducible) (hBW : B.IsContainedIn ℜ.W) {x : X}
    (hx : x ∈ B.pts) (hres : (ℜ.extendBy B).ResolvedAt x) (hnres : ¬ ℜ.ResolvedAt x) {n : ℕ}
    (hn : ℜ.W.dim ≤ n) : B.dim < n := by
  classical
  have := IsAlgebraicScheme.noetherianSpace X
  have hBirr' : _root_.IsIrreducible B.pts := isIrreducible_pts B hBirr
  obtain ⟨C, hC, hBC⟩ := exists_mem_irreducibleComponents_pts_subset hBirr' (pts_subset_of_isContainedIn hBW)
  by_cases heq : B.pts = C.pts
  swap
  · exact dim_lt_of_ssubset_of_mem_irreducibleComponents hC hBirr' ⟨hBC, fun h => heq (Set.Subset.antisymm hBC h)⟩ hn
  exfalso
  have hBC' : B = C := eq_of_pts_eq_of_isReduced hBred (isReduced_of_mem_irreducibleComponents hC) heq
  subst hBC'
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  obtain ⟨hBsimple, hNFall, hNC⟩ := hres
  have hWred : ℜ.W.IsReduced := hℜ.2.2.2.1
  have hWx : x ∈ ℜ.W.pts := pts_subset_of_isContainedIn hBW hx
  -- normal flatness of `W` along `B` at `x`
  have hNFW : IsNormallyFlatAlongIdeal ((B.stalkIdeal x).map (Ideal.Quotient.mk (ℜ.W.stalkIdeal x))) := by
    have h := hNFall (Fin.last ℜ.β)
    have h' : IsNormallyFlatAlongAt' ℜ.W B x := by simpa [DatumI.Raw.extendBy] using h
    exact ((isNormallyFlatAlongAt'_iff ℜ.W B hBW x).mp h').2
  have hBprime : (B.stalkIdeal x).IsPrime := isPrime_stalkIdeal_of_isSimpleAt hBsimple
  have hmin : B.stalkIdeal x ∈ (ℜ.W.stalkIdeal x).minimalPrimes := stalkIdeal_mem_minimalPrimes hC hx
  have hstalk : ℜ.W.stalkIdeal x = B.stalkIdeal x :=
    eq_of_isNormallyFlatAlongIdeal_of_mem_minimalPrimes
      (isRadical_stalkIdeal_of_isReduced hWred x) hmin hNFW
  apply hnres
  refine ⟨⟨hWx, ?_⟩, fun j => ?_, ?_⟩
  · rw [hstalk]; exact hBsimple.2
  · have hWV : ℜ.W.IsContainedIn (ℜ.V j) := hℜ.2.2.2.2 j
    have hBV : B.IsContainedIn (ℜ.V j) := hBW.trans hWV
    have h := hNFall (Fin.castSucc j)
    have h' : IsNormallyFlatAlongAt' (ℜ.V j) B x := by simpa [DatumI.Raw.extendBy] using h
    obtain ⟨-, h2⟩ := (isNormallyFlatAlongAt'_iff (ℜ.V j) B hBV x).mp h'
    exact (isNormallyFlatAlongAt'_iff (ℜ.V j) ℜ.W hWV x).mpr ⟨hWx, by rw [hstalk]; exact h2⟩
  · obtain ⟨z, hz, hcomp, t, htz, ht⟩ := hNC
    exact ⟨z, hz, hcomp, t, htz, by rw [hstalk]; exact ht⟩

end Subscheme

end Hironaka
