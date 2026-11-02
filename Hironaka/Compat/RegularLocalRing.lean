/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Statements

/-!
# Compatibility layer: regular local rings and the order function ν_M(J)

Hironaka works with "regular local rings" and "regular systems of parameters" in the sense
of Zariski–Samuel / Nagata, and with the order ν_M(J) (Ch. I §1, p. 165):

> Let S be a commutative ring with unity, M and J ideals in S. Then we denote by ν_M(J) the
> largest integer ν, if it exists, such that M^ν ⊇ J. (If it does not exist, we let ν_M(J) be
> infinity.) In particular, if S is local and M is the maximal ideal of S, then we write ν(J).

Mathlib ships `IsRegularLocalRing` (Mathlib.RingTheory.RegularLocalRing.Defs: a noetherian local
ring with `(maximalIdeal R).spanFinrank = ringKrullDim R`), and we use it throughout.  Hironaka's
formulation "noetherian and admits a regular system of parameters" is the bridge lemma
`isRegularLocalRing_iff_exists_rsop` below.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section RegularSystems

variable (R : Type u) [CommRing R] [IsLocalRing R]


/-- A local ring is regular (Zariski–Samuel) iff it is noetherian and admits a regular system of
parameters.  This is the notion Hironaka calls "simple", following Grothendieck's absolute sense
(footnote 29, p. 161); the left-hand side is Mathlib's `IsRegularLocalRing`. -/
@[blueprint "lem:regular-local-ring-iff-rsop"
  (statement := /-- A local ring $R$ is regular (i.e. noetherian with $\dim R$ equal to the
    minimal number of generators of its maximal ideal) if and only if it is noetherian and admits
    a regular system of parameters (\cref{def:rsop}). -/)
  (latexEnv := "lemma")]
theorem isRegularLocalRing_iff_exists_rsop :
    IsRegularLocalRing R ↔ IsNoetherianRing R ∧ ∃ s : Finset R, IsRegularSystemOfParameters R s := by
  constructor
  · intro h
    refine ⟨inferInstance, ?_⟩
    -- pick a generating set of the maximal ideal of minimal size `spanFinrank`
    obtain ⟨s, hcard, hspan⟩ :=
      (IsNoetherian.noetherian (maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
    exact ⟨s, hspan, by rw [hcard]; exact h.spanFinrank_maximalIdeal⟩
  · rintro ⟨hN, s, hspan, hcard⟩
    -- `s` generates the maximal ideal, so `spanFinrank ≤ #s = dim R`; the reverse inequality is
    -- Krull's height theorem, packaged in `of_spanFinrank_maximalIdeal_le`.
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [← hcard, ← hspan]
    have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) s.finite_toSet
    rw [Set.ncard_coe_finset] at hle
    exact_mod_cast hle

/-- "A system (z₁,…,zₖ) which can be extended to a regular system of parameters." -/
def ExtendsToRSOP (t : Finset R) : Prop :=
  ∃ s : Finset R, t ⊆ s ∧ IsRegularSystemOfParameters R s

end RegularSystems

section Order

variable {S : Type u} [CommRing S]



/-- `ν ≤ ν_M(J)` as soon as `J ⊆ M^ν`. -/
theorem Ideal.le_ord {M J : Ideal S} {ν : ℕ} (h : J ≤ M ^ ν) : (ν : ℕ∞) ≤ Ideal.ord M J :=
  le_iSup₂ (f := fun (ν : ℕ) (_ : J ≤ M ^ ν) => (ν : ℕ∞)) ν h

/-- `ν_M(J) ≤ a` as soon as every exponent `ν` with `J ⊆ M^ν` satisfies `ν ≤ a`. -/
theorem Ideal.ord_le {M J : Ideal S} {a : ℕ∞} (h : ∀ ν : ℕ, J ≤ M ^ ν → (ν : ℕ∞) ≤ a) :
    Ideal.ord M J ≤ a :=
  iSup₂_le h

/-- Basic facts about the order function (Hironaka uses these without comment). -/
@[blueprint "lem:order-nu-basic"
  (statement := /-- $\nu_M(J)=\infty$ iff $J\subseteq\bigcap_\nu M^\nu$; $\nu_M(J)\ge 1$ iff
    $J\subseteq M$; $\nu_M$ is monotone decreasing in $J$; $\nu_M(J_1J_2)\ge\nu_M(J_1)+\nu_M(J_2)$. -/)
  (latexEnv := "lemma")]
theorem Ideal.ord_basic (M J J₁ J₂ : Ideal S) :
    (Ideal.ord M J = ⊤ ↔ ∀ ν : ℕ, J ≤ M ^ ν) ∧
    (1 ≤ Ideal.ord M J ↔ J ≤ M) ∧
    (J₁ ≤ J₂ → Ideal.ord M J₂ ≤ Ideal.ord M J₁) ∧
    (Ideal.ord M J₁ + Ideal.ord M J₂ ≤ Ideal.ord M (J₁ * J₂)) := by
  refine ⟨⟨fun h ν => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, fun h => ?_, ?_⟩
  · -- `ν_M(J) = ∞ → J ⊆ M^ν`: otherwise, as the powers are antitone, every admissible exponent
    -- is `< ν`, so the supremum is at most `ν < ∞`.
    by_contra hν
    have hle : Ideal.ord M J ≤ (ν : ℕ∞) := Ideal.ord_le fun μ hμ => by
      refine le_of_not_gt fun hlt => hν ?_
      exact hμ.trans (Ideal.pow_le_pow_right (Nat.cast_lt.mp hlt).le)
    rw [h] at hle
    exact ENat.natCast_ne_top ν (top_le_iff.mp hle)
  · -- if `J ⊆ M^ν` for all `ν`, the supremum runs over all of `ℕ`, hence is `∞`.
    refine le_antisymm le_top ?_
    rw [← ENat.iSup_natCast]
    exact iSup_le fun ν => Ideal.le_ord (h ν)
  · -- `1 ≤ ν_M(J)`: some admissible exponent is positive, so `J ⊆ M^ν ⊆ M^1 = M`.
    have h0 : (0 : ℕ∞) < Ideal.ord M J := zero_lt_one.trans_le h
    simp only [Ideal.ord, lt_iSup_iff] at h0
    obtain ⟨ν, hν, hpos⟩ := h0
    have h1 : 0 < ν := by exact_mod_cast hpos
    exact (hν.trans (Ideal.pow_le_pow_right h1)).trans (pow_one M).le
  · -- `J ⊆ M = M^1` gives `1 ≤ ν_M(J)`.
    have h1 := Ideal.le_ord (M := M) (J := J) (ν := 1) (by rwa [pow_one])
    exact_mod_cast h1
  · -- antitone in `J`.
    exact Ideal.ord_le fun ν hν => Ideal.le_ord (h.trans hν)
  · -- superadditivity: `J₁ ⊆ M^i` and `J₂ ⊆ M^j` give `J₁J₂ ⊆ M^i M^j = M^(i+j)`.
    refine ENat.biSup_add_biSup_le' ⟨0, by simp⟩ ⟨0, by simp⟩ fun i hi j hj => ?_
    have hij := Ideal.le_ord (M := M) (J := J₁ * J₂) (ν := i + j)
      (by rw [pow_add]; exact Ideal.mul_mono hi hj)
    exact_mod_cast hij

end Order

end Hironaka
