/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch4.Preparation.Lemmas3To5

/-!
# Ch. IV §2 (pp. 288–292): lemmas for the proof of Proposition 5

The structure of the proof of Proposition 5 (a chain of "we may assume" reductions), and the lemmas its
steps use: transversality and normal crossings of unions of subschemes, the sets `W_*` and `F` of the proof,
irreducible components and Krull dimension, centers avoiding a closed set, and the induction along the
stages of a succession.

This is part 2 of 3 of `Hironaka.Ch4.Preparation`, which imports all parts; its description holds the
notation and the formalization notes for the whole section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u v

noncomputable section

/-! ### Proposition 5: the preparation theorem on `(ℜ^{N,n}_I, U)` (pp. 288–292) -/

/-! ### Proposition 5: structure of the proof (pp. 288–292)

The proof of Proposition 5 is a chain of "we may assume" reductions.  Each reduction replaces
`(ℜ, U)` by its transform `(s.transformI ℜ, s.transformOpen U)` under a permissible succession `s`
and records that the transform satisfies one more of the conditions (1), (2), (3), (3)*, (3)**,
(4), (5) of the paper.  `PrepSetting` bundles the data of the statement (the datum, its
presentation `E = ⋃ E_i`, the open restriction), the predicates `PrepSetting.Cond₁`, … are the
conditions of the paper, and `PrepSetting.StepTo` is "after a permissible succession the
transform satisfies …". -/

section PrepProposition

open Classical

variable {X : Scheme.{u}}

/-- `W_* = W_1 ∪ ⋯ ∪ W_a`: "those irreducible components of `W` which are not contained in
`E_1`" (p. 289). -/
noncomputable def DatumI.Raw.prepWStar (ℜ : DatumI.Raw X) (E₁ : Subscheme X) : Subscheme X :=
  Subscheme.ofClosed (sSup {Z : TopologicalSpace.Closeds X |
    ∃ W₁ ∈ ℜ.W.irreducibleComponents, ¬ W₁.IsContainedIn E₁ ∧ Z = W₁.support})

/-- `F = F_1 ∪ ⋯ ∪ F_δ`: "those reduced irreducible components of `W_* ∩ E_1` which have
non-empty intersection with `U`" (p. 289). -/
noncomputable def DatumI.Raw.prepF (ℜ : DatumI.Raw X) (E₁ : Subscheme X) (U : Set X) :
    Subscheme X :=
  Subscheme.ofClosed (sSup {Z : TopologicalSpace.Closeds X |
    ∃ F_i ∈ ((ℜ.prepWStar E₁).inter E₁).irreducibleComponents,
      (F_i.pts ∩ U).Nonempty ∧ Z = F_i.support})

/-- `⋃_{i ≥ 2} E_i`: the union of the `E_i` different from `E_{i₀}`.

Deviation from the paper (slip; statement modified): the paper's tail is `⋃_{i=2}^α E_i`, but its
convention of p. 274 ("We do not require that `E_i` differ from `E_j` if `i ≠ j`") allows copies of
`E_1` among `E_2, …, E_α`, for which the argument of p. 289 for condition (2) fails; the copies of
`E_{i₀}` are therefore excluded.  -/
def prepERest {α : ℕ} (E : Fin α → Subscheme X) (i₀ : Fin α) : Subscheme X :=
  Subscheme.unionFam (fun i : {i : Fin α // E i ≠ E i₀} => E i)

/-- The data of Proposition 5: a datum `ℜ` of type I with open restriction `U` on `X`, and a
presentation `E = ⋃_{i=1}^α E_i` of its boundary by non-singular irreducible subschemes of
codimension one, `α ≥ 1` (the convention of pp. 274–275). -/
structure PrepSetting (X : Scheme.{u}) where
  α : ℕ
  hα : 0 < α
  E : Fin α → Subscheme X
  hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne
  ℜ : DatumI.Raw X
  hℜ : ℜ.IsDatum
  hEunion : ℜ.E = Subscheme.unionFam E
  U : Set X
  hU : ℜ.IsOpenRestriction U

/-- `E_1`. -/
def PrepSetting.E₁ (P : PrepSetting X) : Subscheme X := P.E ⟨0, P.hα⟩

/-- The conclusion of Proposition 5 for `P`. -/
def PrepSetting.Goal (P : PrepSetting X) : Prop :=
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
    s.IsPermissibleIOpen P.ℜ P.U ∧
    ∃ U'' : Set Y,
      (∃ V : Set Y, IsOpen V ∧ U'' = V ∩ (s.transformI P.ℜ).W.pts) ∧
      s.transformOpen P.U ⊆ U'' ∧
      (∀ x ∈ U'', (s.transformI P.ℜ).ResolvedAt x) ∧
      ∀ W₁ ∈ (s.transformI P.ℜ).W.irreducibleComponents,
        W₁.IsContainedIn (s.strictTransform P.E₁) ∨
          (W₁.inter (s.strictTransform P.E₁)).pts ⊆ U''

/-- `Q` is the transform of `P` under the succession `s`: its datum is `f*ℜ`, its open
restriction is `U'`, and the first member of its presentation is the strict transform of `E_1`
(the presentation of `f*ℜ` by the strict transforms of the `E_i` and the exceptional divisors,
Definition 7, p. 168). -/
def PrepSetting.IsTransform (P : PrepSetting X) {Y : Scheme.{u}} (s : MonoidalSuccession X Y)
    (Q : PrepSetting Y) : Prop :=
  Q.ℜ = s.transformI P.ℜ ∧ Q.U = s.transformOpen P.U ∧ Q.E₁ = s.strictTransform P.E₁

/-- "We may assume": the goal for the transform `Q` of `P` under a permissible succession
implies the goal for `P` (compose the successions).

Deviation from the paper (gap filled): the paper's repeated "Thus, without any loss of
generality, we may assume …" (pp. 290–291) is the composition of permissible successions and of
the transforms of `(ℜ, U)`, of the open restriction and of the strict transform of `E_1`
(`MonoidalSuccession.append`); here it is a lemma. -/
theorem PrepSetting.Goal.of_isTransform {P : PrepSetting X} {Y : Scheme.{u}}
    {s : MonoidalSuccession X Y} {Q : PrepSetting Y} (hs : s.IsPermissibleIOpen P.ℜ P.U)
    (hQ : P.IsTransform s Q) (hgoal : Q.Goal) : P.Goal := by
  obtain ⟨hQℜ, hQU, hQE⟩ := hQ
  obtain ⟨Z, s₂, hs₂, U'', hopen, hsub, hres, hcomp⟩ := hgoal
  rw [hQℜ, hQU] at hs₂
  rw [hQℜ] at hopen hres hcomp
  rw [hQU] at hsub
  rw [hQE] at hcomp
  refine ⟨Z, s.append s₂, (MonoidalSuccession.isPermissibleIOpen_append s s₂ _ _).mpr ⟨hs, hs₂⟩,
    U'', ?_, ?_, ?_, ?_⟩
  · rwa [MonoidalSuccession.transformI_append]
  · rwa [MonoidalSuccession.transformOpen_append]
  · rwa [MonoidalSuccession.transformI_append]
  · rw [MonoidalSuccession.transformI_append, MonoidalSuccession.strictTransform_append]
    exact hcomp

/-- The points of `W_*`. -/
theorem DatumI.Raw.pts_prepWStar (ℜ : DatumI.Raw X) (E₁ : Subscheme X) :
    (ℜ.prepWStar E₁).pts = closure (⋃₀ ((↑) '' {Z : TopologicalSpace.Closeds X |
      ∃ W₁ ∈ ℜ.W.irreducibleComponents, ¬ W₁.IsContainedIn E₁ ∧ Z = W₁.support})) :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

/-- "`Ū ∩ W_*` is an open dense subset of `W_*`": if `U₀ ∩ W` is dense in `W`, then `U₀ ∩ W_*`
is dense in `W_*` (each irreducible component `Z` of `W` contains a point of `U₀`, since the
points of `Z` outside the other components form a non-empty open subset of `W`, and a non-empty
open subset of the irreducible `Z` is dense in `Z`). -/
theorem DatumI.Raw.pts_prepWStar_subset_closure_inter [TopologicalSpace.NoetherianSpace X]
    (ℜ : DatumI.Raw X) (E₁ : Subscheme X) {U₀ : Set X} (hU₀ : IsOpen U₀)
    (hdense : ℜ.W.pts ⊆ closure (U₀ ∩ ℜ.W.pts)) :
    (ℜ.prepWStar E₁).pts ⊆ closure (U₀ ∩ (ℜ.prepWStar E₁).pts) := by
  classical
  rw [DatumI.Raw.pts_prepWStar]
  refine closure_minimal ?_ isClosed_closure
  rintro x ⟨_, ⟨Z, hZS, rfl⟩, hxZ⟩
  obtain ⟨W₁, hW₁, hW₁E, rfl⟩ := hZS
  obtain ⟨Zw, hZwmax, rfl⟩ := id hW₁
  have hZwpts : ((Subscheme.ofClosed Zw).support : Set X) = Zw :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Zw
  have hfin := finite_setOf_maximal_isIrreducible_subset (X := X) ℜ.W.support.isClosed
  set 𝒞 := {Z : TopologicalSpace.Closeds X | Maximal (fun Z : TopologicalSpace.Closeds X =>
      _root_.IsIrreducible (Z : Set X) ∧ (Z : Set X) ⊆ ℜ.W.pts) Z} with h𝒞
  have hZw𝒞 : Zw ∈ 𝒞 := hZwmax
  set K : Set X := ⋃ Z' ∈ 𝒞 \ {Zw}, (Z' : Set X) with hK
  have hKcl : IsClosed K := (hfin.sdiff).isClosed_biUnion fun Z' _ => Z'.isClosed
  set O : Set X := ℜ.W.pts \ K with hO
  have hOsub : O ⊆ Zw := by
    intro p hp
    obtain ⟨G, hG, hpG⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_pts ℜ.W hp.1
    obtain ⟨Z', hZ'max, rfl⟩ := id hG
    have hZ'pts : ((Subscheme.ofClosed Z').support : Set X) = Z' :=
      Scheme.IdealSheafData.coe_support_vanishingIdeal Z'
    have hpG' : p ∈ (Z' : Set X) := by
      have := hpG
      unfold Subscheme.pts at this
      rw [hZ'pts] at this
      exact this
    by_cases h : Z' = Zw
    · subst h; exact hpG'
    · exact absurd (Set.mem_iUnion₂.mpr ⟨Z', ⟨hZ'max, h⟩, hpG'⟩) hp.2
  have hOne : O.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty, hO, Set.sdiff_eq_empty] at hne
    have hZwK : (Zw : Set X) ⊆ K := fun z hz => hne (hZwmax.1.2 hz)
    have hirr := hZwmax.1.1
    obtain ⟨z₀, hz₀, hsub⟩ := isIrreducible_iff_sUnion_isClosed.mp hirr
      ((hfin.sdiff (t := {Zw})).toFinset.image (fun Z' : TopologicalSpace.Closeds X =>
        (Z' : Set X)))
      (by
        intro s hs
        obtain ⟨Z', -, rfl⟩ := Finset.mem_image.mp hs
        exact Z'.isClosed)
      (by
        intro z hz
        obtain ⟨Z', hZ', hzZ'⟩ := Set.mem_iUnion₂.mp (hZwK hz)
        exact Set.mem_sUnion.mpr ⟨(Z' : Set X), Finset.mem_image.mpr
          ⟨Z', (Set.Finite.mem_toFinset _).mpr hZ', rfl⟩, hzZ'⟩)
    obtain ⟨Z', hZ'mem, rfl⟩ := Finset.mem_image.mp hz₀
    have hZ'mem' := (Set.Finite.mem_toFinset _).mp hZ'mem
    have hle : Zw ≤ Z' := hsub
    have := hZwmax.2 hZ'mem'.1.1 hle
    exact hZ'mem'.2 (le_antisymm this hle)
  obtain ⟨p, hpO⟩ := hOne
  have hpcl := hdense hpO.1
  rw [mem_closure_iff] at hpcl
  obtain ⟨u, hu, huU⟩ := hpcl Kᶜ hKcl.isOpen_compl hpO.2
  have huZ : u ∈ (Zw : Set X) := hOsub ⟨huU.2, hu⟩
  have hirr : IsPreirreducible (Zw : Set X) := hZwmax.1.1.isPreirreducible
  have hcl := subset_closure_inter_of_isPreirreducible_of_isOpen hirr hU₀ ⟨u, huZ, huU.1⟩
  have hxZw : x ∈ (Zw : Set X) := by rwa [hZwpts] at hxZ
  refine closure_mono ?_ (hcl hxZw)
  rintro v ⟨hvZ, hvU⟩
  refine ⟨hvU, ?_⟩
  have hv' : v ∈ ((Subscheme.ofClosed Zw).support : Set X) := by rw [hZwpts]; exact hvZ
  exact subset_closure ⟨_, ⟨_, ⟨_, hW₁, hW₁E, rfl⟩, rfl⟩, hv'⟩

/-- `W_* ⊆ W`. -/
theorem DatumI.Raw.pts_prepWStar_subset (ℜ : DatumI.Raw X) (E₁ : Subscheme X) :
    (ℜ.prepWStar E₁).pts ⊆ ℜ.W.pts := by
  rw [DatumI.Raw.pts_prepWStar]
  refine closure_minimal ?_ ℜ.W.support.isClosed
  rintro x ⟨_, ⟨Z, ⟨W₁, hW₁, -, rfl⟩, rfl⟩, hx⟩
  exact Subscheme.pts_subset_of_mem_irreducibleComponents hW₁ hx

/-- The points of `F = F_1 ∪ ⋯ ∪ F_δ`. -/
theorem DatumI.Raw.pts_prepF (ℜ : DatumI.Raw X) (E₁ : Subscheme X) (U : Set X) :
    (ℜ.prepF E₁ U).pts = closure (⋃₀ ((↑) '' {Z : TopologicalSpace.Closeds X |
      ∃ F_i ∈ ((ℜ.prepWStar E₁).inter E₁).irreducibleComponents,
        (F_i.pts ∩ U).Nonempty ∧ Z = F_i.support})) :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

/-- `F ⊆ W_* ∩ E_1`. -/
theorem DatumI.Raw.pts_prepF_subset (ℜ : DatumI.Raw X) (E₁ : Subscheme X) (U : Set X) :
    (ℜ.prepF E₁ U).pts ⊆ ((ℜ.prepWStar E₁).inter E₁).pts := by
  rw [DatumI.Raw.pts_prepF]
  refine closure_minimal ?_ ((ℜ.prepWStar E₁).inter E₁).support.isClosed
  rintro x ⟨_, ⟨Z, ⟨F_i, hF_i, -, rfl⟩, rfl⟩, hx⟩
  exact Subscheme.pts_subset_of_mem_irreducibleComponents hF_i hx

/-- A component of `W_* ∩ E_1` meeting `U` is contained in `F`. -/
theorem DatumI.Raw.pts_subset_pts_prepF (ℜ : DatumI.Raw X) (E₁ : Subscheme X) (U : Set X)
    {G : Subscheme X} (hG : G ∈ ((ℜ.prepWStar E₁).inter E₁).irreducibleComponents)
    (hGU : (G.pts ∩ U).Nonempty) : G.pts ⊆ (ℜ.prepF E₁ U).pts := by
  rw [DatumI.Raw.pts_prepF]
  exact fun x hx => subset_closure ⟨_, ⟨G.support, ⟨G, hG, hGU, rfl⟩, rfl⟩, hx⟩

section PrepTransversalAlgebra

open IsLocalRing
/-- `dim R/I = dim R/√I`. -/
private theorem ringKrullDim_quotient_radical {R : Type u} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]

/-- Transversality, domain case (Proposition 5, step (4), p. 291): in a regular local ring `S`, a
prime `p` with regular quotient and `p = √(z)` which becomes `(z)` after localization at `p`
(`∀ a ∈ p, ∃ s ∉ p, s a ∈ (z)`) equals `(z)`.  The quotient by the single generator `π` of `p`
(`dim S/p = dim S − 1`, `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`) gives
`z = π g` with `g ∉ p`, and Krull's principal ideal theorem shows that `g` is a unit. -/
private theorem eq_span_singleton_of_radical_of_loc {S : Type u} [CommRing S] [IsRegularLocalRing S]
    {z : S} (hz0 : z ≠ 0) (hzm : z ∈ maximalIdeal S) (p : Ideal S) [hpp : p.IsPrime]
    [IsRegularLocalRing (S ⧸ p)] (hp : p = (Ideal.span {z}).radical)
    (hloc : ∀ a ∈ p, ∃ s ∉ p, s * a ∈ Ideal.span {z}) : p = Ideal.span {z} := by
  classical
  have hdom := isDomain_of_isRegularLocalRing S
  obtain ⟨T', T, hT'span, hT'card, hTT', hTp⟩ := exists_finset_span_eq_prime S p inferInstance
  have hrsop : IsRegularSystemOfParameters S T' := rsop_of_span_of_card_le hT'span hT'card.le
  obtain ⟨hreg, hrsopq, hcardq⟩ := rsop_quotient hrsop hTT'
  have h1 : ringKrullDim (S ⧸ p) = ((T' \ T).card : ℕ) := by
    rw [← hTp, ← hrsopq.2, hcardq]
  have h2 : ringKrullDim S = (T'.card : ℕ) := hrsop.2.symm
  have h3 : ringKrullDim (S ⧸ Ideal.span {z}) + 1 = ringKrullDim S :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hz0) hzm
  have h4 : ringKrullDim (S ⧸ p) = ringKrullDim (S ⧸ Ideal.span {z}) := by
    rw [ringKrullDim_quotient_radical (Ideal.span {z}), ← hp]
  have h5 : (T'.card : WithBot ℕ∞) = ((T' \ T).card : ℕ) + 1 := by
    rw [← h2, ← h3, ← h4, h1]
  have h6 : (T' \ T).card + 1 = T'.card := by exact_mod_cast h5.symm
  have h7 := Finset.card_sdiff_add_card_eq_card hTT'
  have hT1 : T.card = 1 := by omega
  obtain ⟨π, rfl⟩ := Finset.card_eq_one.mp hT1
  rw [Finset.coe_singleton] at hTp
  have hzp : z ∈ p := hp ▸ Ideal.le_radical (Ideal.mem_span_singleton_self z)
  rw [← hTp, Ideal.mem_span_singleton] at hzp
  obtain ⟨g, hg⟩ := hzp
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hz0 (by simpa using hg)
  -- `g ∉ p`
  have hgp : g ∉ p := by
    intro hgp
    obtain ⟨s, hsp, hs⟩ := hloc π (hTp ▸ Ideal.mem_span_singleton_self π)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hs
    have : s = c * g := by
      apply mul_right_cancel₀ hπ0
      rw [← hc, hg]; ring
    exact hsp (this ▸ Ideal.mul_mem_left _ _ hgp)
  -- `g` is a unit
  have hgu : IsUnit g := by
    by_contra hgu
    have hgm : g ∈ maximalIdeal S := (mem_maximalIdeal _).mpr hgu
    obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le (show Ideal.span {g} ≤ maximalIdeal S from
      (Ideal.span_singleton_le_iff_mem _).mpr hgm)
    have hqp : q.IsPrime := hq.1.1
    have hh := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {g}) q hq
    have hgq : g ∈ q := hq.1.2 (Ideal.mem_span_singleton_self g)
    have hzq : z ∈ q := hg ▸ Ideal.mul_mem_left _ _ hgq
    have hpq : p ≤ q := by
      calc p = (Ideal.span {z}).radical := hp
        _ ≤ q.radical := Ideal.radical_mono ((Ideal.span_singleton_le_iff_mem _).mpr hzq)
        _ = q := hqp.radical
    have hpbot : p ≠ ⊥ := fun h => hz0 (by
      have : z ∈ p := hp ▸ Ideal.le_radical (Ideal.mem_span_singleton_self z)
      rw [h] at this; simpa using this)
    have hp1 : 1 ≤ p.height := by
      rw [Order.one_le_iff_ne_zero]
      exact fun h => hpbot (Ideal.height_eq_zero_iff_eq_bot.mp h)
    rcases hpq.lt_or_eq with hlt | heq
    · have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have h3 : (1 : ℕ∞) + 1 ≤ 1 := calc (1 : ℕ∞) + 1 ≤ p.height + 1 := add_le_add_left hp1 1
        _ ≤ q.height := h2
        _ ≤ 1 := hh
      exact absurd h3 (by norm_num)
    · exact hgp (heq ▸ hgq)
  have : Ideal.span {z} = p := by
    rw [hg, ← hTp]
    exact Ideal.span_singleton_mul_right_unit hgu π
  exact this.symm

/-- Transversality (Proposition 5, step (4), p. 291): in a regular local ring `R`, primes `Q ⊆ p` with
regular quotients, `z ∉ Q` and `p = √(Q + (z))` with `Q + (z)` equal to `p` after localization at
`p`: then `p = Q + (z)`. -/
theorem eq_sup_span_of_radical_of_loc {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (Q p : Ideal R) [Q.IsPrime] [p.IsPrime] (hQp : Q ≤ p)
    [IsRegularLocalRing (R ⧸ Q)] [IsRegularLocalRing (R ⧸ p)] {z : R} (hzQ : z ∉ Q)
    (hzm : z ∈ maximalIdeal R) (hrad : p = (Q ⊔ Ideal.span {z}).radical)
    (hloc : ∀ y ∈ p, ∃ s ∉ p, s * y ∈ Q ⊔ Ideal.span {z}) : p = Q ⊔ Ideal.span {z} := by
  classical
  set mk := Ideal.Quotient.mk Q with hmk
  have hker : RingHom.ker mk = Q := Ideal.mk_ker
  have hsurj : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hz0 : mk z ≠ 0 := fun h => hzQ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hloc' : IsLocalHom mk := IsLocalHom.of_surjective _ hsurj
  have hzm' : mk z ∈ maximalIdeal (R ⧸ Q) := (mem_maximalIdeal _).mpr fun hu =>
    ((mem_maximalIdeal _).mp hzm) (isUnit_of_map_unit mk z hu)
  have hQp' : RingHom.ker mk ≤ p := by rw [hker]; exact hQp
  have hpbar : (p.map mk).IsPrime := Ideal.map_isPrime_of_surjective hsurj hQp'
  have : IsRegularLocalRing ((R ⧸ Q) ⧸ p.map mk) :=
    IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hQp).symm
  have hmapJ : (Q ⊔ Ideal.span {z}).map mk = Ideal.span {mk z} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton,
      Ideal.map_mk_eq_bot_of_le le_rfl, bot_sup_eq]
  have hrad' : p.map mk = (Ideal.span {mk z}).radical := by
    rw [← hmapJ, ← Ideal.map_radical_of_surjective hsurj
      (by rw [hker]; exact le_sup_left), ← hrad]
  have hloc'' : ∀ a ∈ p.map mk, ∃ s ∉ p.map mk, s * a ∈ Ideal.span {mk z} := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective mk hsurj).mp ha
    obtain ⟨s, hsp, hs⟩ := hloc y hy
    refine ⟨mk s, fun hs' => hsp ?_, ?_⟩
    · obtain ⟨w, hw, hws⟩ := (Ideal.mem_map_iff_of_surjective mk hsurj).mp hs'
      have : s - w ∈ Q := Ideal.Quotient.eq.mp hws.symm
      have h2 : s = (s - w) + w := by ring
      rw [h2]
      exact add_mem (hQp this) hw
    · rw [← map_mul, ← hmapJ]
      exact Ideal.mem_map_of_mem _ hs
  have key := eq_span_singleton_of_radical_of_loc hz0 hzm' (p.map mk) hrad' hloc''
  apply le_antisymm
  · intro y hy
    have : mk y ∈ Ideal.span {mk z} := key ▸ Ideal.mem_map_of_mem mk hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    obtain ⟨c', rfl⟩ := hsurj c
    have h1 : y - c' * z ∈ Q := Ideal.Quotient.eq.mp (by rw [map_mul, hc])
    have h2 : y = (y - c' * z) + c' * z := by ring
    rw [h2]
    exact add_mem (Ideal.mem_sup_left h1)
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self z)))
  · exact sup_le hQp ((Ideal.span_singleton_le_iff_mem _).mpr (hrad ▸ Ideal.le_radical
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self z))))

/-- The normal crossings at the generic point `η` of `F` (Proposition 5, step (4), p. 291, "here we
must use the fact that `ℜ` is resolved at every generic point of `F`"), read on the localization
`R_p = O_η` of the local ring `R = O_x` at `p = F_x`: for `W_η = (t)` and `E_{1,η} = (a)` members of
a regular system of parameters of `R_p`, the maximal ideal of `R_p` is `(t, a)`, so that
`Q + (z)` becomes `p` after localization, and every other prime `E_{j,x} ⊆ p` is contained in
`Q` or equal to `E_{1,x}`. -/
theorem localization_facts_of_isRegularSystemOfParameters {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] [IsRegularLocalRing B] (p Q : Ideal R) [p.IsPrime] [Q.IsPrime]
    [IsLocalization.AtPrime B p] (hQp : Q ≤ p) {z : R} (hzprime : (Ideal.span {z}).IsPrime)
    (hzp : z ∈ p) (hrad : p = (Q ⊔ Ideal.span {z}).radical)
    {Zη tη : Finset B} (hZ : IsRegularSystemOfParameters B Zη) (htη : tη ⊆ Zη)
    (hQB : Q.map (algebraMap R B) = Ideal.span (tη : Set B)) {a : B} (ha : a ∈ Zη)
    (hzB : (Ideal.span {z}).map (algebraMap R B) = Ideal.span {a}) :
    (∀ y ∈ p, ∃ s ∉ p, s * y ∈ Q ⊔ Ideal.span {z}) ∧
    (∀ (D : Ideal R) [D.IsPrime], D ≤ p → ∀ b ∈ Zη, D.map (algebraMap R B) = Ideal.span {b} →
      D ≤ Q ∨ D = Ideal.span {z}) := by
  classical
  have hsub : insert a tη ⊆ Zη := Finset.insert_subset ha htη
  have hext : ExtendsToRSOP B (insert a tη) := ⟨Zη, hsub, hZ⟩
  have h𝔭 : (Ideal.span ((insert a tη : Finset B) : Set B)).IsPrime := hext.isPrime_span
  have h𝔭eq : Ideal.span ((insert a tη : Finset B) : Set B) =
      (Q ⊔ Ideal.span {z}).map (algebraMap R B) := by
    rw [Ideal.map_sup, hQB, hzB, Finset.coe_insert, Set.insert_eq, Ideal.span_union, sup_comm]
  have hm : p.map (algebraMap R B) = maximalIdeal B := IsLocalization.AtPrime.map_eq_maximalIdeal p B
  have hZM : ∀ y ∈ Zη, y ∈ maximalIdeal B := fun y hy => hZ.1 ▸ Ideal.subset_span hy
  have hple : p.map (algebraMap R B) ≤ Ideal.span ((insert a tη : Finset B) : Set B) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [hrad] at hy
    obtain ⟨n, hn⟩ := hy
    rw [Ideal.mem_comap]
    refine h𝔭.mem_of_pow_mem n ?_
    rw [← map_pow, h𝔭eq]
    exact Ideal.mem_map_of_mem _ hn
  have h𝔭m : Ideal.span ((insert a tη : Finset B) : Set B) = maximalIdeal B :=
    le_antisymm (Ideal.span_le.mpr fun y hy => hZM y (hsub (Finset.mem_coe.mp hy)))
      (hm ▸ hple)
  refine ⟨fun y hy => ?_, fun D _ hDp b hb hDb => ?_⟩
  · have hy' : algebraMap R B y ∈ (Q ⊔ Ideal.span {z}).map (algebraMap R B) := by
      rw [← h𝔭eq, h𝔭m, ← hm]
      exact Ideal.mem_map_of_mem _ hy
    obtain ⟨⟨⟨i, hi⟩, ⟨m, hm'⟩⟩, h⟩ :=
      (IsLocalization.mem_map_algebraMap_iff p.primeCompl B).mp hy'
    simp only at h
    rw [← map_mul] at h
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists p.primeCompl B).mp h
    refine ⟨(c : R) * m, Ideal.mem_primeCompl_iff.mp (mul_mem c.2 hm'), ?_⟩
    have : (c : R) * m * y = c * i := by rw [← hc]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hi
  · have hbm : b ∈ insert a tη := by
      by_contra hnot
      exact rsop_notMem_span hZ hsub hb hnot (by rw [h𝔭m]; exact hZM b hb)
    have hdisj : ∀ I : Ideal R, I ≤ p → Disjoint (p.primeCompl : Set R) I := fun I hI =>
      Set.disjoint_left.mpr fun x hx hxI => hx (hI hxI)
    have hD' := IsLocalization.under_map_of_isPrime_disjoint p.primeCompl B (I := D) ‹D.IsPrime›
      (hdisj D hDp)
    rcases Finset.mem_insert.mp hbm with rfl | hbt
    · right
      have hz' := IsLocalization.under_map_of_isPrime_disjoint p.primeCompl B (I := Ideal.span {z})
        hzprime (hdisj _ ((Ideal.span_singleton_le_iff_mem _).mpr hzp))
      rw [← hD', hDb, ← hzB, hz']
    · left
      rw [← hD']
      have hle : D.map (algebraMap R B) ≤ Q.map (algebraMap R B) := by
        rw [hDb, hQB]
        exact Ideal.span_singleton_le_iff_mem _ |>.mpr (Ideal.subset_span (Finset.mem_coe.mpr hbt))
      have hQ' := IsLocalization.under_map_of_isPrime_disjoint p.primeCompl B (I := Q) ‹Q.IsPrime›
        (hdisj Q hQp)
      calc (D.map (algebraMap R B)).under R ≤ (Q.map (algebraMap R B)).under R :=
            Ideal.comap_mono hle
        _ = Q := hQ'

end PrepTransversalAlgebra

section PrepLemmaThreeVariant

open IsLocalRing

/-- Lemma 3 in the form needed in Proposition 5 (p. 291, "with the help of Lemma 3"): at a
point `x` of `W`, if `E = E_1 ∪ ⋯ ∪ E_α` has only normal crossings at `x`, `E' = ⋃_{i≠i₀} E_i`
has only normal crossings with `W` at `x`, and `E_{i₀} ⊇ W` near `x` (`E_{i₀,x} ⊆ W_x`), then
`E` has only normal crossings with `W` at `x`.  A regular system of parameters adapted to the
`E_i` and to `W_x` is built by the linear algebra of `exists_rsop_adapted_to_flag` with the
maximal ideal in the place of `B_x`: the generators of the `E_i` lying in `W_x` need no
partner in the system adapted to `W`. -/
theorem Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_of_stalkIdeal_le
    (hX : X.IsNonsingular) {α : ℕ} (E : Fin α → Subscheme X)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) (i₀ : Fin α)
    (hred : (Subscheme.unionFam E).IsReduced) {W : Subscheme X} {x : X} (hxW : x ∈ W.pts)
    (hi : (Subscheme.unionFam E).HasOnlyNormalCrossingsAt x)
    (hrest : (prepERest E i₀).HasOnlyNormalCrossingsWithAt W x)
    (hz : (E i₀).stalkIdeal x ≤ W.stalkIdeal x) :
    (Subscheme.unionFam E).HasOnlyNormalCrossingsWithAt W x := by
  classical
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  obtain ⟨ZE, hZE, -, hEZE⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt E hE
    (fun i => iInf_le _ i) hi
  obtain ⟨ZW, hZW, ⟨tW, htWZ, hWt⟩, hEZW⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    (fun i : {i : Fin α // E i ≠ E i₀} => E i) (fun i => hE i)
    (fun i => iInf_le (fun j : {j : Fin α // E j ≠ E i₀} => E j) i) hrest
  have hQP : W.stalkIdeal x ≤ maximalIdeal (X.presheaf.stalk x) :=
    Subscheme.stalkIdeal_le_maximalIdeal W hxW
  have hZEm : ∀ c ∈ ZE, c ∈ maximalIdeal (X.presheaf.stalk x) := fun c hc =>
    hZE.1 ▸ Ideal.subset_span hc
  obtain ⟨Z, hZ, hCZ, tP, htPZ, hPt, tQ, htQ, hQt⟩ :=
    exists_rsop_adapted_to_flag (W.stalkIdeal x) (maximalIdeal (X.presheaf.stalk x)) hQP ZE ZE ZW tW
      (ZE.filter fun c => ∃ i, (E i).stalkIdeal x = Ideal.span {c}) hZE (Finset.Subset.refl _)
      hZE.1.symm hZW htWZ hWt (Finset.filter_subset _ _) (by
        intro c hc hcQ
        obtain ⟨hcZ, i, hi'⟩ := Finset.mem_filter.mp hc
        by_cases hii : E i = E i₀
        · have hle : (E i).stalkIdeal x ≤ W.stalkIdeal x := by rw [hii]; exact hz
          exact absurd (hle (hi' ▸ Ideal.mem_span_singleton_self c)) hcQ
        · rcases hEZW ⟨i, hii⟩ with h | ⟨a, ha, haE⟩
          · exfalso
            have h' : (E i).stalkIdeal x = ⊤ := h
            rw [hi', Ideal.span_singleton_eq_top] at h'
            exact (mem_maximalIdeal c).mp (hZEm c hcZ) h'
          · exact ⟨a, ha, hi'.symm.trans haE⟩)
  refine (Subscheme.hasOnlyNormalCrossingsWithAt_iff hred (hX x)).mpr ⟨Z, hZ, ?_,
    ⟨tQ, htQ.trans htPZ, hQt⟩⟩
  obtain ⟨K₁, hK₁, h⟩ := DatumTransform.iInf_eq_span_prod (fun i => (E i).stalkIdeal x)
    (ExtendsToRSOP.of_isRegularSystemOfParameters hZ) (fun i => by
      rcases hEZE i with h | ⟨a, ha, haE⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, hCZ (Finset.mem_filter.mpr ⟨ha, i, haE⟩), haE⟩)
  refine ⟨K₁, hK₁, ?_⟩
  rw [Subscheme.unionFam, DatumTransform.stalkIdeal_iInf_fintype]
  exact h

end PrepLemmaThreeVariant

section PrepTransversal

namespace Subscheme

/-- If `D_y` is prime and `D_η` is the maximal ideal of `O_η` for a generization `η ⤳ y`, then
`D_y` is the prime of `O_y` corresponding to `η`. -/
theorem comap_maximalIdeal_stalkSpecializes_eq {Y : Scheme.{u}} (D : Subscheme Y)
    {η y : Y} (h : η ⤳ y) [(D.stalkIdeal y).IsPrime]
    (hη : D.stalkIdeal η = IsLocalRing.maximalIdeal (Y.presheaf.stalk η)) :
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk η)).comap (Y.presheaf.stalkSpecializes h).hom =
      D.stalkIdeal y := by
  let := (Y.presheaf.stalkSpecializes h).hom.toAlgebra
  have hloc := isLocalization_stalkSpecializes_of_specializes h
  have hmap : D.stalkIdeal η = (D.stalkIdeal y).map (algebraMap _ (Y.presheaf.stalk η)) :=
    stalkIdeal_eq_map_stalkSpecializes D h
  have hle : D.stalkIdeal y ≤ (IsLocalRing.maximalIdeal (Y.presheaf.stalk η)).comap
      (Y.presheaf.stalkSpecializes h).hom := by
    intro a ha
    rw [Ideal.mem_comap, ← hη, hmap]
    exact Ideal.mem_map_of_mem _ ha
  refine le_antisymm ?_ hle
  intro a ha
  rw [Ideal.mem_comap, ← hη, hmap] at ha
  have := IsLocalization.under_map_of_isPrime_disjoint (((IsLocalRing.maximalIdeal
    (Y.presheaf.stalk η)).comap (Y.presheaf.stalkSpecializes h).hom).primeCompl)
    (Y.presheaf.stalk η) (I := D.stalkIdeal y) inferInstance (by
      rw [Set.disjoint_left]
      intro b hb hb'
      exact hb (hle hb'))
  rw [← this]
  exact ha

end Subscheme

/-- A point of `W_*` lies on a component of `W` not contained in `E_1`
(`W_*` is a finite union of closed sets, hence closed). -/
theorem DatumI.Raw.exists_mem_irreducibleComponents_of_mem_pts_prepWStar
    [TopologicalSpace.NoetherianSpace X] (ℜ : DatumI.Raw X) (E₁ : Subscheme X) {x : X}
    (hx : x ∈ (ℜ.prepWStar E₁).pts) :
    ∃ W₁ ∈ ℜ.W.irreducibleComponents, ¬ W₁.IsContainedIn E₁ ∧ x ∈ W₁.pts := by
  rw [DatumI.Raw.pts_prepWStar] at hx
  set S := {Z : Closeds X | ∃ W₁ ∈ ℜ.W.irreducibleComponents, ¬ W₁.IsContainedIn E₁ ∧
    Z = W₁.support} with hS
  have hfin : S.Finite := by
    refine (finite_setOf_maximal_isIrreducible_subset (X := X) ℜ.W.support.isClosed).subset ?_
    rintro Z ⟨W₁, ⟨Zw, hZw, rfl⟩, -, rfl⟩
    have : (Subscheme.ofClosed Zw).support = Zw :=
      SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Zw)
    rw [this]
    exact hZw
  have hcl : IsClosed (⋃₀ ((↑) '' S : Set (Set X))) :=
    (hfin.image _).isClosed_sUnion (by rintro _ ⟨Z, -, rfl⟩; exact Z.isClosed)
  rw [hcl.closure_eq] at hx
  obtain ⟨_, ⟨Z, ⟨W₁, hW₁, hn, rfl⟩, rfl⟩, hxZ⟩ := hx
  exact ⟨W₁, hW₁, hn, hxZ⟩

/-- Two irreducible components, of two (possibly different) subschemes, through `x` with the same
stalk at `x` are equal (`Subscheme.eq_of_stalkIdeal_eq` for two ambient subschemes). -/
theorem Subscheme.eq_of_stalkIdeal_eq_of_mem_irreducibleComponents {D₁ D₂ C₁ C₂ : Subscheme X}
    (hC₁ : C₁ ∈ D₁.irreducibleComponents) (hC₂ : C₂ ∈ D₂.irreducibleComponents) {x : X}
    (hx₁ : x ∈ C₁.pts) (hx₂ : x ∈ C₂.pts) (h : C₁.stalkIdeal x = C₂.stalkIdeal x) :
    C₁ = C₂ := by
  obtain ⟨⟨U, hU⟩, hxW⟩ := Subscheme.exists_affineOpen_mem x
  replace hxW : x ∈ U := hxW
  obtain ⟨q₁, -, hq₁x, rfl⟩ := Subscheme.compStalk_exists_prime D₁ hU hxW hC₁ hx₁
  obtain ⟨q₂, -, hq₂x, rfl⟩ := Subscheme.compStalk_exists_prime D₂ hU hxW hC₂ hx₂
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxW⟩ : U)
  have := hU.isLocalization_stalk ⟨x, hxW⟩
  rw [Subscheme.compStalk_stalkIdeal_ofClosed_closure hU hxW,
    Subscheme.compStalk_stalkIdeal_ofClosed_closure hU hxW] at h
  change q₁.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) =
    q₂.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) at h
  have h' := congrArg (Ideal.comap (algebraMap Γ(X, U) (X.presheaf.stalk x))) h
  rw [Subscheme.compStalk_under_map _ q₁.asIdeal hq₁x,
    Subscheme.compStalk_under_map _ q₂.asIdeal hq₂x] at h'
  have : q₁ = q₂ := PrimeSpectrum.ext h'
  subst this
  rfl

/-- The stalk at `y` of the reduced structure on `closure {y}` is the maximal ideal. -/
theorem stalkIdeal_ofClosed_closure_self' (y : X) :
    (Subscheme.ofClosed ⟨closure {y}, isClosed_closure⟩).stalkIdeal y =
      IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
  obtain ⟨⟨U, hU⟩, hyU⟩ := Subscheme.exists_affineOpen_mem y
  replace hU : IsAffineOpen U := hU
  replace hyU : y ∈ U := hyU
  set q := hU.primeIdealOf ⟨y, hyU⟩
  have hq : hU.fromSpec q = y := hU.fromSpec_primeIdealOf ⟨y, hyU⟩
  have hst := Subscheme.compStalk_stalkIdeal_ofClosed_closure hU hyU q
  rw [hq] at hst
  rw [hst]
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hyU⟩ : U)
  have := hU.isLocalization_stalk ⟨y, hyU⟩
  exact IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal (X.presheaf.stalk y)

/-- Lemma 3 in the transversal form needed in Proposition 5 (p. 291, "with help of Lemma 3"): at a
point `x ∈ F`, if `E = ⋃ E_i` has only normal crossings with `F`, `⋃_{i≠i₀} E_i` has only normal
crossings with `W`, `F ⊆ W`, `F_x = W_x + E_{i₀,x}` (transversality), `E_{i₀} ⊉ W`, and every `E_j`
containing `F` near `x` contains `W` there or equals `E_{i₀}` there, then `E` has only normal
crossings with `W` at `x`.

The proof is the chain of the paper's proof of Lemma 3 (p. 286), with `P = W_x`, `Q = F_x`:
(1) "`(z_1, …, z_β)` can be extended to a minimal base of `P`" (the `z_j`, `j ≤ β`, are the generators
of the components `E_j ≠ E_{i₀}` with `W ⊆ E_j`, taken in the regular system of parameters that the
normal crossings of `⋃_{i≠i₀} E_i` with `W` provide in place of (i); `exists_extendsToRSOP_span_eq_of_extendsToRSOP`);
(2) "`(z, w)` can be extended to a minimal base of `Q`", where `Q = P + (z)` for the generator `z` of
`E_{i₀}` (`exists_extendsToRSOP_insert_span_eq_of_eq_sup`: the minimal base of `Q` is chosen to
contain `z`, which plays the role of `y_1`); (3) "(ii) and (iii) imply that `(z, w, y, z_{β+1}, …, z_α)`
can be extended to a regular system of parameters of `R`" (`exists_extendsToRSOP_union_of_quotient_of_subset`:
the generators `z_j`, `j > β`, of the other components lie in the regular system of parameters given by (ii)
and outside `Q`, by the hypothesis on the `E_j` containing `F`); (4) "It follows that …".

Deviation from the paper (gap filled; incomplete citation): Lemma 3 as stated (hypothesis (iii):
any `E_j` containing `F` contains `W`) does not cover `E_1`, which contains `F = W_* ∩ E_1` but not
`W`.  The paper adds "(Here, we must use the fact that `ℜ` is resolved at every generic point of
`F`)"; that fact gives the transversality `F_x = W_x + E_{1,x}`
(`PrepSetting.resolvedAt_of_mem_prepF`), and the generator of `E_1` is put into the minimal base of
`Q` by the exchange of `exists_extendsToRSOP_insert_span_eq_of_eq_sup`.  The hypothesis
`F ⊆ W` (`_hQF`) follows from the transversality and is not used. -/
theorem Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_of_transversal
    (hX : X.IsNonsingular) {α : ℕ} (E : Fin α → Subscheme X)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) (i₀ : Fin α)
    (hred : (Subscheme.unionFam E).IsReduced) {W F : Subscheme X} {x : X} (hxF : x ∈ F.pts)
    (hiF : (Subscheme.unionFam E).HasOnlyNormalCrossingsWithAt F x)
    (hrest : (prepERest E i₀).HasOnlyNormalCrossingsWithAt W x)
    (_hQF : W.stalkIdeal x ≤ F.stalkIdeal x)
    (hzQ : ¬ (E i₀).stalkIdeal x ≤ W.stalkIdeal x)
    (hT : F.stalkIdeal x = W.stalkIdeal x ⊔ (E i₀).stalkIdeal x)
    (hd : ∀ j, E j ≠ E i₀ → (E j).stalkIdeal x ≤ F.stalkIdeal x →
      (E j).stalkIdeal x ≤ W.stalkIdeal x ∨ (E j).stalkIdeal x = (E i₀).stalkIdeal x) :
    (Subscheme.unionFam E).HasOnlyNormalCrossingsWithAt W x := by
  classical
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  -- (ii): a regular system of parameters `ZE` with the generators of the components of `E`, in
  -- which `Q = F_x` is generated by a part `tF`; the hypothesis on the `E_i`, `E_i ≠ E_{i₀}`, with
  -- `W`: a regular system of parameters `ZW` with the generators of their components, in which
  -- `P = W_x` is generated by a part `tW`
  obtain ⟨ZE, hZE, ⟨tF, htF, hFt⟩, hEZE⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    E hE (fun i => iInf_le _ i) hiF
  obtain ⟨ZW, hZW, ⟨tW, htWZ, hWt⟩, hEZW⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    (fun i : {i : Fin α // E i ≠ E i₀} => E i) (fun i => hE i)
    (fun i => iInf_le (fun j : {j : Fin α // E j ≠ E i₀} => E j) i) hrest
  have hZEm : ∀ c ∈ ZE, c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := fun c hc =>
    hZE.1 ▸ Ideal.subset_span hc
  -- `z` generates `E_{i₀}` at `x` (the component of `E` that contains `F` but not `W`)
  obtain ⟨z, hzZ, hzE⟩ : ∃ z ∈ ZE, (E i₀).stalkIdeal x = Ideal.span {z} := by
    rcases hEZE i₀ with h | h
    · exfalso
      have h1 := Subscheme.stalkIdeal_le_maximalIdeal F hxF
      rw [hT, h, sup_top_eq] at h1
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp h1)
    · exact h
  have hzQ' : z ∉ W.stalkIdeal x := fun h =>
    hzQ (hzE ▸ (Ideal.span_singleton_le_iff_mem _).mpr h)
  have hF : F.stalkIdeal x = W.stalkIdeal x ⊔ Ideal.span {z} := hzE ▸ hT
  -- `P = W_x` and `Q = F_x` are primes with regular quotients (`W` and `F` are non-singular)
  have hPext : ExtendsToRSOP (X.presheaf.stalk x) tW :=
    (ExtendsToRSOP.of_isRegularSystemOfParameters hZW).mono htWZ
  have hPprime : (W.stalkIdeal x).IsPrime := by rw [hWt]; exact hPext.isPrime_span
  have hPreg : IsRegularLocalRing (X.presheaf.stalk x ⧸ W.stalkIdeal x) := by
    rw [hWt]; exact hPext.isRegularLocalRing_quotient
  have hQext : ExtendsToRSOP (X.presheaf.stalk x) tF :=
    (ExtendsToRSOP.of_isRegularSystemOfParameters hZE).mono htF
  have hQprime : (F.stalkIdeal x).IsPrime := by rw [hFt]; exact hQext.isPrime_span
  have hQreg : IsRegularLocalRing (X.presheaf.stalk x ⧸ F.stalkIdeal x) := by
    rw [hFt]; exact hQext.isRegularLocalRing_quotient
  -- "We arrange the indices of the `E_j` in such a way that `W ⊆ E_j` for `j ≤ β` and `W ⊄ E_j`
  -- for `j > β`" (for the `E_j` other than `E_{i₀}`): the generators `z_1, …, z_β` (in `ZW`) and
  -- `z_{β+1}, …, z_α` (in `ZE`, not associate to `z`)
  set Gβ : Finset (X.presheaf.stalk x) := ZW.filter fun a =>
    ∃ j, E j ≠ E i₀ ∧ (E j).stalkIdeal x = Ideal.span {a} ∧ (E j).stalkIdeal x ≤ W.stalkIdeal x
    with hGβ
  set Gγ : Finset (X.presheaf.stalk x) := ZE.filter fun c =>
    ∃ j, E j ≠ E i₀ ∧ (E j).stalkIdeal x = Ideal.span {c} ∧ ¬ (E j).stalkIdeal x ≤ W.stalkIdeal x ∧
      ¬ Ideal.span {c} = Ideal.span {z} with hGγ
  -- `z_j ∈ P` for `j ≤ β`
  have hGβP : (Gβ : Set (X.presheaf.stalk x)) ⊆ W.stalkIdeal x := by
    intro a ha
    obtain ⟨j, -, hja, hjW⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    exact hjW (hja ▸ Ideal.mem_span_singleton_self a)
  -- `z_j ∉ Q` for `j > β` (by the hypothesis on the `E_j` containing `F`)
  have hGγQ : ∀ a ∈ Gγ, a ∉ F.stalkIdeal x := by
    intro a ha haQ
    obtain ⟨j, hj, hja, hjW, hass⟩ := (Finset.mem_filter.mp ha).2
    have hle : (E j).stalkIdeal x ≤ F.stalkIdeal x := by
      rw [hja, Ideal.span_singleton_le_iff_mem]; exact haQ
    rcases hd j hj hle with h | h
    · exact hjW h
    · exact hass (hja.symm.trans (h.trans hzE))
  -- (1) "`(z_1, …, z_β)` can be extended to a minimal base of `P`"
  obtain ⟨T, hGβT, hTe, hTP⟩ := exists_extendsToRSOP_span_eq_of_extendsToRSOP (W.stalkIdeal x)
    hPreg ((ExtendsToRSOP.of_isRegularSystemOfParameters hZW).mono (Finset.filter_subset _ _))
    hGβP
  -- (2) "`(z, w)` can be extended to a minimal base of `Q`", here `Q = P + (z)` and the new
  -- generator `y_1` is `z`, the generator of `E_{i₀}`
  obtain ⟨T', hTT', hzT', hT'e, hT'Q⟩ := exists_extendsToRSOP_insert_span_eq_of_eq_sup
    (F.stalkIdeal x) hQreg hTe (by rw [hTP]; exact hF) (by rw [hTP]; exact hzQ')
  -- (3) "(ii) and (iii) imply that `(z, w, y, z_{β+1}, …, z_α)` can be extended to a regular
  -- system of parameters of `R`"
  obtain ⟨Z, hUZ, hZ⟩ := exists_extendsToRSOP_union_of_quotient_of_subset (F.stalkIdeal x) hT'e
    hT'Q hZE htF hFt.symm (Finset.filter_subset _ _) hGγQ
  have hzZ' : z ∈ Z := hUZ (Finset.mem_union_left _ hzT')
  -- (4) "It follows that `E_1 ∪ ⋯ ∪ E_α` has only normal crossings with `W` at `x`"
  refine (Subscheme.hasOnlyNormalCrossingsWithAt_iff hred (hX x)).mpr ⟨Z, hZ, ?_,
    ⟨T, fun a ha => hUZ (Finset.mem_union_left _ (hTT' ha)), hTP.symm⟩⟩
  obtain ⟨K₁, hK₁, h⟩ := DatumTransform.iInf_eq_span_prod (fun i => (E i).stalkIdeal x)
    (ExtendsToRSOP.of_isRegularSystemOfParameters hZ) (fun i => by
      by_cases hi : E i = E i₀
      · rw [hi]; exact Or.inr ⟨z, hzZ', hzE⟩
      · by_cases hiW : (E i).stalkIdeal x ≤ W.stalkIdeal x
        · rcases hEZW ⟨i, hi⟩ with h | ⟨a, ha, haE⟩
          · exact Or.inl h
          · exact Or.inr ⟨a, hUZ (Finset.mem_union_left _
              (hTT' (hGβT (Finset.mem_filter.mpr ⟨ha, i, hi, haE, hiW⟩)))), haE⟩
        · rcases hEZE i with h | ⟨a, ha, haE⟩
          · exact Or.inl h
          · by_cases hass : Ideal.span {a} = Ideal.span {z}
            · exact Or.inr ⟨z, hzZ', haE.trans hass⟩
            · exact Or.inr ⟨a, hUZ (Finset.mem_union_right _
                (Finset.mem_filter.mpr ⟨ha, i, hi, haE, hiW, hass⟩)), haE⟩)
  refine ⟨K₁, hK₁, ?_⟩
  rw [Subscheme.unionFam, DatumTransform.stalkIdeal_iInf_fintype]
  exact h

/-- Lemma 3 in the trivial case `x ∉ E_{i₀}` (so that `E` and `⋃_{i≠i₀} E_i` agree near `x`). -/
theorem Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_of_stalkIdeal_eq_top
    (hX : X.IsNonsingular) {α : ℕ} (E : Fin α → Subscheme X)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) (i₀ : Fin α)
    (hred : (Subscheme.unionFam E).IsReduced) {W : Subscheme X} {x : X}
    (hrest : (prepERest E i₀).HasOnlyNormalCrossingsWithAt W x)
    (htop : (E i₀).stalkIdeal x = ⊤) :
    (Subscheme.unionFam E).HasOnlyNormalCrossingsWithAt W x := by
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  obtain ⟨ZW, hZW, ⟨tW, htWZ, hWt⟩, hEZW⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    (fun i : {i : Fin α // E i ≠ E i₀} => E i) (fun i => hE i)
    (fun i => iInf_le (fun j : {j : Fin α // E j ≠ E i₀} => E j) i) hrest
  refine (Subscheme.hasOnlyNormalCrossingsWithAt_iff hred (hX x)).mpr ⟨ZW, hZW, ?_,
    ⟨tW, htWZ, hWt⟩⟩
  obtain ⟨K₁, hK₁, h⟩ := DatumTransform.iInf_eq_span_prod (fun i => (E i).stalkIdeal x)
    (ExtendsToRSOP.of_isRegularSystemOfParameters hZW) (fun i => by
      by_cases hi : E i = E i₀
      · rw [hi]; exact Or.inl htop
      · exact hEZW ⟨i, hi⟩)
  refine ⟨K₁, hK₁, ?_⟩
  rw [Subscheme.unionFam, DatumTransform.stalkIdeal_iInf_fintype]
  exact h

/-- A finite union of non-singular irreducible subschemes of codimension one (or empty ones) is
reduced: its stalks are intersections of radical ideals. -/
theorem Subscheme.isReduced_unionFam {ι : Type*} [Fintype ι] (E : ι → Subscheme X)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) : (Subscheme.unionFam E).IsReduced := by
  refine Subscheme.isReduced_of_isRadical_stalkIdeal fun y => ?_
  rw [Subscheme.unionFam, DatumTransform.stalkIdeal_iInf_fintype]
  refine Ideal.isRadical_iInf _ fun i => Subscheme.isRadical_stalkIdeal_of_isReduced ?_ y
  rcases hE i with h | ⟨hns, -, -⟩
  · rw [h]; exact Subscheme.isReduced_empty
  · exact Subscheme.isReduced_of_isNonsingular hns

/-- Normal crossings of `E_1 ∪ ⋯ ∪ E_α` with `D` give those of `⋃_{E_i ≠ E_{i₀}} E_i` with `D`
(the same regular system of parameters works). -/
theorem Subscheme.hasOnlyNormalCrossingsWithAt_prepERest (hX : X.IsNonsingular) {α : ℕ}
    (E : Fin α → Subscheme X) (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) (i₀ : Fin α)
    {D : Subscheme X} {y : X} (h : (Subscheme.unionFam E).HasOnlyNormalCrossingsWithAt D y) :
    (prepERest E i₀).HasOnlyNormalCrossingsWithAt D y := by
  classical
  have : IsRegularLocalRing (X.presheaf.stalk y) := hX y
  obtain ⟨Z, hZ, ⟨T, hTZ, hDT⟩, hEZ⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    E hE (fun i => iInf_le _ i) h
  have hred : (prepERest E i₀).IsReduced :=
    Subscheme.isReduced_unionFam (fun i : {i : Fin α // E i ≠ E i₀} => E i) (fun i => hE i)
  refine (Subscheme.hasOnlyNormalCrossingsWithAt_iff hred (hX y)).mpr ⟨Z, hZ, ?_, ⟨T, hTZ, hDT⟩⟩
  obtain ⟨K₁, hK₁, h⟩ := DatumTransform.iInf_eq_span_prod
    (fun i : {i : Fin α // E i ≠ E i₀} => (E i).stalkIdeal y)
    (ExtendsToRSOP.of_isRegularSystemOfParameters hZ) (fun i => hEZ i)
  refine ⟨K₁, hK₁, ?_⟩
  rw [prepERest, Subscheme.unionFam, DatumTransform.stalkIdeal_iInf_fintype]
  exact h

/-- Normal crossings of `⋃_i E_i` with `D` at `y` give those of every sub-union `⋃_k E_{e(k)}` with `D`
(the same regular system of parameters works).  This generalizes
`Subscheme.hasOnlyNormalCrossingsWithAt_prepERest` to an arbitrary sub-family; it is the tacit step
"a sub-union of the components of `E` also has only normal crossings with `D`" of p. 290 (the tail
`⋃_{i≥2} E_i'` of the presentation of `f*(ℜ)` is a sub-union of the components of `f*(ℜ_tail)`). -/
theorem Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_comp (hX : X.IsNonsingular) {ι κ : Type*}
    [Fintype ι] [Fintype κ] (E : ι → Subscheme X) (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne)
    (e : κ → ι) {D : Subscheme X} {y : X}
    (h : (Subscheme.unionFam E).HasOnlyNormalCrossingsWithAt D y) :
    (Subscheme.unionFam (fun k => E (e k))).HasOnlyNormalCrossingsWithAt D y := by
  classical
  have : IsRegularLocalRing (X.presheaf.stalk y) := hX y
  obtain ⟨Z, hZ, ⟨T, hTZ, hDT⟩, hEZ⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    E hE (fun i => iInf_le _ i) h
  have hred : (Subscheme.unionFam (fun k => E (e k))).IsReduced :=
    Subscheme.isReduced_unionFam (fun k => E (e k)) (fun k => hE (e k))
  refine (Subscheme.hasOnlyNormalCrossingsWithAt_iff hred (hX y)).mpr ⟨Z, hZ, ?_, ⟨T, hTZ, hDT⟩⟩
  obtain ⟨K₁, hK₁, h⟩ := DatumTransform.iInf_eq_span_prod (fun k => (E (e k)).stalkIdeal y)
    (ExtendsToRSOP.of_isRegularSystemOfParameters hZ) (fun k => hEZ (e k))
  refine ⟨K₁, hK₁, ?_⟩
  rw [Subscheme.unionFam, DatumTransform.stalkIdeal_iInf_fintype]
  exact h

/-- A sub-union of the components of the boundary of a datum is the boundary of a datum with the
same `V_j` and `W` (the tail `(⋃_{i∈J} E_i; V; W)`; generalizes `isDatum_rest` to an arbitrary
sub-family of the presentation).  Tacit in the paper (p. 290: the datum
`(⋃_{i≥2} E_i; V_1, …, V_β; W)` is "a resolution datum"). -/
theorem DatumI.Raw.isDatum_tail {X : Scheme.{u}} (hX : X.IsNonsingular) {ι κ : Type*} [Fintype ι]
    [Fintype κ] (E : ι → Subscheme X) (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne)
    (ℜ : DatumI.Raw X) (hℜ : ℜ.IsDatum) (hEunion : ℜ.E = Subscheme.unionFam E) (e : κ → ι) :
    ({ ℜ with E := Subscheme.unionFam (fun k => E (e k)) } : DatumI.Raw X).IsDatum := by
  classical
  have hred : (Subscheme.unionFam (fun k => E (e k))).IsReduced :=
    Subscheme.isReduced_unionFam (fun k => E (e k)) (fun k => hE (e k))
  have hstalk : ∀ y, ∃ K : Finset (X.presheaf.stalk y), ExtendsToRSOP _ K ∧
      (Subscheme.unionFam (fun k => E (e k))).stalkIdeal y = Ideal.span {∏ k ∈ K, k} := by
    intro y
    have : IsRegularLocalRing (X.presheaf.stalk y) := hX y
    have h : (Subscheme.unionFam E).HasOnlyNormalCrossingsAt y := hEunion ▸ hℜ.2.2.1 y
    obtain ⟨Z, hZ, -, hEZ⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
      E hE (fun i => iInf_le _ i) h
    obtain ⟨K₁, hK₁, h⟩ := DatumTransform.iInf_eq_span_prod
      (fun k => (E (e k)).stalkIdeal y)
      (ExtendsToRSOP.of_isRegularSystemOfParameters hZ) (fun k => hEZ (e k))
    refine ⟨K₁, (ExtendsToRSOP.of_isRegularSystemOfParameters hZ).mono hK₁, ?_⟩
    rw [Subscheme.unionFam, DatumTransform.stalkIdeal_iInf_fintype]
    exact h
  exact ⟨hred, DatumTransform.isEverywhereCodimOne_of_forall_stalk hX hstalk,
    DatumTransform.hasOnlyNormalCrossings_of_forall_stalk hX hred hstalk, hℜ.2.2.2.1,
    hℜ.2.2.2.2⟩

/-- Permissibility passes to the tail: if `B` is permissible for `ℜ` (with `ℜ.E = ⋃ E_i`), it is
permissible for the datum with the sub-union `⋃_k E_{e(k)}` of the components as boundary (the
same `V_j` and `W`; the normal crossings with `B` pass to sub-unions).

Deviation from the paper (gap filled): tacit on p. 290, where Lemma 4 is applied to the datum
`(⋃_{i≥2} E_i; V; W)` and the center `B` permissible for `ℜ`. -/
theorem DatumI.Raw.IsPermissible.tail {X : Scheme.{u}} (hX : X.IsNonsingular) {B : Subscheme X}
    {ι κ : Type*} [Fintype ι] [Fintype κ] (E : ι → Subscheme X)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) {ℜ : DatumI.Raw X}
    (hEunion : ℜ.E = Subscheme.unionFam E) (hB : ℜ.IsPermissible B) (e : κ → ι) :
    ({ ℜ with E := Subscheme.unionFam (fun k => E (e k)) } : DatumI.Raw X).IsPermissible B := by
  refine ⟨hB.1, DatumI.Raw.isDatum_tail hX E hE (ℜ.extendBy B) hB.2.1 hEunion e, fun x hx => ?_⟩
  have h := hB.2.2 x hx
  refine ⟨h.1, h.2.1, ?_⟩
  have h3 : (Subscheme.unionFam E).HasOnlyNormalCrossingsWithAt B x := by
    have h4 := h.2.2
    change ℜ.E.HasOnlyNormalCrossingsWithAt B x at h4
    rwa [hEunion] at h4
  exact Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_comp hX E hE e h3

/-- An open restriction for `ℜ` is one for the tail datum `(⋃_k E_{e(k)}; V; W)`: the normal
crossings with `W` at the points of `U` pass to sub-unions.  Tacit on p. 290. -/
theorem DatumI.Raw.IsOpenRestriction.tail {X : Scheme.{u}} (hX : X.IsNonsingular) {U : Set X}
    {ι κ : Type*} [Fintype ι] [Fintype κ] (E : ι → Subscheme X)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) {ℜ : DatumI.Raw X}
    (hEunion : ℜ.E = Subscheme.unionFam E) (hU : ℜ.IsOpenRestriction U) (e : κ → ι) :
    ({ ℜ with E := Subscheme.unionFam (fun k => E (e k)) } : DatumI.Raw X).IsOpenRestriction U := by
  refine ⟨hU.1, hU.2.1, fun x hx => ?_⟩
  have h := hU.2.2 x hx
  refine ⟨h.1, h.2.1, ?_⟩
  have h3 : (Subscheme.unionFam E).HasOnlyNormalCrossingsWithAt ℜ.W x := by
    have h4 := h.2.2
    rwa [hEunion] at h4
  exact Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_comp hX E hE e h3

/-- The boundary of the transform of a tail datum (Definition 7, p. 168, applied to
`(⋃_{i∈J} E_i; V; W)`): if `E'` is the presentation of `f*(ℜ).E` (the strict transforms of the
`E_i` followed by the exceptional divisor), the boundary of `f*` of the tail datum is the
sub-union of the `E_j'` with `j = i + 1`-th for `i ∈ J`, together with the exceptional divisor.

Deviation from the paper (gap filled): the paper writes "`(⋃_{i≥2} E_i'; …)`" for the transform of
the tail without comment (p. 290); Lean proves that the strict transform of a sub-union of the
components is the sub-union of the strict transforms (`DatumTransform.strictTransform_iInf_eq`,
whose hypothesis comes from the normal crossings of `ℜ.E` with itself and with `B`). -/
theorem DatumI.Raw.transform_tail_E {X : Scheme.{u}} (hX : X.IsNonsingular) {B : Subscheme X}
    {α : ℕ} (E : Fin α → Subscheme X) (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne)
    {ℜ : DatumI.Raw X} (hℜ : ℜ.IsDatum) (hEunion : ℜ.E = Subscheme.unionFam E)
    (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B)
    (E' : Fin (α + 1) → Subscheme t.X')
    (hcs : ∀ i : Fin α, E' i.castSucc = Subscheme.strictTransform t (E i))
    (hlast : E' (Fin.last α) = t.exceptional) (J : Set (Fin α)) :
    (({ ℜ with E := Subscheme.unionFam (fun i : J => E i) } : DatumI.Raw X).transform t).E =
      Subscheme.unionFam (fun j : ↥(Fin.castSucc '' J ∪ {Fin.last α}) => E' j) := by
  classical
  have hBns := hB.1.isNonsingular
  have hNC : (⨅ i, E i).HasOnlyNormalCrossings := by
    have := hℜ.2.2.1; rw [hEunion] at this; exact this
  have hNCB : (⨅ i, E i).HasOnlyNormalCrossingsWith B := fun x hx => by
    have := (hB.2.2 x hx).2.2
    change ℜ.E.HasOnlyNormalCrossingsWithAt B x at this
    rw [hEunion] at this; exact this
  have hdata := DatumTransform.exists_rsop_adapted_of_isDatum E hX hE hNC hNCB
  have hst := DatumTransform.strictTransform_iInf_eq hX hBns t (fun i : J => E i) (fun x => by
    obtain ⟨Z, hZ, h1, h2⟩ := hdata x
    exact ⟨Z, hZ, h1, fun i => h2 i⟩)
  change (Subscheme.strictTransform t (⨅ i : J, E i)).union t.exceptional =
    ⨅ j : ↥(Fin.castSucc '' J ∪ {Fin.last α}), E' j
  rw [hst]
  change (⨅ i : J, Subscheme.strictTransform t (E i)) ⊓ t.exceptional = _
  apply le_antisymm
  · refine le_iInf fun ⟨j, hj⟩ => ?_
    rcases hj with ⟨i, hi, rfl⟩ | hj
    · show _ ≤ E' i.castSucc
      rw [hcs]
      exact inf_le_left.trans (iInf_le (fun i : J => Subscheme.strictTransform t (E i)) ⟨i, hi⟩)
    · have hj' : j = Fin.last α := hj
      subst hj'
      show _ ≤ E' (Fin.last α)
      rw [hlast]
      exact inf_le_right
  · refine le_inf (le_iInf fun i => ?_) ?_
    · have := iInf_le (fun j : ↥(Fin.castSucc '' J ∪ {Fin.last α}) => E' j)
        ⟨i.1.castSucc, Or.inl ⟨i.1, i.2, rfl⟩⟩
      rw [hcs] at this
      exact this
    · have := iInf_le (fun j : ↥(Fin.castSucc '' J ∪ {Fin.last α}) => E' j)
        ⟨Fin.last α, Or.inr rfl⟩
      rw [hlast] at this
      exact this

/-- The centers of a succession lie over `Z`: the first center lies in `Z` and the centers of the rest
lie over the strict transform of `Z` (used for "the exceptional divisors `E_j'`, `j > α`, lie over
the centers", p. 290: `W' ∩ E_j' ⊆ f⁻¹(F)`). -/
def MonoidalSuccession.CentersIn : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Subscheme X →
    Prop
  | _, _, .nil _, _ => True
  | _, _, .cons B t rest, Z => B.pts ⊆ Z.pts ∧ rest.CentersIn (Subscheme.strictTransform t Z)

/-- A succession permissible for `(ℜ, U)` has its centers over the principal subscheme `W` (the
center `B ⊆ W − U` at each step, and `W` transforms to its strict transform). -/
theorem MonoidalSuccession.centersIn_of_isPermissibleIOpen {X Y : Scheme.{u}}
    (s : MonoidalSuccession X Y) (ℜ : DatumI.Raw X) (U : Set X) (hs : s.IsPermissibleIOpen ℜ U) :
    s.CentersIn ℜ.W := by
  induction s with
  | nil X => trivial
  | cons B t rest ih => exact ⟨fun x hx => (hs.1.2 hx).1, ih _ _ hs.2⟩

/-- The exceptional divisors of a succession: the strict transforms, under the later steps, of the
exceptional divisors of the successive transformations (the `E_j'` with `j > α` of p. 290). -/
def MonoidalSuccession.exceptionalDivisors : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    Set (Subscheme Y)
  | _, _, .nil _ => ∅
  | _, _, .cons _ t rest => insert (rest.strictTransform t.exceptional) rest.exceptionalDivisors

/-- The presentation of the transformed boundary along a permissible succession, together with the
presentation of the transformed *tail* (Definition 7, p. 168, and the proof of Proposition 5,
p. 290: "the resolution datum `(⋃_{i≥2} E_i'; V_1', …, V_β'; W')`"): for a sub-family `J` of the
`E_i`, the boundary of `f*(⋃_{i∈J} E_i; V; W)` is the sub-union of the `E_j'` over a set `J'` of
indices containing the images of the `i ∈ J` (and no image of an `i ∉ J`) and all the indices
`j ≥ α` of exceptional divisors, and `f` is again permissible for the tail datum with the same open
restriction.

Deviation from the paper (gap filled): tacit in the paper (p. 290). -/
theorem MonoidalSuccession.exists_presentation_transformI_tail [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {X Y : Scheme.{u}}
    (s : MonoidalSuccession X Y) (hXa : IsAlgebraicScheme X) (hX : X.IsNonsingular)
    {α : ℕ} (E : Fin α → Subscheme X) (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne)
    (ℜ : DatumI.Raw X) (hℜ : ℜ.IsDatum) (hEunion : ℜ.E = Subscheme.unionFam E)
    (hs : s.IsPermissibleI ℜ) (J : Set (Fin α)) :
    ∃ (α' : ℕ) (h : α ≤ α') (E' : Fin α' → Subscheme Y),
      (∀ i, (E' i).IsNonsingularIrreducibleCodimOne) ∧
      (s.transformI ℜ).E = Subscheme.unionFam E' ∧
      (∀ i : Fin α, E' (Fin.castLE h i) = s.strictTransform (E i)) ∧
      ∃ J' : Set (Fin α'), (∀ i : Fin α, Fin.castLE h i ∈ J' ↔ i ∈ J) ∧
        (∀ j : Fin α', α ≤ j.val → j ∈ J') ∧
        (s.transformI ({ ℜ with E := Subscheme.unionFam (fun i : J => E i) } :
            DatumI.Raw X)).E = Subscheme.unionFam (fun j : J' => E' j) ∧
        (∀ U, s.IsPermissibleIOpen ℜ U →
          s.IsPermissibleIOpen ({ ℜ with E := Subscheme.unionFam (fun i : J => E i) } :
            DatumI.Raw X) U) ∧
        (∀ Z : Subscheme X, s.CentersIn Z → ∀ j : Fin α', α ≤ j.val → ∀ x ∈ (E' j).pts,
          s.composite.base x ∈ Z.pts) ∧
        (∀ T : Subscheme X, ∀ y : Y, s.composite.base y ∈ T.pts →
          y ∈ (s.strictTransform T).pts ∨ ∃ j : Fin α', α ≤ j.val ∧ y ∈ (E' j).pts) ∧
        ∀ j : Fin α', α ≤ j.val → E' j ∈ s.exceptionalDivisors := by
  induction s generalizing α with
  | nil X =>
    refine ⟨α, le_rfl, E, hE, hEunion, fun i => rfl, J, fun i => Iff.rfl, fun j hj => ?_, rfl,
      fun U h => h, fun Z _ j hj => ?_, fun T y hy => Or.inl hy,
      fun j hj => ?_⟩
    · exact absurd j.2 (by omega)
    · exact absurd j.2 (by omega)
    · exact absurd j.2 (by omega)
  | cons B t rest ih =>
    obtain ⟨E₁, hE₁, hEq₁, hcs₁, hlast₁⟩ :=
      @DatumI.Raw.exists_presentation_transform _ _ hXa hX α E hE ℜ hℜ hEunion t hs.1
    have hdat := (DatumI.Raw.transform_isDatum (X := _) hX ℜ hℜ t hs.1).1
    have hT := DatumI.Raw.transform_tail_E hX E hE hℜ hEunion t hs.1 E₁ hcs₁ hlast₁ J
    have hRJ : ({ ℜ with E := Subscheme.unionFam (fun i : J => E i) } : DatumI.Raw _).transform t =
        ({ (ℜ.transform t) with E := Subscheme.unionFam (fun j : ↥(Fin.castSucc '' J ∪ {Fin.last α}) => E₁ j) } : DatumI.Raw t.X') := by
      rw [← hT]; rfl
    obtain ⟨α', h', E', hE', hEq', hcs', J'', hJ1, hJ2, hJ3, hJ4, hC', hG1', hX1⟩ := ih t.isAlgebraicScheme
      (t.isNonsingular_and_isNonsingular_exceptional hX hs.1.1.isNonsingular).1 E₁ hE₁
      (ℜ.transform t) hdat hEq₁ hs.2 (Fin.castSucc '' J ∪ {Fin.last α})
    refine ⟨α', (Nat.le_succ α).trans h', E', hE', hEq', fun i => ?_, J'', fun i => ?_,
      fun j hj => ?_, ?_, fun U hU => ?_, fun Z hZ j hj x hx => ?_, fun T y hy => ?_, fun j hj => ?_⟩
    · have h1 : Fin.castLE ((Nat.le_succ α).trans h') i = Fin.castLE h' i.castSucc :=
        Fin.ext rfl
      rw [h1, hcs' i.castSucc, hcs₁ i]
      rfl
    · have h1 : Fin.castLE ((Nat.le_succ α).trans h') i = Fin.castLE h' i.castSucc :=
        Fin.ext rfl
      rw [h1, hJ1]
      constructor
      · rintro (⟨i', hi', hii⟩ | hl)
        · rwa [← Fin.castSucc_injective _ hii]
        · exact absurd (Fin.castSucc_lt_last i) (by rw [Set.mem_singleton_iff.mp hl]; exact lt_irrefl _)
      · exact fun hi => Or.inl ⟨i, hi, rfl⟩
    · by_cases hj1 : α + 1 ≤ j.val
      · exact hJ2 j hj1
      · have hjα : j.val = α := by omega
        have : j = Fin.castLE h' (Fin.last α) := Fin.ext (by simp [hjα])
        rw [this, hJ1]
        exact Or.inr rfl
    · show (rest.transformI (({ ℜ with E := Subscheme.unionFam (fun i : J => E i) } :
        DatumI.Raw _).transform t)).E = _
      rw [hRJ]
      exact hJ3
    · refine ⟨?_, ?_⟩
      · exact ⟨DatumI.Raw.IsPermissible.tail hX E hE hEunion hU.1.1 _, hU.1.2⟩
      · show (rest.IsPermissibleIOpen (({ ℜ with E := Subscheme.unionFam (fun i : J => E i) } :
          DatumI.Raw _).transform t) (DatumI.Raw.transformOpen t U))
        rw [hRJ]
        exact hJ4 _ hU.2
    · show t.f.base (rest.composite.base x) ∈ Z.pts
      by_cases hj1 : α + 1 ≤ j.val
      · exact t.pts_strictTransform_subset Z (hC' _ hZ.2 j hj1 x hx)
      · have hjα : j.val = α := by omega
        have hjeq : j = Fin.castLE h' (Fin.last α) := Fin.ext (by simp [hjα])
        rw [hjeq, hcs' (Fin.last α), hlast₁] at hx
        have hx2 := rest.pts_strictTransform_subset _ hx
        rw [MonoidalTransformation.pts_exceptional] at hx2
        exact hZ.1 hx2
    · have hy' : t.f.base (rest.composite.base y) ∈ T.pts := hy
      by_cases hxe : rest.composite.base y ∈ t.exceptional.pts
      · rcases hG1' t.exceptional y hxe with h | ⟨j, hj, hyj⟩
        · refine Or.inr ⟨Fin.castLE h' (Fin.last α), by simp, ?_⟩
          rw [hcs' (Fin.last α), hlast₁]
          exact h
        · exact Or.inr ⟨j, by omega, hyj⟩
      · have hmem : rest.composite.base y ∈ (Subscheme.strictTransform t T).pts := by
          rw [MonoidalTransformation.pts_strictTransform_eq_closure]
          exact subset_closure ⟨hy', hxe⟩
        rcases hG1' _ y hmem with h | ⟨j, hj, hyj⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, by omega, hyj⟩
    · by_cases hj1 : α + 1 ≤ j.val
      · exact Set.mem_insert_of_mem _ (hX1 j hj1)
      · have hjα : j.val = α := by omega
        have hjeq : j = Fin.castLE h' (Fin.last α) := Fin.ext (by simp [hjα])
        rw [hjeq, hcs' (Fin.last α), hlast₁]
        exact Set.mem_insert _ _

/-- Replacing the boundary of a datum changes only the boundary of its transform along a succession
(the `V_j'` and `W'` are the strict transforms, whatever `E` is). -/
theorem MonoidalSuccession.transformI_withE {X Y : Scheme.{u}} (s : MonoidalSuccession X Y)
    (ℜ : DatumI.Raw X) (e : Subscheme X) :
    s.transformI ({ ℜ with E := e } : DatumI.Raw X) =
      { s.transformI ℜ with E := (s.transformI ({ ℜ with E := e } : DatumI.Raw X)).E } := by
  induction s with
  | nil X => rfl
  | cons B t rest ih => exact ih (ℜ.transform t) _

/-- Lemma 4 of this section and Corollary 2 of Theorem 5 (Ch. III), for the tail datum along a
succession (p. 290: "Then in view of Lemma 4 of this section and Corollary 2 of Theorem 5, §6,
Ch. III, the resolution datum `(⋃_{i≥2} E_i'; V_1', …, V_β'; W')` is resolved at every point of
`Ũ'`"): if `s` is permissible for `(ℜ, U)` and the tail datum `(⋃_{i∈J} E_i; V; W)` is resolved at
`f(y)` for a point `y` of `W'`, then `f*` of the tail datum is resolved at `y`.

Deviation from the paper (gap filled): besides the two cited results (`DatumI.Raw.resolvedAt_transform_of_resolvedAt`
and its succession version `MonoidalSuccession.resolvedAt_transformI_of_resolvedAt_open`), the paper
uses tacitly that the tail is a datum (`DatumI.Raw.isDatum_tail`), that `U` is an open restriction
for it (`DatumI.Raw.IsOpenRestriction.tail`; this gives the density of `W − B` in `W`), that `s`
is permissible for the tail datum (`MonoidalSuccession.exists_presentation_transformI_tail`:
the centers are permissible for the tail because the normal crossings of `E` with `B` pass to
sub-unions) and that `f⁻¹(Ũ)` is where the tail datum of `f*(ℜ)` is controlled by that of `ℜ`. -/
theorem MonoidalSuccession.resolvedAt_transformI_tail [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} {X Y : Scheme.{u}}
    (s : MonoidalSuccession X Y) {α : ℕ} (E : Fin α → Subscheme X)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) {ℜ : DatumI.Raw X} {U : Set X}
    (h : IsGoodDatumI N n X ℜ) (hEunion : ℜ.E = Subscheme.unionFam E)
    (hU : ℜ.IsOpenRestriction U) (hs : s.IsPermissibleIOpen ℜ U) (J : Set (Fin α)) {y : Y}
    (hyW : y ∈ (s.transformI ℜ).W.pts)
    (hres : ({ ℜ with E := Subscheme.unionFam (fun i : J => E i) } : DatumI.Raw X).ResolvedAt
      (s.composite.base y)) :
    (s.transformI ({ ℜ with E := Subscheme.unionFam (fun i : J => E i) } :
      DatumI.Raw X)).ResolvedAt y := by
  have := h.1.1
  obtain ⟨α', hα', E', hE', hEq', hcs, J', hJ1, hJ2, hJ3, hperm, -, -, -⟩ :=
    s.exists_presentation_transformI_tail h.1.1 h.1.2.1 E hE ℜ h.2.1 hEunion hs.isPermissibleI J
  have hR : IsGoodDatumI N n X ({ ℜ with E := Subscheme.unionFam (fun i : J => E i) } :
      DatumI.Raw X) :=
    ⟨h.1, DatumI.Raw.isDatum_tail h.1.2.1 E hE ℜ h.2.1 hEunion (fun i : J => i.1), h.2.2⟩
  refine MonoidalSuccession.resolvedAt_transformI_of_resolvedAt_open s hR
    (DatumI.Raw.IsOpenRestriction.tail h.1.2.1 E hE hEunion hU (fun i : J => i.1))
    (hperm U hs) ?_ hres
  rw [MonoidalSuccession.transformI_W] at hyW ⊢
  exact hyW

/-- Lemma 3 (p. 286) at a point `y` of `F`, in the form needed in Proposition 5 (p. 289: "In virtue of
Lemma 3, the resolution datum `(⋃_{i≥2} E_i; V'; W')` must be resolved at every point of `F'`"): if
`E = ⋃ E_j` has only normal crossings with `F` at `y`, `W_y ⊆ F_y` with `W` simple at `y`, and every
`E_j` containing `F` near `y` contains `W` near `y` (hypothesis (iii)), then `E` has only normal
crossings with `W` at `y`.

The proof is that of Lemma 3 (p. 286) at `y`, with `P = W_y`, `Q = F_y` and the `z_j` the
generators of the components `E_j` through `y` (`j ≤ β` if `E_{j,y} ⊆ W_y`):
(1) "`(z_1, …, z_β)` can be extended to a minimal base of `P`", (2) "`(z, w)` can be extended to a
minimal base of `Q`", (3) "(ii) and (iii) imply that `(z, w, y, z_{β+1}, …, z_α)` can be extended to
a regular system of parameters of `R`", (4) "It follows that …" — with the same three lemmas
(`exists_extendsToRSOP_span_eq_of_extendsToRSOP` twice and
`exists_extendsToRSOP_union_of_quotient_of_subset`).

Deviation from the paper (statement modified, pointwise form): the paper's Lemma 3 is global with `W`
and `F` non-singular irreducible subschemes (`hasOnlyNormalCrossingsWithAt_unionFam_of_isContainedIn`);
here (iii) is a condition on the stalks at `y` (`hd`), so the passage from `z_j ∈ Q` to `F ⊆ E_j`
and the irreducibility of `W` and `F` are not needed; hypothesis (i) is not needed either, the
regular system of parameters containing `z_1, …, z_β` being the one given by (ii). -/
theorem Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_of_prime_flag (hX : X.IsNonsingular)
    {ι : Type*} [Fintype ι] (E : ι → Subscheme X)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) {W F : Subscheme X} {y : X}
    (hWy : W.IsSimpleAt y) (hiF : (Subscheme.unionFam E).HasOnlyNormalCrossingsWithAt F y)
    (hQF : W.stalkIdeal y ≤ F.stalkIdeal y)
    (hd : ∀ j, (E j).stalkIdeal y ≤ F.stalkIdeal y → (E j).stalkIdeal y ≤ W.stalkIdeal y) :
    (Subscheme.unionFam E).HasOnlyNormalCrossingsWithAt W y := by
  classical
  have : IsRegularLocalRing (X.presheaf.stalk y) := hX y
  -- `P = W_y` is prime with regular quotient (`W` is simple at `y`)
  have hPreg : IsRegularLocalRing (X.presheaf.stalk y ⧸ W.stalkIdeal y) := hWy.2
  have hPprime : (W.stalkIdeal y).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
  -- (ii): a regular system of parameters `ZE` containing the generators of the components, with
  -- `Q = F_y` generated by the part `tF`
  obtain ⟨ZE, hZE, ⟨tF, htF, hFt⟩, hEZ⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    E hE (fun i => iInf_le _ i) hiF
  have hQext : ExtendsToRSOP (X.presheaf.stalk y) tF :=
    (ExtendsToRSOP.of_isRegularSystemOfParameters hZE).mono htF
  have hQprime : (F.stalkIdeal y).IsPrime := by rw [hFt]; exact hQext.isPrime_span
  have hQreg : IsRegularLocalRing (X.presheaf.stalk y ⧸ F.stalkIdeal y) := by
    rw [hFt]; exact hQext.isRegularLocalRing_quotient
  -- "We arrange the indices of the `E_j` in such a way that `W ⊆ E_j` for `j ≤ β` and `W ⊄ E_j`
  -- for `j > β`": the generators `z_1, …, z_β` and `z_{β+1}, …, z_α`
  set Gβ : Finset (X.presheaf.stalk y) := ZE.filter fun c =>
    ∃ j, (E j).stalkIdeal y = Ideal.span {c} ∧ (E j).stalkIdeal y ≤ W.stalkIdeal y with hGβ
  set Gγ : Finset (X.presheaf.stalk y) := ZE.filter fun c =>
    ∃ j, (E j).stalkIdeal y = Ideal.span {c} ∧ ¬ (E j).stalkIdeal y ≤ W.stalkIdeal y with hGγ
  -- `z_j ∈ P` for `j ≤ β`
  have hGβP : (Gβ : Set (X.presheaf.stalk y)) ⊆ W.stalkIdeal y := by
    intro a ha
    obtain ⟨j, hja, hjW⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    exact hjW (hja ▸ Ideal.mem_span_singleton_self a)
  -- `z_j ∉ Q` for `j > β` (by (iii))
  have hGγQ : ∀ a ∈ Gγ, a ∉ F.stalkIdeal y := by
    intro a ha haQ
    obtain ⟨j, hja, hjW⟩ := (Finset.mem_filter.mp ha).2
    exact hjW (hd j (by rw [hja, Ideal.span_singleton_le_iff_mem]; exact haQ))
  -- (1) "`(z_1, …, z_β)` can be extended to a minimal base of `P`"
  have hGβe : ExtendsToRSOP (X.presheaf.stalk y) Gβ :=
    (ExtendsToRSOP.of_isRegularSystemOfParameters hZE).mono (Finset.filter_subset _ _)
  obtain ⟨T, hGβT, hTe, hTP⟩ := exists_extendsToRSOP_span_eq_of_extendsToRSOP (W.stalkIdeal y)
    hPreg hGβe hGβP
  -- (2) "Since `W` is non-singular, `(z, w)` can be extended to a minimal base of `Q`"
  have hTQ : (T : Set (X.presheaf.stalk y)) ⊆ F.stalkIdeal y := fun a ha =>
    hQF (hTP ▸ Ideal.subset_span ha)
  obtain ⟨T', hTT', hT'e, hT'Q⟩ := exists_extendsToRSOP_span_eq_of_extendsToRSOP (F.stalkIdeal y)
    hQreg hTe hTQ
  -- (3) "Since `F` is non-singular, (ii) and (iii) imply that `(z, w, y, z_{β+1}, …, z_α)` can be
  -- extended to a regular system of parameters of `R`"
  obtain ⟨Z, hUZ, hZ⟩ := exists_extendsToRSOP_union_of_quotient_of_subset (F.stalkIdeal y) hT'e
    hT'Q hZE htF hFt.symm (Finset.filter_subset _ _) hGγQ
  -- (4) "It follows that `E_1 ∪ ⋯ ∪ E_α` has only normal crossings with `W` at `x`"
  refine (Subscheme.hasOnlyNormalCrossingsWithAt_iff (Subscheme.isReduced_unionFam E hE)
    (hX y)).mpr ⟨Z, hZ, ?_, ⟨T, fun a ha => hUZ (Finset.mem_union_left _ (hTT' ha)),
      hTP.symm⟩⟩
  obtain ⟨K₁, hK₁, h⟩ := DatumTransform.iInf_eq_span_prod (fun i => (E i).stalkIdeal y)
    (ExtendsToRSOP.of_isRegularSystemOfParameters hZ) (fun i => by
      rcases hEZ i with h | ⟨a, ha, haE⟩
      · exact Or.inl h
      · refine Or.inr ⟨a, ?_, haE⟩
        by_cases hiW : (E i).stalkIdeal y ≤ W.stalkIdeal y
        · exact hUZ (Finset.mem_union_left _
            (hTT' (hGβT (Finset.mem_filter.mpr ⟨ha, i, haE, hiW⟩))))
        · exact hUZ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha, i, haE, hiW⟩)))
  refine ⟨K₁, hK₁, ?_⟩
  rw [Subscheme.unionFam, DatumTransform.stalkIdeal_iInf_fintype]
  exact h

end PrepTransversal

/-- If `f` maps `α` strictly below an element depending on the argument, then `dim α < n` whenever
`dim β ≤ n`, `n` a natural number. -/
theorem Order.krullDim_lt_of_strictMono_exists_lt {α β : Type*} [Preorder α] [Preorder β]
    [Nonempty α] (f : α → β) (hf : StrictMono f) (h : ∀ a, ∃ c, f a < c) (n : ℕ)
    (hn : Order.krullDim β ≤ n) : Order.krullDim α < n := by
  have key : ∀ p : LTSeries α, p.length + 1 ≤ n := by
    intro p
    obtain ⟨c, hc⟩ := h p.last
    have h1 := Order.LTSeries.length_le_krullDim ((p.map f hf).snoc c (by simpa using hc))
    have h2 : ((p.length + 1 : ℕ) : WithBot ℕ∞) ≤ n := by
      refine le_trans ?_ hn
      simpa using h1
    exact_mod_cast h2
  rw [Order.krullDim_eq_iSup_length]
  obtain ⟨a⟩ := ‹Nonempty α›
  have hn1 := key (RelSeries.singleton _ a)
  have hn1' : 1 ≤ n := by simpa using hn1
  refine lt_of_le_of_lt (WithBot.coe_le_coe.mpr
    (iSup_le fun p => ?_ : (⨆ p : LTSeries α, (p.length : ℕ∞)) ≤ ((n - 1 : ℕ) : ℕ∞))) ?_
  · have := key p
    exact_mod_cast (by omega : p.length ≤ n - 1)
  · exact_mod_cast (by omega : n - 1 < n)

/-- A closed subset `T ⊆ S` such that every irreducible subset of `T` consists of specializations of a
point of `S − T` has `dim T < n` as soon as `dim S ≤ n`. -/
theorem topologicalKrullDim_lt_of_forall_exists {Z : Type*} [TopologicalSpace Z] {T S : Set Z}
    (hT : IsClosed T) (hTS : T ⊆ S) (hTne : T.Nonempty)
    (hc : ∀ A : Set Z, _root_.IsIrreducible A → A ⊆ T →
      ∃ c ∈ S, c ∉ T ∧ ∀ t ∈ A, c ⤳ t) (n : ℕ) (hn : topologicalKrullDim S ≤ n) :
    topologicalKrullDim T < n := by
  obtain ⟨t₀, ht₀⟩ := hTne
  have : Nonempty (IrreducibleCloseds T) :=
    ⟨⟨closure {⟨t₀, ht₀⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have hemb := Topology.IsEmbedding.inclusion hTS
  have hTcl : IsClosed {s : S | (s : Z) ∈ T} := hT.preimage continuous_subtype_val
  refine Order.krullDim_lt_of_strictMono_exists_lt _
    (IrreducibleCloseds.map_strictMono_of_isInducing hemb.isInducing) (fun a => ?_) n hn
  have hAirr : _root_.IsIrreducible (Subtype.val '' (a : Set T)) :=
    a.isIrreducible.image _ continuous_subtype_val.continuousOn
  obtain ⟨c, hcS, hcT, hcsp⟩ := hc _ hAirr (by rintro _ ⟨x, -, rfl⟩; exact x.2)
  refine ⟨⟨closure {⟨c, hcS⟩}, isIrreducible_singleton.closure, isClosed_closure⟩, ?_⟩
  refine lt_of_le_of_ne ?_ fun h => ?_
  · show closure (Set.inclusion hTS '' (a : Set T)) ⊆ closure {⟨c, hcS⟩}
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨x, hxa, rfl⟩
    rw [← specializes_iff_mem_closure]
    exact (Topology.IsInducing.subtypeVal.specializes_iff).mp (hcsp x ⟨x, hxa, rfl⟩)
  · have hmem : (⟨c, hcS⟩ : S) ∈ closure (Set.inclusion hTS '' (a : Set T)) := by
      have h2 := congrArg (fun x : IrreducibleCloseds S => (⟨c, hcS⟩ : S) ∈ (x : Set S)) h
      have h3 : (⟨c, hcS⟩ : S) ∈ closure {(⟨c, hcS⟩ : S)} := subset_closure rfl
      exact Eq.mp h2.symm h3
    have hsub : closure (Set.inclusion hTS '' (a : Set T)) ⊆ {s : S | (s : Z) ∈ T} :=
      closure_minimal (by rintro _ ⟨x, -, rfl⟩; exact x.2) hTcl
    exact hcT (hsub hmem)

/-- An irreducible set contained in a finite union of closed sets lies in one of them. -/
theorem isIrreducible_subset_of_finite_sUnion {A : Set X} (hA : _root_.IsIrreducible A)
    {ℱ : Set (Set X)} (hℱ : ℱ.Finite) (hcl : ∀ B ∈ ℱ, IsClosed B) (hsub : A ⊆ ⋃₀ ℱ) :
    ∃ B ∈ ℱ, A ⊆ B := by
  obtain ⟨B, hB, hAB⟩ := isIrreducible_iff_sUnion_isClosed.mp hA hℱ.toFinset
    (fun z hz => hcl z (by simpa using hz)) (by simpa using hsub)
  exact ⟨B, by simpa using hB, hAB⟩

section PrepTopology

open Set Topology

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

/-- The irreducible components of a subset `T`: the maximal irreducible closed subsets of `T`. -/
def prepComps (T : Set Y) : Set (Closeds Y) :=
  {Z | Maximal (fun Z : Closeds Y => _root_.IsIrreducible (Z : Set Y) ∧ (Z : Set Y) ⊆ T) Z}

/-- `W_*`: the union of the components of `W` not contained in `E`. -/
def prepWStarT (W E : Set Y) : Set Y :=
  closure (⋃₀ ((↑) '' {Z : Closeds Y | Z ∈ prepComps W ∧ ¬ (Z : Set Y) ⊆ E}))

/-- `F`: the union of the components of `W_* ∩ E` meeting `U`. -/
def prepFT (W E U : Set Y) : Set Y :=
  closure (⋃₀ ((↑) '' {Z : Closeds Y | Z ∈ prepComps (prepWStarT W E ∩ E) ∧
    ((Z : Set Y) ∩ U).Nonempty}))

theorem exists_prepComps_ge {T S : Set Y} (hT : IsClosed T) (hS : _root_.IsIrreducible S)
    (hST : S ⊆ T) : ∃ G ∈ prepComps T, S ⊆ G := by
  have hS' : _root_.IsIrreducible (Subtype.val ⁻¹' S : Set T) :=
    isIrreducible_preimage_of_isInducing Topology.IsInducing.subtypeVal hS (by simpa using hST)
  obtain ⟨u, hu, hSu⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hS'
  have hucl : IsClosed u := isClosed_of_mem_irreducibleComponents u hu
  have hTcl : IsClosed (Subtype.val '' u : Set Y) := hT.isClosedEmbedding_subtypeVal.isClosedMap _ hucl
  refine ⟨⟨Subtype.val '' u, hTcl⟩, ⟨⟨hu.1.image _ continuous_subtype_val.continuousOn, ?_⟩, ?_⟩, ?_⟩
  · rintro _ ⟨x, -, rfl⟩; exact x.2
  · intro G hG hle y hy
    have hG' : _root_.IsIrreducible (Subtype.val ⁻¹' (G : Set Y) : Set T) :=
      isIrreducible_preimage_of_isInducing Topology.IsInducing.subtypeVal hG.1 (by simpa using hG.2)
    have hsub : u ⊆ (Subtype.val ⁻¹' (G : Set Y) : Set T) := fun x hx => hle ⟨x, hx, rfl⟩
    have := hu.2 hG' hsub (show (⟨y, hG.2 hy⟩ : T) ∈ Subtype.val ⁻¹' (G : Set Y) from hy)
    exact ⟨_, this, rfl⟩
  · intro y hy
    exact ⟨⟨y, hST hy⟩, hSu hy, rfl⟩

/-- An irreducible set contained in a finite union of closed sets lies in one of them. -/
theorem exists_subset_of_isIrreducible_of_finite_sUnion {A : Set Y} (hA : _root_.IsIrreducible A)
    {ℱ : Set (Set Y)} (hℱ : ℱ.Finite) (hcl : ∀ B ∈ ℱ, IsClosed B) (hsub : A ⊆ ⋃₀ ℱ) :
    ∃ B ∈ ℱ, A ⊆ B := by
  obtain ⟨B, hB, hAB⟩ := isIrreducible_iff_sUnion_isClosed.mp hA hℱ.toFinset
    (fun z hz => hcl z (by simpa using hz)) (by simpa using hsub)
  exact ⟨B, by simpa using hB, hAB⟩

theorem prepComps_finite [NoetherianSpace Y] {T : Set Y} (hT : IsClosed T) :
    (prepComps T).Finite := by
  have hfin : (irreducibleComponents T).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  refine Set.Finite.of_injOn (f := fun Z : TopologicalSpace.Closeds Y =>
    (Subtype.val ⁻¹' (Z : Set Y) : Set T)) (fun Z hZ => ?_) (fun Z hZ Z' hZ' h => ?_) hfin
  · obtain ⟨⟨hZirr, hZT⟩, hZmax⟩ := hZ
    refine ⟨isIrreducible_preimage_of_isInducing Topology.IsInducing.subtypeVal hZirr
      (by simpa using hZT), fun S hS hle => ?_⟩
    have hSirr : _root_.IsIrreducible (Subtype.val '' S) :=
      hS.image _ continuous_subtype_val.continuousOn
    have hcl : closure (Subtype.val '' S) ⊆ T := closure_minimal (by
      rintro _ ⟨s, -, rfl⟩; exact s.2) hT
    have hZle : Z ≤ (⟨closure (Subtype.val '' S), isClosed_closure⟩ : TopologicalSpace.Closeds Y) := by
      intro z hz
      exact subset_closure ⟨⟨z, hZT hz⟩, hle hz, rfl⟩
    have := hZmax (y := ⟨closure (Subtype.val '' S), isClosed_closure⟩) ⟨hSirr.closure, hcl⟩ hZle
    intro s hs
    exact this (subset_closure ⟨s, hs, rfl⟩)
  · have hsub : ∀ Z : TopologicalSpace.Closeds Y, (Z : Set Y) ⊆ T →
        (Z : Set Y) = Subtype.val '' (Subtype.val ⁻¹' (Z : Set Y) : Set T) := fun Z hZ => by
      ext z
      exact ⟨fun hz => ⟨⟨z, hZ hz⟩, hz, rfl⟩, by rintro ⟨s, hs, rfl⟩; exact hs⟩
    exact SetLike.coe_injective <| by
      rw [hsub Z hZ.1.2, hsub Z' hZ'.1.2]
      exact congrArg _ h

theorem sUnion_prepComps [NoetherianSpace Y] {T : Set Y} (hT : IsClosed T) :
    ⋃₀ ((↑) '' prepComps T : Set (Set Y)) = T := by
  refine subset_antisymm ?_ fun t ht => ?_
  · rintro _ ⟨_, ⟨G, hG, rfl⟩, hy⟩
    exact hG.1.2 hy
  · obtain ⟨G, hG, hsub⟩ := exists_prepComps_ge hT (isIrreducible_singleton (x := t)).closure
      (closure_minimal (Set.singleton_subset_iff.mpr ht) hT)
    exact ⟨G, ⟨G, hG, rfl⟩, hsub (subset_closure rfl)⟩

theorem isClosed_sUnion_prepComps [NoetherianSpace Y] {T : Set Y} (hT : IsClosed T)
    (P : Closeds Y → Prop) :
    IsClosed (⋃₀ ((↑) '' {Z : Closeds Y | Z ∈ prepComps T ∧ P Z} : Set (Set Y))) :=
  ((((prepComps_finite hT).subset (fun Z (h : Z ∈ prepComps T ∧ P Z) => h.1)).image _).isClosed_sUnion
    (by rintro _ ⟨Z, -, rfl⟩; exact Z.isClosed))

/-- If `W ⊆ closure (W ∩ O)` then every component of `W` meets `O`. -/
theorem prepComps_meets [NoetherianSpace Y] {W O : Set Y} (hW : IsClosed W)
    (hdense : W ⊆ closure (W ∩ O)) {G : Closeds Y} (hG : G ∈ prepComps W) :
    ((G : Set Y) ∩ O).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hcl := isClosed_sUnion_prepComps hW (fun Z => Z ≠ G)
  have hsub : W ∩ O ⊆ ⋃₀ ((↑) '' {Z : Closeds Y | Z ∈ prepComps W ∧ Z ≠ G} : Set (Set Y)) := by
    rintro w ⟨hwW, hwO⟩
    rw [← sUnion_prepComps hW] at hwW
    obtain ⟨_, ⟨C, hC, rfl⟩, hwC⟩ := hwW
    refine ⟨C, ⟨C, ⟨hC, ?_⟩, rfl⟩, hwC⟩
    rintro rfl
    exact (Set.eq_empty_iff_forall_notMem.mp hne) w ⟨hwC, hwO⟩
  have hGsub : (G : Set Y) ⊆ ⋃₀ ((↑) '' {Z : Closeds Y | Z ∈ prepComps W ∧ Z ≠ G} : Set (Set Y)) :=
    (hG.1.2.trans hdense).trans (closure_minimal hsub hcl)
  obtain ⟨B, ⟨C, ⟨hC, hCG⟩, rfl⟩, hGC⟩ := exists_subset_of_isIrreducible_of_finite_sUnion hG.1.1
    (ℱ := (↑) '' {Z : Closeds Y | Z ∈ prepComps W ∧ Z ≠ G})
    (((prepComps_finite hW).subset (fun Z (h : Z ∈ prepComps W ∧ Z ≠ G) => h.1)).image _)
    (by rintro _ ⟨Z, -, rfl⟩; exact Z.isClosed) hGsub
  exact hCG (le_antisymm (hG.2 hC.1 hGC) hGC)

variable {j : Z → Y}

theorem prepComps_preimage (hj : IsOpenEmbedding j) {T : Set Y} (hT : IsClosed T) {G : Closeds Y}
    (hG : G ∈ prepComps T) (hmeet : ((G : Set Y) ∩ Set.range j).Nonempty) :
    (⟨j ⁻¹' (G : Set Y), G.isClosed.preimage hj.continuous⟩ : Closeds Z) ∈ prepComps (j ⁻¹' T) := by
  obtain ⟨y, hyG, ⟨z, rfl⟩⟩ := hmeet
  have hGcl : (G : Set Y) ⊆ closure (j '' (j ⁻¹' (G : Set Y))) := by
    have := subset_closure_inter_of_isPreirreducible_of_isOpen hG.1.1.isPreirreducible
      hj.isOpen_range ⟨j z, hyG, ⟨z, rfl⟩⟩
    refine this.trans (closure_mono ?_)
    rintro _ ⟨hw, ⟨w, rfl⟩⟩
    exact ⟨w, hw, rfl⟩
  refine ⟨⟨⟨⟨z, hyG⟩, hG.1.1.isPreirreducible.preimage hj⟩, fun w hw => hG.1.2 hw⟩,
    fun S hS hle => ?_⟩
  obtain ⟨hSirr, hSsub⟩ := hS
  have hS1 : _root_.IsIrreducible (closure (j '' (S : Set Z))) :=
    (hSirr.image j hj.continuous.continuousOn).closure
  have hS2 : closure (j '' (S : Set Z)) ⊆ T :=
    closure_minimal (by rintro _ ⟨w, hw, rfl⟩; exact hSsub hw) hT
  have hS3 : (G : Set Y) ⊆ closure (j '' (S : Set Z)) :=
    hGcl.trans (closure_mono (Set.image_mono hle))
  have := hG.2 (y := ⟨closure (j '' (S : Set Z)), isClosed_closure⟩) ⟨hS1, hS2⟩ hS3
  intro w hw
  exact this (subset_closure ⟨w, hw, rfl⟩)

theorem exists_prepComps_closure_image (hj : IsOpenEmbedding j) {T : Set Y} (hT : IsClosed T)
    {G' : Closeds Z} (hG' : G' ∈ prepComps (j ⁻¹' T)) :
    ∃ G ∈ prepComps T, (G : Set Y) = closure (j '' (G' : Set Z)) ∧
      j ⁻¹' (G : Set Y) = (G' : Set Z) := by
  have hS1 : _root_.IsIrreducible (closure (j '' (G' : Set Z))) :=
    (hG'.1.1.image j hj.continuous.continuousOn).closure
  have hS2 : closure (j '' (G' : Set Z)) ⊆ T :=
    closure_minimal (by rintro _ ⟨w, hw, rfl⟩; exact hG'.1.2 hw) hT
  obtain ⟨G, hG, hsub⟩ := exists_prepComps_ge hT hS1 hS2
  obtain ⟨z, hz⟩ := hG'.1.1.nonempty
  have hmeet : ((G : Set Y) ∩ Set.range j).Nonempty :=
    ⟨j z, hsub (subset_closure ⟨z, hz, rfl⟩), ⟨z, rfl⟩⟩
  have hpre := prepComps_preimage hj hT hG hmeet
  have hle : (G' : Set Z) ⊆ j ⁻¹' (G : Set Y) := fun w hw =>
    hsub (subset_closure ⟨w, hw, rfl⟩)
  have heq : j ⁻¹' (G : Set Y) = (G' : Set Z) :=
    le_antisymm (hG'.2 hpre.1 hle) hle
  refine ⟨G, hG, ?_, heq⟩
  have hGcl : (G : Set Y) ⊆ closure (j '' (j ⁻¹' (G : Set Y))) := by
    have := subset_closure_inter_of_isPreirreducible_of_isOpen hG.1.1.isPreirreducible
      hj.isOpen_range hmeet
    refine this.trans (closure_mono ?_)
    rintro _ ⟨hw, ⟨w, rfl⟩⟩
    exact ⟨w, hw, rfl⟩
  rw [heq] at hGcl
  exact subset_antisymm hGcl (closure_minimal (Set.image_subset_iff.mpr hle) G.isClosed)

theorem subset_closure_image_preimage (hj : IsOpenEmbedding j) {G : Set Y}
    (hG : _root_.IsIrreducible G) (hmeet : (G ∩ Set.range j).Nonempty) :
    G ⊆ closure (j '' (j ⁻¹' G)) := by
  have := subset_closure_inter_of_isPreirreducible_of_isOpen hG.isPreirreducible
    hj.isOpen_range hmeet
  refine this.trans (closure_mono ?_)
  rintro _ ⟨hw, ⟨w, rfl⟩⟩
  exact ⟨w, hw, rfl⟩

theorem prepWStarT_eq [NoetherianSpace Y] (hj : IsOpenEmbedding j) {W E : Set Y}
    (hW : IsClosed W) (hE : IsClosed E) (hdense : W ⊆ closure (W ∩ Set.range j)) :
    prepWStarT W E = closure (j '' prepWStarT (j ⁻¹' W) (j ⁻¹' E)) := by
  apply subset_antisymm
  · refine closure_minimal ?_ isClosed_closure
    rintro y ⟨_, ⟨G, ⟨hG, hGE⟩, rfl⟩, hy⟩
    have hmeet := prepComps_meets hW hdense hG
    have hpre := prepComps_preimage hj hW hG hmeet
    have hGE' : ¬ (j ⁻¹' (G : Set Y)) ⊆ j ⁻¹' E := by
      intro h
      apply hGE
      refine (subset_closure_image_preimage hj hG.1.1 hmeet).trans (closure_minimal ?_ hE)
      rintro _ ⟨w, hw, rfl⟩
      exact h hw
    refine closure_mono (Set.image_mono ?_) ((subset_closure_image_preimage hj hG.1.1 hmeet) hy)
    intro w hw
    exact subset_closure ⟨_, ⟨_, ⟨hpre, hGE'⟩, rfl⟩, hw⟩
  · refine closure_minimal ?_ isClosed_closure
    refine (image_closure_subset_closure_image hj.continuous).trans ?_
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨y, ⟨_, ⟨G', ⟨hG', hG'E⟩, rfl⟩, hy⟩, rfl⟩
    obtain ⟨G, hG, hGeq, hGpre⟩ := exists_prepComps_closure_image hj hW hG'
    have hGE : ¬ (G : Set Y) ⊆ E := by
      intro h
      apply hG'E
      rw [← hGpre]
      exact Set.preimage_mono h
    refine subset_closure ⟨_, ⟨G, ⟨hG, hGE⟩, rfl⟩, ?_⟩
    rw [hGeq]
    exact subset_closure ⟨y, hy, rfl⟩

theorem preimage_prepWStarT [NoetherianSpace Y] (hj : IsOpenEmbedding j) {W E : Set Y}
    (hW : IsClosed W) (hE : IsClosed E) (hdense : W ⊆ closure (W ∩ Set.range j)) :
    j ⁻¹' prepWStarT W E = prepWStarT (j ⁻¹' W) (j ⁻¹' E) := by
  rw [prepWStarT_eq hj hW hE hdense, ← hj.isInducing.closure_eq_preimage_closure_image]
  exact closure_closure

theorem prepFT_eq [NoetherianSpace Y] (hj : IsOpenEmbedding j) {W E U : Set Y}
    (hW : IsClosed W) (hE : IsClosed E) (hdense : W ⊆ closure (W ∩ Set.range j))
    (hU : U ⊆ Set.range j) :
    prepFT W E U = closure (j '' prepFT (j ⁻¹' W) (j ⁻¹' E) (j ⁻¹' U)) := by
  have hTcl : IsClosed (prepWStarT W E ∩ E) := isClosed_closure.inter hE
  have hTpre : j ⁻¹' (prepWStarT W E ∩ E) = prepWStarT (j ⁻¹' W) (j ⁻¹' E) ∩ j ⁻¹' E := by
    rw [Set.preimage_inter, preimage_prepWStarT hj hW hE hdense]
  apply subset_antisymm
  · refine closure_minimal ?_ isClosed_closure
    rintro y ⟨_, ⟨G, ⟨hG, hGU⟩, rfl⟩, hy⟩
    obtain ⟨u, huG, huU⟩ := hGU
    have hmeet : ((G : Set Y) ∩ Set.range j).Nonempty := ⟨u, huG, hU huU⟩
    have hpre := prepComps_preimage hj hTcl hG hmeet
    rw [hTpre] at hpre
    obtain ⟨z, rfl⟩ := hU huU
    refine closure_mono (Set.image_mono ?_) ((subset_closure_image_preimage hj hG.1.1 hmeet) hy)
    intro w hw
    exact subset_closure ⟨_, ⟨_, ⟨hpre, ⟨z, huG, huU⟩⟩, rfl⟩, hw⟩
  · refine closure_minimal ?_ isClosed_closure
    refine (image_closure_subset_closure_image hj.continuous).trans ?_
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨y, ⟨_, ⟨G', ⟨hG', ⟨z, hzG, hzU⟩⟩, rfl⟩, hy⟩, rfl⟩
    rw [← hTpre] at hG'
    obtain ⟨G, hG, hGeq, hGpre⟩ := exists_prepComps_closure_image hj hTcl hG'
    refine subset_closure ⟨_, ⟨G, ⟨hG, ⟨j z, ?_, hzU⟩⟩, rfl⟩, ?_⟩
    · rw [hGeq]; exact subset_closure ⟨z, hzG, rfl⟩
    · rw [hGeq]; exact subset_closure ⟨y, hy, rfl⟩

theorem preimage_prepFT [NoetherianSpace Y] (hj : IsOpenEmbedding j) {W E U : Set Y}
    (hW : IsClosed W) (hE : IsClosed E) (hdense : W ⊆ closure (W ∩ Set.range j))
    (hU : U ⊆ Set.range j) :
    j ⁻¹' prepFT W E U = prepFT (j ⁻¹' W) (j ⁻¹' E) (j ⁻¹' U) := by
  rw [prepFT_eq hj hW hE hdense hU, ← hj.isInducing.closure_eq_preimage_closure_image]
  exact closure_closure

end PrepTopology

section PrepStrictDense
open CategoryTheory AlgebraicGeometry
variable {X Y : Scheme.{u}}

/-- Strict transforms keep a set dense in its part over `R`: if `V ⊆ closure (V ∩ R)` then
`V' ⊆ closure (V' ∩ f⁻¹ R)`. -/
theorem MonoidalSuccession.pts_strictTransform_subset_closure_inter (s : MonoidalSuccession X Y)
    (V : Subscheme X) (R : Set X) (hV : V.pts ⊆ closure (V.pts ∩ R)) :
    (s.strictTransform V).pts ⊆
      closure ((s.strictTransform V).pts ∩ s.composite.base ⁻¹' R) := by
  induction s with
  | nil X => simpa using hV
  | cons B t rest ih =>
    have hstep : (Subscheme.strictTransform t V).pts ⊆
        closure ((Subscheme.strictTransform t V).pts ∩ t.f.base ⁻¹' R) := by
      intro p hp
      obtain ⟨q, hq, hqE, hqp⟩ := t.exists_generization_notMem_exceptional V hp
      have hqV : t.f q ∈ V.pts := t.pts_strictTransform_subset V hq
      have hq2 := Hironaka.DatumTransform.mem_closure_of_notMem_exceptional t hqE (hV hqV)
      refine closure_mono ?_ (specializes_iff_mem_closure.mp hqp |> fun h =>
        closure_minimal (Set.singleton_subset_iff.mpr hq2) isClosed_closure h)
      rintro y ⟨hy1, hy2⟩
      exact ⟨(t.mem_pts_strictTransform_iff_of_notMem V hy2).mpr hy1.1, hy1.2⟩
    have := ih (Subscheme.strictTransform t V) (t.f.base ⁻¹' R) hstep
    simpa [MonoidalSuccession.strictTransform, Set.preimage_comp] using this

end PrepStrictDense

section PrepPtsConv
open CategoryTheory AlgebraicGeometry
variable {X : Scheme.{u}}

theorem Subscheme.support_ofClosed (Z : Closeds X) : (Subscheme.ofClosed Z).support = Z :=
  SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

/-- `W_*` in terms of point sets. -/
theorem DatumI.Raw.pts_prepWStar_eq (ℜ : DatumI.Raw X) (E₁ : Subscheme X) :
    (ℜ.prepWStar E₁).pts = prepWStarT ℜ.W.pts E₁.pts := by
  rw [DatumI.Raw.pts_prepWStar]
  unfold prepWStarT
  have : {Z : Closeds X | ∃ W₁ ∈ ℜ.W.irreducibleComponents, ¬ W₁.IsContainedIn E₁ ∧
      Z = W₁.support} = {Z : Closeds X | Z ∈ prepComps ℜ.W.pts ∧ ¬ (Z : Set X) ⊆ E₁.pts} := by
    ext Z
    constructor
    · rintro ⟨W₁, ⟨Zw, hZw, rfl⟩, hn, rfl⟩
      refine ⟨by rw [Subscheme.support_ofClosed]; exact hZw, fun h => hn ?_⟩
      refine Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced Zw) ?_
      rw [show (Subscheme.ofClosed Zw).pts = Zw from
        Scheme.IdealSheafData.coe_support_vanishingIdeal Zw]
      rwa [Subscheme.support_ofClosed] at h
    · rintro ⟨hZ, hZE⟩
      refine ⟨Subscheme.ofClosed Z, ⟨Z, hZ, rfl⟩, fun h => hZE ?_, (Subscheme.support_ofClosed Z).symm⟩
      have := pts_subset_of_isContainedIn h
      rwa [show (Subscheme.ofClosed Z).pts = Z from
        Scheme.IdealSheafData.coe_support_vanishingIdeal Z] at this
  rw [this]

/-- `F` in terms of point sets. -/
theorem DatumI.Raw.pts_prepF_eq (ℜ : DatumI.Raw X) (E₁ : Subscheme X) (U : Set X) :
    (ℜ.prepF E₁ U).pts = prepFT ℜ.W.pts E₁.pts U := by
  rw [DatumI.Raw.pts_prepF]
  unfold prepFT
  have hD : ((ℜ.prepWStar E₁).inter E₁).pts = prepWStarT ℜ.W.pts E₁.pts ∩ E₁.pts := by
    ext y
    rw [Subscheme.mem_pts_inter_iff, DatumI.Raw.pts_prepWStar_eq]
    rfl
  have : {Z : Closeds X | ∃ F_i ∈ ((ℜ.prepWStar E₁).inter E₁).irreducibleComponents,
      (F_i.pts ∩ U).Nonempty ∧ Z = F_i.support} =
      {Z : Closeds X | Z ∈ prepComps (prepWStarT ℜ.W.pts E₁.pts ∩ E₁.pts) ∧
        ((Z : Set X) ∩ U).Nonempty} := by
    ext Z
    constructor
    · rintro ⟨F_i, ⟨Zw, hZw, rfl⟩, hU, rfl⟩
      have hp : (Subscheme.ofClosed Zw).pts = Zw :=
        Scheme.IdealSheafData.coe_support_vanishingIdeal Zw
      refine ⟨?_, by rwa [hp] at hU⟩
      rw [Subscheme.support_ofClosed, ← hD]
      exact hZw
    · rintro ⟨hZ, hZU⟩
      refine ⟨Subscheme.ofClosed Z, ⟨Z, by rw [hD]; exact hZ, rfl⟩, ?_,
        (Subscheme.support_ofClosed Z).symm⟩
      rwa [show (Subscheme.ofClosed Z).pts = Z from
        Scheme.IdealSheafData.coe_support_vanishingIdeal Z]
  rw [this]

end PrepPtsConv

/-- If `η ⤳ y` and the stalk at `y` of `D` lies in that of the reduced structure on `closure {η}`, then
`η ∈ D` (the stalk of `D` at `η` is a proper ideal, being contained in the maximal ideal). -/
theorem _root_.Hironaka.Subscheme.mem_pts_of_stalkIdeal_le_ofClosed_closure {Y : Scheme.{u}} {η y : Y}
    (h : η ⤳ y) (D : Subscheme Y)
    (hD : D.stalkIdeal y ≤ (Subscheme.ofClosed ⟨closure {η}, isClosed_closure⟩).stalkIdeal y) :
    η ∈ D.pts := by
  rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, Subscheme.stalkIdeal_eq_map_stalkSpecializes D h]
  intro htop
  have := Ideal.map_mono (f := (Y.presheaf.stalkSpecializes h).hom) hD
  rw [htop, ← Subscheme.stalkIdeal_eq_map_stalkSpecializes _ h,
    stalkIdeal_ofClosed_closure_self'] at this
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp this)

/-- A non-singular irreducible subscheme is one of its own irreducible components. -/
theorem _root_.Hironaka.Subscheme.mem_irreducibleComponents_self {Y : Scheme.{u}} (D : Subscheme Y)
    (hD : D.IsNonsingular) (hirr : D.IsIrreducible) : D ∈ D.irreducibleComponents :=
  ⟨D.support, ⟨⟨Subscheme.isIrreducible_pts D hirr, subset_rfl⟩, fun _S hS _ => hS.2⟩,
    Subscheme.eq_ofClosed_support D (Subscheme.isReduced_of_isNonsingular hD)⟩

section PrepCentersAvoid
variable {X Y : Scheme.{u}}

theorem MonoidalSuccession.CentersAvoid.mono {s : MonoidalSuccession X Y} {R R' : Set X}
    (h : s.CentersAvoid R') (hR : R ⊆ R') : s.CentersAvoid R := by
  induction s with
  | nil X => trivial
  | cons B t rest ih => exact ⟨fun y hy hyR => h.1 y hy (hR hyR), ih h.2 (Set.preimage_mono hR)⟩

theorem MonoidalSuccession.centersAvoid_compl_of_centersIn (s : MonoidalSuccession X Y) :
    ∀ Z : Subscheme X, s.CentersIn Z → s.CentersAvoid Z.ptsᶜ := by
  induction s with
  | nil X => intro Z _; trivial
  | cons B t rest ih =>
    intro Z hZ
    refine ⟨fun y hy hyc => hyc (hZ.1 hy), ?_⟩
    exact (ih _ hZ.2).mono fun y hy hy' => hy (t.pts_strictTransform_subset Z hy')

/-- The exceptional divisors of a succession lie over the centers: a point of an exceptional
divisor does not map into a set `R` which the centers avoid (p. 290: "the exceptional divisors
`E_j'`, `j > α`, lie over the centers"). -/
theorem MonoidalSuccession.composite_base_notMem_of_mem_exceptionalDivisors :
    ∀ {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {R : Set X}, s.CentersAvoid R →
      ∀ {D : Subscheme Y}, D ∈ s.exceptionalDivisors → ∀ x ∈ D.pts, s.composite.base x ∉ R := by
  intro X Y s
  induction s with
  | nil X => intro R _ D hD; exact absurd hD (by simp [MonoidalSuccession.exceptionalDivisors])
  | cons B t rest ih =>
    intro R hR D hD x hx
    rw [MonoidalSuccession.exceptionalDivisors] at hD
    rcases hD with rfl | hD
    · have h1 := rest.pts_strictTransform_subset t.exceptional hx
      rw [Set.mem_preimage, MonoidalTransformation.pts_exceptional] at h1
      intro hxR
      exact hR.1 _ h1 hxR
    · intro hxR
      refine ih hR.2 hD x hx ?_
      simpa [Set.mem_preimage, MonoidalSuccession.composite_cons] using hxR

/-- Pull-back along a flat preimmersion `g` is an isomorphism on stalks, so the inclusion of stalk
ideals at `g z` is that of the stalk ideals of the total transforms at `z`. -/
theorem stalkIdeal_totalTransform_le_iff {X Z : Scheme.{u}} (g : Z ⟶ X) [Flat g] [IsPreimmersion g]
    (D D' : Subscheme X) (z : Z) :
    (Subscheme.totalTransform g D).stalkIdeal z ≤ (Subscheme.totalTransform g D').stalkIdeal z ↔
      D.stalkIdeal (g z) ≤ D'.stalkIdeal (g z) := by
  have hb : Function.Bijective (g.stalkMap z).hom := FlatPreimm.stalkMap_bijective g z
  rw [stalkIdeal_totalTransform, stalkIdeal_totalTransform]
  constructor
  · intro h
    have h' := Ideal.comap_mono (f := (g.stalkMap z).hom) h
    rwa [Ideal.comap_map_of_bijective _ hb, Ideal.comap_map_of_bijective _ hb] at h'
  · exact Ideal.map_mono

/-- The same for the maximal ideal: `D_{g z}` is the maximal ideal iff the stalk ideal of the total
transform at `z` is. -/
theorem stalkIdeal_totalTransform_eq_maximalIdeal_iff {X Z : Scheme.{u}} (g : Z ⟶ X) [Flat g]
    [IsPreimmersion g] (D : Subscheme X) (z : Z) :
    (Subscheme.totalTransform g D).stalkIdeal z = IsLocalRing.maximalIdeal (Z.presheaf.stalk z) ↔
      D.stalkIdeal (g z) = IsLocalRing.maximalIdeal (X.presheaf.stalk (g z)) := by
  have hb : Function.Bijective (g.stalkMap z).hom := FlatPreimm.stalkMap_bijective g z
  have hmax : (IsLocalRing.maximalIdeal (X.presheaf.stalk (g z))).map (g.stalkMap z).hom =
      IsLocalRing.maximalIdeal (Z.presheaf.stalk z) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hb.2
  rw [stalkIdeal_totalTransform, ← hmax]
  constructor
  · intro h
    have h' := congrArg (Ideal.comap (g.stalkMap z).hom) h
    rwa [Ideal.comap_map_of_bijective _ hb, Ideal.comap_map_of_bijective _ hb] at h'
  · intro h; rw [h]

/-- If the centers of `s` lie over the closed subscheme `F`, then `s` is an isomorphism over `X − F`:
the open immersion `j : X − F → X` lifts to an open immersion `j₁` onto `f⁻¹(X − F)`, compatibly with
strict transforms. -/
theorem MonoidalSuccession.exists_isOpenEmbedding_lift_of_centersIn (s : MonoidalSuccession X Y)
    (F : Subscheme X) (hcenters : s.CentersIn F) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X) (j₁ : Z ⟶ Y), Topology.IsOpenEmbedding j.base ∧
      Topology.IsOpenEmbedding j₁.base ∧ Set.range j.base = F.ptsᶜ ∧
      Set.range j₁.base = s.composite.base ⁻¹' F.ptsᶜ ∧
      (∀ z, s.composite.base (j₁.base z) = j.base z) ∧
      ∀ V : Subscheme X, j₁.base ⁻¹' (s.strictTransform V).pts = j.base ⁻¹' V.pts := by
  let O : X.Opens := ⟨F.ptsᶜ, F.support.isClosed.isOpen_compl⟩
  let j : Scheme.Opens.toScheme O ⟶ X := Scheme.Opens.ι O
  have hjemb : Topology.IsOpenEmbedding j.base := (Scheme.Opens.ι O).isOpenEmbedding
  have hrange : Set.range j.base = F.ptsᶜ := Scheme.Opens.range_ι O
  have hs' : s.CentersAvoid (Set.range j.base) := by
    rw [hrange]; exact MonoidalSuccession.centersAvoid_compl_of_centersIn s F hcenters
  obtain ⟨j₁, hfl, hpre, hcomp, hr, hst, -⟩ := s.exists_lift_of_centersAvoid j hs'
  have hj₁ : Topology.IsOpenEmbedding j₁.base :=
    ⟨hpre.isEmbedding, by
      rw [hr, hrange]; exact F.support.isClosed.isOpen_compl.preimage
        s.composite.base.hom.continuous⟩
  refine ⟨_, j, j₁, hjemb, hj₁, hrange, by rw [hr, hrange], fun z => by rw [← hcomp]; rfl,
    fun V => ?_⟩
  have := congrArg Subscheme.pts (hst V)
  rwa [FlatPreimm.pts_totalTransform, FlatPreimm.pts_totalTransform] at this

theorem MonoidalSuccession.pts_strictTransform_mono (s : MonoidalSuccession X Y)
    {V V' : Subscheme X} (h : V.pts ⊆ V'.pts) :
    (s.strictTransform V).pts ⊆ (s.strictTransform V').pts := by
  induction s with
  | nil X => exact h
  | cons B t rest ih =>
    refine ih ?_
    rw [MonoidalTransformation.pts_strictTransform_eq_closure,
      MonoidalTransformation.pts_strictTransform_eq_closure]
    exact closure_mono (Set.sdiff_subset_sdiff_left (Set.preimage_mono h))

/-- The strict transform of a subscheme contained in a union of two is contained in the union of the
strict transforms. -/
theorem MonoidalSuccession.pts_strictTransform_subset_union (s : MonoidalSuccession X Y)
    {V V₁ V₂ : Subscheme X} (h : V.pts ⊆ V₁.pts ∪ V₂.pts) :
    (s.strictTransform V).pts ⊆ (s.strictTransform V₁).pts ∪ (s.strictTransform V₂).pts := by
  induction s with
  | nil X => exact h
  | cons B t rest ih =>
    refine ih ?_
    rw [MonoidalTransformation.pts_strictTransform_eq_closure,
      MonoidalTransformation.pts_strictTransform_eq_closure,
      MonoidalTransformation.pts_strictTransform_eq_closure, ← closure_union]
    refine closure_mono fun y hy => ?_
    rcases h hy.1 with h1 | h1
    · exact Or.inl ⟨h1, hy.2⟩
    · exact Or.inr ⟨h1, hy.2⟩

end PrepCentersAvoid

section PrepDenseOffF
variable {X : Scheme.{u}}

/-- No irreducible component of `W` lies in `F`: `W − F` is dense in `W`.  (The argument of
`dim_prepF_lt`: an irreducible set in `F ⊆ W_* ∩ E_1` lies in a component of `W` not contained in `E_1`
whose generic point is not in `F`.) -/
theorem DatumI.Raw.pts_subset_closure_diff_prepF [IsAlgebraicScheme X] (ℜ : DatumI.Raw X)
    (E₁ : Subscheme X) (U : Set X) :
    ℜ.W.pts ⊆ closure (ℜ.W.pts \ (ℜ.prepF E₁ U).pts) := by
  classical
  have : TopologicalSpace.NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  set F := ℜ.prepF E₁ U with hFdef
  have hFsub : ∀ y ∈ F.pts, y ∈ (ℜ.prepWStar E₁).pts ∧ y ∈ E₁.pts := fun y hy =>
    Subscheme.mem_pts_inter_iff.mp (ℜ.pts_prepF_subset E₁ U hy)
  have hex : ∀ A : Set X, _root_.IsIrreducible A → A ⊆ F.pts →
      ∃ c ∈ ℜ.W.pts, c ∉ F.pts ∧ ∀ t ∈ A, c ⤳ t := by
    intro A hA hAF
    have hAW : A ⊆ (ℜ.prepWStar E₁).pts := fun y hy => (hFsub y (hAF hy)).1
    rw [DatumI.Raw.pts_prepWStar] at hAW
    set S := {Z : Closeds X | ∃ W₁ ∈ ℜ.W.irreducibleComponents, ¬ W₁.IsContainedIn E₁ ∧
      Z = W₁.support} with hS
    have hfin : S.Finite := by
      refine (finite_setOf_maximal_isIrreducible_subset (X := X) ℜ.W.support.isClosed).subset ?_
      rintro Z ⟨W₁, ⟨Zw, hZw, rfl⟩, -, rfl⟩
      have : (Subscheme.ofClosed Zw).support = Zw :=
        SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Zw)
      rw [this]
      exact hZw
    have hcl : IsClosed (⋃₀ ((↑) '' S : Set (Set X))) :=
      (hfin.image _).isClosed_sUnion (by rintro _ ⟨Z, -, rfl⟩; exact Z.isClosed)
    rw [hcl.closure_eq] at hAW
    obtain ⟨B, hB, hAB⟩ := isIrreducible_subset_of_finite_sUnion hA (hfin.image _)
      (by rintro _ ⟨Z, -, rfl⟩; exact Z.isClosed) hAW
    obtain ⟨Z, ⟨W₁, hW₁, hn1, rfl⟩, rfl⟩ := hB
    obtain ⟨Zw, hZw, hW₁eq⟩ := id hW₁
    have hW₁pts : W₁.pts = Zw := by
      rw [hW₁eq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Zw
    obtain ⟨c, hc⟩ : ∃ c, IsGenericPoint c (Zw : Set X) :=
      QuasiSober.sober hZw.1.1 Zw.isClosed
    have hcW : c ∈ ℜ.W.pts := hZw.1.2 hc.mem
    have hW₁red : W₁.IsReduced := by rw [hW₁eq]; exact Subscheme.ofClosed_isReduced Zw
    refine ⟨c, hcW, fun hcF => hn1 ?_, fun t ht => hc.specializes ?_⟩
    · refine Subscheme.isContainedIn_of_pts_subset hW₁red fun y hy => ?_
      rw [hW₁pts, ← hc.def] at hy
      exact closure_minimal (Set.singleton_subset_iff.mpr (hFsub c hcF).2)
        E₁.support.isClosed hy
    · have := hAB ht
      rwa [show (W₁.support : Set X) = Zw from hW₁pts] at this
  intro w hw
  by_cases hwF : w ∈ F.pts
  · obtain ⟨c, hcW, hcF, hct⟩ := hex (closure {w}) isIrreducible_singleton.closure
      (closure_minimal (Set.singleton_subset_iff.mpr hwF) F.support.isClosed)
    have hc' : ({c} : Set X) ⊆ ℜ.W.pts \ F.pts := Set.singleton_subset_iff.mpr ⟨hcW, hcF⟩
    exact closure_mono hc' (specializes_iff_mem_closure.mp (hct w (subset_closure rfl)))
  · exact subset_closure ⟨hw, hwF⟩

end PrepDenseOffF

section PrepNormalFlatAlg
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]

/-- Normal flatness along a principal prime forces a power of the generator into the ideal. -/
theorem exists_pow_mem_of_isNormallyFlatAlongIdeal_span (π : A) (hπ : (Ideal.span {π}).IsPrime)
    (J : Ideal A) (hJ0 : J ≠ ⊥) (hJP : J ≤ Ideal.span {π})
    (hnf : IsNormallyFlatAlongIdeal ((Ideal.span {π}).map (Ideal.Quotient.mk J))) :
    ∃ a : ℕ, π ^ a ∈ J := by
  classical
  by_contra hno
  simp only [not_exists] at hno
  set P : Ideal A := Ideal.span {π} with hP
  have hJtop : J ≠ ⊤ := fun h => hπ.ne_top (top_le_iff.mp (h ▸ hJP))
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have : IsLocalRing (A ⧸ J) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  set O := A ⧸ J
  set Pb : Ideal O := P.map (Ideal.Quotient.mk J) with hPb
  have hPbspan : Pb = Ideal.span {Ideal.Quotient.mk J π} := by
    rw [hPb, hP, Ideal.map_span, Set.image_singleton]
  -- the quotient `O/Pb ≃ A/P` is a domain
  let e : (O ⧸ Pb) ≃+* A ⧸ P := DoubleQuot.quotQuotEquivQuotOfLE hJP
  have : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  have : IsDomain (O ⧸ Pb) := Function.Injective.isDomain e.toRingHom e.injective
  -- the pieces are torsion-free
  have htf : ∀ n, Module.IsTorsionFree (O ⧸ Pb) (GrPiece Pb n) := fun n => by
    have := hnf n
    infer_instance
  -- the generator of the `n`-th piece
  have hmem : ∀ n : ℕ, (Ideal.Quotient.mk J π) ^ n ∈ Pb ^ n := fun n => by
    rw [hPbspan, Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _
  let g : ∀ n : ℕ, GrPiece Pb n := fun n => Submodule.Quotient.mk ⟨_, hmem n⟩
  have hpiπ : Ideal.Quotient.mk J π ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨u, hu1⟩ := Ideal.Quotient.mk_surjective hu.exists_right_inv.choose
    have h1 : Ideal.Quotient.mk J (π * u) = 1 := by
      rw [map_mul, hu1]; exact hu.exists_right_inv.choose_spec
    have h2 : π * u - 1 ∈ J := by
      rw [← Ideal.Quotient.eq]; simpa using h1
    have h3 : (1 : A) ∈ P := by
      have := hJP h2
      have h4 : π * u ∈ P := Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self π)
      have := P.sub_mem h4 this
      simpa using this
    exact hπ.ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  -- the generators are non-zero
  have hg : ∀ n, g n ≠ 0 := by
    intro n hn
    have h1 : (Ideal.Quotient.mk J π) ^ n ∈ Pb ^ (n + 1) := by
      have := (Submodule.Quotient.mk_eq_zero _).mp hn
      simpa using this
    rw [hPbspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    have hu : IsUnit (1 - Ideal.Quotient.mk J π * c) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (by
        exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right _ _ hpiπ))
    have h2 : (Ideal.Quotient.mk J π) ^ n * (1 - Ideal.Quotient.mk J π * c) = 0 := by
      linear_combination (-1 : O) * hc
    have h3 : (Ideal.Quotient.mk J π) ^ n = 0 := by
      exact hu.mul_left_eq_zero.mp h2
    exact hno n (by rw [← map_pow] at h3; exact Ideal.Quotient.eq_zero_iff_mem.mp h3)
  -- Krull: a nonzero element of `J` has a maximal `π`-order
  obtain ⟨h, hhJ, hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ0
  have hPtop : P ≠ ⊤ := hπ.ne_top
  have hbot := Ideal.iInf_pow_eq_bot_of_isDomain P hPtop
  have hex : ∃ n, h ∉ P ^ n := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have : h ∈ ⨅ n, P ^ n := Submodule.mem_iInf _ |>.mpr hall
    rw [hbot] at this
    exact hh0 this
  classical
  set n₀ := Nat.find hex with hn₀
  have hn₀spec : h ∉ P ^ n₀ := Nat.find_spec hex
  have hn₀pos : 0 < n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h0 | h0
    · exact absurd (by rw [h0]; simp) hn₀spec
    · exact h0
  obtain ⟨N, hN⟩ : ∃ N, n₀ = N + 1 := ⟨n₀ - 1, by omega⟩
  have hhN : h ∈ P ^ N := by
    by_contra hcon
    exact Nat.find_min hex (show N < n₀ by omega) hcon
  have hhN1 : h ∉ P ^ (N + 1) := hN ▸ hn₀spec
  rw [hP, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hhN
  obtain ⟨h₀, hh₀⟩ := hhN
  have hh₀P : h₀ ∉ P := by
    intro hh
    apply hhN1
    rw [hP, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    rw [hP, Ideal.mem_span_singleton'] at hh
    obtain ⟨a, ha⟩ := hh
    exact ⟨a, by rw [← hh₀, ← ha]; ring⟩
  have hsm : (Ideal.Quotient.mk Pb (Ideal.Quotient.mk J h₀)) • g N = 0 := by
    show (Ideal.Quotient.mk J h₀) • g N = 0
    show (Submodule.Quotient.mk ((Ideal.Quotient.mk J h₀) • (⟨_, hmem N⟩ : ↥(Pb ^ N))) : GrPiece Pb N) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have : (Ideal.Quotient.mk J h₀) * (Ideal.Quotient.mk J π) ^ N = 0 := by
      rw [← map_pow, ← map_mul, hh₀]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hhJ
    simp [Submodule.mem_comap, this]
  have hzero := (smul_eq_zero_iff_left (hg N)).mp hsm
  have hcPb : Ideal.Quotient.mk J h₀ ∈ Pb := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  obtain ⟨p, hpP, hpc⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hcPb
  have : h₀ - p ∈ J := by
    rw [← Ideal.Quotient.eq]; exact hpc.symm
  exact hh₀P (by simpa using P.add_mem (hJP this) hpP)

end PrepNormalFlatAlg

section PrepHeightOne
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsDomain A]

/-- Krull's principal ideal theorem in the form: a prime minimal over a principal ideal contains no
non-zero prime strictly. -/
theorem eq_of_isPrime_of_le_of_mem_minimalPrimes_span (z : A) (P : Ideal A) (hP : P ∈ (Ideal.span {z}).minimalPrimes)
    (p : Ideal A) [p.IsPrime] (hp0 : p ≠ ⊥) (hpP : p ≤ P) : p = P := by
  have hPprime : P.IsPrime := hP.1.1
  by_contra hne
  have hlt : p < P := lt_of_le_of_ne hpP hne
  have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {z}) P hP
  have h2 : p.height < P.height := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
  have h3 : p.height = 0 := by
    have : p.height < 1 := lt_of_lt_of_le h2 h1
    exact Order.lt_one_iff.mp this
  rw [Ideal.height_eq_zero_iff] at h3
  rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at h3
  exact hp0 h3

end PrepHeightOne

section PrepPrincipalPrime
open IsLocalRing

/-- In a regular local domain, a non-zero prime `P` with regular quotient which contains no other
non-zero prime is principal (a generator is an element of a minimal system of generators of the
maximal ideal lying in `P`). -/
theorem exists_span_singleton_eq_of_isRegularLocalRing_quotient {A : Type u} [CommRing A]
    [IsRegularLocalRing A] (P : Ideal A) [P.IsPrime] (hreg : IsRegularLocalRing (A ⧸ P))
    (hP0 : P ≠ ⊥) (hmin : ∀ p : Ideal A, p.IsPrime → p ≠ ⊥ → p ≤ P → p = P) :
    ∃ π : A, P = Ideal.span {π} := by
  classical
  obtain ⟨S, T, hS, hcard, hTS, hT⟩ := exists_finset_span_eq_prime A P hreg
  obtain ⟨t, htT, ht0⟩ : ∃ t ∈ T, t ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    apply hP0
    rw [← hT]
    exact Ideal.span_eq_bot.mpr fun t ht => hall t ht
  have htS : t ∈ S := hTS htT
  have htP : t ∈ P := hT ▸ Ideal.subset_span htT
  have htm : t ∈ maximalIdeal A := hS ▸ Ideal.subset_span htS
  have ht2 : t ∉ maximalIdeal A ^ 2 := by
    intro h2
    have := span_erase_eq_of_mem hS htS (Ideal.mem_sup_right h2)
    have hle : (maximalIdeal A).spanFinrank ≤ (S.erase t).card := by
      rw [← this]
      have := Submodule.spanFinrank_span_le_ncard_of_finite (R := A) (S.erase t).finite_toSet
      rwa [Set.ncard_coe_finset] at this
    rw [Finset.card_erase_of_mem htS] at hle
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨t, htS⟩
    omega
  have hloc : IsLocalRing (A ⧸ Ideal.span {t}) :=
    isLocalRing_quotient_of_le ((Ideal.span_singleton_le_iff_mem _).mpr htm)
  have hdom := (quotient_span_singleton_regular htm ht2).1
  have hprime : (Ideal.span {t}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
  refine ⟨t, (hmin _ hprime ?_ ((Ideal.span_singleton_le_iff_mem _).mpr htP)).symm⟩
  intro h
  exact ht0 (by simpa using (Ideal.span_singleton_eq_bot.mp h))

end PrepPrincipalPrime

section PrepRingIII
open IsLocalRing

/-- Ring-level core of "`V` normally flat along its component `F` has no other component through a
point of `F`" (Ch. II type step, p. 290), in the hypersurface situation of a regular local ring `R`:
`Q ⊆ Pf` are primes with regular quotients (`W' ⊇ F'`), `Pf` is minimal over `Q + (z)` (the boundary
`E_1' = (z)`), `JD` is an ideal with `Q ⊆ JD ⊆ Pf` and `z ∈ JD ∖ Q` (the ideal of `(W_* ∩ E_1)'`),
`R/JD` is normally flat along `Pf`, and `q` is a prime containing `JD` (a component through the
point).  Then `Pf ⊆ q`. -/
theorem le_of_isNormallyFlatAlongIdeal_of_mem_minimalPrimes {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (Q Pf JD q : Ideal R) (z : R) [Q.IsPrime] [Pf.IsPrime] [q.IsPrime]
    (hQreg : IsRegularLocalRing (R ⧸ Q)) (hPreg : IsRegularLocalRing (R ⧸ Pf)) (hQP : Q ≤ Pf)
    (hQJ : Q ≤ JD) (hJP : JD ≤ Pf) (hzJ : z ∈ JD) (hzQ : z ∉ Q)
    (hmin : Pf ∈ (Q ⊔ Ideal.span {z}).minimalPrimes)
    (hnf : IsNormallyFlatAlongIdeal (Pf.map (Ideal.Quotient.mk JD))) (hq : JD ≤ q) : Pf ≤ q := by
  classical
  have hqQ : Q ≤ q := hQJ.trans hq
  have hmk := Ideal.Quotient.mk_surjective (I := Q)
  -- the ring `A = R/Q`
  have hAdom : IsDomain (R ⧸ Q) := isDomain_of_isRegularLocalRing _
  set P : Ideal (R ⧸ Q) := Pf.map (Ideal.Quotient.mk Q) with hP
  have hPprime : P.IsPrime := Ideal.map_isPrime_of_surjective hmk (by rw [Ideal.mk_ker]; exact hQP)
  have hqbar : (q.map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective hmk (by rw [Ideal.mk_ker]; exact hqQ)
  -- `A/P ≃ R/Pf` is regular
  let eP : ((R ⧸ Q) ⧸ P) ≃+* R ⧸ Pf := DoubleQuot.quotQuotEquivQuotOfLE hQP
  have hPreg' : IsRegularLocalRing ((R ⧸ Q) ⧸ P) := IsRegularLocalRing.of_ringEquiv eP.symm
  -- `P` is minimal over `(z̄)`
  have hPmin : P ∈ (Ideal.span {Ideal.Quotient.mk Q z}).minimalPrimes := by
    refine ⟨⟨hPprime, ?_⟩, fun p' ⟨hp'prime, hp'z⟩ hp'P => ?_⟩
    · rw [Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_map_of_mem _ (hJP hzJ)
    · have hc : (p'.comap (Ideal.Quotient.mk Q)).IsPrime := Ideal.comap_isPrime _ _
      have h1 : Q ⊔ Ideal.span {z} ≤ p'.comap (Ideal.Quotient.mk Q) := by
        refine sup_le (fun a ha => ?_) ?_
        · rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]; exact p'.zero_mem
        · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
          exact hp'z (Ideal.mem_span_singleton_self _)
      have h2 : p'.comap (Ideal.Quotient.mk Q) ≤ Pf := by
        intro a ha
        have := hp'P ha
        rw [hP] at this
        obtain ⟨b, hb, hba⟩ := (Ideal.mem_map_iff_of_surjective _ hmk).mp this
        have : a - b ∈ Q := by rw [← Ideal.Quotient.eq]; exact hba.symm
        simpa using Pf.add_mem (hQP this) hb
      have h3 := hmin.2 ⟨hc, h1⟩ h2
      intro a ha
      obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hmk).mp ha
      exact h3 hb
  have hP0 : P ≠ ⊥ := by
    intro h
    apply hzQ
    have : Ideal.Quotient.mk Q z ∈ P := Ideal.mem_map_of_mem _ (hJP hzJ)
    rw [h, Ideal.mem_bot] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  obtain ⟨π, hπ⟩ := exists_span_singleton_eq_of_isRegularLocalRing_quotient P hPreg' hP0
    (fun p hp hp0 hpP => eq_of_isPrime_of_le_of_mem_minimalPrimes_span _ P hPmin p hp0 hpP)
  -- the ideal `J = JD/Q`
  set J : Ideal (R ⧸ Q) := JD.map (Ideal.Quotient.mk Q) with hJ
  have hJP' : J ≤ Ideal.span {π} := hπ ▸ Ideal.map_mono hJP
  have hJ0 : J ≠ ⊥ := by
    intro h
    have hz' : Ideal.Quotient.mk Q z ∈ J := Ideal.mem_map_of_mem _ hzJ
    rw [h, Ideal.mem_bot] at hz'
    exact hzQ (Ideal.Quotient.eq_zero_iff_mem.mp hz')
  -- transport the normal flatness
  let eJ : ((R ⧸ Q) ⧸ J) ≃+* R ⧸ JD := DoubleQuot.quotQuotEquivQuotOfLE hQJ
  have hnf' : IsNormallyFlatAlongIdeal ((Ideal.span {π}).map (Ideal.Quotient.mk J)) := by
    refine isNormallyFlatAlongIdeal_transport eJ.symm (Pf.map (Ideal.Quotient.mk JD)) _ ?_ hnf
    rw [← hπ, hP, Ideal.map_map, Ideal.map_map]
    congr 1
  have : IsDomain (R ⧸ Q) := hAdom
  obtain ⟨a, ha⟩ := exists_pow_mem_of_isNormallyFlatAlongIdeal_span π (hπ ▸ hPprime) J hJ0 hJP' hnf'
  have hπq : π ∈ q.map (Ideal.Quotient.mk Q) := by
    have h1 : π ^ a ∈ q.map (Ideal.Quotient.mk Q) := Ideal.map_mono hq ha
    exact hqbar.mem_of_pow_mem a h1
  have hPq : P ≤ q.map (Ideal.Quotient.mk Q) := by
    rw [hπ]; exact (Ideal.span_singleton_le_iff_mem _).mpr hπq
  intro a' ha'
  have h1 : Ideal.Quotient.mk Q a' ∈ q.map (Ideal.Quotient.mk Q) := hPq (Ideal.mem_map_of_mem _ ha')
  obtain ⟨b, hb, hba⟩ := (Ideal.mem_map_iff_of_surjective _ hmk).mp h1
  have : a' - b ∈ Q := by rw [← Ideal.Quotient.eq]; exact hba.symm
  simpa using q.add_mem (hqQ this) hb

end PrepRingIII

section PrepSchemeIII
variable {Y : Scheme.{u}}

/-- Scheme-level form of `le_of_isNormallyFlatAlongIdeal_of_mem_minimalPrimes`: `D` (the strict
transform of `W_* ∩ E_1`) is normally flat along its component `F`, with `F ⊆ D ⊆ W` and `W`, `F`
simple at `x`; `E_1 = (z)` near `x` with `z ∈ D_x ∖ W_x` and `F_x` minimal over `W_x + (z)`.  Then
every prime `q` containing `D_x` contains `F_x`. -/
theorem Subscheme.stalkIdeal_le_of_isNormallyFlatAlongAt'_of_mem_minimalPrimes
    (hY : Y.IsNonsingular) {W F D : Subscheme Y} {x : Y}
    (hW : W.IsSimpleAt x) (hF : F.IsSimpleAt x) (hFD : F.IsContainedIn D)
    (hDW : D.IsContainedIn W) {z : Y.presheaf.stalk x} (hzD : z ∈ D.stalkIdeal x)
    (hzW : z ∉ W.stalkIdeal x)
    (hmin : F.stalkIdeal x ∈ (W.stalkIdeal x ⊔ Ideal.span {z}).minimalPrimes)
    (hnf : Subscheme.IsNormallyFlatAlongAt' D F x)
    {q : Ideal (Y.presheaf.stalk x)} [q.IsPrime] (hq : D.stalkIdeal x ≤ q) :
    F.stalkIdeal x ≤ q := by
  have : IsRegularLocalRing (Y.presheaf.stalk x) := hY x
  have hWp := isPrime_stalkIdeal_of_isSimpleAt hW
  have hFp := isPrime_stalkIdeal_of_isSimpleAt hF
  have hnf' := ((Subscheme.isNormallyFlatAlongAt'_iff D F hFD x).mp hnf).2
  exact le_of_isNormallyFlatAlongIdeal_of_mem_minimalPrimes (W.stalkIdeal x) (F.stalkIdeal x)
    (D.stalkIdeal x) q z hW.2 hF.2
    (stalkIdeal_le_stalkIdeal_of_isContainedIn (hFD.trans hDW) x |>.trans' le_rfl)
    (stalkIdeal_le_stalkIdeal_of_isContainedIn hDW x)
    (stalkIdeal_le_stalkIdeal_of_isContainedIn hFD x) hzD hzW hmin hnf' hq

end PrepSchemeIII

section PrepWStarStalk
variable {Y : Scheme.{u}}

/-- At a point `x` of `W_*` where the stalk of `W` is prime, the stalk of `W_*` is that of `W`: the
unique component of `W` through `x` is a component of `W` not contained in `E_1`, hence lies in `W_*`.
Moreover `E_1` does not contain this component, so `E_{1,x} = (z)` has `z ∉ W_x`. -/
theorem DatumI.Raw.stalkIdeal_prepWStar_eq [IsAlgebraicScheme Y] (ℜ : DatumI.Raw Y) (E₁ : Subscheme Y)
    {x : Y} (hx : x ∈ (ℜ.prepWStar E₁).pts) (hW : (ℜ.W.stalkIdeal x).IsPrime) :
    (ℜ.prepWStar E₁).stalkIdeal x = ℜ.W.stalkIdeal x ∧
      ∃ C ∈ ℜ.W.irreducibleComponents, ¬ C.IsContainedIn E₁ ∧ x ∈ C.pts ∧
        C.stalkIdeal x = ℜ.W.stalkIdeal x := by
  have : TopologicalSpace.NoetherianSpace Y := IsAlgebraicScheme.noetherianSpace Y
  obtain ⟨C, hC, hCE, hxC⟩ := ℜ.exists_mem_irreducibleComponents_of_mem_pts_prepWStar E₁ hx
  have hmin := Subscheme.stalkIdeal_mem_minimalPrimes hC hxC
  rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hmin
  refine ⟨le_antisymm ?_ ?_, C, hC, hCE, hxC, hmin⟩
  · rw [← hmin]
    refine Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn ?_ x
    obtain ⟨Z, hZ, rfl⟩ := hC
    refine Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced Z) ?_
    intro y hy
    rw [DatumI.Raw.pts_prepWStar]
    refine subset_closure ⟨_, ⟨Z, ⟨Subscheme.ofClosed Z, ⟨Z, hZ, rfl⟩, hCE, (Subscheme.support_ofClosed Z).symm⟩, rfl⟩, ?_⟩
    exact hy
  · refine Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn ?_ x
    exact Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced _)
      (ℜ.pts_prepWStar_subset E₁)

end PrepWStarStalk

section PrepInterExceptional
variable {Y : Scheme.{u}}

/-- If `E = ⋃ E_i` has only normal crossings with `W` at `y` and `E_{i₀}` passes through `y` without
containing the branch of `W` there, then `W ∩ E_{i₀}` is simple at `y`: `W_y` and `(E_{i₀})_y` are
generated by parts of one regular system of parameters, with the equation of `E_{i₀}` not among
the generators of `W_y`. -/
theorem Subscheme.isSimpleAt_inter_of_hasOnlyNormalCrossingsWithAt (hY : Y.IsNonsingular) {ι : Type*}
    [Fintype ι] (E : ι → Subscheme Y) (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne)
    {W : Subscheme Y} {y : Y} (hW : y ∈ W.pts)
    (hnc : (Subscheme.unionFam E).HasOnlyNormalCrossingsWithAt W y) (i₀ : ι)
    (hyE : y ∈ (E i₀).pts) (hne : ¬ (E i₀).stalkIdeal y ≤ W.stalkIdeal y) :
    (W.inter (E i₀)).IsSimpleAt y := by
  classical
  have : IsRegularLocalRing (Y.presheaf.stalk y) := hY y
  obtain ⟨Z, hZ, ⟨T, hTZ, hWT⟩, hEZ⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    E hE (fun i => iInf_le _ i) hnc
  obtain ⟨a, haZ, ha⟩ : ∃ a ∈ Z, (E i₀).stalkIdeal y = Ideal.span {a} := by
    rcases hEZ i₀ with h | h
    · exact absurd h ((Subscheme.mem_pts_iff_stalkIdeal_ne_top).mp hyE)
    · exact h
  have haT : a ∉ T := fun haT => hne (by
    rw [ha, hWT, Ideal.span_singleton_le_iff_mem]; exact Ideal.subset_span haT)
  have hext : ExtendsToRSOP _ (insert a T) :=
    (ExtendsToRSOP.of_isRegularSystemOfParameters hZ).mono (Finset.insert_subset haZ hTZ)
  refine ⟨Subscheme.mem_pts_inter_iff.mpr ⟨hW, hyE⟩, ?_⟩
  have hst : (W.inter (E i₀)).stalkIdeal y = Ideal.span ((insert a T : Finset _) : Set _) := by
    show (W ⊔ E i₀).stalkIdeal y = _
    rw [Subscheme.stalkIdeal_sup_eq, ha, hWT, Finset.coe_insert, Ideal.span_insert, sup_comm]
  rw [hst]
  exact hext.isRegularLocalRing_quotient

end PrepInterExceptional

section PrepHeightEq
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A prime `q` of `R` minimal over `Q + (z)` (`Q` prime) contains `Q + (e)` (`e ∉ Q`, `Q + (e)`
prime) only in the trivial way: `Q + (e) = q`.  (Krull's principal ideal theorem in `R/Q`.) -/
theorem sup_span_eq_of_le_of_mem_minimalPrimes {Q : Ideal R} [Q.IsPrime] {z e : R} {q : Ideal R}
    (hq : q ∈ (Q ⊔ Ideal.span {z}).minimalPrimes) (hp : (Q ⊔ Ideal.span {e}).IsPrime) (heQ : e ∉ Q)
    (hpq : Q ⊔ Ideal.span {e} ≤ q) : Q ⊔ Ideal.span {e} = q := by
  classical
  have hmk := Ideal.Quotient.mk_surjective (I := Q)
  have hqprime : q.IsPrime := hq.1.1
  have hQq : Q ≤ q := le_sup_left.trans hq.1.2
  have hAdom : IsDomain (R ⧸ Q) := Ideal.Quotient.isDomain Q
  have hqbar : (q.map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective hmk (by rw [Ideal.mk_ker]; exact hQq)
  have hpbar : ((Q ⊔ Ideal.span {e}).map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective hmk (by rw [Ideal.mk_ker]; exact le_sup_left)
  have hqmin : q.map (Ideal.Quotient.mk Q) ∈ (Ideal.span {Ideal.Quotient.mk Q z}).minimalPrimes := by
    refine ⟨⟨hqbar, ?_⟩, fun p' ⟨hp'prime, hp'z⟩ hp'q => ?_⟩
    · rw [Ideal.span_singleton_le_iff_mem]
      have hzq : z ∈ q :=
        ((le_sup_right : Ideal.span {z} ≤ Q ⊔ Ideal.span {z}).trans hq.1.2)
          (Ideal.mem_span_singleton_self z)
      exact Ideal.mem_map_of_mem _ hzq
    · have hc : (p'.comap (Ideal.Quotient.mk Q)).IsPrime := Ideal.comap_isPrime _ _
      have h1 : Q ⊔ Ideal.span {z} ≤ p'.comap (Ideal.Quotient.mk Q) := by
        refine sup_le (fun a ha => ?_) ?_
        · rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]; exact p'.zero_mem
        · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
          exact hp'z (Ideal.mem_span_singleton_self _)
      have h2 : p'.comap (Ideal.Quotient.mk Q) ≤ q := by
        intro a ha
        have := hp'q ha
        obtain ⟨b, hb, hba⟩ := (Ideal.mem_map_iff_of_surjective _ hmk).mp this
        have : a - b ∈ Q := by rw [← Ideal.Quotient.eq]; exact hba.symm
        simpa using q.add_mem (hQq this) hb
      have h3 := hq.2 ⟨hc, h1⟩ h2
      intro a ha
      obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hmk).mp ha
      exact h3 hb
  have hpne : (Q ⊔ Ideal.span {e}).map (Ideal.Quotient.mk Q) ≠ ⊥ := by
    intro h
    apply heQ
    have : Ideal.Quotient.mk Q e ∈ (Q ⊔ Ideal.span {e}).map (Ideal.Quotient.mk Q) :=
      Ideal.mem_map_of_mem _
        ((le_sup_right : Ideal.span {e} ≤ Q ⊔ Ideal.span {e}) (Ideal.mem_span_singleton_self e))
    rw [h, Ideal.mem_bot] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  have hEq := eq_of_isPrime_of_le_of_mem_minimalPrimes_span _ _ hqmin _ hpne (Ideal.map_mono hpq)
  have hker : RingHom.ker (Ideal.Quotient.mk Q) ≤ Q ⊔ Ideal.span {e} := by
    rw [Ideal.mk_ker]; exact le_sup_left
  have hker' : RingHom.ker (Ideal.Quotient.mk Q) ≤ q := by rw [Ideal.mk_ker]; exact hQq
  calc Q ⊔ Ideal.span {e}
      = ((Q ⊔ Ideal.span {e}).map (Ideal.Quotient.mk Q)).comap (Ideal.Quotient.mk Q) :=
        (Ideal.comap_map_of_surjective _ hmk _).trans (sup_eq_left.mpr hker) |>.symm
    _ = (q.map (Ideal.Quotient.mk Q)).comap (Ideal.Quotient.mk Q) := by rw [hEq]
    _ = q := (Ideal.comap_map_of_surjective _ hmk _).trans (sup_eq_left.mpr hker')

end PrepHeightEq

section PrepGlobalEq
variable {Y : Scheme.{u}}

/-- A component `G` of `W_* ∩ E_1` through `x`, contained in `H = W ∩ E_j` with `H` non-singular
irreducible and `E_{j,x} = (e)`, `e ∉ W_x`, equals `H`: the primes `G_x ⊇ H_x = W_x + (e)` of height one
over `W_x` coincide (Krull), and `H` is irreducible. -/
theorem Subscheme.pts_eq_of_mem_irreducibleComponents_of_inter [IsAlgebraicScheme Y]
    {Wst W E₁ Ej : Subscheme Y} {x : Y} {z e : Y.presheaf.stalk x}
    (hWst : Wst.stalkIdeal x = W.stalkIdeal x) (hWp : (W.stalkIdeal x).IsPrime)
    (hz : E₁.stalkIdeal x = Ideal.span {z}) (he : Ej.stalkIdeal x = Ideal.span {e})
    (heQ : e ∉ W.stalkIdeal x) (hHred : (W.inter Ej).IsReduced) (hHirr : (W.inter Ej).IsIrreducible)
    (hHp : ((W.inter Ej).stalkIdeal x).IsPrime)
    {G : Subscheme Y} (hG : G ∈ (Wst.inter E₁).irreducibleComponents) (hxG : x ∈ G.pts)
    (hsub : G.pts ⊆ (W.inter Ej).pts) : G.pts = (W.inter Ej).pts := by
  classical
  have hmin := Subscheme.stalkIdeal_mem_minimalPrimes hG hxG
  have hDst : (Wst.inter E₁).stalkIdeal x = W.stalkIdeal x ⊔ Ideal.span {z} := by
    show (Wst ⊔ E₁).stalkIdeal x = _
    rw [Subscheme.stalkIdeal_sup_eq, hWst, hz]
  rw [hDst] at hmin
  have hHst : (W.inter Ej).stalkIdeal x = W.stalkIdeal x ⊔ Ideal.span {e} := by
    show (W ⊔ Ej).stalkIdeal x = _
    rw [Subscheme.stalkIdeal_sup_eq, he]
  have hGred : G.IsReduced := by
    obtain ⟨Z, -, rfl⟩ := hG; exact Subscheme.ofClosed_isReduced Z
  have hle : (W.inter Ej).stalkIdeal x ≤ G.stalkIdeal x :=
    stalkIdeal_le_stalkIdeal_of_isContainedIn (Subscheme.isContainedIn_of_pts_subset hGred hsub) x
  have := IsAlgebraicScheme.isNoetherian Y
  have hEq : (W.inter Ej).stalkIdeal x = G.stalkIdeal x := by
    have h1 := sup_span_eq_of_le_of_mem_minimalPrimes (Q := W.stalkIdeal x) hmin
      (hHst ▸ hHp) heQ (hHst ▸ hle)
    rw [hHst]; exact h1
  obtain ⟨ξ, hξ⟩ := Subscheme.exists_isGenericPoint hHirr
  have hxH : x ∈ (W.inter Ej).pts := hsub hxG
  have hξx : ξ ⤳ x := by
    rw [specializes_iff_mem_closure, hξ.def]; exact hxH
  have hHeq : (W.inter Ej) = Subscheme.ofClosed ⟨closure {ξ}, isClosed_closure⟩ := by
    rw [Subscheme.eq_ofClosed_support _ hHred]
    congr 1
    exact Closeds.ext hξ.def.symm
  have hξG : ξ ∈ G.pts := by
    refine Subscheme.mem_pts_of_stalkIdeal_le_ofClosed_closure hξx G ?_
    rw [← hHeq, hEq]
  apply subset_antisymm hsub
  rw [← hξ.def]
  have hGcl : IsClosed G.pts := G.support.isClosed
  exact closure_minimal (Set.singleton_subset_iff.mpr hξG) hGcl

end PrepGlobalEq

section PrepStrictNotExc
variable {X : Scheme.{u}} {B : Subscheme X}

/-- The generic point of an irreducible component of a strict transform does not lie over the
center (`notMem_exceptional_of_generic`, phrased for points of `X'`). -/
theorem MonoidalTransformation.notMem_exceptional_of_isGenericPoint_component
    (t : MonoidalTransformation X B) (V : Subscheme X) {Z : Closeds t.X'}
    (hZ : Maximal (fun Z : Closeds t.X' => _root_.IsIrreducible (Z : Set t.X') ∧
      (Z : Set t.X') ⊆ (Subscheme.strictTransform t V).pts) Z) {ω : t.X'}
    (hω : IsGenericPoint ω (Z : Set t.X')) : ω ∉ t.exceptional.pts := by
  set D := Subscheme.strictTransform t V with hD
  have hωD : ω ∈ D.pts := hZ.1.2 hω.mem
  obtain ⟨y, hy⟩ := Subscheme.exists_ι_eq_of_mem_pts D hωD
  have := MonoidalTransformation.notMem_exceptional_of_generic t V hD y ?_
  · rwa [hy] at this
  · intro w hw
    have h1 : D.ι w ⤳ D.ι y := hw.map D.ι.continuous
    have h2 : D.ι w ∈ D.pts := Subscheme.mem_pts_ι D w
    rw [hy] at h1
    have h3 : (Z : Set t.X') ⊆ closure {D.ι w} := by
      rw [← hω.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp h1))
        isClosed_closure
    have h4 : closure {D.ι w} ⊆ (Z : Set t.X') :=
      hZ.2 (y := ⟨closure {D.ι w}, isClosed_closure⟩)
        ⟨isIrreducible_singleton.closure,
          closure_minimal (Set.singleton_subset_iff.mpr h2) D.support.isClosed⟩ h3
    have h5 : Inseparable (D.ι w) ω := by
      rw [inseparable_iff_closure_eq, hω.def]
      exact le_antisymm h4 h3
    exact D.ι.isClosedEmbedding.injective (h5.eq.trans hy.symm)

/-- The local equation of the exceptional divisor does not lie in the stalk of a component of a
strict transform. -/
theorem MonoidalTransformation.not_stalkIdeal_exceptional_le_of_mem_irreducibleComponents
    (t : MonoidalTransformation X B) (V : Subscheme X) {C : Subscheme t.X'}
    (hC : C ∈ (Subscheme.strictTransform t V).irreducibleComponents) {y : t.X'} (hy : y ∈ C.pts) :
    ¬ t.exceptional.stalkIdeal y ≤ C.stalkIdeal y := by
  intro hle
  obtain ⟨Z, hZ, rfl⟩ := hC
  obtain ⟨ω, hω⟩ : ∃ ω, IsGenericPoint ω (Z : Set t.X') := QuasiSober.sober hZ.1.1 Z.isClosed
  have hωy : ω ⤳ y := by
    rw [specializes_iff_mem_closure, hω.def]
    have := hy
    rwa [Subscheme.pts_ofClosed] at this
  have hZeq : Z = ⟨closure {ω}, isClosed_closure⟩ := Closeds.ext hω.def.symm
  have hst : t.exceptional.stalkIdeal y ≤
      (Subscheme.ofClosed ⟨closure {ω}, isClosed_closure⟩).stalkIdeal y := by
    rw [← hZeq]; exact hle
  exact t.notMem_exceptional_of_isGenericPoint_component V hZ hω
    (Subscheme.mem_pts_of_stalkIdeal_le_ofClosed_closure hωy t.exceptional hst)

end PrepStrictNotExc

section PrepRSOPIndep
open IsLocalRing

/-- An element of a regular system of parameters is not in the ideal generated by the others. -/
theorem not_mem_span_erase_of_isRegularSystemOfParameters {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [DecidableEq R] {Z : Finset R} (hZ : IsRegularSystemOfParameters R Z)
    {g : R} (hg : g ∈ Z) : g ∉ Ideal.span ((Z.erase g : Finset R) : Set R) := by
  intro h
  have h1 := span_erase_eq_of_mem hZ.1 hg (Ideal.mem_sup_left h)
  have hle : (maximalIdeal R).spanFinrank ≤ (Z.erase g).card := by
    rw [← h1]
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Z.erase g).finite_toSet
    rwa [Set.ncard_coe_finset] at this
  have hcard : (Z.card : WithBot ℕ∞) = (maximalIdeal R).spanFinrank := by
    rw [hZ.2]; exact (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  rw [Finset.card_erase_of_mem hg] at hle
  have hpos : 0 < Z.card := Finset.card_pos.mpr ⟨g, hg⟩
  have : Z.card = (maximalIdeal R).spanFinrank := by exact_mod_cast hcard
  omega

end PrepRSOPIndep

section PrepStepIdentity
variable {X : Scheme.{u}} {B : Subscheme X}

/-- One step of the identity `W' ∩ E_i' = (W ∩ E_i)'` used on p. 290 ("`W' ∩ E_j'` … non-singular
irreducible"): for a permissible center `B` at whose points the datum `ℜ` is resolved, the points of
the intersection of the strict transforms of `W` and of a component `E_i` of the boundary are the
points of the strict transform of `W ∩ E_i`.

Proof.  Off the exceptional divisor `f` is a local isomorphism.  At a point `y` over the center the
transformed datum is resolved (Lemma 4 and Corollary 2 of Theorem 5), so `W'_y`, `(E_i')_y` and the
exceptional divisor `(g)` have equations in one regular system of parameters, `g` being neither among
those of `W'_y` nor equal to that of `E_i'` (strict transforms have no component in the exceptional
divisor); hence `g ∉ W'_y + (E_i')_y`, the generic point of the branch of `W' ∩ E_i'` at `y` is not in
the exceptional divisor, and `y` is a specialization of it.

Deviation from the paper (gap filled): tacit on p. 290. -/
theorem MonoidalTransformation.pts_inter_strictTransform_subset [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] [IsAlgebraicScheme X]
    (t : MonoidalTransformation X B) (hX : X.IsNonsingular) (hXirr : IrreducibleSpace X)
    {R : DatumI.Raw X} (hR : R.IsDatum) (hB : R.IsPermissible B)
    (hdense : R.W.pts ⊆ closure (R.W.pts \ B.pts)) (hresB : ∀ x ∈ B.pts, R.ResolvedAt x)
    {α : ℕ} (E : Fin α → Subscheme X) (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne)
    (hEunion : R.E = Subscheme.unionFam E) (i : Fin α) {y : t.X'}
    (hyW : y ∈ (Subscheme.strictTransform t R.W).pts)
    (hyE : y ∈ (Subscheme.strictTransform t (E i)).pts) :
    y ∈ (Subscheme.strictTransform t (R.W.inter (E i))).pts := by
  classical
  have hBns := hB.1.isNonsingular
  have hY : t.X'.IsNonsingular := (t.isNonsingular_and_isNonsingular_exceptional hX hBns).1
  by_cases hyexc : y ∈ t.exceptional.pts
  · have hyB : t.f.base y ∈ B.pts := by rwa [MonoidalTransformation.pts_exceptional] at hyexc
    obtain ⟨E₁, hE₁, hEq₁, hcs₁, hlast₁⟩ :=
      DatumI.Raw.exists_presentation_transform hX E hE R hR hEunion t hB
    have hres := DatumI.Raw.resolvedAt_transform_of_resolvedAt hXirr hX hR hB hdense t hyW
      (hresB _ hyB)
    have hnc : (Subscheme.unionFam E₁).HasOnlyNormalCrossingsWithAt
        (Subscheme.strictTransform t R.W) y := by
      rw [← hEq₁]; exact hres.2.2
    have : IsRegularLocalRing (t.X'.presheaf.stalk y) := hY y
    obtain ⟨Z, hZ, ⟨T, hTZ, hWT⟩, hEZ⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
      E₁ hE₁ (fun k => iInf_le _ k) hnc
    have hyEi : y ∈ (E₁ i.castSucc).pts := by rw [hcs₁ i]; exact hyE
    have hyEg : y ∈ (E₁ (Fin.last α)).pts := by rw [hlast₁]; exact hyexc
    obtain ⟨a, haZ, ha⟩ : ∃ a ∈ Z, (E₁ i.castSucc).stalkIdeal y = Ideal.span {a} := by
      rcases hEZ i.castSucc with h | h
      · exact absurd h ((Subscheme.mem_pts_iff_stalkIdeal_ne_top).mp hyEi)
      · exact h
    obtain ⟨g, hgZ, hg⟩ : ∃ g ∈ Z, (E₁ (Fin.last α)).stalkIdeal y = Ideal.span {g} := by
      rcases hEZ (Fin.last α) with h | h
      · exact absurd h ((Subscheme.mem_pts_iff_stalkIdeal_ne_top).mp hyEg)
      · exact h
    rw [hlast₁] at hg
    -- `g` is not among the generators of `W'_y`, nor equal to `a`
    have hWp : ((Subscheme.strictTransform t R.W).stalkIdeal y).IsPrime :=
      Subscheme.isPrime_stalkIdeal_of_isSimpleAt hres.1
    have hmin : (Subscheme.strictTransform t R.W).stalkIdeal y ∈
        ((Subscheme.strictTransform t R.W).stalkIdeal y).minimalPrimes := by
      rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl
    obtain ⟨C, hC, hyC, hCst⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes
      (Subscheme.strictTransform t R.W) y hmin
    have hgW := t.not_stalkIdeal_exceptional_le_of_mem_irreducibleComponents R.W hC hyC
    rw [hCst, hg] at hgW
    have hgT : g ∉ T := fun hgT => hgW (by
      rw [hWT, Ideal.span_singleton_le_iff_mem]; exact Ideal.subset_span hgT)
    have hEi := hE₁ i.castSucc
    have hEine : E₁ i.castSucc ≠ Subscheme.empty := fun h => by
      rw [h, Subscheme.pts_empty] at hyEi; exact hyEi
    obtain ⟨hEins, hEiirr, -⟩ := hEi.resolve_left hEine
    have hEiC : E₁ i.castSucc ∈ (Subscheme.strictTransform t (E i)).irreducibleComponents := by
      rw [← hcs₁ i]; exact Subscheme.mem_irreducibleComponents_self _ hEins hEiirr
    have hgE := t.not_stalkIdeal_exceptional_le_of_mem_irreducibleComponents (E i) hEiC hyEi
    rw [hg, ha] at hgE
    have hga : g ≠ a := fun h => hgE (by rw [h])
    -- the stalk of `W' ∩ E_i'` at `y`
    have hsub : insert a T ⊆ Z.erase g := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hvT
      · exact Finset.mem_erase.mpr ⟨fun h => hga h.symm, haZ⟩
      · exact Finset.mem_erase.mpr ⟨fun h => hgT (h ▸ hvT), hTZ hvT⟩
    obtain ⟨I, hI⟩ : ∃ I : Ideal (t.X'.presheaf.stalk y),
        I = Ideal.span (↑(insert a T) : Set (t.X'.presheaf.stalk y)) := ⟨_, rfl⟩
    have hgI : g ∉ I := fun h => by
      rw [hI] at h
      exact not_mem_span_erase_of_isRegularSystemOfParameters hZ hgZ
        (Ideal.span_mono (by exact_mod_cast hsub) h)
    have hext : ExtendsToRSOP _ (insert a T) :=
      (ExtendsToRSOP.of_isRegularSystemOfParameters hZ).mono
        (hsub.trans (Finset.erase_subset _ _))
    have hIreg : IsRegularLocalRing (t.X'.presheaf.stalk y ⧸ I) := by
      rw [hI]; exact hext.isRegularLocalRing_quotient
    have hIdom := isDomain_of_isRegularLocalRing (t.X'.presheaf.stalk y ⧸ I)
    have hIprime : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hIdom
    have hHst : ((Subscheme.strictTransform t R.W).inter
        (Subscheme.strictTransform t (E i))).stalkIdeal y = I := by
      show ((Subscheme.strictTransform t R.W) ⊔ (Subscheme.strictTransform t (E i))).stalkIdeal y = _
      rw [Subscheme.stalkIdeal_sup_eq, hWT, ← hcs₁ i, ha, hI, Finset.coe_insert, Ideal.span_insert,
        sup_comm]
    have hmin' : I ∈ (((Subscheme.strictTransform t R.W).inter
        (Subscheme.strictTransform t (E i))).stalkIdeal y).minimalPrimes := by
      rw [hHst, Ideal.minimalPrimes_eq_subsingleton_self]; rfl
    obtain ⟨C', hC', hyC', hC'st⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes
      ((Subscheme.strictTransform t R.W).inter (Subscheme.strictTransform t (E i))) y hmin'
    obtain ⟨Zc, hZc, rfl⟩ := hC'
    have hZcpts : (Subscheme.ofClosed Zc).pts = Zc := Scheme.IdealSheafData.coe_support_vanishingIdeal Zc
    obtain ⟨ζ, hζ⟩ : ∃ ζ, IsGenericPoint ζ (Zc : Set t.X') := QuasiSober.sober hZc.1.1 Zc.isClosed
    have hyZc : y ∈ Zc := by rwa [hZcpts] at hyC'
    have hζy : ζ ⤳ y := by rw [specializes_iff_mem_closure, hζ.def]; exact hyZc
    have hζH : ζ ∈ ((Subscheme.strictTransform t R.W).inter (Subscheme.strictTransform t (E i))).pts :=
      hZc.1.2 hζ.mem
    have hζexc : ζ ∉ t.exceptional.pts := by
      intro hζE
      apply hgI
      have hcont : (Subscheme.ofClosed Zc).IsContainedIn t.exceptional := by
        refine Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced Zc) ?_
        rw [hZcpts, ← hζ.def]
        exact closure_minimal (Set.singleton_subset_iff.mpr hζE) t.exceptional.support.isClosed
      have := Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hcont y
      rw [hg, hC'st] at this
      exact this (Ideal.mem_span_singleton_self g)
    obtain ⟨hζW, hζE⟩ := Subscheme.mem_pts_inter_iff.mp hζH
    have hfζ : t.f.base ζ ∈ (R.W.inter (E i)).pts :=
      Subscheme.mem_pts_inter_iff.mpr ⟨t.pts_strictTransform_subset _ hζW,
        t.pts_strictTransform_subset _ hζE⟩
    have hζmem : ζ ∈ (Subscheme.strictTransform t (R.W.inter (E i))).pts := by
      rw [MonoidalTransformation.pts_strictTransform_eq_closure]
      exact subset_closure ⟨hfζ, hζexc⟩
    exact closure_minimal (Set.singleton_subset_iff.mpr hζmem)
      (Subscheme.strictTransform t (R.W.inter (E i))).support.isClosed
      (specializes_iff_mem_closure.mp hζy)
  · have hfy : t.f.base y ∈ (R.W.inter (E i)).pts :=
      Subscheme.mem_pts_inter_iff.mpr ⟨t.pts_strictTransform_subset _ hyW,
        t.pts_strictTransform_subset _ hyE⟩
    rw [MonoidalTransformation.pts_strictTransform_eq_closure]
    exact subset_closure ⟨hfy, hyexc⟩

end PrepStepIdentity

section PrepStageInduction
variable {X Y : Scheme.{u}}

/-- The standing hypotheses at one stage of a succession `s` permissible for `(R, U)` (the tail datum
of p. 290): `R` is a good datum with open restriction `U`, resolved at the points of `W` over
`Ũ`, and the centers of `s` lie over a closed subscheme `F ⊆ Ũ`. -/
structure StageHyp (N n : ℕ) (s : MonoidalSuccession X Y) (R : DatumI.Raw X) (U Ũ : Set X)
    (F : Subscheme X) : Prop where
  good : IsGoodDatumI N n X R
  openR : R.IsOpenRestriction U
  perm : s.IsPermissibleIOpen R U
  res : ∀ x ∈ Ũ, x ∈ R.W.pts → R.ResolvedAt x
  cent : s.CentersIn F
  sub : F.pts ⊆ Ũ

/-- The hypotheses pass to the transform after the first step. -/
theorem StageHyp.next [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} {B : Subscheme X} {t : MonoidalTransformation X B}
    {rest : MonoidalSuccession t.X' Y} {R : DatumI.Raw X} {U Ũ : Set X} {F : Subscheme X}
    (H : StageHyp N n (MonoidalSuccession.cons B t rest) R U Ũ F) :
    StageHyp N n rest (R.transform t) (DatumI.Raw.transformOpen t U) (t.f.base ⁻¹' Ũ)
      (Subscheme.strictTransform t F) := by
  have hdense := DatumI.Raw.pts_subset_closure_diff_of_isPermissibleOpen H.openR H.perm.1
  obtain ⟨h', hU'⟩ := IsGoodDatumI.transform_open H.good H.openR H.perm.1 t
  have := H.good.1.1
  refine ⟨h', hU', H.perm.2, fun y hy hyW => ?_, H.cent.2, fun y hy => ?_⟩
  · have hxW : t.f.base y ∈ R.W.pts := t.pts_strictTransform_subset _ hyW
    exact DatumI.Raw.resolvedAt_transform_of_resolvedAt H.good.1.2.2.1 H.good.1.2.1 H.good.2.1
      H.perm.1.1 hdense t hyW (H.res _ hy hxW)
  · exact H.sub (t.pts_strictTransform_subset _ hy)

/-- The identity `W' ∩ E_i' = (W ∩ E_i)'` along a succession (iterating
`MonoidalTransformation.pts_inter_strictTransform_subset`). -/
theorem MonoidalSuccession.pts_inter_strictTransform_subset [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} (s : MonoidalSuccession X Y)
    {R : DatumI.Raw X} {U Ũ : Set X} {F : Subscheme X} (H : StageHyp N n s R U Ũ F)
    {α : ℕ} (E : Fin α → Subscheme X) (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne)
    (hEunion : R.E = Subscheme.unionFam E) (i : Fin α) {y : Y}
    (hyW : y ∈ (s.strictTransform R.W).pts) (hyE : y ∈ (s.strictTransform (E i)).pts) :
    y ∈ (s.strictTransform (R.W.inter (E i))).pts := by
  induction s generalizing α with
  | nil X => exact (Subscheme.mem_pts_inter_iff.mpr ⟨hyW, hyE⟩ : y ∈ (R.W.inter (E i)).pts)
  | cons B t rest ih =>
    have := H.good.1.1
    have hdense := DatumI.Raw.pts_subset_closure_diff_of_isPermissibleOpen H.openR H.perm.1
    obtain ⟨E₁, hE₁, hEq₁, hcs₁, hlast₁⟩ :=
      DatumI.Raw.exists_presentation_transform H.good.1.2.1 E hE R H.good.2.1 hEunion t H.perm.1.1
    have hresB : ∀ x ∈ B.pts, R.ResolvedAt x := fun x hx =>
      H.res x (H.sub (H.cent.1 hx)) (H.perm.1.2 hx).1
    have hstep : ∀ z : t.X', z ∈ (Subscheme.strictTransform t R.W).pts →
        z ∈ (Subscheme.strictTransform t (E i)).pts →
        z ∈ (Subscheme.strictTransform t (R.W.inter (E i))).pts := fun z hz1 hz2 =>
      t.pts_inter_strictTransform_subset H.good.1.2.1 H.good.1.2.2.1 H.good.2.1
        H.perm.1.1 hdense hresB E hE hEunion i hz1 hz2
    have hy1 := ih H.next E₁ hE₁ hEq₁ i.castSucc (by exact hyW) (by rw [hcs₁ i]; exact hyE)
    refine rest.pts_strictTransform_mono ?_ hy1
    intro z hz
    obtain ⟨hz1, hz2⟩ := Subscheme.mem_pts_inter_iff.mp hz
    rw [hcs₁ i] at hz2
    exact hstep z hz1 hz2

/-- The strict transform, along a succession, of an irreducible subscheme with non-empty strict
transform is irreducible. -/
theorem MonoidalSuccession.isIrreducible_pts_strictTransform (s : MonoidalSuccession X Y)
    (V : Subscheme X) (hV : _root_.IsIrreducible V.pts) (hne : (s.strictTransform V).pts.Nonempty) :
    _root_.IsIrreducible (s.strictTransform V).pts := by
  induction s with
  | nil X => exact hV
  | cons B t rest ih =>
    have hne' : (Subscheme.strictTransform t V).pts.Nonempty := by
      obtain ⟨y, hy⟩ := hne
      exact ⟨_, rest.pts_strictTransform_subset _ hy⟩
    have hVB : ¬ V.pts ⊆ B.pts := by
      intro hVB
      obtain ⟨y, hy⟩ := hne'
      rw [MonoidalTransformation.pts_strictTransform_eq_closure] at hy
      have : closure (t.f.base ⁻¹' V.pts \ t.exceptional.pts) = ∅ := by
        have h0 : t.f.base ⁻¹' V.pts \ t.exceptional.pts = ∅ := by
          ext z
          simp only [Set.mem_sdiff, Set.mem_preimage, Set.mem_empty_iff_false, iff_false, not_and,
            not_not]
          intro hz
          rw [MonoidalTransformation.pts_exceptional]
          exact hVB hz
        rw [h0, closure_empty]
      rw [this] at hy
      exact hy
    exact ih _ (Subscheme.isIrreducible_pts _ (t.strictTransform_isIrreducible V
      (Subscheme.isIrreducible_of_pts V hV) hVB)) hne

/-- The first exceptional divisor meets the strict transform of `W` in an irreducible set: the
exceptional divisor of the blow-up of the non-singular `W` along the irreducible center `B ⊆ W`
(a projective bundle over `B`) is irreducible.

Proved from `lem:IV.2-5-one-step-irreducible` (Compat/StrictTransformExceptional.lean). -/
theorem MonoidalTransformation.isIrreducible_pts_strictTransform_inter_exceptional [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}]
    [IsAlgebraicScheme X] {B : Subscheme X} (t : MonoidalTransformation X B)
    (_hX : X.IsNonsingular) (_hXirr : IrreducibleSpace X) {R : DatumI.Raw X} (_hR : R.IsDatum)
    (hB : R.IsPermissible B) (hdense : R.W.pts ⊆ closure (R.W.pts \ B.pts))
    (hresB : ∀ x ∈ B.pts, R.ResolvedAt x)
    (hne : ((Subscheme.strictTransform t R.W).pts ∩ t.exceptional.pts).Nonempty) :
    _root_.IsIrreducible ((Subscheme.strictTransform t R.W).pts ∩ t.exceptional.pts) := by
  rcases hB.1 with rfl | ⟨hns, hirr⟩
  · exfalso; obtain ⟨p, -, hp⟩ := hne
    rw [MonoidalTransformation.pts_exceptional] at hp; exact hp
  · exact t.isIrreducible_pts_strictTransform_inter_exceptional_of_isSimpleAt hns hirr
      hB.pts_subset_W (fun x hx => (hresB x hx).1) hne

/-- Irreducibility of `W' ∩ E_j'` for an exceptional divisor `E_j'` of the succession (p. 290: "We can
prove that `W' ∩ E_j'` for `α < j ≤ α'` are non-singular irreducible subschemes of `X'`"):
by induction on the succession, `W' ∩ E_j'` is the strict transform (under the later steps) of the
intersection of `W` with the exceptional divisor of the step in question
(`MonoidalSuccession.pts_inter_strictTransform_subset`), which is irreducible by the first
case (`MonoidalTransformation.isIrreducible_pts_strictTransform_inter_exceptional`); strict
transforms of irreducible sets are irreducible. -/
theorem MonoidalSuccession.isIrreducible_pts_inter_of_mem_exceptionalDivisors [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ}
    (s : MonoidalSuccession X Y) {R : DatumI.Raw X} {U Ũ : Set X} {F : Subscheme X}
    (H : StageHyp N n s R U Ũ F) {α : ℕ} (E : Fin α → Subscheme X)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) (hEunion : R.E = Subscheme.unionFam E)
    {D : Subscheme Y} (hD : D ∈ s.exceptionalDivisors)
    (hne : ((s.strictTransform R.W).pts ∩ D.pts).Nonempty) :
    _root_.IsIrreducible ((s.strictTransform R.W).pts ∩ D.pts) := by
  induction s generalizing α with
  | nil X => exact absurd hD (by simp [MonoidalSuccession.exceptionalDivisors])
  | cons B t rest ih =>
    have := H.good.1.1
    have hdense := DatumI.Raw.pts_subset_closure_diff_of_isPermissibleOpen H.openR H.perm.1
    obtain ⟨E₁, hE₁, hEq₁, hcs₁, hlast₁⟩ :=
      DatumI.Raw.exists_presentation_transform H.good.1.2.1 E hE R H.good.2.1 hEunion t H.perm.1.1
    rcases hD with rfl | hD'
    · -- the exceptional divisor of the first step
      have hresB : ∀ x ∈ B.pts, R.ResolvedAt x := fun x hx =>
        H.res x (H.sub (H.cent.1 hx)) (H.perm.1.2 hx).1
      set W₁ := Subscheme.strictTransform t R.W with hW₁
      have hid : (rest.strictTransform W₁).pts ∩ (rest.strictTransform t.exceptional).pts =
          (rest.strictTransform (W₁.inter t.exceptional)).pts := by
        apply Set.Subset.antisymm
        · rintro y ⟨hy1, hy2⟩
          have := rest.pts_inter_strictTransform_subset H.next E₁ hE₁ hEq₁ (Fin.last α)
            (y := y) hy1 (by rw [hlast₁]; exact hy2)
          rwa [hlast₁] at this
        · intro y hy
          refine ⟨rest.pts_strictTransform_mono (fun z hz =>
            (Subscheme.mem_pts_inter_iff.mp hz).1) hy, rest.pts_strictTransform_mono
            (fun z hz => (Subscheme.mem_pts_inter_iff.mp hz).2) hy⟩
      rw [show ((cons B t rest).strictTransform R.W) = rest.strictTransform W₁ from rfl, hid]
      rw [show ((cons B t rest).strictTransform R.W).pts ∩ (rest.strictTransform t.exceptional).pts =
        (rest.strictTransform W₁).pts ∩ (rest.strictTransform t.exceptional).pts from rfl,
        hid] at hne
      have hne₁ : (W₁.inter t.exceptional).pts.Nonempty := by
        obtain ⟨y, hy⟩ := hne
        exact ⟨_, rest.pts_strictTransform_subset _ hy⟩
      have hirr₁ : _root_.IsIrreducible (W₁.inter t.exceptional).pts := by
        have := t.isIrreducible_pts_strictTransform_inter_exceptional H.good.1.2.1 H.good.1.2.2.1
          H.good.2.1 H.perm.1.1 hdense hresB (by
            obtain ⟨y, hy⟩ := hne₁
            exact ⟨y, Subscheme.mem_pts_inter_iff.mp hy⟩)
        convert this using 1
        ext y; exact Subscheme.mem_pts_inter_iff
      exact rest.isIrreducible_pts_strictTransform _ hirr₁ hne
    · exact ih H.next E₁ hE₁ hEq₁ hD' hne

end PrepStageInduction

end PrepProposition

end

end Hironaka
