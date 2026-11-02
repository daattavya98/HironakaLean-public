/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch3.Basic
public import Hironaka.Compat.RegularQuotient
public import Hironaka.Compat.RegularGraded

/-!
# Compatibility layer: the maximal local extension of a regular local ring (Ch. III, p. 234)

Proof of Theorem 3, p. 234:

> In a fixed algebraic closure of the field of quotients of `R`, we shall take a maximal local
> extension `R'` of `R` such that the local homomorphism `R → R'` transforms a regular system of
> parameters of `R` into such a system of parameters of `R'` and induces a separable algebraic
> extension of the residue fields. The existence of such `R'` can be proved by means of Zorn's
> lemma and, if `R'` is such, then the residue field of `R'` does not admit any separable
> algebraic extension.

This file carries out that argument. Fix an algebraic closure `Ω` of the field of fractions of
`R`, and consider the subrings `A ⊆ Ω` containing (the image of) `R` such that `A` is a
noetherian local ring, `M_R A` is the maximal ideal of `A`, `A` has the same dimension as `R`,
and the residue field of `A` is separable algebraic over that of `R`.

* (F1) Each such `A` is regular, `R → A` maps a regular system of parameters onto one, and for
  `A ⊆ B` the extension is faithfully flat, so `IB ∩ A = I` (`IsCand.comap_map_incl`; flatness
  is `RingHom.MapsRSOP.flat` (Ch. III), a fact the paper asserts without proof on
  p. 207).
* (F2) The union of a chain of such subrings is again one (`IsChainUnion.isCand`): local,
  pure over the members, ideals extended from the members are closed (Krull), noetherian (via
  the associated graded ring, as in Lemma 6 of Ch. II), of dimension `dim R` (a regular system
  of parameters stays a regular sequence), and residually separable. Zorn's lemma gives a
  maximal one (`exists_maximal_isCand`).
* (F3) A maximal one has a separably closed residue field (`isSepClosed_of_maximal`): otherwise
  adjoin a root of a monic lift of a separable irreducible polynomial over its residue field
  (`isCand_adjoinRoot`).

The members of the family are encoded by `MaxLocExt.IsCand`, stated for any `R`-algebra; the
residue field condition is phrased elementwise (`isSeparable_of_sep`, `sep_of_isSeparable`).

The result is used in `PermissibleEffects.lean` (`exists_maximal_local_extension`) for the
reductions to the residually rational case in Theorems 3, 4 and 5 and Proposition 1.
-/

@[expose] public section

open IsLocalRing Polynomial

namespace Hironaka

universe u

/-! ### The family `𝒮` of p. 234

Throughout, `Ω` is an `R`-algebra with `R → Ω` injective (in the application, an algebraic
closure of the field of fractions of `R`), and the candidates for the maximal local extension
are the `R`-subalgebras `A ⊆ Ω`. For such `A` write `M_R A` (`extMax R A`) for the extension of the
maximal ideal of `R`. -/

namespace MaxLocExt

variable {R : Type u} [CommRing R] {Ω : Type u} [CommRing Ω] [Algebra R Ω]
  {A B : Subalgebra R Ω}

/-- The inclusion `A → B` of subalgebras, as a ring homomorphism. -/
abbrev incl (hAB : A ≤ B) : A →+* B := (Subalgebra.inclusion hAB).toRingHom

theorem incl_comp_algebraMap (hAB : A ≤ B) :
    (incl hAB).comp (algebraMap R A) = algebraMap R B := by
  ext r
  rfl

theorem incl_injective (hAB : A ≤ B) : Function.Injective (incl hAB) :=
  Subalgebra.inclusion_injective hAB

theorem algebraMap_injective (hinj : Function.Injective (algebraMap R Ω)) :
    Function.Injective (algebraMap R A) := by
  intro x y hxy
  apply hinj
  have := congrArg (fun a : A => (a : Ω)) hxy
  simpa using this

/-- `Finset.coe_image` with the decidability instance found by unification. -/
theorem coe_image_any {α β : Type*} {_ : DecidableEq β} (f : α → β) (s : Finset α) :
    ((s.image f : Finset β) : Set β) = f '' ↑s :=
  Finset.coe_image

theorem incl_comp_incl {C : Subalgebra R Ω} (hAB : A ≤ B) (hBC : B ≤ C) :
    (incl hBC).comp (incl hAB) = incl (hAB.trans hBC) := by
  ext r
  rfl

theorem map_map_incl {C : Subalgebra R Ω} (hAB : A ≤ B) (hBC : B ≤ C) (I : Ideal A) :
    (I.map (incl hAB)).map (incl hBC) = I.map (incl (hAB.trans hBC)) := by
  rw [Ideal.map_map, incl_comp_incl]

/-- Krull's intersection theorem for an ideal `J` of a noetherian local ring:
`⋂ₙ (J + Mⁿ) = J`. -/
theorem mem_of_forall_mem_sup_maximalIdeal_pow {S : Type*} [CommRing S] [IsNoetherianRing S]
    [IsLocalRing S] (J : Ideal S) (g : S) (hg : ∀ n : ℕ, g ∈ J ⊔ maximalIdeal S ^ n) : g ∈ J := by
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (I := maximalIdeal S) (M := S ⧸ J)
    (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  have hmem : (Submodule.Quotient.mk g : S ⧸ J) ∈
      (⨅ i : ℕ, maximalIdeal S ^ i • ⊤ : Submodule S (S ⧸ J)) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨j, hj, m, hm, rfl⟩ := Submodule.mem_sup.mp (hg i)
    rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero J).mpr hj, zero_add]
    have : (Submodule.Quotient.mk m : S ⧸ J) = m • Submodule.Quotient.mk 1 := by
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem_smul hm Submodule.mem_top
  rw [hK, Submodule.mem_bot] at hmem
  exact (Submodule.Quotient.mk_eq_zero J).mp hmem

section Local

variable [IsLocalRing R]

variable (R) in
/-- The ideal `M_R T` generated by the maximal ideal of `R` in an `R`-algebra `T` (for instance a
subalgebra of `Ω`). -/
abbrev extMax (T : Type*) [CommRing T] [Algebra R T] : Ideal T :=
  (maximalIdeal R).map (algebraMap R T)

variable (R) in
/-- The family `𝒮` of p. 234 (stated for any `R`-algebra `T`; the members of `𝒮` are the
subalgebras `A ⊆ Ω` with `IsCand R A`): `T` is a noetherian local ring with maximal ideal `M_R T`,
of the same dimension as `R`, whose residue field is separable algebraic over that of `R`.
Locality is phrased as "`M_R T ≠ T` and every element outside `M_R T` is a unit"
(`IsCand.isLocalRing`), and separability elementwise: every element of `T` is a root modulo
`M_R T` of a monic polynomial over `R` whose reduction modulo `M_R` is separable
(`IsCand.isSeparable`, `sep_of_isSeparable`). -/
structure IsCand (T : Type*) [CommRing T] [Algebra R T] : Prop where
  ne_top : extMax R T ≠ ⊤
  isUnit_of_notMem : ∀ a : T, a ∉ extMax R T → IsUnit a
  noetherian : IsNoetherianRing T
  dim : ringKrullDim T = ringKrullDim R
  sep : ∀ a : T, ∃ p : R[X], p.Monic ∧ (p.map (residue R)).Separable ∧ aeval a p ∈ extMax R T

theorem map_extMax_incl (hAB : A ≤ B) : (extMax R A).map (incl hAB) = extMax R B := by
  rw [Ideal.map_map, incl_comp_algebraMap]

section General

variable {T : Type*} [CommRing T] [Algebra R T]

/-- An `R`-algebra in which `M_R T ≠ T` and every element outside `M_R T` is a unit is local. -/
theorem isLocalRing_of_extMax (h₁ : extMax R T ≠ ⊤) (h₂ : ∀ a : T, a ∉ extMax R T → IsUnit a) :
    IsLocalRing T := by
  have hnt : Nontrivial T := by
    refine ⟨⟨0, 1, fun h01 => h₁ ?_⟩⟩
    rw [Ideal.eq_top_iff_one, ← h01]
    exact zero_mem _
  have key : ∀ a : T, a ∈ nonunits T ↔ a ∈ extMax R T := by
    intro a
    constructor
    · intro ha
      by_contra hn
      exact ha (h₂ a hn)
    · intro ha hu
      exact h₁ (Ideal.eq_top_of_isUnit_mem _ ha hu)
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [key] at ha hb ⊢
  exact add_mem ha hb

theorem maximalIdeal_eq_extMax [IsLocalRing T] (h₁ : extMax R T ≠ ⊤)
    (h₂ : ∀ a : T, a ∉ extMax R T → IsUnit a) : maximalIdeal T = extMax R T := by
  ext a
  rw [mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro ha
    by_contra hn
    exact ha (h₂ a hn)
  · intro ha hu
    exact h₁ (Ideal.eq_top_of_isUnit_mem _ ha hu)

/-- A member of `𝒮` is a local ring (with maximal ideal `M_R T`, `IsCand.maximalIdeal_eq`). -/
theorem IsCand.isLocalRing (h : IsCand R T) : IsLocalRing T :=
  isLocalRing_of_extMax h.ne_top h.isUnit_of_notMem

theorem IsCand.maximalIdeal_eq [IsLocalRing T] (h : IsCand R T) :
    maximalIdeal T = extMax R T :=
  maximalIdeal_eq_extMax h.ne_top h.isUnit_of_notMem

/-- (F1) `R → T` is a local homomorphism. -/
theorem IsCand.isLocalHom [IsLocalRing T] (h : IsCand R T) :
    IsLocalHom (algebraMap R T) := by
  refine ⟨fun r hr => ?_⟩
  by_contra hn
  have : algebraMap R T r ∈ maximalIdeal T := by
    rw [h.maximalIdeal_eq]
    exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal r).mpr hn)
  exact (mem_maximalIdeal _).mp this hr

end General

/-- (F1) For `A ∈ 𝒮`, the image of a regular system of parameters of `R` is one of `A`. -/
theorem IsCand.rsop_of_coe [IsLocalRing A] (h : IsCand R A)
    (hinj : Function.Injective (algebraMap R Ω)) {s : Finset R}
    (hs : IsRegularSystemOfParameters R s) (t : Finset A)
    (ht : (t : Set A) = algebraMap R A '' s) : IsRegularSystemOfParameters A t := by
  refine ⟨?_, ?_⟩
  · rw [ht, ← Ideal.map_span, hs.1, h.maximalIdeal_eq]
  · have hc : t.card = s.card := by
      rw [← Set.ncard_coe_finset, ht, Set.ncard_image_of_injective _ (algebraMap_injective hinj),
        Set.ncard_coe_finset]
    rw [h.dim, ← hs.2, hc]

/-- (F1) For `A ⊆ B` in `𝒮` the inclusion is local: `M_A = M_R A ⊆ M_R B = M_B`. -/
theorem IsCand.isLocalHom_incl [IsLocalRing A] [IsLocalRing B] (hA : IsCand R A) (hB : IsCand R B)
    (hAB : A ≤ B) : IsLocalHom (incl hAB) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hn
  have h1 : a ∈ extMax R A := hA.maximalIdeal_eq ▸ (mem_maximalIdeal a).mpr hn
  have h2 : incl hAB a ∈ extMax R B := by
    rw [← map_extMax_incl hAB]
    exact Ideal.mem_map_of_mem _ h1
  exact hB.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 ha)

open Classical in
/-- (F1) For `A ⊆ B` in `𝒮` the inclusion transforms a regular system of parameters of `A`
(the image of one of `R`) into one of `B`. -/
theorem IsCand.mapsRSOP_incl [IsLocalRing A] [IsLocalRing B] (hA : IsCand R A) (hB : IsCand R B)
    (hinj : Function.Injective (algebraMap R Ω)) {s : Finset R}
    (hs : IsRegularSystemOfParameters R s) (hAB : A ≤ B) :
    RingHom.MapsRSOP (incl hAB) := by
  refine ⟨s.image (algebraMap R A), hA.rsop_of_coe hinj hs _ (coe_image_any _ _),
    hB.rsop_of_coe hinj hs _ ?_, (incl_injective hAB).injOn⟩
  rw [coe_image_any, coe_image_any, Set.image_image]
  rfl

end Local

section Regular

variable [IsRegularLocalRing R]

theorem exists_rsop_base : ∃ s : Finset R, IsRegularSystemOfParameters R s := by
  obtain ⟨-, h⟩ := (isRegularLocalRing_iff_exists_rsop R).mp ‹_›
  exact h

/-- (F1) A member of `𝒮` is a regular local ring. -/
theorem IsCand.isRegularLocalRing (h : IsCand R A) (hinj : Function.Injective (algebraMap R Ω)) :
    IsRegularLocalRing A := by
  have := h.isLocalRing
  obtain ⟨s, hs⟩ := exists_rsop_base (R := R)
  classical
  exact (isRegularLocalRing_iff_exists_rsop A).mpr
    ⟨h.noetherian, _, h.rsop_of_coe hinj hs (s.image (algebraMap R A)) Finset.coe_image⟩

open Classical in
/-- (F1) `R → A` transforms a regular system of parameters of `R` into one of `A`. -/
theorem IsCand.mapsRSOP [IsLocalRing A] (h : IsCand R A)
    (hinj : Function.Injective (algebraMap R Ω)) : RingHom.MapsRSOP (algebraMap R A) := by
  obtain ⟨s, hs⟩ := exists_rsop_base (R := R)
  exact ⟨s, hs, h.rsop_of_coe hinj hs _ (coe_image_any _ _), (algebraMap_injective hinj).injOn⟩

/-- (F1) For `A ⊆ B` in `𝒮`, `B` is flat over `A` (`RingHom.MapsRSOP.flat`, proved in
Ch. III; asserted without proof by the paper on p. 207). -/
theorem IsCand.flat_incl (hA : IsCand R A) (hB : IsCand R B)
    (hinj : Function.Injective (algebraMap R Ω)) (hAB : A ≤ B) :
    letI := (incl hAB).toAlgebra
    Module.Flat A B := by
  have := hA.isRegularLocalRing hinj
  have := hB.isRegularLocalRing hinj
  have := hA.isLocalHom_incl hB hAB
  obtain ⟨s, hs⟩ := exists_rsop_base (R := R)
  exact RingHom.MapsRSOP.flat (hA.mapsRSOP_incl hB hinj hs hAB)

/-- (F1) purity: for `A ⊆ B` in `𝒮`, `IB ∩ A = I` (faithful flatness). -/
theorem IsCand.comap_map_incl (hA : IsCand R A) (hB : IsCand R B)
    (hinj : Function.Injective (algebraMap R Ω)) (hAB : A ≤ B) (I : Ideal A) :
    (I.map (incl hAB)).comap (incl hAB) = I := by
  let := (incl hAB).toAlgebra
  have := hA.flat_incl hB hinj hAB
  have := hA.isLocalRing
  have := hB.isLocalRing
  have : IsLocalHom (algebraMap A B) := hA.isLocalHom_incl hB hAB
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I

end Regular

/-! ### Unions of chains in `𝒮` -/

section Union

variable [IsRegularLocalRing R]

/-- `U` is the union of the directed family `c` of members of `𝒮`. -/
structure IsChainUnion (c : Set (Subalgebra R Ω)) (U : Subalgebra R Ω) : Prop where
  cand : ∀ A ∈ c, IsCand R A
  dir : DirectedOn (· ≤ ·) c
  le : ∀ A ∈ c, A ≤ U
  mem : ∀ x ∈ U, ∃ A ∈ c, x ∈ A

variable {c : Set (Subalgebra R Ω)} {U : Subalgebra R Ω}

theorem IsChainUnion.exists_ge (hc : IsChainUnion c U) (hA : A ∈ c) {x : Ω} (hx : x ∈ U) :
    ∃ B ∈ c, A ≤ B ∧ x ∈ B := by
  obtain ⟨C, hC, hxC⟩ := hc.mem x hx
  obtain ⟨B, hB, hAB, hCB⟩ := hc.dir A hA C hC
  exact ⟨B, hB, hAB, hCB hxC⟩

/-- Every element of `I U` (for `I` an ideal of a member `A` of the chain) already lies in
`I B` for some member `B ⊇ A` of the chain. -/
theorem IsChainUnion.exists_of_mem_map (hc : IsChainUnion c U) (hA : A ∈ c) (I : Ideal A)
    {x : U} (hx : x ∈ I.map (incl (hc.le A hA))) :
    ∃ B, ∃ hB : B ∈ c, ∃ hAB : A ≤ B, ∃ y ∈ I.map (incl hAB), incl (hc.le B hB) y = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨A, hA, le_rfl, incl le_rfl a, Ideal.mem_map_of_mem _ ha, rfl⟩
  | zero => exact ⟨A, hA, le_rfl, 0, zero_mem _, map_zero _⟩
  | add x₁ x₂ _ _ ih₁ ih₂ =>
    obtain ⟨B₁, hB₁, hAB₁, y₁, hy₁, rfl⟩ := ih₁
    obtain ⟨B₂, hB₂, hAB₂, y₂, hy₂, rfl⟩ := ih₂
    obtain ⟨B, hB, h₁, h₂⟩ := hc.dir B₁ hB₁ B₂ hB₂
    refine ⟨B, hB, hAB₁.trans h₁, incl h₁ y₁ + incl h₂ y₂, add_mem ?_ ?_, ?_⟩
    · rw [← map_map_incl hAB₁ h₁]
      exact Ideal.mem_map_of_mem _ hy₁
    · rw [show hAB₁.trans h₁ = hAB₂.trans h₂ from rfl, ← map_map_incl hAB₂ h₂]
      exact Ideal.mem_map_of_mem _ hy₂
    · rw [map_add]
      rfl
  | smul a x _ ih =>
    obtain ⟨B₁, hB₁, hAB₁, y, hy, rfl⟩ := ih
    obtain ⟨B, hB, h₁, haB⟩ := hc.exists_ge hB₁ a.2
    refine ⟨B, hB, hAB₁.trans h₁, ⟨a, haB⟩ * incl h₁ y, Ideal.mul_mem_left _ _ ?_, ?_⟩
    · rw [← map_map_incl hAB₁ h₁]
      exact Ideal.mem_map_of_mem _ hy
    · rw [map_mul, smul_eq_mul]
      rfl

/-- (F2) purity in the union: `IU ∩ A = I` for `A` in the chain. -/
theorem IsChainUnion.comap_map (hc : IsChainUnion c U)
    (hinj : Function.Injective (algebraMap R Ω)) (hA : A ∈ c) (I : Ideal A) :
    (I.map (incl (hc.le A hA))).comap (incl (hc.le A hA)) = I := by
  refine le_antisymm (fun x hx => ?_) Ideal.le_comap_map
  obtain ⟨B, hB, hAB, y, hy, hyx⟩ := hc.exists_of_mem_map hA I (Ideal.mem_comap.mp hx)
  have hy' : y = incl hAB x := incl_injective (hc.le B hB) hyx
  subst hy'
  rw [← (hc.cand A hA).comap_map_incl (hc.cand B hB) hinj hAB I]
  exact hy

theorem IsChainUnion.extMax_eq (hc : IsChainUnion c U) (hA : A ∈ c) :
    extMax R U = (extMax R A).map (incl (hc.le A hA)) :=
  (map_extMax_incl _).symm

theorem IsChainUnion.nonempty (hc : IsChainUnion c U) : c.Nonempty := by
  obtain ⟨A, hA, -⟩ := hc.mem 0 (zero_mem U)
  exact ⟨A, hA⟩

/-- (F2) `M_R U ≠ U`. -/
theorem IsChainUnion.extMax_ne_top (hc : IsChainUnion c U) : extMax R U ≠ ⊤ := by
  intro htop
  obtain ⟨A, hA⟩ := hc.nonempty
  have h1 : (1 : U) ∈ (extMax R A).map (incl (hc.le A hA)) := by
    rw [← hc.extMax_eq hA, htop]
    exact Submodule.mem_top
  obtain ⟨B, hB, hAB, y, hy, hy1⟩ := hc.exists_of_mem_map hA _ h1
  rw [map_extMax_incl] at hy
  have : y = 1 := incl_injective (hc.le B hB) (by rw [hy1, map_one])
  subst this
  exact (hc.cand B hB).ne_top ((Ideal.eq_top_iff_one _).mpr hy)

/-- (F2) every element of `U` outside `M_R U` is a unit. -/
theorem IsChainUnion.isUnit_of_notMem (hc : IsChainUnion c U) (x : U) (hx : x ∉ extMax R U) :
    IsUnit x := by
  obtain ⟨A, hA, hxA⟩ := hc.mem x x.2
  have hnot : (⟨x, hxA⟩ : A) ∉ extMax R A := by
    intro hmem
    apply hx
    rw [hc.extMax_eq hA]
    exact Ideal.mem_map_of_mem (incl (hc.le A hA)) hmem
  exact ((hc.cand A hA).isUnit_of_notMem _ hnot).map (incl (hc.le A hA))

/-- (F2) the union is local. -/
theorem IsChainUnion.isLocalRing (hc : IsChainUnion c U) : IsLocalRing U :=
  isLocalRing_of_extMax hc.extMax_ne_top hc.isUnit_of_notMem

/-- (F2) the maximal ideal of the union is `M_R U`. -/
theorem IsChainUnion.maximalIdeal_eq [IsLocalRing U] (hc : IsChainUnion c U) :
    maximalIdeal U = extMax R U :=
  maximalIdeal_eq_extMax hc.extMax_ne_top hc.isUnit_of_notMem

/-- (F2) closedness of ideals extended from the chain: if `g ∈ J U + (M_R U)ⁿ` for all `n`,
then `g ∈ J U` (Krull's intersection theorem in a member of the chain, and purity). -/
theorem IsChainUnion.mem_of_forall_mem_sup_pow (hc : IsChainUnion c U)
    (hinj : Function.Injective (algebraMap R Ω)) (hA : A ∈ c) (J : Ideal A) (g : U)
    (hg : ∀ n : ℕ, g ∈ J.map (incl (hc.le A hA)) ⊔ extMax R U ^ n) :
    g ∈ J.map (incl (hc.le A hA)) := by
  obtain ⟨B, hB, hAB, hgB⟩ := hc.exists_ge hA g.2
  have hBc := hc.cand B hB
  have := hBc.isLocalRing
  have := hBc.noetherian
  have hJ : J.map (incl (hc.le A hA)) = (J.map (incl hAB)).map (incl (hc.le B hB)) :=
    (map_map_incl hAB (hc.le B hB) J).symm
  have hg' : (⟨g, hgB⟩ : B) ∈ J.map (incl hAB) := by
    apply mem_of_forall_mem_sup_maximalIdeal_pow
    intro n
    rw [← hc.comap_map hinj hB (J.map (incl hAB) ⊔ maximalIdeal B ^ n), Ideal.mem_comap,
      Ideal.map_sup, Ideal.map_pow, hBc.maximalIdeal_eq, ← hc.extMax_eq hB, ← hJ]
    exact hg n
  rw [hJ]
  exact Ideal.mem_map_of_mem _ hg'

end Union

/-! ### The union of a chain is in `𝒮`: noetherian, dimension, residue field -/

section UnionCand

variable [IsRegularLocalRing R] {c : Set (Subalgebra R Ω)} {U : Subalgebra R Ω}

/-- Finitely many elements of the union lie in one member of the chain. -/
theorem IsChainUnion.exists_mem_finset (hc : IsChainUnion c U) (F : Finset U) :
    ∃ A ∈ c, ∀ x ∈ F, (x : Ω) ∈ A := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨A, hA⟩ := hc.nonempty
    exact ⟨A, hA, by simp⟩
  | insert x F _ ih =>
    obtain ⟨A, hA, hFA⟩ := ih
    obtain ⟨B, hB, hAB, hxB⟩ := hc.exists_ge hA x.2
    refine ⟨B, hB, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hxB
    · exact hAB (hFA y hy)

/-- If the maximal ideal of a local ring is generated by finitely many elements, its associated
graded ring is noetherian (a quotient of a polynomial ring over the residue field). -/
theorem isNoetherianRing_assocGraded_maximalIdeal {S : Type u} [CommRing S] [IsLocalRing S]
    {σ : Type*} [Finite σ] (x : σ → S) (hx : Ideal.span (Set.range x) = maximalIdeal S) :
    IsNoetherianRing (AssocGraded (maximalIdeal S)) := by
  have hx1 : ∀ i, x i ∈ maximalIdeal S ^ 1 := fun i => by
    rw [pow_one, ← hx]
    exact Ideal.subset_span ⟨i, rfl⟩
  let _ : Field (S ⧸ maximalIdeal S) := Ideal.Quotient.field _
  exact isNoetherianRing_of_surjective _ _ _ (aeval_mk_surjective (maximalIdeal S) x hx1 hx)

/-- The image of a regular system of parameters of `R` generates the maximal ideal of `U`. -/
theorem IsChainUnion.span_range_eq [IsLocalRing U] (hc : IsChainUnion c U) {s : Finset R}
    (hs : IsRegularSystemOfParameters R s) :
    Ideal.span (Set.range fun i : s => algebraMap R U i.1) = maximalIdeal U := by
  rw [hc.maximalIdeal_eq, extMax, ← hs.1, Ideal.map_span]
  congr 1
  ext y
  simp

/-- (F2) the union is noetherian: the initial forms of an ideal `J` are generated by those of
finitely many `f₁, …, f_r ∈ J` (`gr(U)` is noetherian); then `J ⊆ (f) + M_Uⁿ` for all `n`, and
`(f)` is closed (`IsChainUnion.mem_of_forall_mem_sup_pow`). -/
theorem IsChainUnion.isNoetherianRing (hc : IsChainUnion c U)
    (hinj : Function.Injective (algebraMap R Ω)) : IsNoetherianRing U := by
  classical
  have := hc.isLocalRing
  obtain ⟨s, hs⟩ := exists_rsop_base (R := R)
  have hgr := isNoetherianRing_assocGraded_maximalIdeal _ (hc.span_range_eq hs)
  refine (isNoetherianRing_iff_ideal_fg U).mpr fun J => ?_
  set M := maximalIdeal U with hMdef
  -- finitely many `f ∈ J` whose initial forms generate `gr_M(J, U)`
  have hfg : (grIdeal M J).FG := IsNoetherian.noetherian _
  obtain ⟨T, hTsub, hTspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  obtain ⟨F, hFJ, rfl⟩ := Finset.subset_set_image_iff.mp hTsub
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀ : Ideal U, J₀ = Ideal.span (F : Set U) := ⟨_, rfl⟩
  have hJ₀J : J₀ ≤ J := hJ₀ ▸ Ideal.span_le.mpr hFJ
  have hgr' : grIdeal M J ≤ grIdeal M J₀ := by
    show Submodule.span _ _ ≤ _
    rw [hTspan, Submodule.span_le]
    intro φ hφ
    rw [Finset.coe_image] at hφ
    obtain ⟨f, hf, rfl⟩ := hφ
    exact Ideal.subset_span (Set.mem_image_of_mem _ (hJ₀ ▸ Ideal.subset_span hf))
  have step : ∀ (n : ℕ) (r : U), r ∈ J → r ∈ M ^ n → ∃ a ∈ J₀, r - a ∈ M ^ (n + 1) := by
    intro n r hrJ hr
    obtain ⟨a, haJ₀, ha, hmk⟩ := grIdeal_le_bound M J₀ (hgr' (mk_mem_grIdeal M hrJ hr)) n
    rw [grProj_mk_same, Submodule.Quotient.eq] at hmk
    have har : a - r ∈ M ^ (n + 1) := hmk
    refine ⟨a, haJ₀, ?_⟩
    rw [← neg_sub]
    exact neg_mem har
  have approx : ∀ n : ℕ, ∀ g ∈ J, ∃ g₀ ∈ J₀, g - g₀ ∈ M ^ n := by
    intro n
    induction n with
    | zero => exact fun g _ => ⟨0, zero_mem _, by simp⟩
    | succ n ih =>
      intro g hg
      obtain ⟨g₀, hg₀, hgn⟩ := ih g hg
      obtain ⟨a, ha, hga⟩ := step n (g - g₀) (sub_mem hg (hJ₀J hg₀)) hgn
      exact ⟨g₀ + a, add_mem hg₀ ha, by rwa [sub_add_eq_sub_sub]⟩
  -- `(f)` is extended from a member `A` of the chain containing `F`
  obtain ⟨A, hA, hFA⟩ := hc.exists_mem_finset F
  have hJ₀A : J₀ = (Ideal.span {a : A | incl (hc.le A hA) a ∈ F}).map (incl (hc.le A hA)) := by
    rw [hJ₀, Ideal.map_span]
    congr 1
    ext y
    constructor
    · intro hy
      exact ⟨⟨y, hFA y hy⟩, hy, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  refine ⟨F, le_antisymm (Ideal.span_le.mpr hFJ) fun g hg => ?_⟩
  rw [← hJ₀, hJ₀A]
  apply hc.mem_of_forall_mem_sup_pow hinj hA
  intro n
  obtain ⟨g₀, hg₀, hgn⟩ := approx n g hg
  rw [← hJ₀A, ← hc.maximalIdeal_eq]
  exact Submodule.mem_sup.mpr ⟨g₀, hg₀, g - g₀, hgn, add_sub_cancel _ _⟩

/-- (F2) the dimension of the union is `dim R`: the image of a regular system of parameters
of `R` is a regular sequence in `U` (it is one in every member of the chain, and `U` is pure
over the members) generating the maximal ideal. -/
theorem IsChainUnion.ringKrullDim_eq (hc : IsChainUnion c U)
    (hinj : Function.Injective (algebraMap R Ω)) [IsLocalRing U] [IsNoetherianRing U] :
    ringKrullDim U = ringKrullDim R := by
  classical
  obtain ⟨s, hs⟩ := exists_rsop_base (R := R)
  set z : Fin s.card → R := fun i => (s.equivFin.symm i : R) with hz
  have hzinj : Function.Injective z := Subtype.val_injective.comp s.equivFin.symm.injective
  set x : Fin s.card → U := fun i => algebraMap R U (z i) with hx
  -- weak regularity of `x` in `U`
  have hwreg : RingTheory.Sequence.IsWeaklyRegular U (List.ofFn x) := by
    rw [isWeaklyRegular_ofFn_iff]
    intro i a ha
    obtain ⟨B, hB, haB⟩ := hc.mem a a.2
    have hBc := hc.cand B hB
    have := hBc.isRegularLocalRing hinj
    set xB : Fin s.card → B := fun i => algebraMap R B (z i) with hxB
    have hrsB := hBc.rsop_of_coe hinj hs (s.image (algebraMap R B)) Finset.coe_image
    have hcard : (s.image (algebraMap R B)).card = (maximalIdeal B).spanFinrank := by
      have h1 := hrsB.2
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := B)] at h1
      exact_mod_cast h1
    have hregB := isRegular_ofFn_of_minimal hrsB.1 hcard
      ((algebraMap_injective hinj).comp hzinj) (fun i => Finset.mem_image_of_mem _ (by simp [z]))
    have hwB := (isWeaklyRegular_ofFn_iff xB).mp hregB.1
    have hmap : ∀ T : Set (Fin s.card), Ideal.span (x '' T) =
        (Ideal.span (xB '' T)).map (incl (hc.le B hB)) := by
      intro T
      rw [Ideal.map_span, Set.image_image]
      rfl
    rw [hmap] at ha ⊢
    have ha' : xB i * ⟨a, haB⟩ ∈ Ideal.span (xB '' {j | j < i}) := by
      rw [← hc.comap_map hinj hB (Ideal.span (xB '' {j | j < i})), Ideal.mem_comap, map_mul]
      exact ha
    exact Ideal.mem_map_of_mem _ (hwB i _ ha')
  have hmem : ∀ r ∈ List.ofFn x, r ∈ maximalIdeal U := by
    intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    rw [← hc.span_range_eq hs]
    exact Ideal.subset_span ⟨⟨z i, by simp [z]⟩, rfl⟩
  have hreg := (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr hwreg
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hreg
  have hof : Ideal.ofList (List.ofFn x) = maximalIdeal U := by
    rw [← hc.span_range_eq hs]
    show Ideal.span {r | r ∈ List.ofFn x} = _
    congr 1
    ext y
    rw [Set.mem_ofPred_eq, List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨z i, by simp [z]⟩, rfl⟩
    · rintro ⟨⟨r, hr⟩, rfl⟩
      exact ⟨s.equivFin ⟨r, hr⟩, by simp [x, z]⟩
  rw [hof, List.length_ofFn] at hdim
  have h0 : ringKrullDim (U ⧸ maximalIdeal U) = 0 := by
    let _ := Ideal.Quotient.field (maximalIdeal U)
    exact ringKrullDim_eq_zero_of_field _
  rw [h0, zero_add] at hdim
  rw [← hdim, hs.2]

/-- (F2) the residue field of the union is separable algebraic over that of `R`. -/
theorem IsChainUnion.sep (hc : IsChainUnion c U) (u : U) :
    ∃ p : R[X], p.Monic ∧ (p.map (residue R)).Separable ∧ aeval u p ∈ extMax R U := by
  obtain ⟨A, hA, huA⟩ := hc.mem u u.2
  obtain ⟨p, hpm, hps, hp⟩ := (hc.cand A hA).sep ⟨u, huA⟩
  refine ⟨p, hpm, hps, ?_⟩
  rw [hc.extMax_eq hA]
  have h1 : Subalgebra.inclusion (hc.le A hA) ⟨u, huA⟩ = u := rfl
  rw [← h1, Polynomial.aeval_algHom_apply]
  exact Ideal.mem_map_of_mem (incl (hc.le A hA)) hp

/-- (F2) the union of a chain in `𝒮` is in `𝒮`. -/
theorem IsChainUnion.isCand (hc : IsChainUnion c U)
    (hinj : Function.Injective (algebraMap R Ω)) : IsCand R U := by
  have := hc.isLocalRing
  have := hc.isNoetherianRing hinj
  exact ⟨hc.extMax_ne_top, hc.isUnit_of_notMem, this, hc.ringKrullDim_eq hinj, hc.sep⟩

/-- The image of `R` itself is in `𝒮`. -/
theorem isCand_bot (hinj : Function.Injective (algebraMap R Ω)) :
    IsCand R (⊥ : Subalgebra R Ω) := by
  set φ := algebraMap R (⊥ : Subalgebra R Ω)
  have hφi : Function.Injective φ := algebraMap_injective hinj
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨r, rfl⟩ := Algebra.mem_bot.mp hy
    exact ⟨r, rfl⟩
  have hmem : ∀ r : R, φ r ∈ extMax R (⊥ : Subalgebra R Ω) ↔ r ∈ maximalIdeal R := by
    intro r
    refine ⟨fun h => ?_, fun h => Ideal.mem_map_of_mem _ h⟩
    obtain ⟨r', hr', hrr'⟩ := (Ideal.mem_map_iff_of_surjective φ hφs).mp h
    rwa [← hφi hrr']
  refine ⟨fun htop => ?_, fun a ha => ?_, isNoetherianRing_of_surjective R _ φ hφs, ?_, fun a => ?_⟩
  · have h1 : φ 1 ∈ extMax R (⊥ : Subalgebra R Ω) := by
      rw [htop]
      exact Submodule.mem_top
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr ((hmem 1).mp h1))
  · obtain ⟨r, rfl⟩ := hφs a
    rw [hmem] at ha
    exact (IsLocalRing.notMem_maximalIdeal.mp ha).map φ
  · exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective φ ⟨hφi, hφs⟩)).symm
  · obtain ⟨r, rfl⟩ := hφs a
    refine ⟨X - C r, monic_X_sub_C r, ?_, ?_⟩
    · rw [Polynomial.map_sub, map_X, map_C]
      exact separable_X_sub_C
    · simp only [map_sub, aeval_X, aeval_C]
      show φ r - φ r ∈ _
      rw [sub_self]
      exact zero_mem _

/-- Zorn's lemma: `𝒮` has a maximal member. -/
theorem exists_maximal_isCand (hinj : Function.Injective (algebraMap R Ω)) :
    ∃ A : Subalgebra R Ω, Maximal (fun B : Subalgebra R Ω => IsCand R B) A := by
  obtain ⟨A, -, hA⟩ := zorn_le_nonempty₀ {A : Subalgebra R Ω | IsCand R A} (fun c hcs hchain y hy => by
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    have hdir : Directed (· ≤ ·) (fun A : c => (A : Subalgebra R Ω)) :=
      hchain.directedOn.directed_val
    have hcU : IsChainUnion c (⨆ A : c, (A : Subalgebra R Ω)) :=
      { cand := fun A hA => hcs hA
        dir := hchain.directedOn
        le := fun A hA => le_iSup (fun A : c => (A : Subalgebra R Ω)) ⟨A, hA⟩
        mem := fun x hx => by
          rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hdir, Set.mem_iUnion] at hx
          obtain ⟨⟨A, hA⟩, hxA⟩ := hx
          exact ⟨A, hA, hxA⟩ }
    exact ⟨_, hcU.isCand hinj, hcU.le⟩) ⊥ (isCand_bot hinj)
  exact ⟨A, hA⟩

end UnionCand

/-! ### Residue fields: elementwise versus field-level separability -/

section Residue

variable [IsLocalRing R] {T : Type*} [CommRing T] [IsLocalRing T] [Algebra R T]

/-- If every element of `T` is a root modulo `M_T` of a monic polynomial over `R` with separable
reduction, the residue field of `T` is separable over that of `R` (for any algebra structure
between the residue fields compatible with `R → T`). -/
theorem isSeparable_of_sep [Algebra (ResidueField R) (ResidueField T)]
    (halg : ∀ r : R, algebraMap (ResidueField R) (ResidueField T) (residue R r) =
      residue T (algebraMap R T r))
    (hsep : ∀ a : T, ∃ p : R[X], p.Monic ∧ (p.map (residue R)).Separable ∧
      aeval a p ∈ maximalIdeal T) :
    Algebra.IsSeparable (ResidueField R) (ResidueField T) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨a, rfl⟩ := residue_surjective y
  obtain ⟨p, -, hps, hp⟩ := hsep a
  have hcomp : (algebraMap (ResidueField R) (ResidueField T)).comp (residue R) =
      (residue T).comp (algebraMap R T) := RingHom.ext halg
  have hroot : aeval (residue T a) (p.map (residue R)) = 0 := by
    rw [aeval_def, eval₂_map, hcomp, ← hom_eval₂, ← aeval_def, residue_eq_zero_iff]
    exact hp
  exact hps.of_dvd (minpoly.dvd _ _ hroot)

/-- Conversely, separability of the residue field extension gives, for every `a ∈ T`, a monic
`p ∈ R[X]` with separable reduction and `p(a) ∈ M_T` (a monic lift of the minimal polynomial of
the residue class of `a`). -/
theorem sep_of_isSeparable [Algebra (ResidueField R) (ResidueField T)]
    (halg : ∀ r : R, algebraMap (ResidueField R) (ResidueField T) (residue R r) =
      residue T (algebraMap R T r))
    [Algebra.IsSeparable (ResidueField R) (ResidueField T)] (a : T) :
    ∃ p : R[X], p.Monic ∧ (p.map (residue R)).Separable ∧ aeval a p ∈ maximalIdeal T := by
  have hy : IsSeparable (ResidueField R) (residue T a) :=
    Algebra.IsSeparable.isSeparable _ (residue T a)
  obtain ⟨p, hpmap, -, hpm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective residue_surjective _) (minpoly.monic hy.isIntegral)
  refine ⟨p, hpm, by rw [hpmap]; exact hy, ?_⟩
  have hcomp : (algebraMap (ResidueField R) (ResidueField T)).comp (residue R) =
      (residue T).comp (algebraMap R T) := RingHom.ext halg
  rw [← residue_eq_zero_iff, aeval_def, hom_eval₂, ← hcomp, ← eval₂_map, ← aeval_def, hpmap,
    minpoly.aeval]

end Residue

/-! ### Transport along isomorphisms, and the regularity of members of `𝒮` -/

section Transport

variable [IsLocalRing R] {T T' : Type*} [CommRing T] [CommRing T'] [Algebra R T] [Algebra R T']

theorem IsCand.of_algEquiv (h : IsCand R T) (e : T ≃ₐ[R] T') : IsCand R T' := by
  have hmap : extMax R T' = (extMax R T).map (e : T →+* T') := by
    rw [extMax, extMax, Ideal.map_map]
    congr 1
    ext r
    simp
  have hmem : ∀ t : T, e t ∈ extMax R T' ↔ t ∈ extMax R T := by
    intro t
    constructor
    · intro ht
      have h1 := Ideal.mem_map_of_mem (e.symm : T' →+* T) ht
      have h2 : (e.symm : T' →+* T).comp (algebraMap R T') = algebraMap R T := by
        ext r
        simp
      rw [extMax, Ideal.map_map, h2] at h1
      simpa using h1
    · intro ht
      rw [hmap]
      exact Ideal.mem_map_of_mem _ ht
  have := h.noetherian
  refine ⟨fun htop => h.ne_top ?_, fun a ha => ?_,
    isNoetherianRing_of_surjective T T' (e : T →+* T') e.surjective, ?_, fun a => ?_⟩
  · rw [Ideal.eq_top_iff_one, ← hmem, map_one, htop]
    exact Submodule.mem_top
  · obtain ⟨t, rfl⟩ := e.surjective a
    rw [hmem] at ha
    exact (h.isUnit_of_notMem t ha).map e
  · rw [← h.dim]
    exact (ringKrullDim_eq_of_ringEquiv (e : T ≃+* T')).symm
  · obtain ⟨t, rfl⟩ := e.surjective a
    obtain ⟨p, hpm, hps, hp⟩ := h.sep t
    refine ⟨p, hpm, hps, ?_⟩
    rw [show aeval (e t) p = e (aeval t p) from Polynomial.aeval_algHom_apply e.toAlgHom t p,
      hmem]
    exact hp

/-- A member of `𝒮` is regular: `M_T = M_R T` is generated by `dim R = dim T` elements. -/
theorem IsCand.isRegularLocalRing_of_isRegularLocalRing {R : Type u} [CommRing R] [IsRegularLocalRing R]
    {T : Type*} [CommRing T] [Algebra R T] [IsLocalRing T] (h : IsCand R T) :
    IsRegularLocalRing T := by
  classical
  have := h.noetherian
  obtain ⟨s, hs⟩ := exists_rsop_base (R := R)
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  have hspan : maximalIdeal T = Ideal.span ↑(s.image (algebraMap R T)) := by
    rw [h.maximalIdeal_eq, extMax, ← hs.1, Ideal.map_span, Finset.coe_image]
  rw [hspan, h.dim, ← hs.2]
  have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := T)
    (s.image (algebraMap R T)).finite_toSet
  rw [Set.ncard_coe_finset] at hle
  exact_mod_cast hle.trans Finset.card_image_le

end Transport

/-! ### Adjoining a root of a monic lift of a separable irreducible polynomial (F3) -/

section AdjoinRoot

variable {D : Type*} [CommRing D] [IsLocalRing D] {f : D[X]}

theorem adjoinRoot_isMaximal_map (hirr : Irreducible (f.map (residue D))) :
    ((maximalIdeal D).map (algebraMap D (AdjoinRoot f))).IsMaximal := by
  let e := AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal D) f
  have hmax : (Ideal.span {f.map (residue D)} : Ideal (ResidueField D)[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hirr
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient] at hmax ⊢
  exact MulEquiv.isField hmax e.toMulEquiv

/-- `D[t]/(f)` is local with maximal ideal `M_D D[t]/(f)` when `f` is monic with irreducible
reduction: its quotient by `M_D` is `k[t]/(f̄)`, a field, and every maximal ideal lies over `M_D`
(`D[t]/(f)` is finite over `D`). -/
theorem adjoinRoot_isLocalRing (hf : f.Monic) (hirr : Irreducible (f.map (residue D))) :
    IsLocalRing (AdjoinRoot f) := by
  have : Module.Finite D (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  have hN := adjoinRoot_isMaximal_map hirr
  refine IsLocalRing.of_unique_max_ideal ⟨_, hN, fun Q hQ => ?_⟩
  have h1 : (Q.under D).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q
  have h2 : Q.under D = maximalIdeal D := IsLocalRing.eq_maximalIdeal h1
  have h3 : (maximalIdeal D).map (algebraMap D (AdjoinRoot f)) ≤ Q := by
    rw [← h2]
    exact Ideal.map_comap_le
  exact (hN.eq_of_le hQ.ne_top h3).symm

theorem adjoinRoot_maximalIdeal [IsLocalRing (AdjoinRoot f)]
    (hirr : Irreducible (f.map (residue D))) :
    maximalIdeal (AdjoinRoot f) = (maximalIdeal D).map (algebraMap D (AdjoinRoot f)) :=
  (IsLocalRing.eq_maximalIdeal (adjoinRoot_isMaximal_map hirr)).symm

theorem isLocalHom_algebraMap_of_map_le {T : Type*} [CommRing T] [IsLocalRing T] [Algebra D T]
    (h : (maximalIdeal D).map (algebraMap D T) ≤ maximalIdeal T) :
    IsLocalHom (algebraMap D T) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hn
  exact (mem_maximalIdeal _).mp (h (Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).mpr hn))) ha

theorem residue_aeval {T : Type*} [CommRing T] [IsLocalRing T] [Algebra D T]
    [IsLocalHom (algebraMap D T)] (x : T) (q : D[X]) :
    residue T (aeval x q) = aeval (residue T x) (q.map (residue D)) := by
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
  congr 1

/-- The residue field of `D[t]/(f)` is generated over that of `D` by the class of `t`, a root of
the separable polynomial `f̄`; hence it is separable. -/
theorem isSeparable_residue_adjoinRoot [IsLocalRing (AdjoinRoot f)]
    [IsLocalHom (algebraMap D (AdjoinRoot f))] (hsep : (f.map (residue D)).Separable) :
    Algebra.IsSeparable (ResidueField D) (ResidueField (AdjoinRoot f)) := by
  set θ := residue (AdjoinRoot f) (AdjoinRoot.root f) with hθdef
  have hroot : aeval θ (f.map (residue D)) = 0 := by
    rw [hθdef, ← residue_aeval, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  have hθ : θ ∈ separableClosure (ResidueField D) (ResidueField (AdjoinRoot f)) :=
    mem_separableClosure_iff.mpr (hsep.of_dvd (minpoly.dvd _ _ hroot))
  refine ⟨fun y => ?_⟩
  obtain ⟨c, rfl⟩ := residue_surjective y
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective c
  rw [← AdjoinRoot.aeval_eq, residue_aeval]
  refine mem_separableClosure_iff.mp ?_
  have h2 : aeval θ (q.map (residue D)) =
      ((aeval (⟨θ, hθ⟩ : separableClosure _ _) (q.map (residue D)) :
        separableClosure (ResidueField D) (ResidueField (AdjoinRoot f))) :
        ResidueField (AdjoinRoot f)) :=
    Polynomial.aeval_algHom_apply
      (separableClosure (ResidueField D) (ResidueField (AdjoinRoot f))).val ⟨θ, hθ⟩
      (q.map (residue D))
  rw [h2]
  exact SetLike.coe_mem _

/-- Krull dimension of a noetherian local ring whose maximal ideal is generated by a regular
sequence: the length of the sequence. -/
theorem ringKrullDim_eq_length_of_isRegular {T : Type*} [CommRing T] [IsLocalRing T]
    [IsNoetherianRing T] (l : List T) (hreg : RingTheory.Sequence.IsRegular T l)
    (hl : Ideal.ofList l = maximalIdeal T) : ringKrullDim T = l.length := by
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hreg
  have h0 : ringKrullDim (T ⧸ maximalIdeal T) = 0 := by
    let _ := Ideal.Quotient.field (maximalIdeal T)
    exact ringKrullDim_eq_zero_of_field _
  rw [hl, h0, zero_add] at hdim
  exact hdim.symm

end AdjoinRoot

section AdjoinRootCand

variable [IsRegularLocalRing R]

/-- (F3) For `D ∈ 𝒮` and `f ∈ D[t]` monic whose reduction `f̄` is irreducible and separable,
`D[t]/(f)` is again in `𝒮`: it is local with maximal ideal `M_R D[t]/(f)` and residue field
`k_D[t]/(f̄)`, noetherian, free (hence faithfully flat) over `D` so that a regular system of
parameters of `D` stays a regular sequence generating the maximal ideal (`dim = dim D`), and its
residue field is separable over `k_D`, hence over `k`. -/
theorem isCand_adjoinRoot {D : Type u} [CommRing D] [Algebra R D] [IsLocalRing D]
    (hD : IsCand R D) {f : D[X]} (hf : f.Monic) (hirr : Irreducible (f.map (residue D)))
    (hsep : (f.map (residue D)).Separable) : IsCand R (AdjoinRoot f) := by
  classical
  have := hD.noetherian
  have := hD.isRegularLocalRing_of_isRegularLocalRing
  have : IsLocalRing (AdjoinRoot f) := adjoinRoot_isLocalRing hf hirr
  have hmaxC := adjoinRoot_maximalIdeal hirr
  have hext : extMax R (AdjoinRoot f) = maximalIdeal (AdjoinRoot f) := by
    rw [hmaxC, hD.maximalIdeal_eq, extMax, extMax, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  have : IsLocalHom (algebraMap D (AdjoinRoot f)) := isLocalHom_algebraMap_of_map_le hmaxC.ge
  have : IsLocalHom (algebraMap R D) := hD.isLocalHom
  have : IsLocalHom (algebraMap R (AdjoinRoot f)) := isLocalHom_algebraMap_of_map_le hext.le
  have hnoeth : IsNoetherianRing (AdjoinRoot f) :=
    isNoetherianRing_of_surjective _ _ (AdjoinRoot.mk f) AdjoinRoot.mk_surjective
  refine ⟨?_, ?_, hnoeth, ?_, ?_⟩
  · rw [hext]
    exact (maximalIdeal.isMaximal _).ne_top
  · intro a ha
    rw [hext] at ha
    exact IsLocalRing.notMem_maximalIdeal.mp ha
  · -- a regular system of parameters of `D` is a regular sequence in `D[t]/(f)`
    obtain ⟨t, ht⟩ := exists_rsop_base (R := D)
    set z : Fin t.card → D := fun i => (t.equivFin.symm i : D) with hz
    have hzinj : Function.Injective z := Subtype.val_injective.comp t.equivFin.symm.injective
    have hcard : t.card = (maximalIdeal D).spanFinrank := by
      have h1 := ht.2
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := D)] at h1
      exact_mod_cast h1
    have hregD := isRegular_ofFn_of_minimal ht.1 hcard hzinj (fun i => (t.equivFin.symm i).2)
    have : Module.Free D (AdjoinRoot f) := .of_basis (AdjoinRoot.powerBasis' hf).basis
    have : Module.FaithfullyFlat D (AdjoinRoot f) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    have hregC := hregD.of_faithfullyFlat (S := AdjoinRoot f)
    have hofD : Ideal.ofList (List.ofFn z) = maximalIdeal D := by
      rw [← ht.1]
      show Ideal.span {r | r ∈ List.ofFn z} = Ideal.span (t : Set D)
      congr 1
      ext y
      rw [Set.mem_ofPred_eq, List.mem_ofFn]
      constructor
      · rintro ⟨i, rfl⟩
        exact (t.equivFin.symm i).2
      · intro hy
        exact ⟨t.equivFin ⟨y, hy⟩, by simp [z]⟩
    have hof : Ideal.ofList ((List.ofFn z).map (algebraMap D (AdjoinRoot f))) =
        maximalIdeal (AdjoinRoot f) := by
      rw [← Ideal.map_ofList, hofD, hmaxC]
    rw [ringKrullDim_eq_length_of_isRegular _ hregC hof, List.length_map, List.length_ofFn,
      ht.2, hD.dim]
  · -- the residue field is separable over `k_D`, which is separable over `k`
    have : Algebra.IsSeparable (ResidueField R) (ResidueField D) :=
      isSeparable_of_sep (fun r => rfl) (fun a => by rw [hD.maximalIdeal_eq]; exact hD.sep a)
    have : Algebra.IsSeparable (ResidueField D) (ResidueField (AdjoinRoot f)) :=
      isSeparable_residue_adjoinRoot hsep
    have : Algebra.IsSeparable (ResidueField R) (ResidueField (AdjoinRoot f)) :=
      Algebra.IsSeparable.trans (ResidueField R) (ResidueField D) _
    intro a
    rw [hext]
    exact sep_of_isSeparable (fun r => rfl) a

/-- (F3) A maximal member `A` of `𝒮` (inside an algebraically closed field `K ⊇ R`) has a
separably closed residue field: otherwise let `f̄` be a separable irreducible monic polynomial
over `k_A` without root, `f` a monic lift, and `θ ∈ K` a root of `f`; then `A[t]/(f)` is in `𝒮`
(`isCand_adjoinRoot`), it is a regular local ring, hence a domain, integral over `A`, so its map
to `K` (`t ↦ θ`), whose kernel lies over `0`, is injective; its image `A[θ]` is in `𝒮` and
contains `A`, so `θ ∈ A` by maximality, and `θ` mod `M_A` would be a root of `f̄`. -/
theorem isSepClosed_of_maximal {K : Type u} [Field K] [IsAlgClosed K] [Algebra R K]
    {A : Subalgebra R K} (hA : Maximal (fun B : Subalgebra R K => IsCand R B) A)
    [IsLocalRing A] : IsSepClosed (ResidueField A) := by
  have hAc : IsCand R A := hA.prop
  refine IsSepClosed.of_exists_root _ fun p hpm hpirr hpsep => ?_
  by_contra hno
  push Not at hno
  -- a monic lift `f` of `p`, and a root `θ ∈ K` of `f`
  obtain ⟨f, hfmap, hfdeg, hfm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective residue_surjective p) hpm
  set φ : A →+* K := (A.val : A →+* K) with hφ
  have hdeg : (f.map φ).degree ≠ 0 := by
    rw [hfm.degree_map, hfdeg]
    exact (Polynomial.degree_pos_of_irreducible hpirr).ne'
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_root _ hdeg
  have hθ' : f.eval₂ φ θ = 0 := by rwa [IsRoot, eval_map] at hθ
  have hirr : Irreducible (f.map (residue A)) := by rw [hfmap]; exact hpirr
  have hsep : (f.map (residue A)).Separable := by rw [hfmap]; exact hpsep
  -- `C = A[t]/(f)` is in `𝒮`, regular, a domain, finite over `A`
  have hC := isCand_adjoinRoot hAc hfm hirr hsep
  have : IsLocalRing (AdjoinRoot f) := adjoinRoot_isLocalRing hfm hirr
  have : IsRegularLocalRing (AdjoinRoot f) := hC.isRegularLocalRing_of_isRegularLocalRing
  have : IsDomain (AdjoinRoot f) := isDomain_of_isRegularLocalRing _
  have : Module.Finite A (AdjoinRoot f) := (AdjoinRoot.powerBasis' hfm).finite
  -- the map `C → K`, `t ↦ θ`, is injective
  set ψ : AdjoinRoot f →ₐ[R] K := AdjoinRoot.liftAlgHom f A.val θ hθ' with hψ
  have hker : (RingHom.ker ψ).under A = ⊥ := by
    refine eq_bot_iff.mpr fun a ha => ?_
    rw [Ideal.under, Ideal.mem_comap, RingHom.mem_ker, AdjoinRoot.algebraMap_eq, hψ,
      AdjoinRoot.liftAlgHom_of] at ha
    exact (Ideal.mem_bot).mpr (Subtype.val_injective ha)
  have hψinj : Function.Injective ψ :=
    (RingHom.injective_iff_ker_eq_bot _).mpr (Ideal.eq_bot_of_under_eq_bot hker)
  -- its image `B = A[θ]` is in `𝒮` and contains `A`, hence equals `A`
  have hBc : IsCand R ψ.range := hC.of_algEquiv (AlgEquiv.ofInjective ψ hψinj)
  have hAB : A ≤ ψ.range := fun x hx =>
    (AlgHom.mem_range _).mpr ⟨AdjoinRoot.of f ⟨x, hx⟩, by rw [hψ, AdjoinRoot.liftAlgHom_of]; rfl⟩
  have hθA : θ ∈ A := hA.2 hBc hAB
    ((AlgHom.mem_range _).mpr ⟨AdjoinRoot.root f, by rw [hψ, AdjoinRoot.liftAlgHom_root]⟩)
  -- then `θ mod M_A` is a root of `p`
  apply hno (residue A ⟨θ, hθA⟩)
  have h1 : φ (f.eval ⟨θ, hθA⟩) = 0 := by
    rw [← Polynomial.eval₂_at_apply]
    exact hθ'
  have h2 : f.eval (⟨θ, hθA⟩ : A) = 0 := Subtype.val_injective h1
  rw [← hfmap, eval_map, Polynomial.eval₂_at_apply, h2, map_zero]

end AdjoinRootCand

end MaxLocExt

open MaxLocExt

/-- The maximal local extension of p. 234: a local homomorphism `R → R'` of regular local rings
transforming a regular system of parameters into one, with separable algebraic residue field
extension and separably closed residue field of `R'`.  `R'` is a maximal member of the family
`𝒮` of subrings of an algebraic closure of the field of fractions of `R` (Zorn's lemma,
`exists_maximal_isCand`); its residue field is separably closed by `isSepClosed_of_maximal`. -/
@[blueprint "compat:maximal-local-extension"
  (statement := /-- Let $R$ be a regular local ring. There is a local homomorphism $R\to R'$ of
    regular local rings which transforms a regular system of parameters of $R$ into such a
    system of parameters of $R'$ (\cref{def:III.rsop-map}), induces a separable algebraic
    extension of the residue fields (\cref{def:III.2-residually}), and such that the residue
    field of $R'$ is separably closed. (Proof of Theorem~3, p.~234.) (Statement modified with
    respect to the paper, which takes $R'$ maximal in a fixed algebraic closure of the field of
    quotients; see \cref{lem:III.5-maximal-local-extension}  -/)
  (proof := /-- Following p.~234: fix an algebraic closure $\Omega$ of the field of quotients of
    $R$ and let $\mathcal S$ be the set of subrings $A\subseteq\Omega$ containing $R$ such that
    $A$ is a noetherian local ring with maximal ideal $M_RA$, $\dim A=\dim R$, and the residue
    field of $A$ is separable algebraic over that of $R$. Each $A\in\mathcal S$ is regular, a
    regular system of parameters $x$ of $R$ being one of $A$; for $A\subseteq B$ in
    $\mathcal S$, $B$ is flat (\cref{lem:III.rsop-map-flat}), hence faithfully flat, over $A$,
    so $IB\cap A=I$ for every ideal $I$ of $A$.

    \emph{Zorn's lemma.} Let $U$ be the union of a chain in $\mathcal S$. It is local with
    maximal ideal $M_RU$ (the non-units of $U$ are the union of the maximal ideals of the
    members), and $IU\cap A=I$ for $A$ in the chain. If $g\in JU+(M_RU)^n$ for all $n$, with
    $J$ an ideal of a member $A\ni g$, then $g\in JA+M_A^n$ for all $n$, so $g\in JA$ by
    Krull's intersection theorem. $U$ is noetherian: $\operatorname{gr}_{M_U}(U)$ is a quotient
    of a polynomial ring over $U/M_U$, so for an ideal $J$ of $U$ the initial forms of $J$
    (\cref{def:II.2-graded-ideal}) are generated by those of finitely many $f_i\in J$; as in
    \cref{lem:II.2-6}, $J\subseteq(f)+(M_RU)^n$ for all $n$, hence $J=(f)$ by the previous
    remark. $x$ is a regular sequence in $U$ (it is one in every member,
    \cref{lem:regular-sequence-rsop}, and $U$ is pure over the members) generating the maximal
    ideal, so $\dim U=\dim R$; the residue field of $U$ is the union of those of the members.
    Hence $U\in\mathcal S$, and $\mathcal S$ (which contains $R$) has a maximal element $R'$.

    \emph{Maximality.} Suppose the residue field $k'$ of $R'$ is not separably closed: let
    $\bar f$ be a monic irreducible separable polynomial over $k'$ without root, $f$ a monic lift
    to $R'$ and $\theta\in\Omega$ a root of $f$. $C=R'[t]/(f)$ is free over $R'$, local with
    maximal ideal $M_{R'}C$ (as $C/M_{R'}C=k'[t]/(\bar f)$ is a field and $C$ is integral over
    $R'$), noetherian, of dimension $\dim R'$ ($x$ stays a regular sequence by faithful
    flatness), and its residue field is generated over $k'$ by a root of $\bar f$, hence
    separable over $k'$ and so over $k$. Thus $C$ is regular, hence a domain
    (\cref{lem:regular-local-domain}); the kernel of $C\to\Omega$, $t\mapsto\theta$, lies over
    $(0)$ and $C$ is integral over $R'$, so it is $(0)$. The image $R'[\theta]\cong C$ lies in
    $\mathcal S$ and contains $R'$, so $\theta\in R'$ and $\theta$ mod $M_{R'}$ would be a root
    of $\bar f$. Hence $k'$ is separably closed. -/)
  (latexEnv := "lemma")]
theorem exists_regularLocal_sepClosed_extension (R : Type u) [CommRing R]
    [IsRegularLocalRing R] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsRegularLocalRing R') (α : R →+* R')
      (_ : IsLocalHom α), RingHom.MapsRSOP α ∧
        RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := R') α ∧
        IsSepClosed (ResidueField R') := by
  have := isDomain_of_isRegularLocalRing R
  have hinj : Function.Injective (algebraMap R (AlgebraicClosure (FractionRing R))) := by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) (AlgebraicClosure (FractionRing R))]
    exact (algebraMap (FractionRing R) _).injective.comp (IsFractionRing.injective R _)
  obtain ⟨A, hA⟩ := exists_maximal_isCand hinj
  have hAc : IsCand R A := hA.prop
  have : IsRegularLocalRing A := hAc.isRegularLocalRing hinj
  have : IsLocalHom (algebraMap R A) := hAc.isLocalHom
  refine ⟨A, inferInstance, inferInstance, algebraMap R A, inferInstance, hAc.mapsRSOP hinj, ?_,
    isSepClosed_of_maximal hA⟩
  let := (ResidueField.map (algebraMap R A)).toAlgebra
  exact isSeparable_of_sep (fun r => rfl) (fun a => by rw [hAc.maximalIdeal_eq]; exact hAc.sep a)

end Hironaka

