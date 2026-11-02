/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch3.Transforms
public import Hironaka.Ch0.AlgebraicScheme
public import Hironaka.Compat.RSOPProducts

/-!
# Orders along the completion: the last step of Lemma (CD.5), p. 320

> We can see that the local homomorphism `S'_s → Ŝ'_s` transforms a regular system of parameters of
> `S'_s` into a system of elements of `Ŝ'_s` which can be extended to a regular system of
> parameters of `Ŝ'_s`. (This can be easily deduced from the fact that `X̂_s = X_s ×_X Spec(Ŝ)` and
> that `S` belongs to the class 𝔅 defined in the introductory paragraphs of Ch. I, where `S` is the
> local ring of `X` at the point `x_0`, and `Ŝ` is the completion of `S`.) Since `Ĵ'_s = J'_sŜ'_s`,
> we can conclude that `J'_s` is contained in the `ν`th power of the maximal ideal of `S'_s`. (p. 320)

Ring-level content:

* `exists_mapsRSOP_quotient_of_flat`: a flat local homomorphism `α : R → R'` of regular local rings
  with regular closed fibre `R'/MR'` transforms a regular system of parameters into part of one:
  `R → R'/(Y)` (`Y` lifting a regular system of parameters of the fibre) is `MapsRSOP`.  Uses the
  dimension formula for flat local maps (`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`).
* `le_pow_maximalIdeal_of_map_le_pow_of_flat`: hence `J R' ⊆ M'^k` implies `J ⊆ M^k`
  (Corollary of Lemma 2, Ch. III, via faithful flatness of `R → R'/(Y)`).
* `le_pow_maximalIdeal_of_map_le_pow_of_isHironakaBase`: for `A` of finite type over `S ∈ 𝔅` and a
  prime `q` of `A ⊗_S Ŝ`: flatness of `S → Ŝ`, regularity of `(A⊗Ŝ)_q` and of the closed fibre
  (a localization of `(A/p) ⊗ Ŝ`) are condition (ii) of 𝔅 (`IsHironakaBase.completion_singularLocus`).

Not done here (the scheme-level bridge): identification of
`S'_s → Ŝ'_s` with `A_p → (A ⊗_S Ŝ)_q` from `X̂_s = X_s ×_X Spec Ŝ`.

Deviation from the paper (gap filled): "This can be easily deduced from …" (p. 320) is proved:
the dimension formula for flat local homomorphisms and the lifting of a regular system of parameters
of the fibre.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section MapsRSOP

variable {R R' : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing R'] [IsRegularLocalRing R']

/-- If a local homomorphism of regular local rings transforms a regular system of parameters into
one, the order of an ideal can be read in the target: `J R' ⊆ M'^k` implies `J ⊆ M^k`. -/
theorem le_pow_maximalIdeal_of_map_le_pow_of_mapsRSOP (α : R →+* R') [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (J : Ideal R) (k : ℕ)
    (h : J.map α ≤ maximalIdeal R' ^ k) : J ≤ maximalIdeal R ^ k := by
  let := α.toAlgebra
  have _ : IsLocalHom (algebraMap R R') := ‹IsLocalHom α›
  have _ : Module.Flat R R' := hα.flat
  have _ : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hM : (maximalIdeal R).map α = maximalIdeal R' := hα.map_maximalIdeal
  have h' : J.map (algebraMap R R') ≤ ((maximalIdeal R) ^ k).map (algebraMap R R') := by
    rw [Ideal.map_pow]
    exact hM ▸ h
  calc J ≤ (J.map (algebraMap R R')).comap (algebraMap R R') := Ideal.le_comap_map
    _ ≤ (((maximalIdeal R) ^ k).map (algebraMap R R')).comap (algebraMap R R') :=
        Ideal.comap_mono h'
    _ = (maximalIdeal R) ^ k := Ideal.comap_map_eq_self_of_faithfullyFlat _


open Classical in
/-- **A flat local homomorphism of regular local rings with regular closed fibre transforms a
regular system of parameters into part of one**: after killing the lifts `Y` of a regular system of
parameters of the closed fibre, `R → R'/(Y)` transforms a regular system of parameters into one
(p. 320: "…transforms a regular system of parameters of `S'_s` into a system of elements of `Ŝ'_s`
which can be extended to a regular system of parameters of `Ŝ'_s`").  Dimension formula for flat
local maps: `dim R' = dim R + dim (R'/MR')`. -/
theorem exists_mapsRSOP_quotient_of_flat (α : R →+* R') [IsLocalHom α] (hflat : α.Flat)
    [IsRegularLocalRing (R' ⧸ (maximalIdeal R).map α)] :
    ∃ (Y : Finset R') (_ : IsRegularLocalRing (R' ⧸ Ideal.span (Y : Set R'))),
      RingHom.MapsRSOP ((Ideal.Quotient.mk (Ideal.span (Y : Set R'))).comp α) := by
  let := α.toAlgebra
  have _ : IsLocalHom (algebraMap R R') := ‹IsLocalHom α›
  have _ : Module.Flat R R' := RingHom.flat_algebraMap_iff.mp hflat
  set I := (maximalIdeal R).map α with hI
  set F := R' ⧸ I
  let mkI : R' →+* F := Ideal.Quotient.mk I
  -- the dimension formula
  have hover : (maximalIdeal R').LiesOver (maximalIdeal R) := inferInstance
  have hdim := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (R := R) (S := R')
    (maximalIdeal R) (maximalIdeal R')
  have hmapF : (maximalIdeal R').map mkI = maximalIdeal F :=
    map_maximalIdeal_of_surjective mkI Ideal.Quotient.mk_surjective
  have hdim' : (maximalIdeal R').height = (maximalIdeal R).height + (maximalIdeal F).height := by
    have h2 : (Ideal.map (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R R')))
        (maximalIdeal R')) = maximalIdeal F := hmapF
    rw [h2] at hdim
    exact hdim
  -- regular systems of parameters of `R` and of the fibre `F`
  obtain ⟨-, x, hx⟩ := (isRegularLocalRing_iff_exists_rsop R).mp inferInstance
  obtain ⟨-, yb, hyb⟩ := (isRegularLocalRing_iff_exists_rsop F).mp inferInstance
  have hxh : (x.card : ℕ∞) = (maximalIdeal R).height := by
    have := hx.2
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at this
    exact_mod_cast this
  have hybh : (yb.card : ℕ∞) = (maximalIdeal F).height := by
    have := hyb.2
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at this
    exact_mod_cast this
  -- lifts of `yb`
  have : IsLocalHom mkI := IsLocalHom.of_surjective mkI Ideal.Quotient.mk_surjective
  let σ : F → R' := Function.surjInv Ideal.Quotient.mk_surjective
  have hσ : ∀ a, mkI (σ a) = a := Function.surjInv_eq _
  let Y : Finset R' := yb.image σ
  have hYcard : Y.card ≤ yb.card := Finset.card_image_le
  let Z : Finset R' := x.image α ∪ Y
  have hIspan : I = Ideal.span ((x.image α : Finset R') : Set R') := by
    rw [hI, ← hx.1, Ideal.map_span, Finset.coe_image]
  have hYimg : Y.image mkI = yb := by
    rw [Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := yb)]
    exact Finset.image_congr fun a _ => hσ a
  have hZspan : Ideal.span (Z : Set R') = maximalIdeal R' := by
    refine le_antisymm (Ideal.span_le.mpr fun z hz => ?_) fun a ha => ?_
    · rcases Finset.mem_union.mp hz with h | h
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
        have hbm : b ∈ maximalIdeal R := hx.1 ▸ Ideal.subset_span hb
        rw [SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff]
        exact fun hu => (mem_maximalIdeal _).mp hbm (isUnit_of_map_unit α b hu)
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
        have ham : a ∈ maximalIdeal F := hyb.1 ▸ Ideal.subset_span ha
        rw [SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have := hu.map mkI
        rw [hσ] at this
        exact (mem_maximalIdeal _).mp ham this
    · have hmem : mkI a ∈ maximalIdeal F := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        exact fun hu => (mem_maximalIdeal _).mp ha (isUnit_of_map_unit mkI a hu)
      rw [← hyb.1, ← hYimg, Finset.coe_image, ← Ideal.map_span] at hmem
      obtain ⟨b, hb, hba⟩ := Ideal.mem_map_iff_of_surjective mkI Ideal.Quotient.mk_surjective |>.mp hmem
      have hab : a - b ∈ I := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hba, sub_self]
      have hspanY : Ideal.span (Y : Set R') ≤ Ideal.span (Z : Set R') :=
        Ideal.span_mono Finset.subset_union_right
      have hIZ : I ≤ Ideal.span (Z : Set R') := by
        rw [hIspan]; exact Ideal.span_mono Finset.subset_union_left
      have := Ideal.add_mem _ (hIZ hab) (hspanY hb)
      simpa using this
  have hdimR' : (maximalIdeal R').height = ((x.card + yb.card : ℕ) : ℕ∞) := by
    rw [hdim', ← hxh, ← hybh]; push_cast; rfl
  have hge : x.card + yb.card ≤ Z.card := by
    have h1 : (maximalIdeal R').height ≤ (maximalIdeal R').spanFinrank :=
      Ideal.height_le_spanFinrank _ Ideal.IsPrime.ne_top'
    have h2 : (maximalIdeal R').spanFinrank ≤ Z.card := by
      rw [← hZspan]
      have := Submodule.spanFinrank_span_le_ncard_of_finite (R := R') Z.finite_toSet
      rwa [Set.ncard_coe_finset] at this
    have := h1.trans (by exact_mod_cast h2 : ((maximalIdeal R').spanFinrank : ℕ∞) ≤ Z.card)
    rw [hdimR'] at this
    exact_mod_cast this
  have hZu : Z.card = (x.image α ∪ Y).card := rfl
  have hle : Z.card ≤ x.card + yb.card :=
    (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le hYcard)
  have hZc : Z.card = x.card + yb.card := le_antisymm hle hge
  have himgc : (x.image α).card = x.card := by
    have := Finset.card_union_le (x.image α) Y
    have h3 : (x.image α).card ≤ x.card := Finset.card_image_le
    have h4 : Y.card ≤ yb.card := hYcard
    omega
  have hYc : Y.card = yb.card := by
    have := Finset.card_union_le (x.image α) Y
    have h3 : (x.image α).card ≤ x.card := Finset.card_image_le
    have h4 : Y.card ≤ yb.card := hYcard
    omega
  have hdisj : Disjoint (x.image α) Y := by
    rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
    have := Finset.card_union_add_card_inter (x.image α) Y
    omega
  have hZrsop : IsRegularSystemOfParameters R' Z := by
    refine ⟨hZspan, ?_⟩
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdimR', hZc]
    norm_cast
  have hKZ : Y ⊆ Z := Finset.subset_union_right
  obtain ⟨hreg, hrs, hcard⟩ := rsop_quotient hZrsop hKZ
  have hZY : Z \ Y = x.image α := by
    ext z
    simp only [Z, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact h
      · exact absurd h h'
    · intro h
      exact ⟨Or.inl h, Finset.disjoint_left.mp hdisj h⟩
  rw [hZY] at hrs hcard
  refine ⟨Y, hreg, x, hx, ?_, ?_⟩
  · rw [Finset.image_image] at hrs
    exact hrs
  · have hc : (x.image ((Ideal.Quotient.mk (Ideal.span (Y : Set R'))) ∘ α)).card = x.card := by
      rw [← Finset.image_image, hcard, himgc]
    exact Finset.card_image_iff.mp hc

/-- **Order descent along a flat local homomorphism of regular local rings with regular closed
fibre**: `J R' ⊆ M'^k` implies `J ⊆ M^k` (p. 320: "Since `Ĵ'_s = J'_sŜ'_s`, we can conclude that
`J'_s` is contained in the `ν`th power of the maximal ideal of `S'_s`").  Combines
`exists_mapsRSOP_quotient_of_flat` with the Corollary of Lemma 2, Ch. III. -/
theorem le_pow_maximalIdeal_of_map_le_pow_of_flat (α : R →+* R') [IsLocalHom α] (hflat : α.Flat)
    [IsRegularLocalRing (R' ⧸ (maximalIdeal R).map α)] (J : Ideal R) (k : ℕ)
    (h : J.map α ≤ maximalIdeal R' ^ k) : J ≤ maximalIdeal R ^ k := by
  obtain ⟨Y, hreg, hmaps⟩ := exists_mapsRSOP_quotient_of_flat α hflat
  set mk := Ideal.Quotient.mk (Ideal.span (Y : Set R'))
  have : IsLocalHom mk := IsLocalHom.of_surjective mk Ideal.Quotient.mk_surjective
  refine le_pow_maximalIdeal_of_map_le_pow_of_mapsRSOP (mk.comp α) hmaps J k ?_
  rw [← Ideal.map_map, ← map_maximalIdeal_of_surjective mk Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow]
  exact Ideal.map_mono h

/-- The same, with the regular closed fibre given as a surjection `ψ : R' → C` with kernel `M R'`
onto a regular local ring `C`. -/
theorem le_pow_maximalIdeal_of_map_le_pow_of_flat_of_surjective {C : Type u} [CommRing C]
    [IsRegularLocalRing C] (α : R →+* R') [IsLocalHom α] (hflat : α.Flat) (ψ : R' →+* C)
    (hψ : Function.Surjective ψ) (hker : RingHom.ker ψ = (maximalIdeal R).map α)
    (J : Ideal R) (k : ℕ) (h : J.map α ≤ maximalIdeal R' ^ k) : J ≤ maximalIdeal R ^ k := by
  let e : R' ⧸ (maximalIdeal R).map α ≃+* C :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hψ)
  have : IsRegularLocalRing (R' ⧸ (maximalIdeal R).map α) :=
    IsRegularLocalRing.of_ringEquiv e.symm
  exact le_pow_maximalIdeal_of_map_le_pow_of_flat α hflat J k h

end MapsRSOP


section Fibre

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- The closed fibre of `A_p → B_q` is a localization of the quotient: if `π : B → C` is surjective
with kernel `pB`, then `B_q → C_{q'}` is onto with kernel `(pA_p)B_q`, where `q = π⁻¹(q')`. -/
theorem localRingHom_surjective_and_ker_eq (f : A →+* B) (π : B →+* C)
    (hπ : Function.Surjective π) (p : Ideal A) [p.IsPrime] (hker : RingHom.ker π = p.map f)
    (q' : Ideal C) [q'.IsPrime] (q : Ideal B) [q.IsPrime] (hqq : q = Ideal.comap π q')
    (hpq : p = Ideal.comap f q) :
    Function.Surjective (Localization.localRingHom q q' π hqq) ∧
      RingHom.ker (Localization.localRingHom q q' π hqq) =
        (maximalIdeal (Localization.AtPrime p)).map (Localization.localRingHom p q f hpq) := by
  subst hqq
  set q := Ideal.comap π q' with hq
  set ψ := Localization.localRingHom q q' π rfl
  set φ := Localization.localRingHom p q f hpq
  have hmax : (maximalIdeal (Localization.AtPrime p)).map φ =
      (p.map f).map (algebraMap B (Localization.AtPrime q)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map]
    congr 1
    ext a
    exact Localization.localRingHom_to_map p q f hpq a
  refine ⟨?_, ?_⟩
  · intro z
    obtain ⟨⟨c, t'⟩, rfl⟩ := IsLocalization.mk'_surjective q'.primeCompl z
    obtain ⟨b, rfl⟩ := hπ c
    obtain ⟨t, ht⟩ := hπ (t' : C)
    have htq : t ∈ q.primeCompl := by
      show t ∉ q
      rw [hq, Ideal.mem_comap, ht]
      exact t'.2
    refine ⟨IsLocalization.mk' _ b ⟨t, htq⟩, ?_⟩
    rw [Localization.localRingHom_mk' q q' π rfl b ⟨t, htq⟩]
    congr 1
    exact Subtype.ext ht
  · rw [hmax]
    apply le_antisymm
    · intro z hz
      obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
      rw [RingHom.mem_ker, Localization.localRingHom_mk' q q' π rfl b s] at hz
      rw [IsLocalization.mk'_eq_zero_iff] at hz
      obtain ⟨t', ht'⟩ := hz
      obtain ⟨t, ht⟩ := hπ (t' : C)
      have htq : t ∈ q.primeCompl := by
        show t ∉ q
        rw [hq, Ideal.mem_comap, ht]
        exact t'.2
      have h1 : t * b ∈ RingHom.ker π := by
        rw [RingHom.mem_ker, map_mul, ht]
        exact ht'
      rw [hker] at h1
      have h2 : algebraMap B (Localization.AtPrime q) (t * b) ∈
          (p.map f).map (algebraMap B (Localization.AtPrime q)) := Ideal.mem_map_of_mem _ h1
      have h3 : IsLocalization.mk' (Localization.AtPrime q) b s =
          algebraMap B _ (t * b) * IsLocalization.mk' (Localization.AtPrime q) (1 : B)
            (⟨t, htq⟩ * s) := by
        rw [← IsLocalization.mk'_eq_mul_mk'_one, ← IsLocalization.mk'_cancel b s ⟨t, htq⟩]
        rw [mul_comm t b, mul_comm (⟨t, htq⟩ : q.primeCompl) s]
      show IsLocalization.mk' (Localization.AtPrime q) b s ∈ _
      rw [h3]
      exact Ideal.mul_mem_right _ _ h2
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, Localization.localRingHom_to_map]
      have h0 : π a = 0 := by rw [← RingHom.mem_ker, hker]; exact ha
      rw [h0, map_zero]

end Fibre


section Completion

open scoped TensorProduct

variable {S : Type u} [CommRing S] [IsLocalRing S] [IsHironakaBase S]
  {A : Type u} [CommRing A] [Algebra S A] [Algebra.FiniteType S A]

set_option maxHeartbeats 800000 in
/-- **Lemma (CD.5), last step, algebraic form** (p. 320): for `A` of finite type over a local ring
`S` of the class 𝔅 and a prime `q` of `A ⊗_S Ŝ` (`Ŝ` the completion of `S`) over the prime `p` of
`A`, if `A_p` is regular and `J (A⊗Ŝ)_q ⊆ M_q^k` for an ideal `J` of `A_p`, then `J ⊆ (pA_p)^k`.
Flat (`S → Ŝ` is flat), `(A⊗Ŝ)_q` regular by (ii), and the closed fibre is a localization of
`(A/p)⊗Ŝ` at a point over the generic point of `A/p`, regular by (ii) for `A/p`.

Deviation from the paper (gap filled): "We can see that the local homomorphism `S'_s → Ŝ'_s`
transforms a regular system of parameters of `S'_s` into a system of elements of `Ŝ'_s` which can be
extended to a regular system of parameters of `Ŝ'_s`. (This can be easily deduced from the fact that
`X̂_s = X_s ×_X Spec(Ŝ)` and that `S` belongs to the class 𝔅 defined in the introductory paragraphs
of Ch. I, where `S` is the local ring of `X` at the point `x_0`, and `Ŝ` is the completion of `S`.)
Since `Ĵ'_s = J'_sŜ'_s`, we can conclude that `J'_s` is contained in the `ν`th power of the maximal
ideal of `S'_s`." (p. 320). -/
@[blueprint "lem:IV.CD-5-completion-order"
  (statement := /-- Let $S$ be a local ring of the class $\mathfrak B$ (p.~161), $\hat S$ its
    completion, $A$ an $S$-algebra of finite type, $q$ a prime of $A\otimes_S\hat S$ and $p$ its
    contraction to $A$. If $A_p$ is regular and $J$ is an ideal of $A_p$ with
    $J\,(A\otimes_S\hat S)_q\subseteq M_q^k$, then $J\subseteq(pA_p)^k$. (Used on p.~320.) -/)
  (proof := /-- $S\to\hat S$ is flat, so $A_p\to(A\otimes\hat S)_q$ is flat; $(A\otimes\hat S)_q$ is
    regular by condition (ii) of $\mathfrak B$; its closed fibre is a localization of
    $(A/p)\otimes_S\hat S$ at a point over the generic point of $A/p$, regular by (ii) applied to
    $A/p$. A flat local homomorphism of regular local rings with regular closed fibre has
    $\dim R'=\dim R+\dim(R'/MR')$; lifting a regular system of parameters of the fibre, the image of a
    regular system of parameters of $A_p$ is part of one of $(A\otimes\hat S)_q$, so
    $R\to R'/(Y)$ transforms a regular system of parameters into one and the Corollary of Lemma~2 of
    Ch.~III gives the order statement.

    \textbf{Deviation from the paper (gap filled).} The paper writes ``We can see that the local
    homomorphism $S'_s\to\hat S'_s$ transforms a regular system of parameters of $S'_s$ into a system
    of elements of $\hat S'_s$ which can be extended to a regular system of parameters of $\hat S'_s$.
    (This can be easily deduced from the fact that $\hat X_s=X_s\times_X\operatorname{Spec}(\hat S)$ and
    that $S$ belongs to the class $\mathfrak B$ \dots)'' (p.~320). -/)
  (proofUses := ["lem:III.rsop-map-flat"])
  (latexEnv := "lemma")]
theorem le_pow_maximalIdeal_of_map_le_pow_of_isHironakaBase
    (q : Ideal (A ⊗[S] AdicCompletion (maximalIdeal S) S)) [hq : q.IsPrime]
    [hreg : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap A
      (A ⊗[S] AdicCompletion (maximalIdeal S) S))))]
    (J : Ideal (Localization.AtPrime (q.comap (algebraMap A
      (A ⊗[S] AdicCompletion (maximalIdeal S) S))))) (k : ℕ)
    (h : J.map (Localization.localRingHom (q.comap (algebraMap A
      (A ⊗[S] AdicCompletion (maximalIdeal S) S))) q (algebraMap A
      (A ⊗[S] AdicCompletion (maximalIdeal S) S)) rfl) ≤ maximalIdeal (Localization.AtPrime q) ^ k) :
    J ≤ maximalIdeal (Localization.AtPrime (q.comap (algebraMap A
      (A ⊗[S] AdicCompletion (maximalIdeal S) S)))) ^ k := by
  classical
  set B := A ⊗[S] AdicCompletion (maximalIdeal S) S with hBdef
  set f : A →+* B := algebraMap A B with hf
  set p := q.comap f with hp
  have hpprime : p.IsPrime := Ideal.comap_isPrime _ _
  have hflatf : f.Flat := by
    rw [hf, RingHom.flat_algebraMap_iff]; infer_instance
  have hflatφ := RingHom.Flat.localRingHom hflatf q p hp
  have := Localization.isLocalHom_localRingHom p q f hp
  have hBreg : IsRegularLocalRing (Localization.AtPrime q) :=
    (IsHironakaBase.completion_singularLocus A ⟨q, hq⟩).mpr hreg
  -- the closed fibre
  let π : B →ₐ[S] (A ⧸ p) ⊗[S] AdicCompletion (maximalIdeal S) S :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ S p)
      (AlgHom.id S (AdicCompletion (maximalIdeal S) S))
  have hπs : Function.Surjective π := Algebra.TensorProduct.map_surjective _ _
    Ideal.Quotient.mk_surjective (fun x => ⟨x, rfl⟩)
  have hker : RingHom.ker π = p.map f := by
    have := Algebra.TensorProduct.rTensor_ker (R := S) (Ideal.Quotient.mkₐ S p)
      (C := AdicCompletion (maximalIdeal S) S) Ideal.Quotient.mk_surjective
    rw [show RingHom.ker (Ideal.Quotient.mkₐ S p) = p from Ideal.Quotient.mkₐ_ker S p] at this
    exact this
  have hkerq : p.map f ≤ q := by
    rw [hp]; exact Ideal.map_comap_le
  have hq' : (q.map π).IsPrime := Ideal.map_isPrime_of_surjective hπs (by rw [hker]; exact hkerq)
  have hqq : q = Ideal.comap π (q.map π) := by
    rw [Ideal.comap_map_of_surjective π hπs, ← RingHom.ker_eq_comap_bot, hker]
    exact (sup_eq_left.mpr hkerq).symm
  obtain ⟨hsurj, hkerψ⟩ := localRingHom_surjective_and_ker_eq f π hπs p hker (q.map π) q hqq hp
  let e := (Ideal.quotEquivOfEq hkerψ.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing S A
  have hfield : IsRegularLocalRing (Localization.AtPrime (⊥ : Ideal (A ⧸ p))) := by
    let : Field (Localization.AtPrime (⊥ : Ideal (A ⧸ p))) := IsField.toField <| by
      simp [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
    infer_instance
  have hC : IsRegularLocalRing (Localization.AtPrime (q.map π)) := by
    have hcomap : PrimeSpectrum.comap (algebraMap (A ⧸ p)
        ((A ⧸ p) ⊗[S] AdicCompletion (maximalIdeal S) S)) ⟨q.map π, hq'⟩ =
        ⟨⊥, (inferInstance : (⊥ : Ideal (A ⧸ p)).IsPrime)⟩ := by
      refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      show algebraMap (A ⧸ p) _ (Ideal.Quotient.mk p a) ∈ q.map π ↔ _
      have h1 : algebraMap (A ⧸ p) ((A ⧸ p) ⊗[S] AdicCompletion (maximalIdeal S) S)
          (Ideal.Quotient.mk p a) = π (f a) := rfl
      rw [h1, ← Ideal.mem_comap, ← hqq]
      show f a ∈ q ↔ Ideal.Quotient.mk p a ∈ (⊥ : Ideal (A ⧸ p))
      rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
      rfl
    have := (IsHironakaBase.completion_singularLocus (A ⧸ p) ⟨q.map π, hq'⟩).mpr
      (by rw [hcomap]; exact hfield)
    exact this
  have : IsRegularLocalRing (Localization.AtPrime q) := hBreg
  have : IsRegularLocalRing (Localization.AtPrime p) := hreg
  refine le_pow_maximalIdeal_of_map_le_pow_of_flat_of_surjective
    (R := Localization.AtPrime p) (R' := Localization.AtPrime q)
    (Localization.localRingHom p q f hp) hflatφ
    _ hsurj hkerψ J k ?_
  exact h

end Completion

end Hironaka
