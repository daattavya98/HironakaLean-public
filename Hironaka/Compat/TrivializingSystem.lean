/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import Architect
public import Hironaka.Ch4.MainTheoremIIZero
public import Hironaka.Compat.ExtendSuccessionWeak
public import Hironaka.Compat.WeakTransformProduct
public import Hironaka.Statements

/-!
# The trivialization of a system of sheaves of ideals (Ch. 0 §5, pp. 143–144, proof of Corollary 1)

The printed proof of Corollary 1 (pp. 143–144) takes for `d` the maximum of `ν((∏_j J_j)_x)` for the points `x` at
which no `J_j` is trivial, for `T` the set of the points with `ν((∏ J_j)_x) ≧ d` and for `S` the set of those points
of `T` at which some `J_j` is trivial: "we can prove that `T`, `S` and `T − S` are all closed"; Main Theorem II is
applied to `∏ J_j` on `X − S`; by (ii) the centers are mapped into `T − S`, so that the succession extends to `X`
(the quote in `Hironaka/Compat/ExtendSuccessionWeak.lean`); and "as is easily seen" the maximum `d` drops or (2) is
achieved, which ends the proof by induction on `d`.

This file carries out that proof (every step is unprinted, so every step is a gap filled):

* `Subscheme.hasOnlyNormalCrossings_empty`, `Subscheme.isEverywhereCodimOne_empty`: `E₀ = ∅` is admissible in Main
  Theorem II;
* `isClosed_inter_of_specializes`: in a noetherian sober space, `T ∩ O` (`T` closed, `O` open) is closed if it is
  stable under specialization (the closedness of `S`);
* `MonoidalSuccession.isTrivializingSteps_of_isMainIIZero`: the stage analysis along the succession of Main
  Theorem II applied to `∏ J_j` ("as is easily seen"): property (1) of Corollary 1 (the per-factor constancy and the
  positivity of `ν(J_j(i)_y)` on the centers `D(i)`), the centers are mapped into `T − S`, and at the end
  `ν(∏_j J_j(r)) < d` everywhere; the positivity needs the invariant "where some `J_j(i)` is trivial,
  `ν(∏_j J_j(i)) < d`", which the paper does not mention;
* `MainTheorem.Ch0.exists_isTrivializingSteps_step`: one round of the proof (`d` is reduced);
* `MainTheorem.Ch0.exists_isTrivializingSteps_of_le`: the induction on `d`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

/-! ### Small facts on `ν`, products and weak transforms -/

section Facts

variable {X : Scheme.{u}}

/-- `J_x` is the unit ideal iff `ν(J_x) = 0`. -/
theorem Subscheme.stalkIdeal_eq_top_iff_nu_eq_zero (J : Subscheme X) (x : X) :
    J.stalkIdeal x = ⊤ ↔ Ideal.nu (J.stalkIdeal x) = 0 := by
  rw [← not_iff_not, ← Ne, ← J.one_le_nu_stalkIdeal_iff x, Order.one_le_iff_ne_zero]

/-- On a non-singular scheme a finite product of sheaves of non-zero ideals has non-zero stalks (the local rings are
domains). -/
theorem Subscheme.stalkIdeal_prod_ne_bot (hX : X.IsNonsingular) {ι : Type*} (s : Finset ι)
    {J : ι → Subscheme X} (hJ : ∀ i x, (J i).stalkIdeal x ≠ ⊥) (x : X) :
    (∏ i ∈ s, J i).stalkIdeal x ≠ ⊥ := by
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk x)
  rw [Subscheme.stalkIdeal_prod, ← Ideal.zero_eq_bot]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by rw [Ideal.zero_eq_bot]; exact hJ i x

/-- On a non-singular scheme the weak transform of a sheaf of non-zero ideals has non-zero stalks (the maps
`O_{X,f(y)} → O_{X',y}` are injective, `R → R'` for a monoidal transform `R'` of `R`). -/
theorem Subscheme.stalkIdeal_weakTransform_ne_bot (hX : X.IsNonsingular) {B : Subscheme X}
    (t : MonoidalTransformation X B) {K : Subscheme X} (hK : ∀ x, K.stalkIdeal x ≠ ⊥) (y : t.X') :
    (Subscheme.weakTransform t K).stalkIdeal y ≠ ⊥ := by
  by_cases h : ∃ ξ : X, IsGenericPoint ξ B.pts
  · obtain ⟨ξ, hξ⟩ := h
    have : IsRegularLocalRing (X.presheaf.stalk ξ) := hX ξ
    obtain ⟨m, hm⟩ := Ideal.exists_nu_eq_natCast (hK ξ)
    rw [Subscheme.weakTransform_eq_divPow t K hξ hm]
    exact Subscheme.stalkIdeal_divPow_totalTransform_ne_bot hX t hK m y
  · rw [Subscheme.weakTransform_eq_totalTransform_of_not_exists t K h, stalkIdeal_totalTransform]
    have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
    have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
    obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk y
    have hinj : Function.Injective (t.f.stalkMap y) := by
      have : ⇑(t.f.stalkMap y) = ⇑(e.toRingHom.comp s.toRing) := by rw [he]
      rw [this]
      exact e.injective.comp s.toRing_injective
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    exact hK _

/-- Strict comparison of the orders of two products: if `ν((K_k)_{x'}) ≤ ν((L_k)_x)` for every `k`, the stalks being
non-zero ideals of regular local rings, and if `(K_k)_{x'}` is the unit ideal while `(L_k)_x` is not, for one `k`,
then `ν((∏ K_k)_{x'}) < ν((∏ L_k)_x)`. -/
theorem Subscheme.nu_stalkIdeal_prod_lt {X' : Scheme.{u}} (hX : X.IsNonsingular) (hX' : X'.IsNonsingular)
    {ι : Type*} [Fintype ι] {K : ι → Subscheme X'} {L : ι → Subscheme X} {x' : X'} {x : X}
    (hK : ∀ k, (K k).stalkIdeal x' ≠ ⊥) (hL : ∀ k, (L k).stalkIdeal x ≠ ⊥)
    (hle : ∀ k, Ideal.nu ((K k).stalkIdeal x') ≤ Ideal.nu ((L k).stalkIdeal x)) (k : ι)
    (hk0 : (K k).stalkIdeal x' = ⊤) (hk1 : (L k).stalkIdeal x ≠ ⊤) :
    Ideal.nu ((∏ k, K k).stalkIdeal x') < Ideal.nu ((∏ k, L k).stalkIdeal x) := by
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  have : IsRegularLocalRing (X'.presheaf.stalk x') := hX' x'
  choose a ha using fun l => Ideal.exists_nu_eq_natCast (hK l)
  choose b hb using fun l => Ideal.exists_nu_eq_natCast (hL l)
  rw [Subscheme.nu_stalkIdeal_prod hX', Subscheme.nu_stalkIdeal_prod hX,
    Finset.sum_congr rfl fun l _ => ha l, Finset.sum_congr rfl fun l _ => hb l, ← Nat.cast_sum,
    ← Nat.cast_sum, Nat.cast_lt]
  refine Finset.sum_lt_sum (fun l _ => ?_) ⟨k, Finset.mem_univ k, ?_⟩
  · have := hle l
    rw [ha l, hb l] at this
    exact_mod_cast this
  · have h0 := ((K k).stalkIdeal_eq_top_iff_nu_eq_zero x').mp hk0
    have h1 := ((L k).one_le_nu_stalkIdeal_iff x).mpr hk1
    rw [ha k] at h0
    rw [hb k] at h1
    have h0' : a k = 0 := by exact_mod_cast h0
    have h1' : 1 ≤ b k := by exact_mod_cast h1
    omega

/-- The empty subscheme has only normal crossings on a non-singular scheme (it has no irreducible components, and the
condition on `D = X` is met by the empty part of a regular system of parameters). -/
theorem Subscheme.hasOnlyNormalCrossings_empty (hX : X.IsNonsingular) :
    (Subscheme.empty : Subscheme X).HasOnlyNormalCrossings := by
  intro x
  unfold Subscheme.HasOnlyNormalCrossingsAt Subscheme.HasOnlyNormalCrossingsWithAt
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  obtain ⟨-, s, hs⟩ := (isRegularLocalRing_iff_exists_rsop (X.presheaf.stalk x)).mp this
  refine ⟨s, hs, fun C hC hxC => ?_, ∅, Finset.empty_subset _, by
    simp [Subscheme.stalkIdeal_bot_eq]⟩
  have := Subscheme.pts_subset_of_mem_irreducibleComponents hC hxC
  rw [Subscheme.pts_empty] at this
  exact this.elim

/-- The empty subscheme is everywhere of codimension one (vacuously; the agreement of p. 163). -/
theorem Subscheme.isEverywhereCodimOne_empty :
    (Subscheme.empty : Subscheme X).IsEverywhereCodimOne := fun x hx => by
  rw [Subscheme.pts_empty] at hx
  exact hx.elim

end Facts

/-! ### A closedness criterion in a noetherian sober space -/

/-- In a noetherian sober space, the intersection `T ∩ O` of a closed set `T` and an open set `O` is closed if it is
stable under specialization: `T` is the finite union of its irreducible closed pieces `t`, and a piece meeting `O`
has its generic point in `T ∩ O`, hence lies in `T ∩ O`.  (Used for the closedness of `S`, p. 144: "Then we can prove
that `T`, `S` and `T − S` are all closed".) -/
theorem isClosed_inter_of_specializes {α : Type*} [TopologicalSpace α] [NoetherianSpace α] [QuasiSober α]
    {T O : Set α} (hT : IsClosed T) (hO : IsOpen O) (h : ∀ x ∈ T ∩ O, ∀ y, x ⤳ y → y ∈ O) :
    IsClosed (T ∩ O) := by
  obtain ⟨F, hFf, hFc, hFi, hTF⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  have key : T ∩ O = ⋃₀ {t ∈ F | (t ∩ O).Nonempty} := by
    ext x
    constructor
    · rintro ⟨hxT, hxO⟩
      rw [hTF] at hxT
      obtain ⟨t, ht, hxt⟩ := hxT
      exact ⟨t, ⟨ht, x, hxt, hxO⟩, hxt⟩
    · rintro ⟨t, ⟨ht, hne⟩, hxt⟩
      have hg := (hFi t ht).isGenericPoint_genericPoint_closure
      rw [(hFc t ht).closure_eq] at hg
      have hηO := (hg.mem_open_set_iff hO).mpr hne
      have htT : t ⊆ T := hTF ▸ Set.subset_sUnion_of_mem ht
      exact ⟨htT hxt, h _ ⟨htT hg.mem, hηO⟩ x (hg.specializes hxt)⟩
  rw [key]
  exact (hFf.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hFc t ht.1

/-! ### Successions: concatenation, non-singularity and non-zero stalks along property (1) -/

namespace MonoidalSuccession

variable {e : ℕ}

/-- The weak transforms of a system along a concatenation of successions. -/
theorem weakTransformFamily_append {X Y Z : Scheme.{u}} (s : MonoidalSuccession X Y)
    (s' : MonoidalSuccession Y Z) :
    ∀ J : Fin e → Subscheme X,
      (s.append s').weakTransformFamily J = s'.weakTransformFamily (s.weakTransformFamily J) := by
  induction s with
  | nil _ => intro J; rfl
  | cons B t rest ih => intro J; exact ih s' _

/-- Property (1) of Corollary 1 for a concatenation of successions. -/
theorem isTrivializingSteps_append {X Y Z : Scheme.{u}} (s : MonoidalSuccession X Y)
    (s' : MonoidalSuccession Y Z) :
    ∀ J : Fin e → Subscheme X, s.IsTrivializingSteps J →
      s'.IsTrivializingSteps (s.weakTransformFamily J) → (s.append s').IsTrivializingSteps J := by
  induction s with
  | nil _ => intro J _ h; exact h
  | cons B t rest ih =>
    intro J h h'
    obtain ⟨hB, hc, hrest⟩ := h
    exact ⟨hB, hc, ih s' _ hrest h'⟩

/-- Along a succession with property (1) of Corollary 1 (the centers are non-singular irreducible, or empty), the
schemes stay algebraic and non-singular and the weak transforms `J_j(i)` of a system of sheaves of non-zero ideals
stay sheaves of non-zero ideals. -/
theorem isNonsingular_of_isTrivializingSteps [Hironaka.HironakaCitedResults.{u}] {Z Z' : Scheme.{u}} (s : MonoidalSuccession Z Z') :
    ∀ (_hZa : IsAlgebraicScheme Z) (_hZ : Z.IsNonsingular) (K : Fin e → Subscheme Z),
      (∀ k z, (K k).stalkIdeal z ≠ ⊥) → s.IsTrivializingSteps K →
        IsAlgebraicScheme Z' ∧ Z'.IsNonsingular ∧
          ∀ k z, (s.weakTransformFamily K k).stalkIdeal z ≠ ⊥ := by
  induction s with
  | nil _ => intro hZa hZ K hK _; exact ⟨hZa, hZ, hK⟩
  | cons B t rest ih =>
    intro hZa hZ K hK h
    obtain ⟨hB, -, hrest⟩ := h
    have := hZa
    exact ih t.isAlgebraicScheme (t.isNonsingular_and_isNonsingular_exceptional hZ hB.isNonsingular).1 _
      (fun k z => Subscheme.stalkIdeal_weakTransform_ne_bot hZ t (hK k) z) hrest

/-! ### The stage analysis along the succession of Main Theorem II ("as is easily seen", p. 144) -/

/-- **The stage analysis of the proof of Corollary 1** (p. 144, "as is easily seen"; gap filled).  Let `s` be a
succession with the properties (i)–(iv) of Main Theorem II and the remark of p. 143 for the product `∏_k K_k` of a
system of sheaves of non-zero ideals, the integer `d` and some `E`, and assume the invariant: wherever some `K_k` is
the unit ideal, `ν((∏ K_k)_z) < d`.  Then:

* property (1) of Corollary 1 holds for `s` and the system `(K_k)`: on each center `D(i)` the orders
  `ν(K_k(i)_y)` are constant (each is upper semicontinuous, `≥` its value at the generic point, and their sum is the
  constant `d`) and positive (by the invariant, as their sum is `d`); the invariant passes to the weak transforms by
  (B\*) applied to each factor (`MonoidalTransformation.nu_weakTransform_le`), using that the weak transform of the
  product is the product of the weak transforms (`Subscheme.weakTransform_prod`);
* the centers lie over `C` if every point with `ν((∏ K_k)_z) ≥ d` does (by (B\*) the orders do not increase); and
* at the end `ν(∏_k K_k(r)) < d` everywhere ((iv)). -/
theorem isTrivializingSteps_of_isMainIIZero [Hironaka.HironakaCitedResults.{u}] (d : ℕ) {Z Z' : Scheme.{u}} (s : MonoidalSuccession Z Z') :
    ∀ (_hZa : IsAlgebraicScheme Z) (_hZ : Z.IsNonsingular) {Y : Scheme.{u}} (q : Z ⟶ Y) (C : Set Y)
      (K : Fin e → Subscheme Z) (E : Subscheme Z), (∀ k z, (K k).stalkIdeal z ≠ ⊥) →
      (∀ z, (∃ k, (K k).stalkIdeal z = ⊤) → Ideal.nu ((∏ k, K k).stalkIdeal z) < d) →
      (∀ z, (d : ℕ∞) ≤ Ideal.nu ((∏ k, K k).stalkIdeal z) → q.base z ∈ C) →
      s.IsMainIIZero d (∏ k, K k) E → s.IsMainIIZeroRemark d (∏ k, K k) E →
      s.IsTrivializingSteps K ∧ s.CentersClosedIn q C ∧
        ∀ z : Z', Ideal.nu ((∏ k, s.weakTransformFamily K k).stalkIdeal z) < d := by
  induction s with
  | nil _ =>
    intro _ _ Y q C K E _ _ _ hM _
    exact ⟨trivial, trivial, hM.2⟩
  | @cons Z₀ B t _ rest ih =>
    intro hZa hZ Y q C K E hK hI hC hM hR
    have := hZa
    obtain ⟨hB, -, -, hMrest⟩ := hM
    obtain ⟨-, hgreat, hBeq, hRrest⟩ := hR
    -- (1): the orders `ν(K_k)` are positive constants on the center
    have hconst : ∀ k, ∃ c : ℕ, 0 < c ∧ ∀ y ∈ B.pts, Ideal.nu ((K k).stalkIdeal y) = c := by
      intro k
      by_cases hne : ∃ ξ, IsGenericPoint ξ B.pts
      · obtain ⟨ξ, hξ⟩ := hne
        have : IsRegularLocalRing (Z₀.presheaf.stalk ξ) := hZ ξ
        have hξtop : ∀ l, (K l).stalkIdeal ξ ≠ ⊤ := fun l h => by
          have := hI ξ ⟨l, h⟩
          rw [hBeq ξ hξ.mem] at this
          exact lt_irrefl _ this
        have key : ∀ y ∈ B.pts, ∀ l, Ideal.nu ((K l).stalkIdeal y) = Ideal.nu ((K l).stalkIdeal ξ) := by
          intro y hy
          have : IsRegularLocalRing (Z₀.presheaf.stalk y) := hZ y
          have hsp : ξ ⤳ y := hξ.specializes hy
          have hle : ∀ l, Ideal.nu ((K l).stalkIdeal ξ) ≤ Ideal.nu ((K l).stalkIdeal y) := fun l =>
            hsp.mem_closed (Subscheme.isClosed_setOf_le_nu_stalkIdeal hZ (K l) _)
              (show Ideal.nu ((K l).stalkIdeal ξ) ≤ Ideal.nu ((K l).stalkIdeal ξ) from le_rfl)
          have hsum : Ideal.nu ((∏ k, K k).stalkIdeal y) = Ideal.nu ((∏ k, K k).stalkIdeal ξ) := by
            rw [hBeq y hy, hBeq ξ hξ.mem]
          rw [Subscheme.nu_stalkIdeal_prod hZ, Subscheme.nu_stalkIdeal_prod hZ] at hsum
          choose a ha using fun l => Ideal.exists_nu_eq_natCast (hK l y)
          choose b hb using fun l => Ideal.exists_nu_eq_natCast (hK l ξ)
          rw [Finset.sum_congr rfl fun l _ => ha l, Finset.sum_congr rfl fun l _ => hb l,
            ← Nat.cast_sum, ← Nat.cast_sum, Nat.cast_inj] at hsum
          have hba : ∀ l ∈ Finset.univ, b l ≤ a l := fun l _ => by
            have := hle l
            rw [ha l, hb l] at this
            exact_mod_cast this
          intro l
          rw [ha l, hb l, ((Finset.sum_eq_sum_iff_of_le hba).mp hsum.symm l (Finset.mem_univ l))]
        obtain ⟨c, hc⟩ := Ideal.exists_nu_eq_natCast (hK k ξ)
        refine ⟨c, ?_, fun y hy => (key y hy k).trans hc⟩
        have := ((K k).one_le_nu_stalkIdeal_iff ξ).mpr (hξtop k)
        rw [hc] at this
        exact_mod_cast this
      · refine ⟨1, one_pos, fun y hy => absurd ?_ hne⟩
        rcases hB with hB | hB
        · rw [hB, Subscheme.pts_empty] at hy
          exact hy.elim
        · exact Subscheme.exists_isGenericPoint hB.2
    -- (B*) for each factor
    have hBstar : ∀ k (y : t.X'), Ideal.nu ((Subscheme.weakTransform t (K k)).stalkIdeal y) ≤
        Ideal.nu ((K k).stalkIdeal (t.f y)) := fun k y =>
      MonoidalTransformation.nu_weakTransform_le hZ (K k) (hK k) hB t (fun x hx x' hx' => by
        obtain ⟨c, -, hc⟩ := hconst k
        rw [hc x hx, hc x' hx']) y
    have hprod : Subscheme.weakTransform t (∏ k, K k) = ∏ k, Subscheme.weakTransform t (K k) :=
      Subscheme.weakTransform_prod hZ hB t Finset.univ K hK
    have hZ' := (t.isNonsingular_and_isNonsingular_exceptional hZ hB.isNonsingular).1
    have hK' : ∀ k z, (Subscheme.weakTransform t (K k)).stalkIdeal z ≠ ⊥ := fun k z =>
      Subscheme.stalkIdeal_weakTransform_ne_bot hZ t (hK k) z
    have hsum_le : ∀ z', Ideal.nu ((∏ k, Subscheme.weakTransform t (K k)).stalkIdeal z') ≤
        Ideal.nu ((∏ k, K k).stalkIdeal (t.f z')) := fun z' => by
      rw [Subscheme.nu_stalkIdeal_prod hZ', Subscheme.nu_stalkIdeal_prod hZ]
      exact Finset.sum_le_sum fun k _ => hBstar k z'
    -- the invariant passes to the weak transforms
    have hI' : ∀ z', (∃ k, (Subscheme.weakTransform t (K k)).stalkIdeal z' = ⊤) →
        Ideal.nu ((∏ k, Subscheme.weakTransform t (K k)).stalkIdeal z') < d := by
      rintro z' ⟨k, hk⟩
      by_cases hk0 : (K k).stalkIdeal (t.f z') = ⊤
      · exact (hsum_le z').trans_lt (hI _ ⟨k, hk0⟩)
      · exact (Subscheme.nu_stalkIdeal_prod_lt hZ hZ' (fun l => hK' l z') (fun l => hK l _)
          (fun l => hBstar l z') k hk hk0).trans_le (hgreat.2 ⟨_, rfl⟩)
    have hC' : ∀ z', (d : ℕ∞) ≤ Ideal.nu ((∏ k, Subscheme.weakTransform t (K k)).stalkIdeal z') →
        (t.f ≫ q).base z' ∈ C := fun z' h => by
      rw [Scheme.Hom.comp_apply]
      exact hC _ (h.trans (hsum_le z'))
    rw [hprod] at hMrest hRrest
    obtain ⟨h1, h2, h3⟩ := ih t.isAlgebraicScheme hZ' (t.f ≫ q) C _ _ hK' hI' hC' hMrest hRrest
    refine ⟨⟨hB, hconst, h1⟩, ⟨hB.isReduced, ?_, h2⟩, h3⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hC z (hBeq z hz).ge

end MonoidalSuccession

/-! ### One round of the proof of Corollary 1, and the induction on `d` -/

namespace MainTheorem.Ch0

variable {e : ℕ}

/-- **One round of the proof of Corollary 1** (p. 144).  Let `d ≥ 1` be the maximum of `ν((∏_j J_j)_x)` for the
points `x` at which no `J_j` is trivial (attained at `x₀`).  Then there is a succession `{f_i}` of `X` with
property (1) of Corollary 1 such that, at every point `y` of the last scheme at which no `J_j(r)` is trivial,
`ν((∏_j J_j(r))_y) < d` ("either `d` gets reduced, or (2) is achieved").

Proof, as printed: `T = {x | ν((∏ J_j)_x) ≥ d}` is closed (upper semicontinuity of `ν`); `S = T ∩ O`, where `O` is the
open set of the points at which some `J_j` is trivial, is closed, because it is stable under specialization (at a
specialization in `T − O` the order of the product would exceed `d`, `Subscheme.nu_stalkIdeal_prod_lt`;
`isClosed_inter_of_specializes`); `T − S = T ∩ ⋂_j V(J_j)` is closed.  Main Theorem II with the remark of p. 143
(`exists_isMainIIZero_of_isAlgebraicScheme`) is applied to `∏ J_j` on `X − S` with `E₀ = ∅` (there `d` is the
maximum of `ν`); the stage analysis (`MonoidalSuccession.isTrivializingSteps_of_isMainIIZero`) gives (1) and shows
that the centers are mapped into `T − S`; the succession extends to `X`
(`MonoidalSuccession.exists_extension_weak`), and over `S` the extended succession is a local isomorphism, so that
some `J_j(r)` is trivial at the points over `S` (`MonoidalSuccession.stalkIdeal_weakTransformFamily_eq_top_iff`). -/
theorem exists_isTrivializingSteps_step [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (J : Fin e → Subscheme X) (hJ : ∀ k x, (J k).stalkIdeal x ≠ ⊥) (d : ℕ) (hd1 : 1 ≤ d)
    (hbound : ∀ x, (∀ k, (J k).stalkIdeal x ≠ ⊤) → Ideal.nu ((∏ k, J k).stalkIdeal x) ≤ d)
    (x₀ : X) (hx₀ : ∀ k, (J k).stalkIdeal x₀ ≠ ⊤) (hx₀d : Ideal.nu ((∏ k, J k).stalkIdeal x₀) = d) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), IsAlgebraicScheme Y ∧ Y.IsNonsingular ∧
      s.IsTrivializingSteps J ∧ (∀ k y, (s.weakTransformFamily J k).stalkIdeal y ≠ ⊥) ∧
      ∀ y, (∀ k, (s.weakTransformFamily J k).stalkIdeal y ≠ ⊤) →
        Ideal.nu ((∏ k, s.weakTransformFamily J k).stalkIdeal y) < d := by
  classical
  have := IsAlgebraicScheme.noetherianSpace X
  -- the closed set `T`, the open set `O` of the points where some `J_j` is trivial, `S = T ∩ O`
  set T : Set X := {x | (d : ℕ∞) ≤ Ideal.nu ((∏ k, J k).stalkIdeal x)}
  set O : Set X := {x | ∃ k, (J k).stalkIdeal x = ⊤}
  have hT : IsClosed T := Subscheme.isClosed_setOf_le_nu_stalkIdeal hX _ _
  have hOeq : O = ⋃ k, ((J k).pts)ᶜ := by
    ext x
    simp only [O, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_compl_iff,
      Subscheme.mem_pts_iff_stalkIdeal_ne_top, not_not]
  have hO : IsOpen O := hOeq ▸ isOpen_iUnion fun k => (J k).support.isClosed.isOpen_compl
  have hsemi : ∀ x y : X, x ⤳ y → ∀ l,
      Ideal.nu ((J l).stalkIdeal x) ≤ Ideal.nu ((J l).stalkIdeal y) := fun x y hxy l =>
    hxy.mem_closed (Subscheme.isClosed_setOf_le_nu_stalkIdeal hX (J l) _)
      (show Ideal.nu ((J l).stalkIdeal x) ≤ Ideal.nu ((J l).stalkIdeal x) from le_rfl)
  -- `S` is closed: it is stable under specialization
  have hS : IsClosed (T ∩ O) := by
    refine isClosed_inter_of_specializes hT hO fun x hx y hxy => ?_
    obtain ⟨hxT, k, hk⟩ := hx
    by_contra hyO
    have hyG : ∀ l, (J l).stalkIdeal y ≠ ⊤ := fun l h => hyO ⟨l, h⟩
    have hlt := Subscheme.nu_stalkIdeal_prod_lt hX hX (fun l => hJ l x) (fun l => hJ l y)
      (hsemi x y hxy) k hk (hyG k)
    exact lt_irrefl _ ((hxT.trans_lt hlt).trans_le (hbound y hyG))
  -- the open subscheme `X − S`
  let U : X.Opens := ⟨(T ∩ O)ᶜ, hS.isOpen_compl⟩
  have : IsAlgebraicScheme U.toScheme := isAlgebraicScheme_of_isOpenImmersion U.ι
  have hU : U.toScheme.IsNonsingular := LocSucc.isNonsingular U.ι hX
  have hmemU : ∀ z : U.toScheme, U.ι z ∉ T ∩ O := fun z => by
    have : U.ι z ∈ Set.range U.ι := ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι] at this
    exact this
  obtain ⟨Jb, hJb⟩ : ∃ Jb : Fin e → Subscheme U.toScheme,
      Jb = fun k => Subscheme.totalTransform U.ι (J k) := ⟨_, rfl⟩
  have hnuJb : ∀ k z, Ideal.nu ((Jb k).stalkIdeal z) = Ideal.nu ((J k).stalkIdeal (U.ι z)) :=
    fun k z => by
      rw [hJb]
      exact FlatPreimm.nu_stalkIdeal_totalTransform U.ι (J k) z
  have hJbne : ∀ k z, (Jb k).stalkIdeal z ≠ ⊥ := fun k z => by
    rw [hJb, FlatPreimm.stalkIdeal_totalTransform, Ne,
      Ideal.map_eq_bot_iff_of_injective (FlatPreimm.stalkEquiv U.ι z).injective]
    exact hJ k _
  have htopJb : ∀ k z, (Jb k).stalkIdeal z = ⊤ ↔ (J k).stalkIdeal (U.ι z) = ⊤ := fun k z => by
    rw [Subscheme.stalkIdeal_eq_top_iff_nu_eq_zero, Subscheme.stalkIdeal_eq_top_iff_nu_eq_zero,
      hnuJb]
  have hnuP : ∀ z, Ideal.nu ((∏ k, Jb k).stalkIdeal z) =
      Ideal.nu ((∏ k, J k).stalkIdeal (U.ι z)) := fun z => by
    rw [Subscheme.nu_stalkIdeal_prod hU, Subscheme.nu_stalkIdeal_prod hX]
    exact Finset.sum_congr rfl fun k _ => hnuJb k z
  -- `d` is the maximum of `ν(∏ J_j)` on `X − S`
  have hgreat : IsGreatest (Set.range fun z => Ideal.nu ((∏ k, Jb k).stalkIdeal z)) (d : ℕ∞) := by
    have hx₀U : x₀ ∈ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro ⟨-, k, hk⟩
      exact hx₀ k hk
    obtain ⟨z₀, hz₀⟩ := hx₀U
    refine ⟨⟨z₀, ?_⟩, ?_⟩
    · show Ideal.nu ((∏ k, Jb k).stalkIdeal z₀) = d
      rw [hnuP, hz₀, hx₀d]
    · rintro _ ⟨z, rfl⟩
      show Ideal.nu ((∏ k, Jb k).stalkIdeal z) ≤ d
      rw [hnuP]
      by_cases hG : ∀ k, (J k).stalkIdeal (U.ι z) ≠ ⊤
      · exact hbound _ hG
      · push Not at hG
        exact (not_le.mp fun h => hmemU z ⟨h, hG⟩).le
  -- Main Theorem II on `X − S`, for `∏ J_j` and `E₀ = ∅`
  obtain ⟨Yb, sb, hM, hR⟩ := exists_isMainIIZero_of_isAlgebraicScheme U.toScheme hU (∏ k, Jb k)
    (Subscheme.stalkIdeal_prod_ne_bot hU Finset.univ hJbne) d hgreat hd1 Subscheme.empty
    Subscheme.isReduced_empty Subscheme.isEverywhereCodimOne_empty
    (Subscheme.hasOnlyNormalCrossings_empty hU)
  -- the closed set `C = T − S = T ∩ ⋂_j V(J_j)`
  let C : Set X := T ∩ ⋂ k, (J k).pts
  obtain ⟨hITSb, hccb, hltb⟩ := sb.isTrivializingSteps_of_isMainIIZero d inferInstance hU U.ι C Jb _
    hJbne
    (fun z ⟨k, hk⟩ => by
      rw [hnuP]
      exact not_le.mp fun h => hmemU z ⟨h, k, (htopJb k z).mp hk⟩)
    (fun z hz => by
      rw [hnuP] at hz
      exact ⟨hz, Set.mem_iInter.mpr fun k =>
        Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr fun hk => hmemU z ⟨hz, k, hk⟩⟩)
    hM hR
  have hCcl : IsClosed C := hT.inter (isClosed_iInter fun k => (J k).support.isClosed)
  have hCS : ∀ x ∈ C, x ∉ T ∩ O := fun x hx ⟨_, k, hk⟩ =>
    Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp (Set.mem_iInter.mp hx.2 k) hk
  have hCU : C ⊆ Set.range U.ι.base := fun x hx => by
    show x ∈ Set.range U.ι
    rw [Scheme.Opens.range_ι]
    exact hCS x hx
  -- the extension of the succession to `X`
  obtain ⟨Y, sY, j', hfl, hpre, -, hrange', hccY, hfam⟩ := sb.exists_extension_weak U.ι C hCcl hCU hccb
  obtain ⟨hpull, htransfer⟩ := hfam J
  rw [← hJb] at hpull htransfer
  have hITS := htransfer hITSb
  obtain ⟨hYa, hY, hJY⟩ := sY.isNonsingular_of_isTrivializingSteps inferInstance hX J hJ hITS
  refine ⟨Y, sY, hYa, hY, hITS, hJY, fun y hy => ?_⟩
  by_cases hyr : y ∈ Set.range j'.base
  · obtain ⟨z, hz⟩ := hyr
    have hyz : y = j' z := hz.symm
    subst hyz
    rw [← FlatPreimm.nu_stalkIdeal_totalTransform j' (∏ k, sY.weakTransformFamily J k) z,
      Subscheme.totalTransform_prod, Finset.prod_congr rfl fun k _ => hpull k]
    exact hltb z
  · exfalso
    have hc : sY.composite.base y ∈ T ∩ O := by
      by_contra hc
      apply hyr
      rw [hrange']
      show sY.composite.base y ∈ Set.range U.ι
      rw [Scheme.Opens.range_ι]
      exact hc
    obtain ⟨k, hk⟩ := hc.2
    exact hy k ((MonoidalSuccession.stalkIdeal_weakTransformFamily_eq_top_iff sY C hccY J y
      (fun h => hCS _ h hc) k).mpr hk)

/-- **The induction on `d` of the proof of Corollary 1** (p. 144): if `ν((∏_j J_j)_x) ≤ D` at all the points at which
no `J_j` is trivial, there is a succession with the properties (1) and (2) of Corollary 1.  For `D = 0` there is no
such point (there `ν(∏ J_j) ≥ e ≥ 1`), and the empty succession does; otherwise, if the bound `D` is attained, one round
(`exists_isTrivializingSteps_step`) lowers it, and the successions are concatenated. -/
theorem exists_isTrivializingSteps_of_le [Hironaka.HironakaCitedResults.{u}] (he : 1 ≤ e) (D : ℕ) :
    ∀ (X : Scheme.{u}) (_hXa : IsAlgebraicScheme X) (_hX : X.IsNonsingular) (J : Fin e → Subscheme X),
      (∀ k x, (J k).stalkIdeal x ≠ ⊥) →
      (∀ x, (∀ k, (J k).stalkIdeal x ≠ ⊤) → Ideal.nu ((∏ k, J k).stalkIdeal x) ≤ D) →
      ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsTrivializingSteps J ∧
        ∀ y, ∃ k, (s.weakTransformFamily J k).stalkIdeal y = ⊤ := by
  induction D with
  | zero =>
    intro X _ hX J _ hbound
    refine ⟨X, MonoidalSuccession.nil X, trivial, fun x => ?_⟩
    by_contra h
    push Not at h
    have h1 : 1 ≤ Ideal.nu ((J ⟨0, he⟩).stalkIdeal x) :=
      ((J _).one_le_nu_stalkIdeal_iff x).mpr (h _)
    have h2 : Ideal.nu ((J ⟨0, he⟩).stalkIdeal x) ≤ Ideal.nu ((∏ k, J k).stalkIdeal x) := by
      rw [Subscheme.nu_stalkIdeal_prod hX]
      exact Finset.single_le_sum (f := fun i => Ideal.nu ((J i).stalkIdeal x)) (fun _ _ => zero_le)
        (Finset.mem_univ _)
    have := (h1.trans h2).trans (hbound x h)
    exact absurd this (by norm_num)
  | succ D ih =>
    intro X hXa hX J hJ hbound
    have hle : ∀ a : ℕ∞, a < ((D + 1 : ℕ) : ℕ∞) → a ≤ D := fun a h => by
      induction a using ENat.recTopCoe with
      | top => exact absurd h (not_lt.mpr le_top)
      | coe n =>
        have : n < D + 1 := by exact_mod_cast h
        exact_mod_cast Nat.lt_succ_iff.mp this
    by_cases hmax : ∃ x₀, (∀ k, (J k).stalkIdeal x₀ ≠ ⊤) ∧
        Ideal.nu ((∏ k, J k).stalkIdeal x₀) = ((D + 1 : ℕ) : ℕ∞)
    · obtain ⟨x₀, hx₀, hx₀d⟩ := hmax
      obtain ⟨Y, sY, hYa, hY, hITS, hJY, hlt⟩ :=
        exists_isTrivializingSteps_step X hX J hJ (D + 1) (by omega) hbound x₀ hx₀ hx₀d
      obtain ⟨Z, s₂, h₂, h₂'⟩ := ih Y hYa hY _ hJY fun y hy => hle _ (hlt y hy)
      refine ⟨Z, sY.append s₂, sY.isTrivializingSteps_append s₂ J hITS h₂, fun z => ?_⟩
      rw [sY.weakTransformFamily_append s₂ J]
      exact h₂' z
    · push Not at hmax
      exact ih X hXa hX J hJ fun x hx => hle _ ((hbound x hx).lt_of_ne (hmax x hx))

end MainTheorem.Ch0

end Hironaka
