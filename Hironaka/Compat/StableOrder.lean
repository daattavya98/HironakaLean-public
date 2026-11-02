/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch3.JStability
public import Hironaka.Compat.BlowupDim
public import Hironaka.Compat.RegularGraded
public import Hironaka.Compat.StalkFrameStep

/-!
# The order of a `J`-stable element along a permissible center (Ch. IV, p. 302)

> "The prime ideal `Q̂_s` of `B̄'_s` (i.e., that of `B̂_s`) in `Ŝ_s` contains the element `z_s` of
> `Ŝ_s` and it is a permissible center for `Ĵ_j(s)`.  It follows that `g_{jk}(s) ∈ Q̂^{ν_{jk}}`"
> (p. 302)

Ring-level content: a `J`-stable element `f` of a regular local ring `R` with residue field of
characteristic zero has the same order along a non-zero permissible prime center `Q` as along the
maximal ideal.  Definition 11 of Ch. III (`IsJStable`) at `ᾱ = 0` is applied to the sequence
`R, R₁, R₁, …`, where `R₁` is a monoidal transform of `R` with center `Q` which is residually
separable algebraic over `R` (a closed point of the fibre of `R[x⁻¹Q]` over the maximal ideal of
`R`: its residue field is finite over that of `R` by Zariski's lemma, and separable as the
characteristic is `0`) and the later steps are trivial.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

namespace StableOrder

noncomputable section

section Existence

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- **A residually separable algebraic monoidal transform with a given center.**  For a prime
`Q ≠ 0` of a regular local ring `R` with residue field of characteristic zero and `R/Q` regular,
there is a monoidal transform of `R` with center `Q` which is residually separable algebraic over
`R`.  (Choose `x ∈ Q ∖ M²`, a maximal ideal `M'` of `R[x⁻¹Q]` over `M`, and use Zariski's lemma and
`char = 0`.) -/
theorem exists_monoidalTransform_isResiduallySeparableAlgebraic [CharZero (ResidueField R)]
    (Q : Ideal R) [hQ : Q.IsPrime] (hQ0 : Q ≠ ⊥) (hQreg : IsRegularLocalRing (R ⧸ Q)) :
    ∃ T : MonoidalTransform R Q, RingHom.IsResiduallySeparableAlgebraic T.toRing := by
  obtain ⟨S, T, hSM, hScard, hTS, hTQ⟩ := exists_finset_span_eq_prime R Q hQreg
  have hS : IsRegularSystemOfParameters R S := by
    refine ⟨hSM, ?_⟩
    rw [hScard, IsRegularLocalRing.spanFinrank_maximalIdeal]
  have hext : ExtendsToRSOP R T := ⟨S, hTS, hS⟩
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hQ0 (by rw [← hTQ]; simp)
  obtain ⟨x, hxT⟩ := hTne
  have hxQ : x ∈ Q := hTQ ▸ Ideal.subset_span hxT
  have hx2 := hext.notMem_maximalIdeal_sq hxT
  have hQM : Q ≤ maximalIdeal R := le_maximalIdeal hQ.ne_top
  have hx0 : x ≠ 0 := fun h => hx2 (h ▸ zero_mem _)
  have hne := map_maximalIdeal_blowupAlgebra_ne_top hxQ hQM hx2
  obtain ⟨M', hM', hle⟩ := Ideal.exists_le_maximal _ hne
  let T₁ : MonoidalTransform R Q :=
    { x := x, x_mem := hxQ, x_ne_zero := hx0, M' := M', isPrime := hM'.isPrime, le := hle }
  refine ⟨T₁, ?_⟩
  have hmax : T₁.M'.IsMaximal := hM'
  have halg := (T₁.isMaximal_iff_isResiduallyAlgebraic).mp hmax
  unfold RingHom.IsResiduallyAlgebraic at halg
  unfold RingHom.IsResiduallySeparableAlgebraic
  let _ := (ResidueField.map T₁.toRing).toAlgebra
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- A monoidal transform with the unit ideal as center exists (it is `R` itself). -/
theorem exists_monoidalTransform_top : Nonempty (MonoidalTransform R ⊤) := by
  set K := FractionRing R
  have hgen : ∀ b : blowupAlgebra R ⊤ 1, ∃ r : R, (b : K) = algebraMap R K r := by
    intro b
    have hb := b.2
    unfold blowupAlgebra at hb
    refine Algebra.adjoin_induction (p := fun y _ => ∃ r : R, y = algebraMap R K r) ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨q, -, rfl⟩
      exact ⟨q, by simp; rfl⟩
    · intro r; exact ⟨r, rfl⟩
    · rintro _ _ _ _ ⟨r, rfl⟩ ⟨r', rfl⟩; exact ⟨r + r', by simp⟩
    · rintro _ _ _ _ ⟨r, rfl⟩ ⟨r', rfl⟩; exact ⟨r * r', by simp⟩
  have hinj : Function.Injective (algebraMap R (blowupAlgebra R ⊤ 1)) := by
    intro a b hab
    have := congrArg (fun y : blowupAlgebra R ⊤ 1 => (y : K)) hab
    simp only [Subalgebra.coe_algebraMap] at this
    exact IsFractionRing.injective R K this
  have hsurj : Function.Surjective (algebraMap R (blowupAlgebra R ⊤ 1)) := by
    intro b
    obtain ⟨r, hr⟩ := hgen b
    exact ⟨r, Subtype.ext (by simpa using hr.symm)⟩
  have hne : (maximalIdeal R).map (algebraMap R (blowupAlgebra R ⊤ 1)) ≠ ⊤ := by
    intro h
    have := Ideal.comap_map_of_bijective (f := algebraMap R (blowupAlgebra R ⊤ 1))
      ⟨hinj, hsurj⟩ (I := maximalIdeal R)
    rw [h, Ideal.comap_top] at this
    exact (maximalIdeal.isMaximal R).ne_top this.symm
  obtain ⟨M', hM', hle⟩ := Ideal.exists_le_maximal _ hne
  exact ⟨{ x := 1, x_mem := Submodule.mem_top, x_ne_zero := one_ne_zero, M' := M'
           isPrime := hM'.isPrime, le := hle }⟩

end Existence


section Sequences

/-- The strict transform of an ideal with center `P = R` is `J R'` (the generators `x⁻ᵛ f` have
`x` a unit); cf. the private `strictTransformIdeal_eq_map_of_eq_top` of Ch. III. -/
theorem strictTransformIdeal_eq_map_of_eq_top {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {P : Ideal R} (hP : P = ⊤) (T : MonoidalTransform R P) (J : Ideal R) :
    strictTransformIdeal T J = J.map T.toRing := by
  subst hP
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.map_le_iff_le_comap.mpr fun f hf => ?_)
  · rintro y ⟨x, hx, f, hf, ν, -, hy⟩
    rw [Ideal.map_top, Ideal.span_singleton_eq_top] at hx
    obtain ⟨w, hw⟩ := hx.pow ν
    rw [← hw] at hy
    have : y = ↑w⁻¹ * T.toRing f := by rw [← hy, ← mul_assoc, Units.inv_mul, one_mul]
    rw [SetLike.mem_coe, this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hf)
  · refine Ideal.subset_span ⟨1, by rw [Ideal.map_top, Ideal.span_singleton_one], f, hf, 0,
      by simp, by rw [pow_zero, one_mul]⟩

/-- The constant sequence of trivial monoidal transforms (center `R`) of `R`, carrying the ideal
`J` (p. 209: the monoidal transform with center `R` is `R` itself). -/
def constSeq {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] (J : Ideal R)
    {c : Ideal R} (hc : c = ⊤) (T₀ : MonoidalTransform R c) [IsLocalHom T₀.toRing] :
    MonoidalSequence.{u} where
  ring _ := R
  ideal _ := J
  center _ := c
  transform _ := T₀
  equiv _ := (RingEquiv.ofBijective T₀.toRing (T₀.bijective_toRing_of_eq_top hc)).symm
  ideal_succ _ := by
    show J = (strictTransformIdeal T₀ J).map
      (RingEquiv.ofBijective T₀.toRing (T₀.bijective_toRing_of_eq_top hc)).symm
    rw [strictTransformIdeal_eq_map_of_eq_top hc T₀ J, ← Ideal.map_coe, Ideal.map_map]
    conv_lhs => rw [← Ideal.map_id J]
    congr 1
    ext r
    exact ((RingEquiv.ofBijective T₀.toRing (T₀.bijective_toRing_of_eq_top hc)).symm_apply_apply
      r).symm

/-- The trivial monoidal transforms are permissible (the center is the unit ideal). -/
theorem constSeq_isPermissible {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (J : Ideal R) {c : Ideal R} (hc : c = ⊤) (T₀ : MonoidalTransform R c)
    [IsLocalHom T₀.toRing] : (constSeq J hc T₀).IsPermissible := fun _ => Or.inl hc

/-- The sequence obtained by prepending the monoidal transform `T` of `R` (with center `P`) to a
sequence `Sq` of monoidal transforms of `T`. -/
def consSeq {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] (J : Ideal R)
    {P : Ideal R} (T : MonoidalTransform R P) [IsLocalHom T.toRing]
    (Sq : MonoidalSequence.{u}) (e : T.ring ≃+* Sq.ring 0)
    (h0 : Sq.ideal 0 = (strictTransformIdeal T J).map e) : MonoidalSequence.{u} where
  ring n := match n with
    | 0 => R
    | n + 1 => Sq.ring n
  commRing n := match n with
    | 0 => inferInstanceAs (CommRing R)
    | n + 1 => inferInstanceAs (CommRing (Sq.ring n))
  isRegularLocalRing n := match n with
    | 0 => inferInstanceAs (IsRegularLocalRing R)
    | n + 1 => inferInstanceAs (IsRegularLocalRing (Sq.ring n))
  isDomain n := match n with
    | 0 => inferInstanceAs (IsDomain R)
    | n + 1 => inferInstanceAs (IsDomain (Sq.ring n))
  ideal n := match n with
    | 0 => J
    | n + 1 => Sq.ideal n
  center n := match n with
    | 0 => P
    | n + 1 => Sq.center n
  transform n := match n with
    | 0 => T
    | n + 1 => Sq.transform n
  equiv n := match n with
    | 0 => e
    | n + 1 => Sq.equiv n
  ideal_succ n := match n with
    | 0 => h0
    | n + 1 => Sq.ideal_succ n


/-- A monoidal transform with center the unit ideal is residually separable algebraic (it is an
isomorphism, p. 209). -/
theorem isResiduallySeparableAlgebraic_toRing_of_eq_top {R : Type u}
    [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R} (hP : P = ⊤)
    (T : MonoidalTransform R P) [IsLocalHom T.toRing] :
    RingHom.IsResiduallySeparableAlgebraic T.toRing := by
  unfold RingHom.IsResiduallySeparableAlgebraic
  let _ := (ResidueField.map T.toRing).toAlgebra
  have hbij := T.bijective_toRing_of_eq_top hP
  refine ⟨fun w => ?_⟩
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective w
  obtain ⟨r, rfl⟩ := hbij.2 z
  have : algebraMap (ResidueField R) (ResidueField T.ring) (IsLocalRing.residue _ r) =
      IsLocalRing.residue _ (T.toRing r) := ResidueField.map_residue _ _
  rw [← this]
  exact isSeparable_algebraMap _

/-- The sequence `R, R₁, R₁, …`: the monoidal transform `T` of `R` followed by trivial monoidal
transforms of (a copy `R₁'` of) `R₁`. -/
def consConstSeq {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (J : Ideal R) {P : Ideal R} (T : MonoidalTransform R P) [IsLocalHom T.toRing]
    {R₁ : Type u} [CommRing R₁] [IsRegularLocalRing R₁] [IsDomain R₁] (e₁ : T.ring ≃+* R₁)
    {c : Ideal R₁} (hc : c = ⊤) (T₀ : MonoidalTransform R₁ c) [IsLocalHom T₀.toRing] :
    MonoidalSequence.{u} :=
  consSeq J T (constSeq ((strictTransformIdeal T J).map e₁) hc T₀) e₁
    rfl

/-- The sequence `R, R₁, R₁, …` is permissible if its first center is. -/
theorem consConstSeq_isPermissible {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {J : Ideal R} {P : Ideal R} (hP : IsPermissibleCenter R J P)
    (T : MonoidalTransform R P) [IsLocalHom T.toRing]
    {R₁ : Type u} [CommRing R₁] [IsRegularLocalRing R₁] [IsDomain R₁] (e₁ : T.ring ≃+* R₁)
    {c : Ideal R₁} (hc : c = ⊤) (T₀ : MonoidalTransform R₁ c) [IsLocalHom T₀.toRing] :
    (consConstSeq J T e₁ hc T₀).IsPermissible := fun n => match n with
  | 0 => hP
  | _ + 1 => constSeq_isPermissible _ hc T₀ 0

/-- The sequence `R, R₁, R₁, …` is residually separable algebraic if its first step is. -/
theorem consConstSeq_isResiduallySeparableAlgebraic {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] (J : Ideal R) {P : Ideal R} (T : MonoidalTransform R P)
    [IsLocalHom T.toRing] (hsep : RingHom.IsResiduallySeparableAlgebraic T.toRing)
    {R₁ : Type u} [CommRing R₁] [IsRegularLocalRing R₁] [IsDomain R₁] (e₁ : T.ring ≃+* R₁)
    {c : Ideal R₁} (hc : c = ⊤) (T₀ : MonoidalTransform R₁ c) [IsLocalHom T₀.toRing] :
    (consConstSeq J T e₁ hc T₀).IsResiduallySeparableAlgebraic := fun n =>
  match n with
  | 0 => hsep
  | _ + 1 => isResiduallySeparableAlgebraic_toRing_of_eq_top hc T₀

theorem ideal_map_refl {A : Type u} [CommRing A] (I : Ideal A) :
    I.map (RingEquiv.refl A) = I := by
  rw [← Ideal.map_coe]
  exact Ideal.map_id I

/-- A `J`-stable element has, along a permissible center `P ≠ R` admitting a residually separable
algebraic monoidal transform `R₁`, the order it has along the maximal ideal (Definition 11 of
Ch. III at `ᾱ = 0`, for the sequence `R, R₁, R₁, …`). -/
theorem ordElem_eq_of_monoidalTransform {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] {J : Ideal R} {f : R} (hf : IsJStable J f) {P : Ideal R}
    (hP : IsPermissibleCenter R J P) (hPtop : P ≠ ⊤) (T : MonoidalTransform R P)
    [IsLocalHom T.toRing] (hsep : RingHom.IsResiduallySeparableAlgebraic T.toRing)
    {R₁ : Type u} [CommRing R₁] [IsRegularLocalRing R₁] [IsDomain R₁] (e₁ : T.ring ≃+* R₁)
    {c : Ideal R₁} (hc : c = ⊤) (T₀ : MonoidalTransform R₁ c) [IsLocalHom T₀.toRing] :
    Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f :=
  (hf (consConstSeq J T e₁ hc T₀) (RingEquiv.refl R) (ideal_map_refl J).symm
    (consConstSeq_isPermissible hP T e₁ hc T₀)
    (consConstSeq_isResiduallySeparableAlgebraic J T hsep e₁ hc T₀) 0 rfl rfl
    (fun _ _ _ => rfl) f rfl).2 hPtop

end Sequences

section Bot

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- `y ∈ P^d` gives `y / x^d ∈ R[x⁻¹P]`. -/
theorem div_pow_mem_blowupAlgebra {P : Ideal R} {x : R} (d : ℕ) {y : R}
    (hy : y ∈ P ^ d) :
    algebraMap R (FractionRing R) y / algebraMap R (FractionRing R) x ^ d ∈
      blowupAlgebra R P x := by
  induction d generalizing y with
  | zero =>
    rw [pow_zero, div_one]
    exact Subalgebra.algebraMap_mem _ y
  | succ d ih =>
    rw [pow_succ'] at hy
    refine Submodule.mul_induction_on (C := fun y => algebraMap R (FractionRing R) y /
      algebraMap R (FractionRing R) x ^ (d + 1) ∈ blowupAlgebra R P x) hy ?_ ?_
    · intro m hm n hn
      have h1 : algebraMap R (FractionRing R) m / algebraMap R (FractionRing R) x ∈
          blowupAlgebra R P x := Algebra.subset_adjoin ⟨m, hm, rfl⟩
      have := Subalgebra.mul_mem _ h1 (ih hn)
      convert this using 1
      by_cases hx0 : algebraMap R (FractionRing R) x = 0
      · simp [hx0]
      · rw [map_mul, pow_succ']
        field_simp
    · intro a b ha hb
      rw [map_add, add_div]
      exact add_mem ha hb

/-- Elements of `M R[x⁻¹M]` are fractions `c / xᴺ` with `c ∈ M^{N+1}`. -/
theorem exists_mem_pow_succ_of_mem_map_maximalIdeal {x : R} (hxM : x ∈ maximalIdeal R) (hx0 : x ≠ 0)
    {w : blowupAlgebra R (maximalIdeal R) x}
    (hw : w ∈ (maximalIdeal R).map (algebraMap R (blowupAlgebra R (maximalIdeal R) x))) :
    ∃ (N : ℕ) (c : R), c ∈ maximalIdeal R ^ (N + 1) ∧
      (w : FractionRing R) * algebraMap R (FractionRing R) x ^ N =
        algebraMap R (FractionRing R) c := by
  unfold Ideal.map at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, hm, rfl⟩ := hy
    exact ⟨0, m, by rwa [zero_add, pow_one], by simp⟩
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add w₁ w₂ _ _ h₁ h₂ =>
    obtain ⟨N₁, c₁, hc₁, e₁⟩ := h₁
    obtain ⟨N₂, c₂, hc₂, e₂⟩ := h₂
    refine ⟨N₁ + N₂, c₁ * x ^ N₂ + c₂ * x ^ N₁, add_mem ?_ ?_, ?_⟩
    · have := Ideal.mul_mem_mul hc₁ (Ideal.pow_mem_pow hxM N₂)
      rw [← pow_add] at this
      convert this using 2
      ring
    · have := Ideal.mul_mem_mul hc₂ (Ideal.pow_mem_pow hxM N₁)
      rw [← pow_add] at this
      convert this using 2
      ring
    · simp only [AddMemClass.coe_add, map_add, map_mul, map_pow]
      rw [← e₁, ← e₂]
      ring
  | smul a w _ h =>
    obtain ⟨N, c, hc, e⟩ := h
    obtain ⟨m, g, hg, hag⟩ :=
      MonoidalTransform.exists_mul_pow_eq_of_mem_blowupAlgebra hxM hx0 a.2
    refine ⟨N + m, g * c, ?_, ?_⟩
    · have := Ideal.mul_mem_mul (Ideal.pow_right_mono (le_refl _) m hg) hc
      rw [← pow_add] at this
      convert this using 2
      ring
    · simp only [smul_eq_mul, MulMemClass.coe_mul, map_mul]
      rw [← hag, ← e]
      ring

omit [IsDomain R] in
theorem ordElem_pow_maximalIdeal (f : R) (n : ℕ) :
    Ideal.ordElem (maximalIdeal R) (f ^ n) = n * Ideal.ordElem (maximalIdeal R) f := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    have : (1 : R) ∉ maximalIdeal R ^ (0 + 1) := by
      rw [zero_add, pow_one]
      exact fun h => (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h)
    exact le_antisymm (by exact_mod_cast Ideal.ordElem_le_of_notMem this) zero_le
  | succ n ih => rw [pow_succ, ordElem_mul_maximalIdeal, ih]; push_cast; ring

/-- The class of `g = f/x^d` is not nilpotent modulo `M R[x⁻¹M]`, where `d = ν_M(f)`. -/
theorem pow_notMem_map_maximalIdeal {x f : R} (hxM : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) {d : ℕ} (hfd : Ideal.ordElem (maximalIdeal R) f = d)
    (g : blowupAlgebra R (maximalIdeal R) x)
    (hg : (g : FractionRing R) * algebraMap R (FractionRing R) x ^ d =
      algebraMap R (FractionRing R) f) (n : ℕ) :
    g ^ n ∉ (maximalIdeal R).map (algebraMap R (blowupAlgebra R (maximalIdeal R) x)) := by
  intro h
  have hx0 : x ≠ 0 := fun h0 => hx2 (h0 ▸ zero_mem _)
  obtain ⟨N, c, hc, e⟩ := exists_mem_pow_succ_of_mem_map_maximalIdeal hxM hx0 h
  have hK : f ^ n * x ^ N = c * x ^ (d * n) := by
    apply IsFractionRing.injective R (FractionRing R)
    simp only [map_mul, map_pow]
    rw [← hg] at *
    rw [SubmonoidClass.coe_pow] at e
    rw [← e]
    ring
  have h1 : Ideal.ordElem (maximalIdeal R) x = 1 :=
    Ideal.ordElem_eq_one_of_mem_of_notMem_sq (maximalIdeal.isMaximal R).ne_top hxM hx2
  have hL : Ideal.ordElem (maximalIdeal R) (f ^ n * x ^ N) = ((d * n + N : ℕ) : ℕ∞) := by
    rw [ordElem_mul_maximalIdeal, ordElem_pow_maximalIdeal, ordElem_pow_maximalIdeal, hfd, h1]
    push_cast
    ring
  have hR : c * x ^ (d * n) ∈ maximalIdeal R ^ (N + 1 + d * n) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow hxM _)
  have := Ideal.le_ordElem hR
  rw [← hK, hL] at this
  norm_cast at this
  omega

/-- `R[x⁻¹P]` is of finite type over `R` (`P` is finitely generated). -/
theorem finiteType_blowupAlgebra (P : Ideal R) (x : R) :
    Algebra.FiniteType R (blowupAlgebra R P x) := by
  classical
  rw [← Subalgebra.fg_iff_finiteType]
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian P : P.FG)
  refine ⟨s.image (fun p => algebraMap R (FractionRing R) p /
    algebraMap R (FractionRing R) x), ?_⟩
  rw [blowupAlgebra, Finset.coe_image]
  apply le_antisymm
  · exact Algebra.adjoin_mono (Set.image_mono (by rw [← hs]; exact Submodule.subset_span))
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨p, hp, rfl⟩
    rw [← hs] at hp
    induction hp using Submodule.span_induction with
    | mem y hy => exact Algebra.subset_adjoin ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      dsimp only at hy hz ⊢
      rw [map_add, add_div]
      exact add_mem hy hz
    | smul r y _ hy =>
      dsimp only at hy ⊢
      rw [smul_eq_mul, map_mul, mul_div_assoc]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) hy

omit [IsDomain R] in
/-- If no power of `g` in a finite-type algebra `B` over the local ring `R` lies in `M B`, there is
a maximal ideal of `B` over `M` not containing `g` (Jacobson property of the finite-type
`R/M`-algebra `B/M B`). -/
theorem exists_isMaximal_not_mem_of_forall_pow_notMem {B : Type u} [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] (g : B)
    (hg : ∀ n : ℕ, g ^ n ∉ (maximalIdeal R).map (algebraMap R B)) :
    ∃ M' : Ideal B, M'.IsMaximal ∧ (maximalIdeal R).map (algebraMap R B) ≤ M' ∧ g ∉ M' := by
  let I : Ideal B := (maximalIdeal R).map (algebraMap R B)
  let := Ideal.Quotient.algebraQuotientOfLEComap
    (R := R) (A := B) (p := maximalIdeal R) (P := I) (Ideal.map_le_iff_le_comap.mp le_rfl)
  have : IsScalarTower R (R ⧸ maximalIdeal R) (B ⧸ I) := inferInstance
  have : Algebra.FiniteType R (B ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ_surjective R I)
  have : Algebra.FiniteType (R ⧸ maximalIdeal R) (B ⧸ I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  obtain ⟨n, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType (R ⧸ maximalIdeal R) (B ⧸ I))
  have : IsJacobsonRing (R ⧸ maximalIdeal R) := by
    let := Ideal.Quotient.field (maximalIdeal R)
    infer_instance
  have : IsJacobsonRing (B ⧸ I) := isJacobsonRing_of_surjective ⟨ψ.toRingHom, hψ⟩
  have hnil : Ideal.Quotient.mk I g ∉ (⊥ : Ideal (B ⧸ I)).radical := by
    rintro ⟨k, hk⟩
    exact hg k (by
      rw [← map_pow, Ideal.mem_bot] at hk
      exact Ideal.Quotient.eq_zero_iff_mem.mp hk)
  rw [Ideal.radical_eq_jacobson, Ideal.jacobson] at hnil
  simp only [Submodule.mem_sInf, not_forall] at hnil
  obtain ⟨𝔫, ⟨-, h𝔫⟩, hg𝔫⟩ := hnil
  refine ⟨Ideal.comap (Ideal.Quotient.mk I) 𝔫, Ideal.comap_isMaximal_of_surjective _
    Ideal.Quotient.mk_surjective, fun w hw => ?_, hg𝔫⟩
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hw]
  exact zero_mem _

/-- A monoidal transform whose prime `M'` is maximal is residually separable algebraic in
characteristic zero. -/
theorem isResiduallySeparableAlgebraic_of_isMaximal [CharZero (ResidueField R)] {P : Ideal R}
    (T : MonoidalTransform R P) (hmax : T.M'.IsMaximal) :
    RingHom.IsResiduallySeparableAlgebraic T.toRing := by
  have halg := (T.isMaximal_iff_isResiduallyAlgebraic).mp hmax
  unfold RingHom.IsResiduallyAlgebraic at halg
  unfold RingHom.IsResiduallySeparableAlgebraic
  let _ := (ResidueField.map T.toRing).toAlgebra
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- If `g ∈ R[x⁻¹P]` with `xᵈ g = f` lies outside `M'`, the strict transform of `(f)` in the
monoidal transform is the unit ideal (`g` becomes a unit and `x⁻ᵈ f = g`). -/
theorem strictTransformIdeal_span_eq_top {P : Ideal R} (T : MonoidalTransform R P) {f : R} {d : ℕ}
    (hd : (d : ℕ∞) ≤ Ideal.ordElem P f) (g : blowupAlgebra R P T.x)
    (hgB : algebraMap R (blowupAlgebra R P T.x) T.x ^ d * g =
      algebraMap R (blowupAlgebra R P T.x) f) (hgM : g ∉ T.M') :
    strictTransformIdeal T (Ideal.span {f}) = ⊤ := by
  have hunit : IsUnit (algebraMap (blowupAlgebra R P T.x) T.ring g) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff T.ring T.M' g).mpr hgM
  have hy : T.xR ^ d * algebraMap (blowupAlgebra R P T.x) T.ring g = T.toRing f := by
    have := congrArg (algebraMap (blowupAlgebra R P T.x) T.ring) hgB
    simpa [MonoidalTransform.xR, MonoidalTransform.toRing, map_mul, map_pow] using this
  have hmem : algebraMap (blowupAlgebra R P T.x) T.ring g ∈
      strictTransformIdeal T (Ideal.span {f}) :=
    Ideal.subset_span ⟨T.xR, T.span_xR_eq_map, f, Ideal.mem_span_singleton_self f, d, hd, hy⟩
  exact Ideal.eq_top_of_isUnit_mem _ hmem hunit

/-- **A closed point of the fibre outside the vanishing locus of the initial form.**  If `M ≠ 0` and
`f ≠ 0` lies in `M`, there is a monoidal transform of `R` with center `M`, residually separable
algebraic over `R`, in which the strict transform of `(f)` is the unit ideal (the strict transform
`f/xᵈ`, `d = ν_M(f)`, is a unit at a closed point of the fibre outside `V(in(f))`). -/
theorem exists_monoidalTransform_strictTransformIdeal_eq_top [CharZero (ResidueField R)] {f : R}
    (hf0 : f ≠ 0) (hfM : f ∈ maximalIdeal R) (hM : maximalIdeal R ≠ ⊥) :
    ∃ (T : MonoidalTransform R (maximalIdeal R)),
      RingHom.IsResiduallySeparableAlgebraic T.toRing ∧
        strictTransformIdeal T (Ideal.span {f}) = ⊤ ∧
        1 ≤ Ideal.ordElem (maximalIdeal R) f := by
  have hreg : IsRegularLocalRing (R ⧸ maximalIdeal R) := by
    let := Ideal.Quotient.field (maximalIdeal R)
    infer_instance
  obtain ⟨x, hxM, hx2⟩ := exists_mem_notMem_maximalIdeal_sq (R := R) (P := maximalIdeal R)
    (maximalIdeal.isMaximal R).isPrime hreg hM
  have hx0 : x ≠ 0 := fun h0 => hx2 (h0 ▸ zero_mem _)
  have hord1 : (1 : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) f := by
    exact_mod_cast Ideal.le_ordElem (I := maximalIdeal R) (f := f) (ν := 1) (by simpa using hfM)
  have hfin : Ideal.ordElem (maximalIdeal R) f ≠ ⊤ := fun h =>
    hf0 ((Ideal.ordElem_eq_top_iff_eq_zero (maximalIdeal.isMaximal R).ne_top).mp h)
  obtain ⟨d, hd⟩ : ∃ d : ℕ, Ideal.ordElem (maximalIdeal R) f = d :=
    ⟨_, (ENat.natCast_toNat hfin).symm⟩
  have hfd : f ∈ maximalIdeal R ^ d := Ideal.mem_pow_of_ordElem hd
  set K := FractionRing R
  have hxK : algebraMap R K x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hx0
  let g : blowupAlgebra R (maximalIdeal R) x :=
    ⟨algebraMap R K f / algebraMap R K x ^ d, div_pow_mem_blowupAlgebra d hfd⟩
  have hg : (g : K) * algebraMap R K x ^ d = algebraMap R K f := by
    show algebraMap R K f / algebraMap R K x ^ d * _ = _
    exact div_mul_cancel₀ _ (pow_ne_zero d hxK)
  have := finiteType_blowupAlgebra (maximalIdeal R) x
  obtain ⟨M', hM', hle, hgM'⟩ := exists_isMaximal_not_mem_of_forall_pow_notMem g
    (pow_notMem_map_maximalIdeal hxM hx2 hd g hg)
  let T : MonoidalTransform R (maximalIdeal R) :=
    { x := x, x_mem := hxM, x_ne_zero := hx0, M' := M', isPrime := hM'.isPrime, le := hle }
  refine ⟨T, isResiduallySeparableAlgebraic_of_isMaximal T hM', ?_, hord1⟩
  have hgB : (algebraMap R (blowupAlgebra R (maximalIdeal R) x) x) ^ d * g =
      algebraMap R (blowupAlgebra R (maximalIdeal R) x) f := by
    apply Subtype.ext
    simpa [mul_comm] using hg
  exact strictTransformIdeal_span_eq_top T (by rw [hd]) g hgB hgM'

end Bot

section BotCase

theorem grIdeal_bot_eq_bot {A : Type u} [CommRing A] (I : Ideal A) :
    grIdeal I (⊥ : Ideal A) = ⊥ := by
  have h0 : initialForm I (0 : A) = 0 := by
    have htop : Ideal.ordElem I (0 : A) = ⊤ := Ideal.ordElem_eq_top_iff.mpr fun n => zero_mem _
    simp only [initialForm, htop, ↓reduceDIte]
  unfold grIdeal
  rw [Ideal.span_eq_bot]
  intro a ha
  obtain ⟨b, hb, rfl⟩ := ha
  have : b = 0 := by simpa using hb
  rw [this, h0]

/-- `ν*(0)` is constantly `∞`. -/
theorem nuI_bot {S : Type u} [CommRing S] [IsRegularLocalRing S] (i : ℕ+) :
    nuI S (⊥ : Ideal S) i = ⊤ := by
  refine ENat.eq_top_iff_forall_ge.mpr fun m => ?_
  have hsys : IsNuSystem S (⊥ : Ideal S) m ((i : ℕ) - 1)
      (fun _ => (0 : AssocGraded (maximalIdeal S))) := by
    refine ⟨fun j => ⟨?_, 0, Submodule.zero_mem _⟩, fun μ _ ψ _ => ?_⟩
    · rw [grIdeal_bot_eq_bot]; exact Submodule.zero_mem _
    · rw [grIdeal_bot_eq_bot]
      have : Ideal.span (Set.range fun _ : Fin ((i : ℕ) - 1) =>
          (0 : AssocGraded (maximalIdeal S))) = ⊥ := by
        rw [Ideal.span_eq_bot]
        rintro _ ⟨j, rfl⟩
        rfl
      rw [this]
  unfold nuI
  exact le_iSup₂_of_le m ⟨_, hsys⟩ le_rfl

theorem nuStar_bot (S : Type u) [CommRing S] [IsRegularLocalRing S] :
    nuStar S (⊥ : Ideal S) = toLex fun _ => ⊤ := by
  unfold nuStar
  congr 1
  funext i
  exact nuI_bot i

theorem t_bot (S : Type u) [CommRing S] [IsRegularLocalRing S] : t S (⊥ : Ideal S) = 0 := by
  have : muSet S (⊥ : Ideal S) = ∅ := by
    ext μ
    simp only [muSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    intro i hi
    rw [nuI_bot] at hi
    exact ENat.top_ne_natCast _ hi
  unfold t
  rw [this, Set.ncard_empty]

theorem isPermissibleCenter_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R]
    (_hreg : IsRegularLocalRing R) (J : Ideal R) (hJ : J ≤ maximalIdeal R) :
    IsPermissibleCenter R J (maximalIdeal R) := by
  refine Or.inr ⟨(maximalIdeal.isMaximal R).isPrime, hJ, ?_, ?_⟩
  · let := Ideal.Quotient.field (maximalIdeal R)
    infer_instance
  · have hmax : ((maximalIdeal R).map (Ideal.Quotient.mk J)).IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk J)
        Ideal.Quotient.mk_surjective (maximalIdeal.isMaximal R) with h | h
      · exfalso
        have := Ideal.comap_map_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
          (maximalIdeal R)
        rw [h, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker (I := J),
          sup_eq_left.mpr hJ] at this
        exact (maximalIdeal.isMaximal R).ne_top this.symm
      · exact h
    intro p
    let := Ideal.Quotient.field ((maximalIdeal R).map (Ideal.Quotient.mk J))
    exact Module.Free.of_divisionRing _ _

theorem strictTransformIdeal_bot {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (T : MonoidalTransform R (maximalIdeal R)) (hM : maximalIdeal R ≠ ⊥) :
    strictTransformIdeal T (⊥ : Ideal R) = ⊥ := by
  have hdom : IsDomain T.ring := inferInstance
  have hx0 : T.xR ≠ 0 := by
    intro h
    apply hM
    have : (maximalIdeal R).map T.toRing = ⊥ := by
      rw [← T.span_xR_eq_map, h, Ideal.span_singleton_eq_bot]
    refine eq_bot_iff.mpr fun m hm => ?_
    rw [Ideal.mem_bot]
    exact T.toRing_injective ((Ideal.mem_bot.mp (this ▸ Ideal.mem_map_of_mem _ hm)).trans
      (map_zero _).symm)
  refine le_bot_iff.mp (Ideal.span_le.mpr ?_)
  rintro y ⟨x, hx, f, hf, ν, -, hy⟩
  rw [Ideal.mem_bot] at hf
  subst hf
  rw [map_zero] at hy
  have hx' : x ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hx
    apply hx0
    rw [← Ideal.span_singleton_eq_bot, T.span_xR_eq_map, ← hx]
  rcases mul_eq_zero.mp hy with h | h
  · exact absurd (pow_eq_zero_iff'.mp h).1 hx'
  · exact h

/-- A `0`-stable element of a regular local ring of positive dimension (char 0) is zero or a unit:
Definition 11 for the ideal `0` and a closed point of the fibre of the blow-up of the maximal
ideal outside the vanishing locus of the initial form of `f`. -/
theorem ordElem_maximalIdeal_eq_zero_of_isJStable_bot {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [CharZero (ResidueField R)] {f : R} (hf : IsJStable (⊥ : Ideal R) f)
    (hf0 : f ≠ 0) (hM : maximalIdeal R ≠ ⊥) : Ideal.ordElem (maximalIdeal R) f = 0 := by
  have hdom : IsDomain R := Transforms.isDomain_of_isRegularLocalRing R
  by_contra hne
  have hfM : f ∈ maximalIdeal R := by
    have h1 : (1 : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) f := Order.one_le_iff_ne_zero.mpr hne
    simpa using Ideal.mem_pow_of_le_ordElem (I := maximalIdeal R) (ν := 1) h1
  obtain ⟨T, hsep, hstrict, -⟩ := exists_monoidalTransform_strictTransformIdeal_eq_top hf0 hfM hM
  have hreg : IsRegularLocalRing (R ⧸ maximalIdeal R) := by
    let := Ideal.Quotient.field (maximalIdeal R)
    infer_instance
  have hT : IsRegularLocalRing T.ring :=
    (T.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map (maximalIdeal.isMaximal R).isPrime hM
      hreg).1
  have : IsDomain T.ring := Transforms.isDomain_of_isRegularLocalRing T.ring
  obtain ⟨T₀⟩ := exists_monoidalTransform_top (R := T.ring)
  have hperm : IsPermissibleCenter R ⊥ (maximalIdeal R) :=
    isPermissibleCenter_maximalIdeal inferInstance ⊥ bot_le
  let Sq := consConstSeq (⊥ : Ideal R) T (RingEquiv.refl T.ring) (rfl : (⊤ : Ideal T.ring) = ⊤) T₀
  have hid1 : Sq.ideal 1 = ⊥ := by
    show (strictTransformIdeal T (⊥ : Ideal R)).map (RingEquiv.refl T.ring) = ⊥
    rw [strictTransformIdeal_bot T hM]
    exact Ideal.map_bot
  have key := hf Sq (RingEquiv.refl R) (ideal_map_refl ⊥).symm
    (consConstSeq_isPermissible hperm T (RingEquiv.refl T.ring) rfl T₀)
    (consConstSeq_isResiduallySeparableAlgebraic ⊥ T hsep (RingEquiv.refl T.ring) rfl T₀) 1
    (by rw [hid1, nuStar_bot, nuStar_bot])
    (by rw [hid1, t_bot, t_bot])
    (fun a ha1 ha2 => by rw [t_bot] at ha2; omega) (1 : T.ring) (by
      show Ideal.span {(1 : T.ring)} = (strictTransformIdeal T (Ideal.span {f})).map
        (RingEquiv.refl T.ring)
      rw [hstrict, Ideal.map_top, Ideal.span_singleton_one])
  have h1 : Ideal.ordElem (maximalIdeal T.ring) (1 : T.ring) = 0 := by
    refine le_antisymm ?_ zero_le
    refine Ideal.ordElem_le_of_notMem (m := 0) ?_
    rw [zero_add, pow_one]
    exact fun h => (maximalIdeal.isMaximal T.ring).ne_top ((Ideal.eq_top_iff_one _).mpr h)
  exact hne (key.1.symm.trans h1)

end BotCase

end

end StableOrder

/-- **The order of a `J`-stable element along a permissible center** (p. 302, "It follows that
`g_{jk}(s) ∈ Q̂^{ν_{jk}}`"): if `f` is `J`-stable and `Q ≠ 0` is a prime permissible center for `J`
in a regular local ring `R` whose residue field has characteristic zero, then
`ν_Q(f) = ν_M(f)`.

Deviation from the paper (gap filled): the paper gives no argument.  Lean applies Definition 11 of
Ch. III at `ᾱ = 0` to the sequence `R, R₁, R₁, …`, where `R₁` is a monoidal transform of `R` with
center `Q` which is residually separable algebraic over `R`
(`StableOrder.exists_monoidalTransform_isResiduallySeparableAlgebraic`: a maximal ideal of
`R[x⁻¹Q]` over `M`, finite residue extension by Zariski's lemma, separable in characteristic `0`)
and the later steps are trivial.

Added hypothesis `Q ≠ ⊥` (statement corrected/restricted): no monoidal transform has center `0`
(`MonoidalTransform.x_ne_zero`), so for `Q = 0` Definition 11 says nothing about `Q`.  The case
`Q = 0`, `J = 0` is not covered; the conclusion there says that every `J`-stable `f` is zero or a
unit, which should follow by applying Definition 11 to the center `M` (the strict transform of `f`
then loses order), but this is not proved here.  In the use
on p. 302 the prime contains the non-zero element `z_s`, so `Q ≠ 0`. -/
@[blueprint "lem:IV.AB-4-stable-order-ne-bot"
  (statement := /-- Let $R$ be a regular local ring whose residue field has characteristic zero,
    $J$ an ideal, $f\in R$ a $J$-stable element and $Q\neq0$ a prime ideal which is a permissible
    center for $J$. Then $\nu_Q(f)=\nu_M(f)$. -/)
  (proof := /-- \textbf{Deviation from the paper (gap filled).} Definition~11 at $\bar\alpha=0$ for
    the sequence $R,R_1,R_1,\dots$ with $R_1$ a residually separable algebraic monoidal transform
    of $R$ with center $Q$: choose $x\in Q\setminus M^2$, a maximal ideal of $R[x^{-1}Q]$ over $M$
    (it exists since $MR[x^{-1}Q]\ne R[x^{-1}Q]$), its residue field is algebraic over that of $R$
    (Zariski's lemma) hence separable (characteristic $0$). The restriction $Q\ne0$ is added:
    there is no monoidal transform with center $0$. -/)
  (latexEnv := "lemma")]
theorem IsJStable.ordElem_eq_of_isPermissibleCenter_of_ne_bot {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [CharZero (ResidueField R)] {J : Ideal R} {f : R}
    (hf : IsJStable J f) (Q : Ideal R) [hQp : Q.IsPrime] (hQ : IsPermissibleCenter R J Q)
    (hQ0 : Q ≠ ⊥) :
    Ideal.ordElem Q f = Ideal.ordElem (maximalIdeal R) f := by
  have : IsDomain R := Transforms.isDomain_of_isRegularLocalRing R
  have hreg : IsRegularLocalRing (R ⧸ Q) := by
    rcases hQ with h | ⟨-, -, h, -⟩
    · exact absurd h hQp.ne_top
    · exact h
  obtain ⟨T, hsep⟩ := StableOrder.exists_monoidalTransform_isResiduallySeparableAlgebraic Q hQ0 hreg
  have hT : IsRegularLocalRing T.ring :=
    (T.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map hQp hQ0 hreg).1
  have : IsDomain T.ring := Transforms.isDomain_of_isRegularLocalRing T.ring
  obtain ⟨T₀⟩ := StableOrder.exists_monoidalTransform_top (R := T.ring)
  exact StableOrder.ordElem_eq_of_monoidalTransform hf hQ hQp.ne_top T hsep
    (RingEquiv.refl T.ring) rfl T₀

end Hironaka

namespace Hironaka

universe u

open IsLocalRing

/-- **The order of a `J`-stable element along a permissible center, unrestricted** (p. 302, "It
follows that `g_{jk}(s) ∈ Q̂^{ν_{jk}}`"): if `f` is `J`-stable and `Q` is a prime permissible
center for `J` in a regular local ring `R` whose residue field has characteristic zero, then
`ν_Q(f) = ν_M(f)`.

Deviation from the paper (gap filled): the paper gives no argument.  For `Q ≠ 0`
(`IsJStable.ordElem_eq_of_isPermissibleCenter_of_ne_bot`) Lean applies Definition 11 of Ch. III at
`ᾱ = 0` to the sequence `R, R₁, R₁, …`, `R₁` a monoidal transform of `R` with center `Q` which is
residually separable algebraic over `R`: a maximal ideal of `R[x⁻¹Q]` over `M` (it exists, the
extension `M R[x⁻¹Q]` being proper), whose residue field is algebraic over that of `R` by Zariski's
lemma and separable in characteristic `0`.  This tacit existence of a separable closed point of the
fibre is
proved (`StableOrder.exists_monoidalTransform_isResiduallySeparableAlgebraic`).  For `Q = 0`
the ideal `J` is `0` and the conclusion says that a `0`-stable element is zero or a unit (or
`dim R = 0`): Definition 11 at `ᾱ = 1` for the sequence `R, R₁, R₁, …`, `R₁` the monoidal transform
of `R` with center `M` at a closed point of the fibre outside the vanishing locus of the initial
form of `f` (Jacobson property of the finite type `R/M`-algebra `R[x⁻¹M]/M R[x⁻¹M]`), in which
the strict transform of `f` is a unit (`ν*(0)` and `t(0)` do not change). -/
@[blueprint "lem:IV.AB-4-stable-order-full"
  (statement := /-- Let $R$ be a regular local ring whose residue field has characteristic zero,
    $J$ an ideal, $f\in R$ a $J$-stable element and $Q$ a prime ideal which is a permissible
    center for $J$. Then $\nu_Q(f)=\nu_M(f)$. -/)
  (proof := /-- \textbf{Deviation from the paper (gap filled).} For $Q\ne0$: Definition~11 at
    $\bar\alpha=0$ for the sequence $R,R_1,R_1,\dots$ with $R_1$ a residually separable algebraic
    monoidal transform with center $Q$ (a maximal ideal of $R[x^{-1}Q]$ over $M$, algebraic
    residue field by Zariski's lemma, separable in characteristic $0$). For $Q=0$ (then $J=0$):
    if $f\ne0$ is not a unit, take $R_1$ the monoidal transform with center $M$ at a closed point
    of the fibre outside the zero locus of the initial form of $f$; the strict transform of $f$
    is a unit, and Definition~11 at $\bar\alpha=1$ gives $0=\nu_M(f)$, a contradiction; $\nu^*(0)$
    and $t(0)$ are the same in every ring. -/)
  (latexEnv := "lemma")]
theorem IsJStable.ordElem_eq_of_isPermissibleCenter_of_charZero {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [CharZero (ResidueField R)] {J : Ideal R} {f : R}
    (hf : IsJStable J f) (Q : Ideal R) [hQp : Q.IsPrime] (hQ : IsPermissibleCenter R J Q) :
    Ideal.ordElem Q f = Ideal.ordElem (maximalIdeal R) f := by
  by_cases hQ0 : Q = ⊥
  · subst hQ0
    have hJ : J = ⊥ := by
      rcases hQ with h | ⟨-, h, -⟩
      · exact absurd h hQp.ne_top
      · exact le_bot_iff.mp h
    subst hJ
    by_cases hM : maximalIdeal R = ⊥
    · rw [hM]
    by_cases hf0 : f = 0
    · subst hf0
      rw [Ideal.ordElem_eq_top_iff.mpr fun n => zero_mem _,
        Ideal.ordElem_eq_top_iff.mpr fun n => zero_mem _]
    · rw [StableOrder.ordElem_maximalIdeal_eq_zero_of_isJStable_bot hf hf0 hM]
      refine le_antisymm ?_ zero_le
      refine Ideal.ordElem_le_of_notMem (m := 0) ?_
      rw [zero_add, pow_one]
      exact fun h => hf0 (Ideal.mem_bot.mp h)
  · exact hf.ordElem_eq_of_isPermissibleCenter_of_ne_bot Q hQ hQ0

end Hironaka
