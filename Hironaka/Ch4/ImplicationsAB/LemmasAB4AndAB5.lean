/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch4.ImplicationsAB.LemmasAB1ToAB3
public import Hironaka.Statements

/-!
# Ch. IV §3 (pp. 299–307): Lemmas (AB.4) and (AB.5)

The local computation of the proof of Lemma (AB.4) and its Corollary (pp. 299–303), with the frames
`(T_t; z_t)` of its proof (pp. 300–302), and Lemma (AB.5) (pp. 303–307).  Lemma (AB.4) and its
Corollary, repaired, are in `Hironaka/Ch4/ComponentwiseConstruction.lean`.

This is part 2 of 3 of `Hironaka.Ch4.ImplicationsAB`, which imports all parts; its description holds the
notation and the formalization notes for the whole section.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

namespace Hironaka

universe u

noncomputable section

namespace AB

/-! ## Lemma (AB.4) and its Corollary (pp. 299–303) -/

/-- The conditions (1), (2), (3) of Lemma (AB.4) on a point `x` of `X_s`: (1) `X_s` has
dimension `N` at `x`, (2) `g_s(x) = x_0`, and (3) `ν*_x(V_1(s), …, V_β(s), W(s)/X_s) =
ν*_{x_0}(V_1, …, V_β, W/X)` and `τ*_x(…/X_s) = τ*_{x_0}(…/X)`.  Condition (3) includes that
`X_s` is simple at `x`, where the characters are formed. -/
def Cond (N : ℕ) {X : Scheme.{u}} (ℜ : DatumI.Raw X) (T : Tower X) (x₀ : X)
    (hx₀ : X.IsSimpleAt x₀) (s : ℕ) (x : T.X s) : Prop :=
  (T.X s).dimAt x = (N : WithBot ℕ∞) ∧ (T.pre s).composite.base x = x₀ ∧
    ∃ hx : (T.X s).IsSimpleAt x,
      NuStarSystemEq (datumSystem ℜ) x₀ hx₀ (T.sys ℜ s) x hx ∧
      TauStarSystemEq (datumSystem ℜ) x₀ hx₀ (T.sys ℜ s) x hx

/-- p. 300: "By Theorem 3, § 5, Ch. III, the image `x_t` of `x` in `X_t` (`0 ≤ t ≤ s`) satisfies
also the conditions (1), (2) and (3)", one step at a time.

\textbf{Deviation from the paper (gap filled).} Spelled out: `N = dim_x X_{s+1} ≤ dim_y X_s ≤ N`
at `y = f_s(x)`; the `ν*` at `y` lie between those at `x` and at `x_0`, which agree; and then the
`τ*` at `y` lie between those at `x_0` and at `x`, which agree. -/
theorem Standing.cond_f_of_cond_succ [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    (hS : Standing N n ℜ P r T x₀) (s : ℕ) (x : T.X (s + 1))
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) (s + 1) x) :
    Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((T.f s).base x) := by
  obtain ⟨hdim, hg, hxs, hν, hτ⟩ := hx
  have hgy : (T.pre s).composite.base ((T.f s).base x) = x₀ := by
    rw [← hg, Tower.composite_pre_succ]
    rfl
  have hydim : (T.X s).dimAt ((T.f s).base x) = N := le_antisymm (hS.dimAt_X_le s _)
    (hdim ▸ MonoidalTransformation.dimAt_le (hS.isNonsingular_X s) (hS.isNonsingular_B s)
      (T.monoidalTransformation s) x)
  have hys := hS.isNonsingular_X s ((T.f s).base x)
  obtain ⟨h3ν, h3τ⟩ := hS.nuStarSystemAt_le_and_tauStarSystemAt_ge_of_nuStarSystemEq s _ hydim hgy
    hys
  have hstep := hS.nuStarAt_sys_succ_le_and_tauAt_le s x hxs hdim
  have hνs : NuStarSystemEq (datumSystem ℜ) x₀ (hS.ambient.2.1 x₀) (T.sys ℜ s) _ hys :=
    fun j => le_antisymm (h3ν j) ((hν j).symm.le.trans (hstep j).1)
  refine ⟨hydim, hgy, hys, hνs, fun j i => le_antisymm (h3τ hνs j i) ?_⟩
  have hab : (T.sys ℜ (s + 1) j).nuStarAt x hxs = (T.sys ℜ s j).nuStarAt _ hys :=
    (hν j).trans (hνs j).symm
  exact ((hstep j).2 hab (i : ℕ) i.pos).trans (hτ j i).ge

/-- p. 299: a point `x` of `X_s` over `x_0` has a unique point `x̂` of `X̂_s` with `c_s(x̂) = x`
(Lemma (AB.2), first assertion, `Completion.bijOn_c_of_isNonsingular`; the `X_s` and `B_s` are
non-singular by the standing assumptions of §3). -/
theorem Completion.existsUnique_c_apply_eq {X : Scheme.{u}} {T : Tower X} {x₀ : X}
    (𝒞 : Completion T x₀) (hx : X.IsSimpleAt x₀) (hX : ∀ s, (T.X s).IsNonsingular)
    (hB : ∀ s, (T.B s).IsNonsingular) (s : ℕ)
    (x : T.X s) (hg : (T.pre s).composite.base x = x₀) :
    ∃! xh : 𝒞.tHat.X s, (𝒞.c s).base xh = x := by
  have hbij := 𝒞.bijOn_c_of_isNonsingular hx hX hB s
  obtain ⟨xh, hxh, hcx⟩ := hbij.2.2 (show x ∈ (T.pre s).composite.base ⁻¹' {x₀} from hg)
  refine ⟨xh, hcx, fun yh hyh => ?_⟩
  have hy : (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx :=
    𝒞.composite_tHat_eq_xhat0 hx s yh (by rw [hyh]; exact hg)
  exact hbij.2.1 hy hxh (hyh.trans hcx.symm)

/-- The first assertion of Lemma (AB.4) (p. 299) from the condition [g] at the earlier stages:
"If the first and the second assertions are verified for certain `s ≥ 0`, then the first
assertion for `s + 1` follows immediately by the definition `X'_{s+1}`. The first assertion is
trivially true for `s = 0`." -/
theorem Frame.mem_xPrime_of_cond [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS) (s : ℕ)
    (hG : ∀ t < s, ∀ y ∈ (T.B t).pts, Cond N ℜ T x₀ (hS.ambient.2.1 x₀) t y → 𝒮.CaseG t)
    (x : T.X s) (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s x) : x ∈ 𝒮.xPrime s := by
  induction s with
  | zero => exact trivial
  | succ s ih =>
    have hy := hS.cond_f_of_cond_succ s x hx
    have hyX := ih (fun t ht => hG t (Nat.lt_succ_of_lt ht)) _ hy
    classical
    rw [xPrime_succ]
    by_cases hc : 𝒮.CaseG s
    · rw [ite_eq_left hc]
      exact hyX
    · rw [ite_eq_right hc]
      refine ⟨hyX, fun hyB => hc (hG s (Nat.lt_succ_self s) _ hyB hy)⟩

end AB

/-! ### Ring-level lemmas for the frames of Lemma (AB.4) (Ch. III, §§ 2, 8, 9) -/

/-- The order along the maximal ideal is transported by ring isomorphisms. -/
theorem ordElem_maximalIdeal_ringEquiv {R R' : Type u} [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] (e : R ≃+* R') (a : R) :
    Ideal.ordElem (maximalIdeal R') (e a) = Ideal.ordElem (maximalIdeal R) a := by
  have hmem : ∀ ν : ℕ, e a ∈ maximalIdeal R' ^ ν ↔ a ∈ maximalIdeal R ^ ν := by
    intro ν
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e, ← Ideal.map_pow, ← Ideal.comap_symm,
      Ideal.mem_comap]
    simp
  simp only [Ideal.ordElem, hmem]

/-- `J`-stability is transported by ring isomorphisms. -/
theorem IsJStable.map_ringEquiv [Hironaka.HironakaCitedResults.{u}] {R R' : Type u} [CommRing R]
    [IsRegularLocalRing R] [CommRing R'] [IsRegularLocalRing R'] {J : Ideal R} {f : R}
    (hf : IsJStable J f) (e : R ≃+* R') : IsJStable (J.map e) (e f) := by
  intro Sq e' h0 hperm hsep α hν ht hτ fα hfα
  have h0' : Sq.ideal 0 = J.map (e.trans e') := by
    rw [h0, ← Ideal.map_coe e J, ← Ideal.map_coe e' _, ← Ideal.map_coe (e.trans e') J,
      Ideal.map_map]
    rfl
  obtain ⟨hn, ht', hτ'⟩ := AB.nuStar_t_tau_map_ringEquiv e J
  have hord : Ideal.ordElem (maximalIdeal R') (e f) = Ideal.ordElem (maximalIdeal R) f :=
    ordElem_maximalIdeal_ringEquiv e f
  have := hf Sq (e.trans e') h0' hperm hsep α (hν.trans hn) (ht.trans ht')
    (fun a ha1 ha2 => (hτ a ha1 (ht' ▸ ha2)).trans (hτ' a)) fα hfα
  rw [hord]
  exact this

namespace MonoidalSequence

/-- The constant sequence of trivial monoidal transforms (center `R`) of `R`, carrying the ideal
`J` (p. 209: the monoidal transform with center `R` is `R` itself). -/
def const {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] (J : Ideal R)
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
    rw [AB.strictTransformIdeal_eq_map_toRing_of_eq_top hc T₀ J, ← Ideal.map_coe, Ideal.map_map]
    conv_lhs => rw [← Ideal.map_id J]
    congr 1
    ext r
    exact ((RingEquiv.ofBijective T₀.toRing (T₀.bijective_toRing_of_eq_top hc)).symm_apply_apply
      r).symm

/-- The trivial monoidal transforms are permissible (the center is the unit ideal). -/
theorem const_isPermissible {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (J : Ideal R) {c : Ideal R} (hc : c = ⊤) (T₀ : MonoidalTransform R c)
    [IsLocalHom T₀.toRing] : (const J hc T₀).IsPermissible := fun _ => Or.inl hc

/-- The sequence obtained by prepending the monoidal transform `T` of `R` (with center `P`) to a
sequence `Sq` of monoidal transforms of `T`. -/
def cons {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] (J : Ideal R)
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

/-- Along the prepended sequence, the strict transforms are those along `Sq` of the strict
transform in `T`. -/
theorem cons_strictAlong_succ {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (J : Ideal R) {P : Ideal R} (T : MonoidalTransform R P) [IsLocalHom T.toRing]
    (Sq : MonoidalSequence.{u}) (e : T.ring ≃+* Sq.ring 0)
    (h0 : Sq.ideal 0 = (strictTransformIdeal T J).map e) (I : Ideal R) (n : ℕ) :
    (cons J T Sq e h0).strictAlong I (n + 1) =
      Sq.strictAlong ((strictTransformIdeal T I).map e) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (strictTransformIdeal (Sq.transform n) ((cons J T Sq e h0).strictAlong I (n + 1))).map
      (Sq.equiv n) = _
    rw [ih]
    rfl

end MonoidalSequence

/-- A monoidal transform with center the unit ideal is residually separable algebraic (it is an
isomorphism, p. 209). -/
theorem MonoidalTransform.isResiduallySeparableAlgebraic_toRing_of_eq_top {R : Type u}
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
def MonoidalSequence.consConst {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (J : Ideal R) {P : Ideal R} (T : MonoidalTransform R P) [IsLocalHom T.toRing]
    {R₁ : Type u} [CommRing R₁] [IsRegularLocalRing R₁] [IsDomain R₁] (e₁ : T.ring ≃+* R₁)
    {c : Ideal R₁} (hc : c = ⊤) (T₀ : MonoidalTransform R₁ c) [IsLocalHom T₀.toRing] :
    MonoidalSequence.{u} :=
  MonoidalSequence.cons J T (MonoidalSequence.const ((strictTransformIdeal T J).map e₁) hc T₀) e₁
    rfl

/-- The sequence `R, R₁, R₁, …` is permissible if its first center is. -/
theorem MonoidalSequence.consConst_isPermissible {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {J : Ideal R} {P : Ideal R} (hP : IsPermissibleCenter R J P)
    (T : MonoidalTransform R P) [IsLocalHom T.toRing]
    {R₁ : Type u} [CommRing R₁] [IsRegularLocalRing R₁] [IsDomain R₁] (e₁ : T.ring ≃+* R₁)
    {c : Ideal R₁} (hc : c = ⊤) (T₀ : MonoidalTransform R₁ c) [IsLocalHom T₀.toRing] :
    (MonoidalSequence.consConst J T e₁ hc T₀).IsPermissible := fun n => match n with
  | 0 => hP
  | _ + 1 => MonoidalSequence.const_isPermissible _ hc T₀ 0

/-- The sequence `R, R₁, R₁, …` is residually separable algebraic if its first step is. -/
theorem MonoidalSequence.consConst_isResiduallySeparableAlgebraic {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] (J : Ideal R) {P : Ideal R} (T : MonoidalTransform R P)
    [IsLocalHom T.toRing] (hsep : RingHom.IsResiduallySeparableAlgebraic T.toRing)
    {R₁ : Type u} [CommRing R₁] [IsRegularLocalRing R₁] [IsDomain R₁] (e₁ : T.ring ≃+* R₁)
    {c : Ideal R₁} (hc : c = ⊤) (T₀ : MonoidalTransform R₁ c) [IsLocalHom T₀.toRing] :
    (MonoidalSequence.consConst J T e₁ hc T₀).IsResiduallySeparableAlgebraic := fun n =>
  match n with
  | 0 => hsep
  | _ + 1 => MonoidalTransform.isResiduallySeparableAlgebraic_toRing_of_eq_top hc T₀

private theorem ideal_map_refl {A : Type u} [CommRing A] (I : Ideal A) :
    I.map (RingEquiv.refl A) = I := by
  rw [← Ideal.map_coe]
  exact Ideal.map_id I

/-- A `J`-stable element has, along a permissible center `P ≠ R` admitting a residually separable
algebraic monoidal transform `R₁`, the order it has along the maximal ideal (Definition 11 of
Ch. III at `ᾱ = 0`, for the sequence `R, R₁, R₁, …`). -/
theorem IsJStable.ordElem_eq_of_monoidalTransform {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] {J : Ideal R} {f : R} (hf : IsJStable J f) {P : Ideal R}
    (hP : IsPermissibleCenter R J P) (hPtop : P ≠ ⊤) (T : MonoidalTransform R P)
    [IsLocalHom T.toRing] (hsep : RingHom.IsResiduallySeparableAlgebraic T.toRing)
    {R₁ : Type u} [CommRing R₁] [IsRegularLocalRing R₁] [IsDomain R₁] (e₁ : T.ring ≃+* R₁)
    {c : Ideal R₁} (hc : c = ⊤) (T₀ : MonoidalTransform R₁ c) [IsLocalHom T₀.toRing] :
    Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f :=
  (hf (MonoidalSequence.consConst J T e₁ hc T₀) (RingEquiv.refl R) (ideal_map_refl J).symm
    (MonoidalSequence.consConst_isPermissible hP T e₁ hc T₀)
    (MonoidalSequence.consConst_isResiduallySeparableAlgebraic J T hsep e₁ hc T₀) 0 rfl rfl
    (fun _ _ _ => rfl) f rfl).2 hPtop

/-- **`J`-stability along one monoidal transform.**  Let `f` be `J`-stable, `P` a permissible
center for `J`, `R₁` a monoidal transform of `R` with center `P`, residually separable algebraic
over `R`, such that the strict transform `J₁` of `J` has `ν*(J₁) = ν*(J)` and `τ*(J₁) = τ*(J)`,
and `f₁` a strict transform of `f` in `R₁`.  Then `ν_{M₁}(f₁) = ν_M(f)` and `f₁` is `J₁`-stable
(Definition 11 of Ch. III, applied to the sequences through `R₁`; the trivial transforms of a copy
of `R₁` continue the sequence `R, R₁`).  This is the step "then we get a `Ĵ_j(t)`-stable standard
base of `Ĵ_j(t)`" of p. 301. -/
theorem IsJStable.strictTransform [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    {J : Ideal R} {f : R} (hf : IsJStable J f) {P : Ideal R} (hP : IsPermissibleCenter R J P)
    (T : MonoidalTransform R P) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic T.toRing)
    (hν : nuStar T.ring (strictTransformIdeal T J) = nuStar R J)
    (ht : t T.ring (strictTransformIdeal T J) = t R J)
    (hτ : ∀ a, 1 ≤ a → a ≤ t R J → tau T.ring (strictTransformIdeal T J) a = tau R J a)
    (f₁ : T.ring) (hf₁ : Ideal.span {f₁} = strictTransformIdeal T (Ideal.span {f}))
    {R₁ : Type u} [CommRing R₁] [IsRegularLocalRing R₁] [IsDomain R₁] (e₁ : T.ring ≃+* R₁)
    {c : Ideal R₁} (hc : c = ⊤) (T₀ : MonoidalTransform R₁ c) [IsLocalHom T₀.toRing] :
    Ideal.ordElem (maximalIdeal T.ring) f₁ = Ideal.ordElem (maximalIdeal R) f ∧
      IsJStable (strictTransformIdeal T J) f₁ := by
  -- applying Definition 11 to a sequence through `R₁`
  have key : ∀ (Sq : MonoidalSequence.{u}) (e : T.ring ≃+* Sq.ring 0)
      (h0 : Sq.ideal 0 = (strictTransformIdeal T J).map e), Sq.IsPermissible →
      Sq.IsResiduallySeparableAlgebraic →
      ∀ α : ℕ, nuStar (Sq.ring α) (Sq.ideal α) = nuStar R J → t (Sq.ring α) (Sq.ideal α) = t R J →
      (∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring α) (Sq.ideal α) a = tau R J a) →
      ∀ fα : Sq.ring α, Ideal.span {fα} = Sq.strictAlong (Ideal.span {e f₁}) α →
        Ideal.ordElem (maximalIdeal (Sq.ring α)) fα = Ideal.ordElem (maximalIdeal R) f ∧
          (Sq.center α ≠ ⊤ →
            Ideal.ordElem (Sq.center α) fα = Ideal.ordElem (maximalIdeal R) f) := by
    intro Sq e h0 hperm hsep' α hνα htα hτα fα hfα
    let C := MonoidalSequence.cons J T Sq e h0
    have hpermC : C.IsPermissible := fun n => match n with
      | 0 => hP
      | n + 1 => hperm n
    have hsepC : C.IsResiduallySeparableAlgebraic := fun n => match n with
      | 0 => hsep
      | n + 1 => hsep' n
    refine hf C (RingEquiv.refl R) (ideal_map_refl J).symm hpermC hsepC (α + 1) hνα htα hτα fα ?_
    have hC := MonoidalSequence.cons_strictAlong_succ J T Sq e h0 (Ideal.span {f}) α
    rw [← hf₁, Ideal.map_span, Set.image_singleton] at hC
    exact hfα.trans hC.symm
  have hν' := (AB.nuStar_t_tau_map_ringEquiv e₁ (strictTransformIdeal T J))
  have hord' := (key (MonoidalSequence.const ((strictTransformIdeal T J).map e₁) hc T₀) e₁ rfl
    (MonoidalSequence.const_isPermissible _ hc T₀)
    (fun _ => MonoidalTransform.isResiduallySeparableAlgebraic_toRing_of_eq_top hc T₀) 0
    (hν'.1.trans hν) (hν'.2.1.trans ht)
    (fun a ha1 ha2 => (hν'.2.2 a).trans (hτ a ha1 ha2)) (e₁ f₁)
    (by show Ideal.span {e₁ f₁} = Ideal.span {e₁ f₁}; rfl)).1
  have hord : Ideal.ordElem (maximalIdeal T.ring) f₁ = Ideal.ordElem (maximalIdeal R) f := by
    rw [← ordElem_maximalIdeal_ringEquiv e₁ f₁]
    exact hord'
  refine ⟨hord, ?_⟩
  intro Sq e h0 hperm hsep' α hνα htα hτα fα hfα
  rw [hord]
  exact key Sq e h0 hperm hsep' α (hνα.trans hν) (htα.trans ht)
    (fun a ha1 ha2 => (hτα a ha1 (ht ▸ ha2)).trans (hτ a ha1 ha2)) fα hfα

/-- Remark 2 of § 9, Ch. III for one monoidal transform: the strict transforms of a `J`-stable
standard base of `J` form a standard base of the strict transform `J₁`, if `ν*(J₁) = ν*(J)` and
`τ*(J₁) = τ*(J)` ("then we get a `Ĵ_j(t)`-stable standard base of `Ĵ_j(t)`", p. 301).  Stated in
a copy `R₁'` of `R₁`. -/
theorem IsStandardBase.map_strictTransform_of_isJStableSystem [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] {J : Ideal R} {m : ℕ} {g : Fin m → R}
    (hg : IsStandardBase R J g) (hst : IsJStableSystem J g) {P : Ideal R}
    (hP : IsPermissibleCenter R J P) (T : MonoidalTransform R P) [IsLocalHom T.toRing]
    [IsRegularLocalRing T.ring] (hsep : RingHom.IsResiduallySeparableAlgebraic T.toRing)
    (hν : nuStar T.ring (strictTransformIdeal T J) = nuStar R J)
    (ht : t T.ring (strictTransformIdeal T J) = t R J)
    (hτ : ∀ a, 1 ≤ a → a ≤ t R J → tau T.ring (strictTransformIdeal T J) a = tau R J a)
    (g₁ : Fin m → T.ring) (hg₁ : ∀ k, Ideal.span {g₁ k} = strictTransformIdeal T (Ideal.span {g k}))
    {R₁ : Type u} [CommRing R₁] [IsRegularLocalRing R₁] [IsDomain R₁] (e₁ : T.ring ≃+* R₁)
    {c : Ideal R₁} (hc : c = ⊤) (T₀ : MonoidalTransform R₁ c) [IsLocalHom T₀.toRing] :
    IsStandardBase R₁ ((strictTransformIdeal T J).map e₁) fun k => e₁ (g₁ k) := by
  have hν' := AB.nuStar_t_tau_map_ringEquiv e₁ (strictTransformIdeal T J)
  exact isStandardBase_strictTransform_of_isJStableSystem J g hg hst
    (MonoidalSequence.consConst J T e₁ hc T₀) (RingEquiv.refl R) (ideal_map_refl J).symm
    (MonoidalSequence.consConst_isPermissible hP T e₁ hc T₀)
    (MonoidalSequence.consConst_isResiduallySeparableAlgebraic J T hsep e₁ hc T₀) 1
    (hν'.1.trans hν) (hν'.2.1.trans ht) (fun a ha1 ha2 => (hν'.2.2 a).trans (hτ a ha1 ha2))
    (fun k => e₁ (g₁ k)) (fun k => by
      show Ideal.span {e₁ (g₁ k)} = (strictTransformIdeal T (Ideal.span {g k})).map e₁
      rw [← hg₁ k, Ideal.map_span, Set.image_singleton])

/-- A local homomorphism whose residue field map is surjective is residually separable. -/
theorem RingHom.isResiduallySeparable_of_surjective_residueField_map {A B : Type u} [CommRing A]
    [IsLocalRing A] [CommRing B] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ]
    (hφ : Function.Surjective (ResidueField.map φ)) : RingHom.IsResiduallySeparable φ := by
  let _ := (ResidueField.map φ).toAlgebra
  have hbij : Function.Bijective (ResidueField.map φ) := ⟨(ResidueField.map φ).injective, hφ⟩
  intro k' _ _ _
  let eB : ResidueField B ≃ₐ[ResidueField A] ResidueField A :=
    (AlgEquiv.ofBijective (Algebra.ofId (ResidueField A) (ResidueField B)) hbij).symm
  let e' := (Algebra.TensorProduct.congr eB (AlgEquiv.refl : k' ≃ₐ[ResidueField A] k')).trans
    (Algebra.TensorProduct.lid (ResidueField A) k')
  exact isReduced_of_injective e' e'.injective

/-- `t(J)` is determined by `ν*(J)` (Definition 6 of Ch. III). -/
theorem t_eq_of_nuStar_eq {R R' : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing R']
    [IsRegularLocalRing R'] {J : Ideal R} {J' : Ideal R'} (h : nuStar R J = nuStar R' J') :
    t R J = t R' J' := by
  have hI : ∀ i, nuI R J i = nuI R' J' i := fun i => congrFun (congrArg ofLex h) i
  unfold t muSet
  simp only [hI]

/-- `J`-stability is unchanged by a unit factor (the strict transforms and the orders of `f` and
`uf` agree). -/
theorem IsJStable.unit_mul {R : Type u} [CommRing R] [IsRegularLocalRing R] {J : Ideal R}
    {f : R} (hf : IsJStable J f) (u : Rˣ) : IsJStable J (u * f) := by
  intro Sq e h0 hperm hsep α hν ht hτ fα hfα
  have hspan : Ideal.span {e (u * f)} = Ideal.span {e f} := by
    rw [map_mul]
    exact Ideal.span_singleton_mul_left_unit ((u.isUnit).map e) _
  have hord : Ideal.ordElem (maximalIdeal R) ((u : R) * f) =
      Ideal.ordElem (maximalIdeal R) f := by
    have hmem : ∀ n : ℕ, (u : R) * f ∈ maximalIdeal R ^ n ↔ f ∈ maximalIdeal R ^ n := fun n =>
      ⟨fun h => by simpa [← mul_assoc] using Ideal.mul_mem_left _ (((u⁻¹ : Rˣ) : R)) h,
        fun h => Ideal.mul_mem_left _ _ h⟩
    simp only [Ideal.ordElem, hmem]
  rw [hord]
  refine hf Sq e h0 hperm hsep α hν ht hτ fα ?_
  show Ideal.span {fα} = Sq.strictAlong (Ideal.span {e f}) α
  rw [← hspan]
  exact hfα

/-- At the closed point of `Spec R` (`R` local), the stalk of the ideal sheaf `V(I)` is `I`, read in
the stalk through `stalkClosedPointIso`. -/
theorem stalkIdeal_ofIdealTop_closedPoint (R : CommRingCat.{u}) [IsLocalRing R] (I : Ideal R) :
    Subscheme.stalkIdeal (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso R).inv.hom) : Subscheme (Spec R)) (IsLocalRing.closedPoint R) =
      I.map (stalkClosedPointIso R).inv.hom := by
  have hP : IsLocalRing.closedPoint R ∈ ((⊤ : (Spec R).Opens) : Set (Spec R)) := trivial
  rw [Subscheme.stalkIdeal_eq_map_germ_affine _ ⟨⊤, isAffineOpen_top _⟩ hP]
  show Ideal.map _ (Ideal.map _ (Ideal.map _ I)) = _
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  have h2 : (Spec R).presheaf.map (homOfLE (le_refl (⊤ : (Spec R).Opens))).op = 𝟙 _ :=
    (Spec R).presheaf.map_id _
  rw [h2, ← ΓSpecIso_hom_stalkClosedPointIso_inv]
  ext a
  simp

namespace AB

/-! ### The frames `(T_t; z_t)` of the proof of Lemma (AB.4) (pp. 300–302) -/

/-- The local rings of `X̂_s` are regular: `X̂_s` is non-singular
(`Completion.isNonsingular_tHat`). -/
instance Frame.instIsRegularLocalRingStalk [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X s) :
    IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk xh) :=
  𝒮.toCompletion.isNonsingular_tHat (hS.ambient.2.1 x₀) hS.isNonsingular_X
    hS.isNonsingular_B s xh

/-- At a point of `X̂_s` over a point satisfying (1), (2), (3), the characters `ν*`, `t`, `τ*` of
`Ĵ_j(s)` are those of `J_j` at `x_0` (condition (3), and `S_s → Ŝ_s` transforms a regular system
of parameters into one, with the same residue field, Lemma (AB.2)). -/
theorem Frame.nuStar_t_tau_eq_of_cond [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base xh)) (j : Fin (ℜ.β + 1)) :
    haveI : IsRegularLocalRing (X.presheaf.stalk x₀) := hS.ambient.2.1 x₀
    nuStar _ ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh) =
        nuStar _ ((datumSystem ℜ j).stalkIdeal x₀) ∧
      t _ ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh) =
        t _ ((datumSystem ℜ j).stalkIdeal x₀) ∧
      ∀ a, 1 ≤ a → tau _ ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh) a =
        tau _ ((datumSystem ℜ j).stalkIdeal x₀) a := by
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hS.ambient.2.1 x₀
  obtain ⟨-, hg, hxs, hν, hτ⟩ := hx
  have hxh0 : (𝒮.tHat.pre s).composite.base xh = xhat0 X x₀ (hS.ambient.2.1 x₀) :=
    𝒮.composite_tHat_eq_xhat0 (hS.ambient.2.1 x₀) s xh hg
  obtain ⟨-, hα, hres⟩ := 𝒮.isRegularLocalRing_and_mapsRSOP_stalkMap (hS.ambient.2.1 x₀)
    hS.isNonsingular_X hS.isNonsingular_B s xh hxh0
  have : IsRegularLocalRing ((T.X s).presheaf.stalk ((𝒮.c s).base xh)) := hxs
  have hsep := RingHom.isResiduallySeparable_of_surjective_residueField_map _ hres
  rw [stalkIdeal_totalTransform]
  have h1 := (nuStar_map_eq_of_mapsRSOP _ hα ((T.sys ℜ s j).stalkIdeal ((𝒮.c s).base xh))).symm
  have h2 : nuStar _ ((T.sys ℜ s j).stalkIdeal ((𝒮.c s).base xh)) =
      nuStar _ ((datumSystem ℜ j).stalkIdeal x₀) := hν j
  obtain ⟨h3, h4, -⟩ := tauStar_map _ hα hsep ((T.sys ℜ s j).stalkIdeal ((𝒮.c s).base xh))
  have hnu := h1.trans h2
  refine ⟨hnu, t_eq_of_nuStar_eq hnu, fun a ha => ?_⟩
  by_cases hat : a ≤ t _ ((T.sys ℜ s j).stalkIdeal ((𝒮.c s).base xh))
  · rw [h4 a ha hat]
    exact (hτ j ⟨a, ha⟩).symm
  · push Not at hat
    rw [tau_eq_zero_of_t_lt _ (h3.symm ▸ hat)]
    exact (tau_eq_zero_of_t_lt _ ((t_eq_of_nuStar_eq h2) ▸ hat)).symm

/-- Lemma (AB.4), local part, for an arbitrary permissible center `B'` at stage `s`: at a point
`x̂ ∈ X̂_s` over a point `x ∈ B'` satisfying (1), (2), (3), with a frame `(T_s; z_s)` as in
`lem:IV.AB-4-frames`, the ideal `Q̂'` of `c_s⁻¹(B')` is a prime with regular quotient, a
permissible center for every `Ĵ_j(s)` ("Since `Q_s` is a permissible center for `J_0(s)`, `Q̂_s`
is such for `Ĵ_0(s)`"), and `z_s ∈ Q̂'` ("and therefore we have `z_s ∈ Q̂_s`", p. 300).  The proof
of Lemma (AB.4) uses of `B_s` only that it is a permissible center for `(ℜ(s), r(s))` at the
stage `s`; this is the statement for any such center, of which the case `B' = B_s` is
`isPermissibleCenter_and_mem_of_mem_B`. -/
theorem Frame.isPermissibleCenter_and_mem_of_isPermissible [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}}
    {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS) (s : ℕ) (B' : Subscheme (T.X s))
    (hB' : ((T.pre s).transformI ℜ).IsPermissible B')
    (hBF : ∀ F₁, r = .closed F₁ → B'.pts ⊆ ((T.pre s).strictTransform F₁).pts)
    (xh : 𝒮.tHat.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base xh))
    (hxB : (𝒮.c s).base xh ∈ B'.pts)
    (F : RegularFrame ((𝒮.tHat.X s).presheaf.stalk xh)) (z : (𝒮.tHat.X s).presheaf.stalk xh)
    (hr : F.r = 1) (hz : ∀ i, F.z i = z) (hX : (𝒮.xBar s).stalkIdeal xh = Ideal.span {z})
    (hFst : ∀ U, r = .opn U → F.IsJStable
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal xh)) :
    ((Subscheme.totalTransform (𝒮.c s) B').stalkIdeal xh).IsPrime ∧
      IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk xh ⧸
        (Subscheme.totalTransform (𝒮.c s) B').stalkIdeal xh) ∧
      (∀ j, IsPermissibleCenter _ ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh)
        ((Subscheme.totalTransform (𝒮.c s) B').stalkIdeal xh)) ∧
      z ∈ (Subscheme.totalTransform (𝒮.c s) B').stalkIdeal xh := by
  classical
  have : IsRegularLocalRing ((T.X s).presheaf.stalk ((𝒮.c s).base xh)) :=
    hS.isNonsingular_X s _
  have hBns : B'.IsNonsingular := hB'.1.isNonsingular
  have hQperm : ∀ j, IsPermissibleCenter _ ((T.sys ℜ s j).stalkIdeal ((𝒮.c s).base xh))
      (B'.stalkIdeal ((𝒮.c s).base xh)) := by
    intro j
    obtain ⟨j', hj'⟩ := exists_datumSystem_transformI_eq_sys ℜ T s j
    rw [← hj']
    exact DatumI.Raw.isPermissibleCenter_stalkIdeal_datumSystem hB' _ j'
  have hQne : B'.stalkIdeal ((𝒮.c s).base xh) ≠ ⊤ :=
    Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hxB
  have : (B'.stalkIdeal ((𝒮.c s).base xh)).IsPrime :=
    Subscheme.isPrime_stalkIdeal_of_isNonsingular hBns hxB
  set α := ((𝒮.c s).stalkMap xh).hom with hαdef
  have hxh0 : (𝒮.tHat.pre s).composite.base xh = xhat0 X x₀ (hS.ambient.2.1 x₀) :=
    𝒮.composite_tHat_eq_xhat0 (hS.ambient.2.1 x₀) s xh hx.2.1
  have hα : RingHom.MapsRSOP α := (𝒮.isRegularLocalRing_and_mapsRSOP_stalkMap
    (hS.ambient.2.1 x₀) hS.isNonsingular_X hS.isNonsingular_B s xh hxh0).2.1
  have hQh : (Subscheme.totalTransform (𝒮.c s) B').stalkIdeal xh =
      (B'.stalkIdeal ((𝒮.c s).base xh)).map α := by
    rw [stalkIdeal_totalTransform]
  have hQhperm : ∀ j, IsPermissibleCenter _
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh)
      ((Subscheme.totalTransform (𝒮.c s) B').stalkIdeal xh) := by
    intro j
    have hJP := ((hQperm j).resolve_left hQne).2.1
    rw [hQh, stalkIdeal_totalTransform]
    exact ((isPermissibleCenter_map_iff α hα _ _ hJP).2.2.2).mp (hQperm j)
  have hQhne : (Subscheme.totalTransform (𝒮.c s) B').stalkIdeal xh ≠ ⊤ := by
    rw [hQh]
    refine ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top
      (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_)
    exact map_nonunit α a (le_maximalIdeal hQne ha)
  obtain ⟨hQhprime, -, hQhreg, -⟩ := (hQhperm (Fin.last _)).resolve_left hQhne
  refine ⟨hQhprime, hQhreg, hQhperm, ?_⟩
  have hcases : ∀ r' : Restriction X, (∃ F, r' = .closed F) ∨ ∃ U, r' = .opn U := by
    intro r'
    cases r' with
    | closed F => exact Or.inl ⟨F, rfl⟩
    | opn U => exact Or.inr ⟨U, rfl⟩
  rcases hcases r with ⟨F₀, hr'⟩ | ⟨U, hr'⟩
  · have hXF := 𝒮.xBar_eq_totalTransform_of_closed s F₀ hr'
    have hle : ((T.pre s).strictTransform F₀).stalkIdeal ((𝒮.c s).base xh) ≤
        B'.stalkIdeal ((𝒮.c s).base xh) :=
      DatumTransform.stalkIdeal_le_of_pts_subset
        (Subscheme.isReduced_of_isNonsingular hBns) (hBF F₀ hr') _
    have hzX : z ∈ (𝒮.xBar s).stalkIdeal xh := by
      rw [hX]; exact Ideal.mem_span_singleton_self z
    rw [hXF, stalkIdeal_totalTransform] at hzX
    rw [hQh]
    exact Ideal.map_mono hle hzX
  · have := isDomain_of_isRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk xh)
    have h := (remark3_frameTransform F _ (hFst U hr')).1 _ (hQhperm (Fin.last _))
    have hz0 : F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ∈ F.idealZ :=
      Ideal.subset_span ⟨_, rfl⟩
    rw [hz] at hz0
    exact h hz0

/-- At a point `x̂ ∈ X̂_s` over a point `x ∈ B_s` satisfying (1), (2), (3), with a frame
`(T_s; z_s)` as in `lem:IV.AB-4-frames`: the ideal `Q̂_s` of `B̂_s` is a prime with regular
quotient,
a permissible center for every `Ĵ_j(s)` ("Since `Q_s` is a permissible center for `J_0(s)`, `Q̂_s`
is such for `Ĵ_0(s)`"), and `z_s ∈ Q̂_s` ("and therefore we have `z_s ∈ Q̂_s`", p. 300; by
Remark 3 of § 9, Ch. III in the case `(ℜ^{N,n}_I, U)`, and because `B_s ⊆ F(s)` in the case
`(ℜ^{N,n}_I, F)`). -/
theorem Frame.isPermissibleCenter_and_mem_of_mem_B [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}}
    {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base xh))
    (hxB : (𝒮.c s).base xh ∈ (T.B s).pts)
    (F : RegularFrame ((𝒮.tHat.X s).presheaf.stalk xh)) (z : (𝒮.tHat.X s).presheaf.stalk xh)
    (hr : F.r = 1) (hz : ∀ i, F.z i = z) (hX : (𝒮.xBar s).stalkIdeal xh = Ideal.span {z})
    (hFst : ∀ U, r = .opn U → F.IsJStable
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal xh)) :
    ((𝒮.tHat.B s).stalkIdeal xh).IsPrime ∧
      IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk xh ⧸ (𝒮.tHat.B s).stalkIdeal xh) ∧
      (∀ j, IsPermissibleCenter _ ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh)
        ((𝒮.tHat.B s).stalkIdeal xh)) ∧
      z ∈ (𝒮.tHat.B s).stalkIdeal xh := by
  classical
  have hBperm := isPermissible_transformI_of_isPermissibleI_snoc (T.pre s) (T.B s)
    (T.monoidalTransformation s) ℜ (hS.permissible (s + 1)).isPermissibleI
  have hBF : ∀ F₁, r = .closed F₁ → (T.B s).pts ⊆ ((T.pre s).strictTransform F₁).pts := by
    intro F₁ hF₁
    subst hF₁
    exact (isPermissibleClosed_transformI_of_isPermissibleIClosed_snoc (T.pre s) (T.B s)
      (T.monoidalTransformation s) ℜ F₁ (hS.permissible (s + 1))).2.trans
        Set.inter_subset_right
  rw [𝒮.B_hat s]
  exact 𝒮.isPermissibleCenter_and_mem_of_isPermissible s (T.B s) hBperm hBF xh hx hxB F z hr hz hX
    hFst

/-- At a point of `X̂_s` over a point of `X_s` where `X_s` has dimension `N` (condition (1)), the
local ring of `X̂_s` has dimension `N` (Lemma (AB.2)). -/
theorem Frame.ringKrullDim_stalk_of_cond {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base xh)) :
    ringKrullDim ((𝒮.tHat.X s).presheaf.stalk xh) = N := by
  classical
  have hxh0 : (𝒮.tHat.pre s).composite.base xh = xhat0 X x₀ (hS.ambient.2.1 x₀) :=
    𝒮.composite_tHat_eq_xhat0 (hS.ambient.2.1 x₀) s xh hx.2.1
  obtain ⟨-, ⟨t₀, ht, ht', hinj⟩, -⟩ := 𝒮.isRegularLocalRing_and_mapsRSOP_stalkMap
    (hS.ambient.2.1 x₀) hS.isNonsingular_X hS.isNonsingular_B s xh hxh0
  rw [← ht'.2, Finset.card_image_of_injOn hinj, ht.2]
  exact hx.1

/-- At a point of `X̂_{s+1}` satisfying (1), (2), (3), over a point of `B̂_s`, the local ring is
residually separable algebraic over that of `X̂_s` (both have dimension `N`, Ch. III, Lemma of
§ 2 on dimensions; characteristic zero). -/
theorem Frame.isResiduallySeparableAlgebraic_toRing_of_cond [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}}
    {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X (s + 1))
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) (s + 1) ((𝒮.c (s + 1)).base xh))
    (hmem : (𝒮.tHat.f s).base xh ∈ (𝒮.tHat.B s).pts)
    [IsDomain ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh))]
    (T₁ : MonoidalTransform ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh))
      ((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh))) [IsLocalHom T₁.toRing]
    (e : T₁.ring ≃+* (𝒮.tHat.X (s + 1)).presheaf.stalk xh) :
    RingHom.IsResiduallySeparableAlgebraic T₁.toRing := by
  unfold RingHom.IsResiduallySeparableAlgebraic
  let _ := (ResidueField.map T₁.toRing).toAlgebra
  have hc : (𝒮.c s).base ((𝒮.tHat.f s).base xh) = (T.f s).base ((𝒮.c (s + 1)).base xh) :=
    congrArg (fun φ => φ.base xh) (𝒮.c_comm s)
  have hxs : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base ((𝒮.tHat.f s).base xh)) := by
    rw [hc]; exact hS.cond_f_of_cond_succ s _ hx
  have hB : (𝒮.tHat.B s).IsNonsingular := 𝒮.isNonsingular_B (hS.ambient.2.1 x₀)
    hS.isNonsingular_X hS.isNonsingular_B s
  have hP := Subscheme.isPrime_stalkIdeal_of_isNonsingular hB hmem
  have hSq := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hB hmem
  have hP0 : (𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨T₁.x, T₁.x_mem, T₁.x_ne_zero⟩
  have hres : RingHom.IsResiduallyAlgebraic T₁.toRing :=
    (MonoidalTransform.ringKrullDim_eq_iff T₁ hP hP0 hSq).mp (by
      rw [ringKrullDim_eq_of_ringEquiv e, 𝒮.ringKrullDim_stalk_of_cond (s + 1) xh hx,
        𝒮.ringKrullDim_stalk_of_cond s _ hxs])
  have : CharZero (ResidueField ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh))) := by
    have := hS.isAlgebraicScheme_X s
    exact (RingHom.charZero_iff (ResidueField.map
      ((𝒮.c s).stalkMap ((𝒮.tHat.f s).base xh)).hom).injective).mp
      (charZero_residueField_stalk (T.X s) _)
  have : Algebra.IsAlgebraic (ResidueField ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh)))
      (ResidueField T₁.ring) := hres
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- The stalk at `x̂_0` of the total transform `c_0⁻¹(V)` is `V_{x_0} Ŝ`, read in the stalk
through `stalkClosedPointIso`. -/
theorem stalkIdeal_totalTransform_c0_xhat0 {X : Scheme.{u}} {x₀ : X} (hx : X.IsSimpleAt x₀)
    (V : Subscheme X) :
    haveI : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
    (Subscheme.totalTransform (c0 X x₀) V).stalkIdeal (xhat0 X x₀ hx) =
      ((V.stalkIdeal x₀).map (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))).map
        (stalkClosedPointIso (CommRingCat.of (Shat X x₀))).inv.hom := by
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  have h1 : (c0 X x₀).stalkMap (xhat0 X x₀ hx) =
      ((X.presheaf.stalkCongr (Inseparable.of_eq (c0_apply_xhat0 X x₀ hx))).hom ≫
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))) ≫
        (stalkClosedPointIso (CommRingCat.of (Shat X x₀))).inv := by
    rw [← stalkMap_c0_xhat0]
    erw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h2 : (((X.presheaf.stalkCongr (Inseparable.of_eq (c0_apply_xhat0 X x₀ hx))).hom ≫
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))) ≫
      (stalkClosedPointIso (CommRingCat.of (Shat X x₀))).inv).hom =
      (stalkClosedPointIso (CommRingCat.of (Shat X x₀))).inv.hom.comp
        ((algebraMap (X.presheaf.stalk x₀) (Shat X x₀)).comp
          (X.presheaf.stalkCongr (Inseparable.of_eq (c0_apply_xhat0 X x₀ hx))).hom.hom) := rfl
  rw [stalkIdeal_totalTransform, h1]
  erw [h2]
  exact (Ideal.map_map _ _).symm.trans (congrArg _ ((Ideal.map_map _ _).symm.trans
    (congrArg _ (stalkIdeal_map_stalkCongr V (c0_apply_xhat0 X x₀ hx)))))

/-- A `J`-stable element `f` has, along every prime permissible center `Q` of `J`, the order it
has along the maximal ideal: `ν_Q(f) = ν_M(f)`.  This is the step "The prime ideal `Q̂_s` …
contains the element `z_s` of `Ŝ_s` and it is a permissible center for `Ĵ_j(s)`.  It follows
that `g_{jk}(s) ∈ Q̂_s^{ν_{jk}}`" (p. 302), for the `Ĵ_j(s)`-stable `g_{jk}(s)`.

\textbf{Deviation from the paper (gap filled).} The paper gives no argument.  The intended one
is Definition 11 of Ch. III at `ᾱ = 0`, for a permissible sequence whose first center is `Q`
(continued by trivial monoidal transforms); it needs a monoidal transform of `R` with center `Q`
that is residually separable algebraic over `R` (a closed point of the fibre; the residue field
has characteristic zero).  Proved by `IsJStable.ordElem_eq_of_isPermissibleCenter_of_charZero`
(`lem:IV.AB-4-stable-order-full`, `Compat/StableOrder.lean`). -/
@[blueprint "lem:IV.AB-4-stable-order"
  (statement := /-- Let $R$ be a regular local ring whose residue field has characteristic
    zero, $J$ an ideal of $R$, $f\in R$ a $J$-stable element (\cref{def:III.11}) and $Q$ a
    prime ideal of $R$ which is a permissible center for $J$ (\cref{def:III.8}). Then
    $\nu_Q(f)=\nu_M(f)$, $M$ the maximal ideal of $R$. (The step ``It follows that
    $g_{jk}(s)\in\hat Q_s^{\nu_{jk}}$'' of p.~302.) -/)
  (proof := /-- \textbf{Deviation from the paper (gap filled).} The paper gives no argument.
    Apply Definition~11 (\cref{def:III.11}) at $\bar\alpha=0$ to a permissible sequence whose
    first center is $Q$, continued by trivial monoidal transforms: this needs a monoidal
    transform of $R$ with center $Q$ which is residually separable algebraic over $R$ (a closed
    point of the fibre of the blow-up; the residue field has characteristic zero). Proved by
    \cref{lem:IV.AB-4-stable-order-full} (\texttt{Compat/StableOrder.lean}). -/)
  (latexEnv := "lemma")]
theorem _root_.Hironaka.IsJStable.ordElem_eq_of_isPermissibleCenter {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [CharZero (ResidueField R)] {J : Ideal R} {f : R}
    (hf : IsJStable J f) (Q : Ideal R) [Q.IsPrime] (hQ : IsPermissibleCenter R J Q) :
    Ideal.ordElem Q f = Ideal.ordElem (maximalIdeal R) f := by
  exact hf.ordElem_eq_of_isPermissibleCenter_of_charZero Q hQ

namespace Frame

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}

/-- The conclusion of `Frame.exists_regularFrame_stalk_of_cond` (`lem:IV.AB-4-frames`) at the
point `x̂` of `X̂_s`: a regular frame `(T_s; z_s)` (`F`, `r = 1`, `F.z = z`) of `Ŝ_s` with `z_s`
generating the ideal of `X̄_s`, `Ĵ_0(s)`-stable in the open case; `Ĵ_j(s)`-stable standard bases
`g_{jk}(s)` of `Ĵ_j(s)` with `ν_M(g_{jk}(s)) = ν_{jk} = ν^{(k)}(J_j)`, `b = ∏ ν_{jk}!` and
`g_{jk}(s) = z_s^{ν_{jk}} + ∑ g_{jki}(s) z_s^{ν_{jk}-i}`, `g_{jki}(s) ∈ T_s`; and the stalks of
`J̄(s)` at the points of `X̄_s` over `x̂` generated by the images of the `g_{jki}(s)^{b/i}`
(pp. 300–302).  (`J̄(s)` is formed on all of `X̄_s`, `def:IV.3-construction`, so the last clause
is stated at every point of `X̄_s` over `x̂`, not only at those of `X̄'_s`; the induction never
uses `X'_s`.)  `HasStalkFrame` says that some regular frame `F` works (`HasStalkFrameWith`). -/
def HasStalkFrame [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X s) : Prop :=
  ∃ (F : RegularFrame ((𝒮.tHat.X s).presheaf.stalk xh)) (z : (𝒮.tHat.X s).presheaf.stalk xh)
    (m : Fin (ℜ.β + 1) → ℕ) (ν : ∀ j, Fin (m j) → ℕ)
    (g : ∀ j, Fin (m j) → (𝒮.tHat.X s).presheaf.stalk xh)
    (co : ∀ j k, Fin (ν j k) → F.S),
    F.r = 1 ∧ (∀ i, F.z i = z) ∧
    (𝒮.xBar s).stalkIdeal xh = Ideal.span {z} ∧
    (∀ U, r = .opn U → F.IsJStable
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal xh)) ∧
    (∀ j, IsStandardBase _
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh) (g j)) ∧
    (∀ j k, IsJStable ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh)
      (g j k)) ∧
    (∀ j k, Ideal.ordElem (maximalIdeal _) (g j k) = ν j k) ∧
    (∀ j k, haveI : IsRegularLocalRing (X.presheaf.stalk x₀) := hS.ambient.2.1 x₀
      (ν j k : ℕ∞) = nuI (X.presheaf.stalk x₀) ((datumSystem ℜ j).stalkIdeal x₀)
        (k : ℕ).succPNat) ∧
    𝒮.b = ∏ j, ∏ k, (ν j k).factorial ∧
    (∀ j k, g j k = z ^ ν j k + ∑ i : Fin (ν j k),
      algebraMap F.S _ (co j k i) * z ^ (ν j k - ((i : ℕ) + 1))) ∧
    ∀ xb : (𝒮.xBar s).toScheme, ∀ h : xh = (𝒮.xBar s).ι.base xb,
      (𝒮.jBar s).stalkIdeal xb = (Ideal.span {y | ∃ j k i,
        y = algebraMap F.S _ (co j k i) ^ (𝒮.b / ((i : ℕ) + 1))}).map
        (((𝒮.tHat.X s).presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫
          (𝒮.xBar s).ι.stalkMap xb).hom

/-- `c_{s+1}⁻¹(V_j(s+1))` is the strict transform of `c_s⁻¹(V_j(s))` by `f̂_s` (strict transforms
commute with the flat base change `c_s`). -/
theorem totalTransform_c_sys_succ (𝒮 : Frame hS) (s : ℕ) (j : Fin (ℜ.β + 1)) :
    Subscheme.totalTransform (𝒮.c (s + 1)) (T.sys ℜ (s + 1) j) =
      Subscheme.strictTransform (𝒮.tHat.monoidalTransformation s)
        (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)) := by
  have : Flat (show (𝒮.tHat.monoidalTransformation s).X' ⟶ (T.monoidalTransformation s).X' from
      𝒮.c (s + 1)) := 𝒮.flat_c (hS.ambient.2.1 x₀) (s + 1)
  have hsys : T.sys ℜ (s + 1) j =
      Subscheme.strictTransform (T.monoidalTransformation s) (T.sys ℜ s j) :=
    Hironaka.MonoidalSuccession.strictTransform_snoc _ _ _ _
  rw [hsys]
  exact MonoidalTransformation.totalTransform_strictTransform_of_flat_square
    (T.monoidalTransformation s) (𝒮.tHat.monoidalTransformation s) (𝒮.c s) (𝒮.c (s + 1))
    (𝒮.c_comm s).symm (𝒮.B_hat s).symm _

/-- The two identifications of the stalks at equal points compose to the identity. -/
@[reassoc]
theorem _root_.Hironaka.stalkCongr_hom_comp_stalkCongr_hom {Y : Scheme.{u}} {p q : Y} (h₁ : p = q)
    (h₂ : q = p) :
    (Y.presheaf.stalkCongr (.of_eq h₁)).hom ≫ (Y.presheaf.stalkCongr (.of_eq h₂)).hom = 𝟙 _ := by
  subst h₁
  simp

/-- The stalk maps of `ι_{s+1}`, `ι_s`, `f̂_s`, `f̄_s` commute (`ι_s ∘ f̄_s = f̂_s ∘ ι_{s+1}`). -/
theorem stalkMap_fBar_comp_eq (𝒮 : Frame hS) (s : ℕ) (xb' : (𝒮.xBar (s + 1)).toScheme)
    (h : (𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb') =
      (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb')) :
    ((𝒮.fBar s).stalkMap xb').hom.comp
      (((𝒮.tHat.X s).presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫
        (𝒮.xBar s).ι.stalkMap ((𝒮.fBar s).base xb')).hom =
    ((𝒮.xBar (s + 1)).ι.stalkMap xb').hom.comp ((𝒮.tHat.f s).stalkMap
      ((𝒮.xBar (s + 1)).ι.base xb')).hom := by
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Category.assoc,
    ← Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_congr_hom _ _ (𝒮.fBar_comm s),
    Scheme.Hom.stalkMap_comp]
  erw [Hironaka.stalkCongr_hom_comp_stalkCongr_hom_assoc]
  all_goals first | rfl | exact h | exact h.symm

set_option maxHeartbeats 400000 in
/-- The case `s = 0` of `lem:IV.AB-4-frames`: at `x̂_0`, the frame `(T; z)` of [a], [b] and the
standard bases of [c] with `J̄(0) = (g_{jki}^{b/i}) T̄` of [e] ("`g_{jk}(0) = g_{jk}`",
"`g_{jki}(0) = g_{jki}`", p. 301; "By replacing `g_{jk}` by `g_{jk}/u_{jk}` we may assume
`g_{jk} = z^{ν_{jk}} + ∑ g_{jki} z^{ν_{jk}-i}`", p. 297), transported to the local ring of
`X̂_0 = Spec(Ŝ)` at its closed point (`stalkClosedPointIso`); the members of the system are
reindexed from `jSys` (`W` first) to `datumSystem` (`W` last); `ν_M(g_{jk}) = ν^{(k)}(J_j)` is the
order of the `k`-th member of a standard base (Lemma 1 of Ch. III) and `ν^{(k)}(Ĵ_j) = ν^{(k)}(J_j)`
(`S → Ŝ` transforms a regular system of parameters into one). -/
theorem hasStalkFrame_zero [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (xh : 𝒮.tHat.X 0)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) 0 ((𝒮.c 0).base xh)) :
    𝒮.HasStalkFrame 0 xh := by
  classical
  have hx0 := hS.ambient.2.1 x₀
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx0
  -- `x̂` is the closed point `x̂_0` of `X̂_0 = Spec(Ŝ)`
  have hxh : xh = xhat0 X x₀ hx0 := 𝒮.composite_tHat_eq_xhat0 hx0 0 xh hx.2.1
  subst hxh
  have := 𝒮.regShat
  -- the data [a]–[e] of the frame (p. 296–297), in `Ŝ`
  obtain ⟨Fr, h1, hFz, -, hbst, m, g, v, ν, co, hstd, hst, hν, hshape, hbprod, hjGen⟩ := 𝒮.frame
  -- `Ŝ ≅ O_{X̂_0, x̂_0}`
  let κ := stalkClosedPointIso (CommRingCat.of (Shat X x₀))
  have : IsRegularLocalRing ((𝒮.tHat.X 0).presheaf.stalk (xhat0 X x₀ hx0)) :=
    Frame.instIsRegularLocalRingStalk 𝒮 0 (xhat0 X x₀ hx0)
  let e : Shat X x₀ ≃+* (𝒮.tHat.X 0).presheaf.stalk (xhat0 X x₀ hx0) :=
    κ.symm.commRingCatIsoToRingEquiv
  have he : ∀ a, e a = κ.inv.hom a := fun _ => rfl
  let α := algebraMap (X.presheaf.stalk x₀) (Shat X x₀)
  have hmaps : RingHom.MapsRSOP α := mapsRSOP_algebraMap_adicCompletion
  -- the members of the system: `datumSystem` lists `W` last, `jSys` first
  let σ := finRotate (ℜ.β + 1)
  have hσ : ∀ j, jSys ℜ x₀ (σ j) = (datumSystem ℜ j).stalkIdeal x₀ := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [σ, finRotate_last, jSys, Fin.cons_zero, datumSystem, Fin.snoc_last]
    · have : σ i.castSucc = i.succ :=
        Fin.ext (by rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last i).ne]; simp)
      rw [this]
      simp only [jSys, Fin.cons_succ, datumSystem, Fin.snoc_castSucc]
  have hJ0 : ∀ j, (Subscheme.totalTransform (𝒮.c 0) (T.sys ℜ 0 j)).stalkIdeal
      (xhat0 X x₀ hx0) = ((jSys ℜ x₀ (σ j)).map α).map e := by
    intro j
    rw [hσ j, 𝒮.c_zero]
    exact stalkIdeal_totalTransform_c0_xhat0 hx0 (T.sys ℜ 0 j)
  have hFz' : ∀ i, Fr.z i = 𝒮.z := fun i => by
    rw [← hFz]; congr 1; exact Fin.ext (by have := i.2; omega)
  have hσlast : σ (Fin.last ℜ.β) = 0 := finRotate_last
  -- "By replacing `g_{jk}` by `g_{jk}/u_{jk}` we may assume …" (p. 297)
  have hstd' : ∀ j, IsStandardBase (Shat X x₀) ((jSys ℜ x₀ j).map α)
      (fun k => ((v j k)⁻¹ : (Shat X x₀)ˣ) * g j k) := fun j =>
    IsStandardBase.of_unit_mul (hstd j) (fun k => (v j k)⁻¹) (fun _ => rfl)
  have hshape' : ∀ j k, ((v j k)⁻¹ : (Shat X x₀)ˣ) * g j k = 𝒮.z ^ ν j k +
      ∑ i : Fin (ν j k), algebraMap Fr.S (Shat X x₀) (co j k i) * 𝒮.z ^ (ν j k - ((i : ℕ) + 1)) :=
    fun j k => by rw [hshape j k, Units.inv_mul_cancel_left]
  refine ⟨Fr.transport e, e 𝒮.z, fun j => m (σ j), fun j k => ν (σ j) k,
    fun j k => e (((v (σ j) k)⁻¹ : (Shat X x₀)ˣ) * g (σ j) k), fun j k i => co (σ j) k i, h1,
    fun i => congrArg e (hFz' i), ?_, ?_, fun j => ?_, fun j k => ?_, fun j k => ?_,
    fun j k => ?_, ?_, fun j k => ?_, ?_⟩
  · -- `X̄_0 = V(z)`
    have h2 := stalkIdeal_ofIdealTop_closedPoint (CommRingCat.of (Shat X x₀))
      (Ideal.span {𝒮.z})
    have h3 : Ideal.span {e 𝒮.z} = (Ideal.span {𝒮.z}).map κ.inv.hom := by
      rw [Ideal.map_span, Set.image_singleton]; rfl
    rw [h3]
    exact h2
  · intro U hU i
    rw [hJ0, hσlast]
    exact IsJStable.map_ringEquiv (hbst U hU i) e
  · rw [hJ0]
    have h2 := (isStandardBase_iff_isStandardBase_map
      (e : Shat X x₀ →+* (𝒮.tHat.X 0).presheaf.stalk (xhat0 X x₀ hx0))
      (mapsRSOP_ringEquiv e) _ _).mp (hstd' (σ j))
    rwa [Ideal.map_coe] at h2
  · rw [hJ0]
    exact IsJStable.map_ringEquiv (IsJStable.unit_mul (hst (σ j) k) _) e
  · rw [ordElem_maximalIdeal_ringEquiv e, ordElem_eq_nuI_of_isStandardBase _ _ (hstd' (σ j)) k,
      ← nuI_map_eq_of_mapsRSOP α hmaps _ _, ← hν (σ j) k]
  · rw [hν (σ j) k, hσ j]
  · rw [hbprod]
    exact (Equiv.prod_comp σ (fun j => ∏ k, (ν j k).factorial)).symm
  · show e _ = e 𝒮.z ^ ν (σ j) k + ∑ i : Fin (ν (σ j) k),
      e (algebraMap Fr.S (Shat X x₀) (co (σ j) k i)) * e 𝒮.z ^ (ν (σ j) k - ((i : ℕ) + 1))
    rw [hshape' (σ j) k, map_add, map_pow, map_sum]
    simp only [map_mul, map_pow]
  · -- [f]: `J̄(0)` is generated by the images of the `g_{jki}^{b/i}`
    intro xb h
    let O : Subscheme (𝒮.tHat.X 0) := Scheme.IdealSheafData.ofIdealTop ((Ideal.span 𝒮.jGen).map
      (Scheme.ΓSpecIso (CommRingCat.of (Shat X x₀))).inv.hom)
    have hO : Subscheme.stalkIdeal O (xhat0 X x₀ hx0) = (Ideal.span 𝒮.jGen).map κ.inv.hom :=
      stalkIdeal_ofIdealTop_closedPoint (CommRingCat.of (Shat X x₀)) (Ideal.span 𝒮.jGen)
    have hG : Ideal.span {y | ∃ j k i, y = algebraMap (Fr.transport e).S
        ((𝒮.tHat.X 0).presheaf.stalk (xhat0 X x₀ hx0)) (co (σ j) k i) ^
          (𝒮.b / ((i : ℕ) + 1))} = (Ideal.span 𝒮.jGen).map e := by
      rw [Ideal.map_span, hjGen]
      congr 1
      ext y
      constructor
      · rintro ⟨j, k, i, rfl⟩
        exact ⟨_, ⟨σ j, k, i, rfl⟩, (map_pow e _ _)⟩
      · rintro ⟨_, ⟨j', k, i, rfl⟩, rfl⟩
        obtain ⟨j, rfl⟩ := σ.surjective j'
        exact ⟨j, k, i, (map_pow e _ _)⟩
    show (Subscheme.totalTransform (𝒮.xBar 0).ι O).stalkIdeal xb = _
    rw [stalkIdeal_totalTransform, Subscheme.stalkIdeal_eq_map_stalkCongr O h, hO, hG,
      CommRingCat.hom_comp, ← Ideal.map_coe e]
    refine ((congrArg (Ideal.map _) (Ideal.map_map _ _)).trans (Ideal.map_map _ _)).trans ?_
    rw [Ideal.map_map]
    rfl

/-- The step `t → t + 1` of `lem:IV.AB-4-frames` at a point `x̂_{t+1}` whose image `x̂_t` is not
on `B̂_t` ("trivial monoidal transforms for which the centers `Q_t` are unit ideals (that is,
exactly for those cases in which `x_t` is not contained in `B_t`)", p. 300): `f̂_t` is a local
isomorphism at `x̂_{t+1}` and the data are transported along `Ŝ_t ≅ Ŝ_{t+1}`; off `B̂_t` the
divisor `f̄_t⁻¹(B̄_t)` is trivial, so `J̄(t + 1)` is the inverse image of `J̄(t)`. -/
theorem hasStalkFrame_succ_of_notMem [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X (s + 1))
    (hmem : (𝒮.tHat.f s).base xh ∉ (𝒮.tHat.B s).pts)
    (h : 𝒮.HasStalkFrame s ((𝒮.tHat.f s).base xh)) : 𝒮.HasStalkFrame (s + 1) xh := by
  classical
  obtain ⟨F, z, m, ν, g, co, hr, hz, hX, hFst, hstd, hgst, hord, hν, hb, hsh, hJ⟩ := h
  have hexc : xh ∉ (𝒮.tHat.monoidalTransformation s).exceptional.pts := by
    rw [MonoidalTransformation.exceptional, Subscheme.pts_totalTransform_eq_preimage]
    exact hmem
  let e : (𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh) ≃+*
      (𝒮.tHat.X (s + 1)).presheaf.stalk xh :=
    RingEquiv.ofBijective ((𝒮.tHat.f s).stalkMap xh).hom
      ((𝒮.tHat.monoidalTransformation s).bijective_stalkMap_of_notMem xh hmem)
  -- off the center, the stalks of strict transforms are the images of the stalks
  have hst : ∀ V : Subscheme (𝒮.tHat.X s),
      (Subscheme.strictTransform (𝒮.tHat.monoidalTransformation s) V).stalkIdeal xh =
        (V.stalkIdeal ((𝒮.tHat.f s).base xh)).map e := by
    intro V
    rw [MonoidalTransformation.strictTransform_stalkIdeal_of_notMem _ V hexc]
    exact stalkIdeal_totalTransform _ _ _
  have hJs : ∀ j, (Subscheme.totalTransform (𝒮.c (s + 1)) (T.sys ℜ (s + 1) j)).stalkIdeal xh =
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal
        ((𝒮.tHat.f s).base xh)).map e := by
    intro j
    have := hst (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j))
    rw [𝒮.totalTransform_c_sys_succ s j]
    exact this
  refine ⟨F.transport e, e z, m, ν, fun j k => e (g j k), co, hr, fun i => ?_, ?_, ?_, ?_, ?_,
    fun j k => (ordElem_maximalIdeal_ringEquiv e (g j k)).trans (hord j k), hν, hb, ?_, ?_⟩
  · exact congrArg e (hz i)
  · have := hst (𝒮.xBar s)
    rw [hX, Ideal.map_span, Set.image_singleton] at this
    exact this
  · intro U hU i
    rw [hJs]
    exact IsJStable.map_ringEquiv (hFst U hU i) e
  · intro j
    have h1 := (isStandardBase_iff_isStandardBase_map (e : (𝒮.tHat.X s).presheaf.stalk
      ((𝒮.tHat.f s).base xh) →+* (𝒮.tHat.X (s + 1)).presheaf.stalk xh) (mapsRSOP_ringEquiv e)
      _ (g j)).mp (hstd j)
    rw [Ideal.map_coe] at h1
    rw [hJs]
    exact h1
  · intro j k
    rw [hJs]
    exact IsJStable.map_ringEquiv (hgst j k) e
  · intro j k
    show e (g j k) = e z ^ ν j k + ∑ i : Fin (ν j k),
      e (algebraMap F.S _ (co j k i)) * e z ^ (ν j k - ((i : ℕ) + 1))
    rw [hsh j k, map_add, map_pow, map_sum]
    simp only [map_mul, map_pow]
  · intro xb' h'
    subst h'
    have hcomm : (𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb') =
        (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb') :=
      (congrArg (fun φ => φ.base xb') (𝒮.fBar_comm s)).symm
    have hIH := hJ _ hcomm
    have hBtop : (𝒮.tHat.B s).stalkIdeal ((𝒮.xBar s).ι.base ((𝒮.fBar s).base xb')) = ⊤ :=
      Subscheme.stalkIdeal_eq_top_of_notMem_pts (hcomm ▸ hmem)
    have hB : (𝒮.bBarOn s).stalkIdeal ((𝒮.fBar s).base xb') = ⊤ := by
      show (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s)).stalkIdeal _ = ⊤
      rw [stalkIdeal_totalTransform, hBtop, Ideal.map_top]
    rw [jBar_succ, Subscheme.stalkIdeal_divPow_of_isLocallyPrincipal
      (𝒮.isLocallyPrincipal_totalTransform_fBar_bBarOn s), stalkIdeal_totalTransform,
      stalkIdeal_totalTransform, hB, Ideal.map_top, Ideal.top_pow, Submodule.top_coe,
      Submodule.colon_univ, hIH, Ideal.map_map, 𝒮.stalkMap_fBar_comp_eq s xb' hcomm]
    have hG : {y | ∃ j k i, y = algebraMap (F.transport e).S
        ((𝒮.tHat.X (s + 1)).presheaf.stalk ((𝒮.xBar (s + 1)).ι.base xb')) (co j k i) ^
          (𝒮.b / ((i : ℕ) + 1))} =
        e '' {y | ∃ j k i, y = algebraMap F.S _ (co j k i) ^ (𝒮.b / ((i : ℕ) + 1))} := by
      ext y
      constructor
      · rintro ⟨j, k, i, rfl⟩
        exact ⟨_, ⟨j, k, i, rfl⟩, map_pow e _ _⟩
      · rintro ⟨_, ⟨j, k, i, rfl⟩, rfl⟩
        exact ⟨j, k, i, map_pow e _ _⟩
    erw [hG]
    rw [← Ideal.map_span, ← Ideal.map_coe e, Ideal.map_map]
    congr 1
    ext a
    simp [e, TopCat.Presheaf.stalkCongr_hom]
    rfl

private theorem unit_mul_pow_aux {A : Type*} [CommRing A] (c₁ x : A) (u : Aˣ) (n : ℕ) :
    c₁ * x ^ n = c₁ * ((u⁻¹ : Aˣ) : A) ^ n * ((u : A) * x) ^ n := by
  have : ((u⁻¹ : Aˣ) : A) ^ n * (u : A) ^ n = 1 := by
    rw [← mul_pow, Units.inv_mul, one_pow]
  calc c₁ * x ^ n = c₁ * (((u⁻¹ : Aˣ) : A) ^ n * (u : A) ^ n) * x ^ n := by rw [this, mul_one]
    _ = _ := by rw [mul_pow]; ring

section FrameTransformTuple

attribute [local instance] RegularFrame.isDomain_S

/-- Tuple of a frame transform with a denominator in the center (p. 300: "`z_{t+1} = z_t/v_t` with the
denominator `v_t ∈ T_t`", "`(v_t) Ŝ_{t+1} = Q̂_t Ŝ_{t+1}`"; p. 301: "`g_{jki}(t)/v_t^i = g_{jki}(t+1)`").
Ring level. -/
theorem _root_.Hironaka.RegularFrame.FrameTransform.exists_tuple {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] {F : RegularFrame R} {Q : Ideal R}
    {T : MonoidalTransform R Q} (FT : F.FrameTransform T)
    (hr : F.r = 1) (z : R) (hzF : ∀ j, F.z j = z) (x₀ : F.S)
    (hx₀Q : algebraMap F.S R x₀ ∈ Q) (hx₀ : FT.x = T.toRing (algebraMap F.S R x₀)) :
    ∃ (z' : T.ring) (c₀ : FT.TS.ring), (∀ j, FT.w j = z') ∧ FT.β c₀ = FT.x ∧ c₀ ≠ 0 ∧
      T.toRing z = FT.β c₀ * z' ∧
      ∀ (n : ℕ) (c : F.S), c ∈ (Q.comap (algebraMap F.S R)) ^ n →
        ∃ c' : FT.TS.ring, T.toRing (algebraMap F.S R c) = FT.β c' * (FT.β c₀) ^ n := by
  classical
  have hdomS := F.isDomain_S
  have := FT.isRegular
  have hlocβ : IsLocalHom FT.β := FT.canonical.isLocalHom
  set TS := FT.TS with hTS
  have hcomm : ∀ s : F.S, FT.β (TS.toRing s) = T.toRing (algebraMap F.S R s) := fun s =>
    RingHom.congr_fun FT.canonical.comm s
  have hinjS : Function.Injective (algebraMap F.S R) := fun a b hab =>
    F.quot_bijective.1 (by simp only [RingHom.comp_apply]; rw [hab])
  have hxne : FT.x ≠ 0 := by
    intro h0
    have h1 : T.toRing T.x ∈ Ideal.span {FT.x} := by
      rw [FT.span_x]; exact Ideal.mem_map_of_mem _ T.x_mem
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
    rw [h0, mul_zero] at ha
    exact T.x_ne_zero (T.toRing_injective (by rw [← ha, map_zero]))
  let j0 : Fin F.r := ⟨0, by rw [hr]; exact Nat.one_pos⟩
  have hFTw : ∀ j, FT.w j = FT.w j0 := fun j => by
    apply mul_left_cancel₀ hxne
    rw [FT.mul_w, FT.mul_w, hzF j, hzF j0]
  have hβc₀ : FT.β (TS.toRing x₀) = FT.x := by rw [hcomm, ← hx₀]
  refine ⟨FT.w j0, TS.toRing x₀, fun j => hFTw j, hβc₀, ?_, ?_, ?_⟩
  · intro h0
    apply hxne
    rw [← hβc₀, h0, map_zero]
  · rw [hβc₀, FT.mul_w j0, hzF j0]
  · intro n c hc
    have hx0mem : x₀ ∈ Q.comap (algebraMap F.S R) := Ideal.mem_comap.mpr hx₀Q
    have hspan := TS.span_xR_eq_map
    obtain ⟨a, ha⟩ : ∃ a : TS.ring, a * TS.xR = TS.toRing x₀ :=
      Ideal.mem_span_singleton'.mp (by rw [hspan]; exact Ideal.mem_map_of_mem _ hx0mem)
    have hβx : FT.β TS.xR ∈ Ideal.span {FT.x} := by
      rw [FT.span_x]
      have : FT.β TS.xR = T.toRing (algebraMap F.S R TS.x) := hcomm TS.x
      rw [this]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mp TS.x_mem)
    have hβxne : FT.β TS.xR ≠ 0 := by
      intro h0
      have : FT.β TS.xR = T.toRing (algebraMap F.S R TS.x) := hcomm TS.x
      rw [this] at h0
      exact TS.x_ne_zero (hinjS (T.toRing_injective (by rw [h0, map_zero, map_zero])))
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hβx
    have hunit : IsUnit a := by
      have h1 : FT.x = FT.β a * FT.β TS.xR := by rw [← hβc₀, ← ha, map_mul]
      have h2 : FT.β TS.xR * (b * FT.β a) = FT.β TS.xR * 1 := by
        calc FT.β TS.xR * (b * FT.β a) = (b * FT.x) := by rw [h1]; ring
          _ = FT.β TS.xR := hb
          _ = FT.β TS.xR * 1 := (mul_one _).symm
      have h3 : b * FT.β a = 1 := mul_left_cancel₀ hβxne h2
      exact isUnit_of_map_unit FT.β a (IsUnit.of_mul_eq_one b (by rw [mul_comm]; exact h3))
    obtain ⟨ua, hua⟩ := hunit
    have hmem : TS.toRing c ∈ Ideal.span {TS.xR ^ n} := by
      rw [← Ideal.span_singleton_pow, hspan, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hc
    obtain ⟨c₁, hc₁⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨c₁ * ((ua⁻¹ : TS.ringˣ) : TS.ring) ^ n, ?_⟩
    have hmain : TS.toRing c = c₁ * ((ua⁻¹ : TS.ringˣ) : TS.ring) ^ n * (TS.toRing x₀) ^ n := by
      rw [← ha, ← hua, ← hc₁]
      exact unit_mul_pow_aux c₁ TS.xR ua n
    rw [← hcomm c, hmain, map_mul, map_pow]

end FrameTransformTuple

/-- The strict transform of the principal ideal `(g)` along a monoidal transform with prime center
(or unit center) is `(g')`, when `g = v^k g'` with `(v) = P R'` and `k = ν_P(g)`. -/
theorem _root_.Hironaka.strictTransformIdeal_span_singleton_eq_of_eq_pow_mul {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] {P : Ideal R} (t : MonoidalTransform R P)
    (hP : (P.IsPrime ∧ IsRegularLocalRing (R ⧸ P)) ∨ P = ⊤) (v : t.ring)
    (hv : Ideal.span {v} = P.map t.toRing) (g : R) (k : ℕ) (g' : t.ring)
    (hk : P = ⊤ ∨ Ideal.ordElem P g = k) (hg : t.toRing g = v ^ k * g') :
    strictTransformIdeal t (Ideal.span {g}) = Ideal.span {g'} := by
  rcases hP with ⟨hPp, hPr⟩ | hPt
  · have hkP : Ideal.ordElem P g = k := hk.resolve_left hPp.ne_top
    obtain ⟨u, hu⟩ : Associated t.xR v :=
      Ideal.span_singleton_eq_span_singleton.mp (t.span_xR_eq_map.trans hv.symm)
    have hg'' : t.xR ^ (Ideal.ordElem P g).toNat * ((u : t.ring) ^ k * g') = t.toRing g := by
      rw [hkP, ENat.toNat_natCast, hg, ← hu, mul_pow, mul_assoc]
    rw [strictTransformIdeal_span_singleton_eq t hPp hPr g ((u : t.ring) ^ k * g') hg'']
    exact Ideal.span_singleton_mul_left_unit (u.isUnit.pow _) _
  · rw [strictTransformIdeal_eq_map_toRing_of_eq_top hPt t, Ideal.map_span, Set.image_singleton,
      hg]
    have hvu : IsUnit v := by
      have h1 : (1 : R) ∈ P := by rw [hPt]; exact Submodule.mem_top
      have h2 : (1 : t.ring) ∈ P.map t.toRing := by
        have := Ideal.mem_map_of_mem t.toRing h1
        rwa [map_one] at this
      rw [← hv] at h2
      exact Ideal.span_singleton_eq_top.mp (Ideal.eq_top_of_isUnit_mem _ h2 isUnit_one)
    exact Ideal.span_singleton_mul_left_unit (hvu.pow k) g'

/-- The local rings of `X̂_s` are domains (they are regular). -/
instance instIsDomainStalk [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X s) :
    IsDomain ((𝒮.tHat.X s).presheaf.stalk xh) :=
  isDomain_of_isRegularLocalRing _

/-- At a point `x̂ ∈ X̂_s` the ideal `Q̂_s` of `B̂_s` is a prime with regular quotient, or the unit
ideal (`B̂_s` is non-singular). -/
theorem isPrime_and_isRegularLocalRing_quotient_or_eq_top_stalkIdeal_B [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ)
    (xs : 𝒮.tHat.X s) :
    (((𝒮.tHat.B s).stalkIdeal xs).IsPrime ∧
      IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk xs ⧸ (𝒮.tHat.B s).stalkIdeal xs)) ∨
      (𝒮.tHat.B s).stalkIdeal xs = ⊤ := by
  by_cases hmem : xs ∈ (𝒮.tHat.B s).pts
  · have hB : (𝒮.tHat.B s).IsNonsingular := 𝒮.isNonsingular_B (hS.ambient.2.1 x₀)
      hS.isNonsingular_X hS.isNonsingular_B s
    exact Or.inl ⟨Subscheme.isPrime_stalkIdeal_of_isNonsingular hB hmem,
      Subscheme.isRegularLocalRing_quotient_of_isNonsingular hB hmem⟩
  · exact Or.inr (Subscheme.stalkIdeal_eq_top_of_notMem_pts hmem)

/-- At a point `x̂ ∈ X̂_s` over a point `x ∈ B_s` satisfying (1), (2), (3): the ideal `Q̂_s` of
`B̂_s` is a prime with regular quotient and a permissible center for every `Ĵ_j(s)`
("Since `Q_s` is a permissible center for `J_0(s)`, `Q̂_s` is such for `Ĵ_0(s)`", p. 300). -/
theorem isPermissibleCenter_stalkIdeal_of_mem_B [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base xh))
    (hxB : (𝒮.c s).base xh ∈ (T.B s).pts) (j : Fin (ℜ.β + 1)) :
    IsPermissibleCenter _ ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh)
        ((𝒮.tHat.B s).stalkIdeal xh) := by
  classical
  have : IsRegularLocalRing ((T.X s).presheaf.stalk ((𝒮.c s).base xh)) :=
    hS.isNonsingular_X s _
  have hBperm := isPermissible_transformI_of_isPermissibleI_snoc (T.pre s) (T.B s)
    (T.monoidalTransformation s) ℜ (hS.permissible (s + 1)).isPermissibleI
  have hQperm : ∀ j, IsPermissibleCenter _ ((T.sys ℜ s j).stalkIdeal ((𝒮.c s).base xh))
      ((T.B s).stalkIdeal ((𝒮.c s).base xh)) := by
    intro j
    obtain ⟨j', hj'⟩ := exists_datumSystem_transformI_eq_sys ℜ T s j
    rw [← hj']
    exact DatumI.Raw.isPermissibleCenter_stalkIdeal_datumSystem hBperm _ j'
  have hQne : (T.B s).stalkIdeal ((𝒮.c s).base xh) ≠ ⊤ :=
    Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hxB
  have : ((T.B s).stalkIdeal ((𝒮.c s).base xh)).IsPrime :=
    Subscheme.isPrime_stalkIdeal_of_isNonsingular (hS.isNonsingular_B s) hxB
  set α := ((𝒮.c s).stalkMap xh).hom with hαdef
  have hxh0 : (𝒮.tHat.pre s).composite.base xh = xhat0 X x₀ (hS.ambient.2.1 x₀) :=
    𝒮.composite_tHat_eq_xhat0 (hS.ambient.2.1 x₀) s xh hx.2.1
  have hα : RingHom.MapsRSOP α := (𝒮.isRegularLocalRing_and_mapsRSOP_stalkMap
    (hS.ambient.2.1 x₀) hS.isNonsingular_X hS.isNonsingular_B s xh hxh0).2.1
  have hQh : (𝒮.tHat.B s).stalkIdeal xh = ((T.B s).stalkIdeal ((𝒮.c s).base xh)).map α := by
    rw [𝒮.B_hat s, stalkIdeal_totalTransform]
  have hJP := ((hQperm j).resolve_left hQne).2.1
  rw [hQh, stalkIdeal_totalTransform]
  exact ((isPermissibleCenter_map_iff α hα _ _ hJP).2.2.2).mp (hQperm j)

/-- At any point `x̂ ∈ X̂_s` over a point satisfying (1), (2), (3), the ideal `Q̂_s` of `B̂_s` is a
permissible center for `Ĵ_j(s)` (trivially if `x̂ ∉ B̂_s`, `Q̂_s` being the unit ideal; the trivial
monoidal transforms which "we permit here", p. 300). -/
theorem isPermissibleCenter_stalkIdeal_B [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base xh)) (j : Fin (ℜ.β + 1)) :
    IsPermissibleCenter _ ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh)
        ((𝒮.tHat.B s).stalkIdeal xh) := by
  by_cases hmem : xh ∈ (𝒮.tHat.B s).pts
  · have hxB : (𝒮.c s).base xh ∈ (T.B s).pts := by
      have h1 := hmem
      rw [𝒮.B_hat s, Subscheme.pts_totalTransform_eq_preimage] at h1
      exact h1
    exact 𝒮.isPermissibleCenter_stalkIdeal_of_mem_B s xh hx hxB j
  · exact Or.inl (Subscheme.stalkIdeal_eq_top_of_notMem_pts hmem)

/-- A monoidal transform of the local ring of `X̂_s` at `x̂_s = f̂_s(x̂_{s+1})`, with center `Q̂_s`, is
residually separable algebraic over it (both have dimension `N`, Lemma (AB.2); trivial if
`x̂_s ∉ B̂_s`). -/
theorem isResiduallySeparableAlgebraic_toRing_of_cond' [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ)
    (xh : 𝒮.tHat.X (s + 1))
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) (s + 1) ((𝒮.c (s + 1)).base xh))
    [IsDomain ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh))]
    (T₁ : MonoidalTransform ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh))
      ((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh))) [IsLocalHom T₁.toRing]
    (e : T₁.ring ≃+* (𝒮.tHat.X (s + 1)).presheaf.stalk xh) :
    RingHom.IsResiduallySeparableAlgebraic T₁.toRing := by
  by_cases hmem : (𝒮.tHat.f s).base xh ∈ (𝒮.tHat.B s).pts
  · exact 𝒮.isResiduallySeparableAlgebraic_toRing_of_cond s xh hx hmem T₁ e
  · exact MonoidalTransform.isResiduallySeparableAlgebraic_toRing_of_eq_top
      (Subscheme.stalkIdeal_eq_top_of_notMem_pts hmem) T₁

/-- The conclusion of `Frame.exists_regularFrame_stalk_of_cond` (`lem:IV.AB-4-frames`) at the
point `x̂` of `X̂_s` for a given regular frame `F` of `Ŝ_s`: `F` (with `F.r = 1`, `F.z = z`) is the
frame `(T_s; z_s)` of the lemma, together with the data `g_{jk}(s)`, `ν_{jk}`, `g_{jki}(s)` (`co`)
and the stalks of `J̄(s)` (see `HasStalkFrame`, which says that some `F` works). -/
def HasStalkFrameWith [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X s)
    (F : RegularFrame ((𝒮.tHat.X s).presheaf.stalk xh)) : Prop :=
  ∃ (z : (𝒮.tHat.X s).presheaf.stalk xh)
    (m : Fin (ℜ.β + 1) → ℕ) (ν : ∀ j, Fin (m j) → ℕ)
    (g : ∀ j, Fin (m j) → (𝒮.tHat.X s).presheaf.stalk xh)
    (co : ∀ j k, Fin (ν j k) → F.S),
    F.r = 1 ∧ (∀ i, F.z i = z) ∧
    (𝒮.xBar s).stalkIdeal xh = Ideal.span {z} ∧
    (∀ U, r = .opn U → F.IsJStable
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal xh)) ∧
    (∀ j, IsStandardBase _
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh) (g j)) ∧
    (∀ j k, IsJStable ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh)
      (g j k)) ∧
    (∀ j k, Ideal.ordElem (maximalIdeal _) (g j k) = ν j k) ∧
    (∀ j k, haveI : IsRegularLocalRing (X.presheaf.stalk x₀) := hS.ambient.2.1 x₀
      (ν j k : ℕ∞) = nuI (X.presheaf.stalk x₀) ((datumSystem ℜ j).stalkIdeal x₀)
        (k : ℕ).succPNat) ∧
    𝒮.b = ∏ j, ∏ k, (ν j k).factorial ∧
    (∀ j k, g j k = z ^ ν j k + ∑ i : Fin (ν j k),
      algebraMap F.S _ (co j k i) * z ^ (ν j k - ((i : ℕ) + 1))) ∧
    ∀ xb : (𝒮.xBar s).toScheme, ∀ h : xh = (𝒮.xBar s).ι.base xb,
      (𝒮.jBar s).stalkIdeal xb = (Ideal.span {y | ∃ j k i,
        y = algebraMap F.S _ (co j k i) ^ (𝒮.b / ((i : ℕ) + 1))}).map
        (((𝒮.tHat.X s).presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫
          (𝒮.xBar s).ι.stalkMap xb).hom

set_option maxHeartbeats 400000 in
/-- **The step `t → t + 1` of `lem:IV.AB-4-frames`, given the frame transform.**  Let
`(T_t; z_t)` be a frame of `Ŝ_t` at `x̂_t = f̂_t(x̂_{t+1})` as in `HasStalkFrameWith`, `Ŝ_{t+1}` the
monoidal transform `T₁` of `Ŝ_t` with center `Q̂_t` (possibly the unit ideal: the trivial transforms
"permitted here", p. 300), and `(T_{t+1}; z_{t+1})` a regular frame `F'` of `T₁` with
"`z_{t+1} = z_t/v_t` with the denominator `v_t ∈ T_t`", "`(v_t)Ŝ_{t+1} = Q̂_tŜ_{t+1}`" (p. 300),
and "`g_{jki}(t)/v_t^i = g_{jki}(t + 1)`" (p. 301) (the hypotheses `hzv`, `hspan`, `hdiv`: `v_t` is
`algebraMap F'.S T₁.ring c₀`).  Then `(T_{t+1}; z_{t+1})` is a frame of `Ŝ_{t+1}` at `x̂_{t+1}` in
the sense of `HasStalkFrameWith`: "`g_{jk}(t)/v_t^{ν_{jk}} = g_{jk}(t + 1)`", "`g_{jki}(t)/v_t^i =
g_{jki}(t + 1)`", "`J̄(t + 1)_{x̂_{t+1}} = (v̄_t^{-b} J̄(t)_{x̂_t}) T̄_{t+1}`" (p. 301). -/
theorem hasStalkFrameWith_succ_of_frameTransform [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X (s + 1))
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) (s + 1) ((𝒮.c (s + 1)).base xh))
    (F : RegularFrame ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh)))
    (h : 𝒮.HasStalkFrameWith s ((𝒮.tHat.f s).base xh) F)
    (Q : Ideal ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh)))
    (hQdef : Q = (𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh))
    (T₁ : MonoidalTransform ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh)) Q)
    [hreg : IsRegularLocalRing T₁.ring]
    (e : T₁.ring ≃+* (𝒮.tHat.X (s + 1)).presheaf.stalk xh)
    (he : e.toRingHom.comp T₁.toRing = ((𝒮.tHat.f s).stalkMap xh).hom)
    (F' : RegularFrame T₁.ring) (z' : T₁.ring) (c₀ : F'.S)
    (hr' : F'.r = 1) (hz' : ∀ j, F'.z j = z')
    (hspan : Ideal.span {algebraMap F'.S T₁.ring c₀} = Q.map T₁.toRing)
    (hzv : ∀ j, T₁.toRing (F.z j) = algebraMap F'.S T₁.ring c₀ * z') (hc₀0 : c₀ ≠ 0)
    (hdiv : ∀ (n : ℕ) (c : F.S),
      c ∈ (Q.comap (algebraMap F.S ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh)))) ^ n →
      ∃ c' : F'.S, T₁.toRing (algebraMap F.S _ c) =
        algebraMap F'.S T₁.ring c' * (algebraMap F'.S T₁.ring c₀) ^ n) :
    𝒮.HasStalkFrameWith (s + 1) xh (F'.transport e) := by
  classical
  subst hQdef
  obtain ⟨z, m, ν, g, co, hr, hz, hX, hFst, hstd, hgst, hord, hν, hb, hsh, hJ⟩ := h
  -- the stage `s` at `x̂_s = f̂_s(x̂_{s+1})`
  have hc : (𝒮.c s).base ((𝒮.tHat.f s).base xh) = (T.f s).base ((𝒮.c (s + 1)).base xh) :=
    congrArg (fun φ => φ.base xh) (𝒮.c_comm s)
  have hxs : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base ((𝒮.tHat.f s).base xh)) := by
    rw [hc]; exact hS.cond_f_of_cond_succ s _ hx
  have : IsDomain ((𝒮.tHat.X s).presheaf.stalk
      ((𝒮.tHat.monoidalTransformation s).f.base xh)) := isDomain_of_isRegularLocalRing _
  -- `Q̂_s` is a prime with regular quotient, or the unit ideal
  have hQ := 𝒮.isPrime_and_isRegularLocalRing_quotient_or_eq_top_stalkIdeal_B s
    ((𝒮.tHat.f s).base xh)
  have hQperm := 𝒮.isPermissibleCenter_stalkIdeal_B s ((𝒮.tHat.f s).base xh) hxs
  have hsep := 𝒮.isResiduallySeparableAlgebraic_toRing_of_cond' s xh hx T₁ e
  -- `Ĵ_j(s+1) = Ĵ_j(s)'` (the strict transform)
  have hJ1 : ∀ j, (Subscheme.totalTransform (𝒮.c (s + 1)) (T.sys ℜ (s + 1) j)).stalkIdeal xh =
      (strictTransformIdeal T₁ ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal
        ((𝒮.tHat.f s).base xh))).map e := by
    intro j
    rw [𝒮.totalTransform_c_sys_succ s j]
    exact MonoidalTransformation.stalkIdeal_strictTransform_eq_map
      (𝒮.tHat.monoidalTransformation s) xh T₁ e he hQ _
  -- `ν*`, `τ*` are unchanged (condition (3) at `x_s` and `x_{s+1}`)
  have hchar : ∀ j,
      nuStar T₁.ring (strictTransformIdeal T₁ ((Subscheme.totalTransform (𝒮.c s)
        (T.sys ℜ s j)).stalkIdeal ((𝒮.tHat.f s).base xh))) =
        nuStar _ ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal
          ((𝒮.tHat.f s).base xh)) ∧
      t T₁.ring (strictTransformIdeal T₁ ((Subscheme.totalTransform (𝒮.c s)
        (T.sys ℜ s j)).stalkIdeal ((𝒮.tHat.f s).base xh))) =
        t _ ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal
          ((𝒮.tHat.f s).base xh)) ∧
      ∀ a, 1 ≤ a → a ≤ t _ ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal
          ((𝒮.tHat.f s).base xh)) →
        tau T₁.ring (strictTransformIdeal T₁ ((Subscheme.totalTransform (𝒮.c s)
          (T.sys ℜ s j)).stalkIdeal ((𝒮.tHat.f s).base xh))) a =
        tau _ ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal
          ((𝒮.tHat.f s).base xh)) a := by
    intro j
    obtain ⟨a1, a2, a3⟩ := 𝒮.nuStar_t_tau_eq_of_cond (s + 1) xh hx j
    obtain ⟨b1, b2, b3⟩ := 𝒮.nuStar_t_tau_eq_of_cond s _ hxs j
    obtain ⟨c1, c2, c3⟩ := nuStar_t_tau_map_ringEquiv e (strictTransformIdeal T₁
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal ((𝒮.tHat.f s).base xh)))
    rw [← hJ1] at c1 c2 c3
    refine ⟨c1.symm.trans (a1.trans b1.symm), c2.symm.trans (a2.trans b2.symm),
      fun a ha _ => (c3 a).symm.trans ((a3 a ha).trans (b3 a ha).symm)⟩
  -- the trivial monoidal transforms of `Ŝ_{s+1}` (continuing the sequences of Definition 11)
  have : IsDomain ((𝒮.tHat.X (s + 1)).presheaf.stalk
      ((MonoidalTransformation.idEmpty (𝒮.tHat.X (s + 1))).f.base xh)) :=
    isDomain_of_isRegularLocalRing _
  obtain ⟨T₀, -, -⟩ :=
    (MonoidalTransformation.idEmpty (𝒮.tHat.X (s + 1))).exists_monoidalTransform_stalk xh
  have hc₀ : (Subscheme.empty : Subscheme (𝒮.tHat.X (s + 1))).stalkIdeal
      ((MonoidalTransformation.idEmpty (𝒮.tHat.X (s + 1))).f.base xh) = ⊤ :=
    Subscheme.stalkIdeal_top_eq _
  let e' : T₁.ring ≃+* (𝒮.tHat.X (s + 1)).presheaf.stalk
      ((MonoidalTransformation.idEmpty (𝒮.tHat.X (s + 1))).f.base xh) := e
  -- the denominator `v_s = c₀` and the frame transform `(T_{s+1}; z_{s+1})`
  set v := algebraMap F'.S T₁.ring c₀ with hvdef
  have hdomT := isDomain_of_isRegularLocalRing T₁.ring
  have hxR0 : T₁.xR ≠ 0 := fun h0 => T₁.x_ne_zero (T₁.toRing_injective (by
    rw [map_zero]; exact h0))
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 : T₁.xR ∈ Ideal.span {v} := by
      rw [hspan, ← T₁.span_xR_eq_map]; exact Ideal.mem_span_singleton_self _
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at h1
    exact hxR0 (Ideal.mem_bot.mp h1)
  have hzv' : T₁.toRing z = v * z' := by
    have := hzv ⟨0, by rw [hr]; exact Nat.one_pos⟩
    rwa [hz] at this
  -- `z ∈ Q̂_s` and `ν_{Q̂_s}(z) = 1`, `ν_{Q̂_s}(g_{jk}(s)) = ν_{jk}` (unless `Q̂_s` is the unit ideal)
  have hkz : (𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh) = ⊤ ∨
      Ideal.ordElem ((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh)) z = 1 := by
    rcases hQ with ⟨hQprime, hQreg⟩ | hQtop
    · right
      have hxB : (𝒮.c s).base ((𝒮.tHat.f s).base xh) ∈ (T.B s).pts := by
        have h1 : (𝒮.tHat.f s).base xh ∈ (𝒮.tHat.B s).pts :=
          Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr hQprime.ne_top
        rw [𝒮.B_hat s, Subscheme.pts_totalTransform_eq_preimage] at h1
        exact h1
      obtain ⟨-, -, -, hzQ⟩ := 𝒮.isPermissibleCenter_and_mem_of_mem_B s _ hxs hxB
        F z hr hz hX hFst
      have hz2 : z ∉ maximalIdeal _ ^ 2 := F.extends_rsop.notMem_maximalIdeal_sq
        (Finset.mem_image.mpr ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, Finset.mem_univ _, hz _⟩)
      exact Ideal.ordElem_eq_one_of_mem_of_notMem_sq hQprime.ne_top hzQ hz2
    · exact Or.inl hQtop
  have hzspan : Ideal.span {z'} = strictTransformIdeal T₁ (Ideal.span {z}) :=
    (strictTransformIdeal_span_singleton_eq_of_eq_pow_mul T₁ hQ v hspan z 1 z' hkz
      (by rw [hzv', pow_one])).symm
  have hXst : (𝒮.xBar (s + 1)).stalkIdeal xh = Ideal.span {e z'} := by
    have h1 : (𝒮.xBar (s + 1)).stalkIdeal xh =
        (strictTransformIdeal T₁ ((𝒮.xBar s).stalkIdeal ((𝒮.tHat.f s).base xh))).map e :=
      MonoidalTransformation.stalkIdeal_strictTransform_eq_map
        (𝒮.tHat.monoidalTransformation s) xh T₁ e he hQ (𝒮.xBar s)
    rw [h1, hX, ← hzspan, Ideal.map_span, Set.image_singleton]
  have hordQ : ∀ j k, (𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh) = ⊤ ∨
      Ideal.ordElem ((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh)) (g j k) = ν j k := by
    intro j k
    rcases hQ with ⟨hQprime, hQreg⟩ | hQtop
    · right
      rw [IsJStable.ordElem_eq_of_monoidalTransform (hgst j k) (hQperm j) hQprime.ne_top T₁ hsep
        e' hc₀ T₀, hord]
    · exact Or.inl hQtop
  -- "`g_{jki}(s) ∈ (Q̂_s ∩ T_s)^i`"
  have hcoQ : ∀ j k (i : Fin (ν j k)), co j k i ∈
      (((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh)).comap (algebraMap F.S _)) ^
        ((i : ℕ) + 1) := by
    intro j k i
    rcases hQ with ⟨hQprime, hQreg⟩ | hQtop
    · have hxB : (𝒮.c s).base ((𝒮.tHat.f s).base xh) ∈ (T.B s).pts := by
        have h1 : (𝒮.tHat.f s).base xh ∈ (𝒮.tHat.B s).pts :=
          Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr hQprime.ne_top
        rw [𝒮.B_hat s, Subscheme.pts_totalTransform_eq_preimage] at h1
        exact h1
      obtain ⟨-, -, -, hzQ⟩ := 𝒮.isPermissibleCenter_and_mem_of_mem_B s _ hxs hxB
        F z hr hz hX hFst
      have hgQ : ∀ j k, g j k ∈ ((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh)) ^ ν j k :=
        fun j k => Ideal.mem_pow_of_le_ordElem ((hordQ j k).resolve_left hQprime.ne_top).ge
      exact RegularFrame.coeff_mem_comap_pow_of_mem_pow F z hz hr _ hQreg hzQ (ν j k) (co j k)
        (by rw [← hsh]; exact hgQ j k) i
    · rw [hQtop, Ideal.comap_top, Ideal.top_pow]; trivial
  -- "`g_{jki}(s)/v_s^i = g_{jki}(s + 1)`"
  choose c' hc' using fun j k (i : Fin (ν j k)) => hdiv ((i : ℕ) + 1) (co j k i) (hcoQ j k i)
  -- "`g_{jk}(s)/v_s^{ν_{jk}} = g_{jk}(s + 1)`"
  set g' : ∀ j, Fin (m j) → T₁.ring := fun j k => z' ^ ν j k + ∑ i : Fin (ν j k),
    algebraMap F'.S _ (c' j k i) * z' ^ (ν j k - ((i : ℕ) + 1)) with hg'def
  have hTg : ∀ j k, T₁.toRing (g j k) = v ^ ν j k * g' j k := by
    intro j k
    rw [hsh j k, map_add, map_pow, map_sum, hzv', mul_pow, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hzv', hc' j k i, mul_pow]
    have hi : (i : ℕ) + 1 ≤ ν j k := i.2
    have : v ^ ν j k = v ^ ((i : ℕ) + 1) * v ^ (ν j k - ((i : ℕ) + 1)) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    ring
  have hg'span : ∀ j k, Ideal.span {g' j k} = strictTransformIdeal T₁ (Ideal.span {g j k}) :=
    fun j k => (strictTransformIdeal_span_singleton_eq_of_eq_pow_mul T₁ hQ v hspan (g j k)
      (ν j k) (g' j k) (hordQ j k) (hTg j k)).symm
  -- the strict transforms `z_{s+1}`, `g_{jk}(s + 1)` are `Ĵ(s + 1)`-stable (Definition 11)
  have hinh : ∀ j k, Ideal.ordElem (maximalIdeal T₁.ring) (g' j k) =
      Ideal.ordElem (maximalIdeal _) (g j k) ∧
      IsJStable (strictTransformIdeal T₁ ((Subscheme.totalTransform (𝒮.c s)
        (T.sys ℜ s j)).stalkIdeal ((𝒮.tHat.f s).base xh))) (g' j k) := fun j k =>
    IsJStable.strictTransform (hgst j k) (hQperm j) T₁ hsep (hchar j).1 (hchar j).2.1
      (hchar j).2.2 (g' j k) (hg'span j k) e' hc₀ T₀
  refine ⟨e z', m, ν, fun j k => e (g' j k), c', hr', fun i => ?_, ?_, ?_, ?_,
    ?_, fun j k => ?_, hν, hb, fun j k => ?_, ?_⟩
  · exact congrArg e (hz' i)
  · exact hXst
  · intro U hU i
    show IsJStable _ (e (F'.z i))
    rw [hJ1, hz' i]
    have hzst : IsJStable ((Subscheme.totalTransform (𝒮.c s)
        (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal ((𝒮.tHat.f s).base xh)) z := by
      have := hFst U hU ⟨0, by rw [hr]; exact Nat.one_pos⟩
      rwa [hz] at this
    have h1 := (IsJStable.strictTransform hzst (hQperm _) T₁ hsep (hchar _).1 (hchar _).2.1
      (hchar _).2.2 z' hzspan e' hc₀ T₀).2
    exact IsJStable.map_ringEquiv h1 e
  · intro j
    rw [hJ1]
    exact IsStandardBase.map_strictTransform_of_isJStableSystem (hstd j) (hgst j) (hQperm j) T₁ hsep
      (hchar j).1 (hchar j).2.1 (hchar j).2.2 (g' j) (hg'span j) e' hc₀ T₀
  · intro j k
    rw [hJ1]
    exact IsJStable.map_ringEquiv (hinh j k).2 e
  · rw [ordElem_maximalIdeal_ringEquiv e (g' j k), (hinh j k).1, hord]
  · show e (g' j k) = e z' ^ ν j k + ∑ i : Fin (ν j k),
      e (algebraMap F'.S _ (c' j k i)) * e z' ^ (ν j k - ((i : ℕ) + 1))
    simp only [hg'def, map_add, map_pow, map_sum, map_mul]
  · -- "`J̄(s + 1)_{x̂_{s+1}} = (v̄_s^{-b} J̄(s)_{x̂_s}) T̄_{s+1}`" (p. 301)
    intro xb' h'
    subst h'
    have hcomm : (𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb') =
        (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb') :=
      (congrArg (fun φ => φ.base xb') (𝒮.fBar_comm s)).symm
    have hIH := hJ _ hcomm
    have hBb : (𝒮.bBarOn s).stalkIdeal ((𝒮.fBar s).base xb') =
        ((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb'))).map
          (((𝒮.tHat.X s).presheaf.stalkCongr (Inseparable.of_eq hcomm)).hom ≫
            (𝒮.xBar s).ι.stalkMap ((𝒮.fBar s).base xb')).hom := by
      show (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s)).stalkIdeal _ = _
      rw [stalkIdeal_totalTransform, CommRingCat.hom_comp, ← Ideal.map_map,
        stalkIdeal_map_stalkCongr _ hcomm]
    rw [jBar_succ, Subscheme.stalkIdeal_divPow_of_isLocallyPrincipal
      (𝒮.isLocallyPrincipal_totalTransform_fBar_bBarOn s), stalkIdeal_totalTransform,
      stalkIdeal_totalTransform, hIH, hBb, Ideal.map_map, Ideal.map_map,
      𝒮.stalkMap_fBar_comp_eq s xb' hcomm, ← he]
    obtain ⟨ψ', hψ'⟩ : ∃ ψ' : T₁.ring →+* (𝒮.xBar (s + 1)).toScheme.presheaf.stalk xb',
        ψ' = ((𝒮.xBar (s + 1)).ι.stalkMap xb').hom.comp e.toRingHom := ⟨_, rfl⟩
    have hcompφ : ((𝒮.xBar (s + 1)).ι.stalkMap xb').hom.comp (e.toRingHom.comp T₁.toRing) =
        ψ'.comp T₁.toRing := by rw [hψ']; rfl
    -- `b = ∏ ν_{jk}!` is divisible by every `i ≤ ν_{jk}`
    have hdvd : ∀ j k (i : Fin (ν j k)), (i : ℕ) + 1 ∣ 𝒮.b := by
      intro j k i
      rw [hb]
      exact ((Nat.dvd_factorial (Nat.succ_pos _) i.2).trans
        (Finset.dvd_prod_of_mem (fun k => (ν j k).factorial) (Finset.mem_univ k))).trans
          (Finset.dvd_prod_of_mem (fun j => ∏ k, (ν j k).factorial) (Finset.mem_univ j))
    -- "`(g_{jki}(s)^{b/i})/v_s^b = g_{jki}(s + 1)^{b/i}`"
    have hGT : (Ideal.span {y | ∃ j k i,
        y = algebraMap F.S _ (co j k i) ^ (𝒮.b / ((i : ℕ) + 1))}).map T₁.toRing =
        Ideal.span (Set.range fun p : (Σ j, Σ k : Fin (m j), Fin (ν j k)) =>
          v ^ 𝒮.b * algebraMap F'.S _ (c' p.1 p.2.1 p.2.2) ^ (𝒮.b / ((p.2.2 : ℕ) + 1))) := by
      have key : ∀ j k (i : Fin (ν j k)), T₁.toRing (algebraMap F.S _ (co j k i) ^
          (𝒮.b / ((i : ℕ) + 1))) = v ^ 𝒮.b * algebraMap F'.S _ (c' j k i) ^
            (𝒮.b / ((i : ℕ) + 1)) := by
        intro j k i
        rw [map_pow, hc' j k i, mul_pow, ← pow_mul, Nat.mul_div_cancel' (hdvd j k i), mul_comm]
      rw [Ideal.map_span]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨j, k, i, hx⟩, hy⟩
        exact ⟨⟨j, k, i⟩, by rw [← hy, hx, key]⟩
      · rintro ⟨⟨j, k, i⟩, hy⟩
        exact ⟨_, ⟨j, k, i, rfl⟩, by rw [key]; exact hy⟩
    -- the local ring `T̄_{s+1}` of `X̄_{s+1}` is a domain, and `v̄_s ≠ 0` in it
    have hker : RingHom.ker ((𝒮.xBar (s + 1)).ι.stalkMap xb').hom = Ideal.span {e z'} := by
      rw [← stalkIdeal_eq_ker_stalkMap, hXst]
    have hrange : Set.range F'.z = {z'} := by
      ext a
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩; exact hz' j
      · rintro rfl
        exact ⟨⟨0, by rw [hr']; exact Nat.one_pos⟩, hz' _⟩
    have hq := F'.quot_bijective
    rw [hrange] at hq
    have := RegularFrame.isDomain_S F'
    have hprime : (Ideal.span {z'}).IsPrime := by
      have : IsDomain (T₁.ring ⧸ Ideal.span {z'}) :=
        (RingEquiv.ofBijective _ hq).symm.injective.isDomain
          ((RingEquiv.ofBijective _ hq).symm : T₁.ring ⧸ Ideal.span {z'} →+* F'.S)
      exact (Ideal.Quotient.isDomain_iff_prime _).mp this
    have hprime' : (Ideal.span {e z'}).IsPrime := by
      have := Ideal.map_isPrime_of_equiv e (I := Ideal.span {z'})
      rwa [Ideal.map_span, Set.image_singleton] at this
    have hdomD : IsDomain ((𝒮.xBar (s + 1)).toScheme.presheaf.stalk xb') := by
      have : IsDomain ((𝒮.tHat.X (s + 1)).presheaf.stalk ((𝒮.xBar (s + 1)).ι.base xb') ⧸
          RingHom.ker ((𝒮.xBar (s + 1)).ι.stalkMap xb').hom) := by
        rw [hker]; exact (Ideal.Quotient.isDomain_iff_prime _).mpr hprime'
      let φ := RingHom.quotientKerEquivOfSurjective ((𝒮.xBar (s + 1)).ι.stalkMap_surjective xb')
      exact Function.Injective.isDomain φ.symm φ.symm.injective
    have hv0' : ψ' v ≠ 0 := by
      intro h0
      have h1 : e v ∈ RingHom.ker ((𝒮.xBar (s + 1)).ι.stalkMap xb').hom := by
        rw [hψ'] at h0; exact h0
      rw [hker, Ideal.mem_span_singleton'] at h1
      obtain ⟨a, ha⟩ := h1
      have h2 : v ∈ Ideal.span {z'} := by
        rw [Ideal.mem_span_singleton']
        refine ⟨e.symm a, e.injective ?_⟩
        rw [map_mul, RingEquiv.apply_symm_apply, ha]
      apply hc₀0
      apply hq.1
      rw [RingHom.comp_apply, RingHom.comp_apply, map_zero, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h2
    have h1 : Ideal.map (ψ'.comp T₁.toRing) (Ideal.span {y | ∃ j k i,
        y = algebraMap F.S _ (co j k i) ^ (𝒮.b / ((i : ℕ) + 1))}) =
        Ideal.span (Set.range fun p : (Σ j, Σ k : Fin (m j), Fin (ν j k)) =>
          ψ' v ^ 𝒮.b * ψ' (algebraMap F'.S _ (c' p.1 p.2.1 p.2.2)) ^
            (𝒮.b / ((p.2.2 : ℕ) + 1))) := by
      refine (Ideal.map_map T₁.toRing ψ').symm.trans ((congrArg (Ideal.map ψ') hGT).trans ?_)
      rw [Ideal.map_span, ← Set.range_comp]
      refine congrArg Ideal.span (congrArg Set.range (funext fun p => ?_))
      simp only [Function.comp_apply, map_mul, map_pow]
    have h2 : Ideal.map (ψ'.comp T₁.toRing)
        ((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb'))) =
        Ideal.span {ψ' v} := by
      refine (Ideal.map_map T₁.toRing ψ').symm.trans ?_
      rw [← hspan, Ideal.map_span, Set.image_singleton]
    have key : Submodule.colon (Ideal.map (ψ'.comp T₁.toRing) (Ideal.span {y | ∃ j k i,
        y = algebraMap F.S _ (co j k i) ^ (𝒮.b / ((i : ℕ) + 1))}))
        ((Ideal.map (ψ'.comp T₁.toRing) ((𝒮.tHat.B s).stalkIdeal
          ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb'))) ^ 𝒮.b : Ideal _) : Set _) =
        Ideal.span (Set.range fun p : (Σ j, Σ k : Fin (m j), Fin (ν j k)) =>
          ψ' (algebraMap F'.S _ (c' p.1 p.2.1 p.2.2)) ^ (𝒮.b / ((p.2.2 : ℕ) + 1))) := by
      rw [h1, h2]
      exact Ideal.colon_span_range_mul_pow (ψ' v) hv0' 𝒮.b _
    rw [hcompφ]
    refine key.trans ?_
    rw [Ideal.map_span]
    refine congrArg Ideal.span ?_
    ext y
    constructor
    · rintro ⟨⟨j, k, i⟩, hy⟩
      refine ⟨_, ⟨j, k, i, rfl⟩, ?_⟩
      rw [← hy, hψ']
      simp [TopCat.Presheaf.stalkCongr_hom]
      rfl
    · rintro ⟨x, ⟨j, k, i, hx⟩, hy⟩
      refine ⟨⟨j, k, i⟩, ?_⟩
      rw [← hy, hx, hψ']
      simp [TopCat.Presheaf.stalkCongr_hom]
      rfl

/-- A point of one of the schemes `X̂_t`, `t ∈ ℕ`: the stage `t` and the point `x̂_t ∈ X̂_t`
(p. 300: "Let `x̂_t` be the image of `x̂` in `X̂'_t`, so that we have `x_t = c_t(x̂_t)` for
`0 ≤ t ≤ s`").  Its
local ring is `Ŝ_t`, "the local ring of `X̂_t` at `x̂_t`". -/
structure TowerPoint (𝒮 : Frame hS) where
  /-- The stage `t`. -/
  stage : ℕ
  /-- The point `x̂_t` of `X̂_t`. -/
  pt : 𝒮.tHat.X stage

namespace TowerPoint

variable {𝒮 : Frame hS}

/-- `Ŝ_t`, the local ring of `X̂_t` at `x̂_t`. -/
abbrev ring (y : 𝒮.TowerPoint) : Type u := (𝒮.tHat.X y.stage).presheaf.stalk y.pt

/-- `Ĵ_0(t) = J_0(t) Ŝ_t`, the ideal of `c_t⁻¹(W(t))` in `Ŝ_t`. -/
noncomputable def ideal (y : 𝒮.TowerPoint) : Ideal y.ring :=
  (Subscheme.totalTransform (𝒮.c y.stage) (T.sys ℜ y.stage (Fin.last ℜ.β))).stalkIdeal y.pt

/-- The conditions (1), (2), (3) of Lemma (AB.4) at the image `x_t = c_t(x̂_t)`. -/
def Cond (y : 𝒮.TowerPoint) : Prop :=
  AB.Cond N ℜ T x₀ (hS.ambient.2.1 x₀) y.stage ((𝒮.c y.stage).base y.pt)

/-- The image `x̂_{t-1} = f̂_{t-1}(x̂_t)` of `x̂_t` (the point itself at stage `0`).  (Reducible, so
that instance search sees `down ⟨t + 1, x⟩ = ⟨t, f̂_t(x)⟩`.) -/
@[reducible] def down : 𝒮.TowerPoint → 𝒮.TowerPoint
  | ⟨0, x⟩ => ⟨0, x⟩
  | ⟨t + 1, x⟩ => ⟨t, (𝒮.tHat.f t).base x⟩

theorem stage_down (y : 𝒮.TowerPoint) : (down y).stage = y.stage - 1 := by
  obtain ⟨t, x⟩ := y
  cases t <;> rfl

theorem down_ne_self {y : 𝒮.TowerPoint} (h : y.stage ≠ 0) : down y ≠ y := by
  intro hd
  have := congrArg TowerPoint.stage hd
  rw [stage_down] at this
  omega

/-- The canonical homomorphism `Ŝ_{t-1} → Ŝ_t` of the stalks of `f̂_{t-1}` at `x̂_t`. -/
noncomputable def stalkMap : (y : 𝒮.TowerPoint) → (down y).ring →+* y.ring
  | ⟨0, _⟩ => RingHom.id _
  | ⟨t + 1, x⟩ => ((𝒮.tHat.f t).stalkMap x).hom

/-- "By Theorem 3, § 5, Ch. III, the image `x_t` of `x` in `X'_t` `(0 ≤ t ≤ s)` satisfies also the
conditions (1), (2) and (3)" (p. 300). -/
theorem Cond.down [Hironaka.HironakaCitedResults.{u}] {y : 𝒮.TowerPoint} (hy : y.Cond) : (down y).Cond := by
  obtain ⟨t, x⟩ := y
  cases t with
  | zero => exact hy
  | succ s =>
    have hc : (𝒮.c s).base ((𝒮.tHat.f s).base x) = (T.f s).base ((𝒮.c (s + 1)).base x) :=
      congrArg (fun φ => φ.base x) (𝒮.c_comm s)
    show AB.Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base ((𝒮.tHat.f s).base x))
    rw [hc]
    exact hS.cond_f_of_cond_succ s _ hy

/-- The points `x̂_k`, `0 ≤ k ≤ s`, over `x̂_s = y` (the stage-`s` point `y` itself for `k ≥ s`). -/
def chainPt (y : 𝒮.TowerPoint) (k : ℕ) : 𝒮.TowerPoint := down^[y.stage - k] y

theorem stage_iterate_down (y : 𝒮.TowerPoint) (m : ℕ) : (down^[m] y).stage = y.stage - m := by
  induction m generalizing y with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, ih, stage_down]; omega

theorem stage_chainPt (y : 𝒮.TowerPoint) {k : ℕ} (hk : k ≤ y.stage) : (chainPt y k).stage = k := by
  unfold chainPt
  rw [stage_iterate_down]
  omega

theorem cond_chainPt [Hironaka.HironakaCitedResults.{u}] {y : 𝒮.TowerPoint} (hy : y.Cond) (k : ℕ) : (chainPt y k).Cond := by
  unfold chainPt
  generalize y.stage - k = m
  induction m with
  | zero => exact hy
  | succ m ih => rw [Function.iterate_succ_apply']; exact ih.down

theorem down_chainPt_succ (y : 𝒮.TowerPoint) {k : ℕ} (hk : k < y.stage) :
    down (chainPt y (k + 1)) = chainPt y k := by
  unfold chainPt
  have : y.stage - k = (y.stage - (k + 1)) + 1 := by omega
  rw [this, Function.iterate_succ_apply']

theorem chainPt_of_le (y : 𝒮.TowerPoint) {k : ℕ} (hk : y.stage ≤ k) : chainPt y k = y := by
  unfold chainPt
  rw [Nat.sub_eq_zero_of_le hk]
  rfl

/-- One step `Ŝ_t → Ŝ_{t+1}` of the sequence of local rings along the images of `x̂`: the pair
`(y, y')` is `(x̂_t, x̂_{t+1})` and `Ŝ_{t+1}` is a monoidal transform of `Ŝ_t` with center `Q̂_t`
(or a trivial one, the unit ideal), `Ĵ_0(t+1)` its strict transform of `Ĵ_0(t)`, "residually
separable algebraic", `Q̂_t` a permissible center for `Ĵ_0(t)` (pp. 299--300).  For a real step
(`y = down y'`) the center is the ideal of `B̂_t` and the identification is the one of
`MonoidalTransformation.exists_monoidalTransform_stalk` (`real`). -/
structure StepData [Hironaka.HironakaCitedResults.{u}] (y y' : 𝒮.TowerPoint) where
  /-- The center `Q̂_t`. -/
  center : Ideal y.ring
  /-- The monoidal transform. -/
  Tr : MonoidalTransform y.ring center
  /-- Its identification with `Ŝ_{t+1}`. -/
  e : Tr.ring ≃+* y'.ring
  /-- `Ĵ_0(t+1)` is the strict transform of `Ĵ_0(t)`. -/
  ideal_succ : y'.ideal = (strictTransformIdeal Tr y.ideal).map e
  /-- `Q̂_t` is a permissible center for `Ĵ_0(t)`. -/
  perm : IsPermissibleCenter y.ring y.ideal center
  /-- `Ŝ_{t+1}` is residually separable algebraic over `Ŝ_t`. -/
  sep : RingHom.IsResiduallySeparableAlgebraic Tr.toRing
  /-- For a real step: the center is the ideal of `B̂_t` and `e` is compatible with the stalk map
  of `f̂_t`. -/
  real : down y' = y → y'.stage ≠ 0 →
    HEq center ((𝒮.tHat.B (down y').stage).stalkIdeal (down y').pt) ∧
      HEq (e.toRingHom.comp Tr.toRing) y'.stalkMap

instance [Hironaka.HironakaCitedResults.{u}] {y y' : 𝒮.TowerPoint} (SD : StepData y y') : IsRegularLocalRing SD.Tr.ring :=
  IsRegularLocalRing.of_ringEquiv SD.e.symm

set_option maxHeartbeats 400000 in
/-- A real step exists at every point satisfying (1), (2), (3) (the monoidal transform of
`MonoidalTransformation.exists_monoidalTransform_stalk`). -/
theorem exists_stepData_of_down_eq [Hironaka.HironakaCitedResults.{u}] (y y' : 𝒮.TowerPoint) (h : down y' = y) (hne : y'.stage ≠ 0)
    (hx : y'.Cond) : Nonempty (StepData y y') := by
  subst h
  obtain ⟨t, xh⟩ := y'
  cases t with
  | zero => exact absurd rfl hne
  | succ s =>
    have hx' : AB.Cond N ℜ T x₀ (hS.ambient.2.1 x₀) (s + 1) ((𝒮.c (s + 1)).base xh) := hx
    have hxs : AB.Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base ((𝒮.tHat.f s).base xh)) :=
      Cond.down (y := ⟨s + 1, xh⟩) hx
    have : IsDomain ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh)) :=
      isDomain_of_isRegularLocalRing _
    have : IsDomain ((𝒮.tHat.X s).presheaf.stalk
        ((𝒮.tHat.monoidalTransformation s).f.base xh)) := isDomain_of_isRegularLocalRing _
    obtain ⟨T₁, e, he⟩ : ∃ (T₁ : MonoidalTransform ((𝒮.tHat.X s).presheaf.stalk
        ((𝒮.tHat.f s).base xh)) ((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh)))
        (e : T₁.ring ≃+* (𝒮.tHat.X (s + 1)).presheaf.stalk xh),
        e.toRingHom.comp T₁.toRing = ((𝒮.tHat.f s).stalkMap xh).hom :=
      (𝒮.tHat.monoidalTransformation s).exists_monoidalTransform_stalk xh
    have : IsRegularLocalRing T₁.ring := IsRegularLocalRing.of_ringEquiv e.symm
    have hQ := 𝒮.isPrime_and_isRegularLocalRing_quotient_or_eq_top_stalkIdeal_B s
      ((𝒮.tHat.f s).base xh)
    refine ⟨{
      center := (𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh)
      Tr := T₁
      e := e
      ideal_succ := ?_
      perm := 𝒮.isPermissibleCenter_stalkIdeal_B s _ hxs (Fin.last ℜ.β)
      sep := 𝒮.isResiduallySeparableAlgebraic_toRing_of_cond' s xh hx' T₁ e
      real := fun _ _ => ⟨HEq.rfl, heq_of_eq he⟩ }⟩
    show (Subscheme.totalTransform (𝒮.c (s + 1)) (T.sys ℜ (s + 1) (Fin.last ℜ.β))).stalkIdeal xh =
      (strictTransformIdeal T₁ ((Subscheme.totalTransform (𝒮.c s)
        (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal ((𝒮.tHat.f s).base xh))).map e
    rw [𝒮.totalTransform_c_sys_succ s (Fin.last ℜ.β)]
    exact MonoidalTransformation.stalkIdeal_strictTransform_eq_map
      (𝒮.tHat.monoidalTransformation s) xh T₁ e he hQ _

/-- A padding step exists: "we permit here some trivial monoidal transforms for which the centers
`Q_t` are unit ideals" (p. 300; the monoidal transform with center `R` is `R` itself, p. 209). -/
theorem exists_stepData_of_eq [Hironaka.HironakaCitedResults.{u}] (y y' : 𝒮.TowerPoint) (h : y' = y) :
    Nonempty (StepData y y') := by
  subst h
  let T₀ : MonoidalTransform y'.ring ⊤ := MonoidalTransform.top y'.ring
  let Sq := MonoidalSequence.const y'.ideal (rfl : (⊤ : Ideal y'.ring) = ⊤) T₀
  exact ⟨{
    center := ⊤
    Tr := T₀
    e := Sq.equiv 0
    ideal_succ := Sq.ideal_succ 0
    perm := Or.inl rfl
    sep := MonoidalTransform.isResiduallySeparableAlgebraic_toRing_of_eq_top rfl T₀
    real := fun hd hne => absurd hd (down_ne_self hne) }⟩

end TowerPoint

namespace TowerPoint

variable {𝒮 : Frame hS}

theorem exists_stepData_chainPt [Hironaka.HironakaCitedResults.{u}] (y₀ : 𝒮.TowerPoint) (hy₀ : y₀.Cond) (k : ℕ) :
    Nonempty (StepData (chainPt y₀ k) (chainPt y₀ (k + 1))) := by
  by_cases hk : k < y₀.stage
  · refine exists_stepData_of_down_eq _ _ (down_chainPt_succ y₀ hk) ?_ (cond_chainPt hy₀ _)
    have := stage_chainPt y₀ (show k + 1 ≤ y₀.stage by omega)
    rw [this]
    omega
  · refine exists_stepData_of_eq _ _ ?_
    rw [chainPt_of_le y₀ (show y₀.stage ≤ k + 1 by omega),
      chainPt_of_le y₀ (show y₀.stage ≤ k by omega)]

/-- The step from `x̂_k` to `x̂_{k+1}` (chosen). -/
noncomputable def stepData [Hironaka.HironakaCitedResults.{u}] (y₀ : 𝒮.TowerPoint) (hy₀ : y₀.Cond) (k : ℕ) :
    StepData (chainPt y₀ k) (chainPt y₀ (k + 1)) :=
  Classical.choice (exists_stepData_chainPt y₀ hy₀ k)

/-- The sequence `Ŝ_0, Ŝ_1, …, Ŝ_s, Ŝ_s, …` of local rings of `X̂_t` at the images `x̂_t` of
`x̂ = y₀` (pp. 299--300): "`{(Ĵ_j(t), Ŝ_t, Q̂_{t-1})}` is a permissible sequence of strict monoidal
transforms of `(Ĵ_j, Ŝ) = (Ĵ_j(0), Ŝ_0)` ... note that we permit here some trivial monoidal
transforms for which the centers `Q_t` are unit ideals", continued by trivial monoidal transforms
after `Ŝ_s`; the ideal is `Ĵ_0(t)`. -/
noncomputable def towerSequence [Hironaka.HironakaCitedResults.{u}] (y₀ : 𝒮.TowerPoint) (hy₀ : y₀.Cond) : MonoidalSequence.{u} where
  ring k := (chainPt y₀ k).ring
  commRing _ := inferInstance
  isRegularLocalRing _ := inferInstance
  isDomain _ := inferInstance
  ideal k := (chainPt y₀ k).ideal
  center k := (stepData y₀ hy₀ k).center
  transform k := (stepData y₀ hy₀ k).Tr
  equiv k := (stepData y₀ hy₀ k).e
  ideal_succ k := (stepData y₀ hy₀ k).ideal_succ

theorem towerSequence_isPermissible [Hironaka.HironakaCitedResults.{u}] (y₀ : 𝒮.TowerPoint) (hy₀ : y₀.Cond) :
    (towerSequence y₀ hy₀).IsPermissible := fun k => (stepData y₀ hy₀ k).perm

theorem towerSequence_isResiduallySeparableAlgebraic [Hironaka.HironakaCitedResults.{u}] (y₀ : 𝒮.TowerPoint) (hy₀ : y₀.Cond) :
    (towerSequence y₀ hy₀).IsResiduallySeparableAlgebraic := fun k => (stepData y₀ hy₀ k).sep

end TowerPoint

/-- The frame `(F; z)` is carried along the identity of the ring unchanged. -/
theorem HasStalkFrameWith.transport_refl [Hironaka.HironakaCitedResults.{u}] {𝒮 : Frame hS} {s : ℕ} {xh : 𝒮.tHat.X s}
    {F : RegularFrame ((𝒮.tHat.X s).presheaf.stalk xh)} (h : 𝒮.HasStalkFrameWith s xh F) :
    𝒮.HasStalkFrameWith s xh (F.transport (RingEquiv.refl _)) := h

set_option maxHeartbeats 400000 in
/-- **One step of the induction in `lem:IV.AB-4-frames` along the chain of frame transforms.**
Let `(T_t; z_t)` be a frame of `Ŝ_t` at `x̂_t = f̂_t(x̂_{t+1})` as in `HasStalkFrameWith`, and
`(T_{t+1}; z_{t+1})` its frame transform in the monoidal transform `Ŝ_{t+1}` of `Ŝ_t` with center
`Q̂_t` (a step of the sequence `TowerPoint.towerSequence`), with a denominator `v_t ∈ T_t`
which is the image of an element of the center ("Here the denominator ... can be taken in
`P_{β-1} ∩ S_{β-1}`", Remark 3, p. 264; "the denominator `v_t ∈ T_t`", p. 300).  Then
`(T_{t+1}; z_{t+1})` is a frame of `Ŝ_{t+1}` at `x̂_{t+1}` (`hasStalkFrameWith_succ_of_frameTransform`). -/
theorem hasStalkFrameWith_of_stepData [Hironaka.HironakaCitedResults.{u}] {𝒮 : Frame hS} (y y' : 𝒮.TowerPoint) (h : TowerPoint.down y' = y)
    (hne : y'.stage ≠ 0) (hx : y'.Cond) (SD : TowerPoint.StepData y y')
    (F : RegularFrame y.ring) (hF : 𝒮.HasStalkFrameWith y.stage y.pt F)
    (FT : F.FrameTransform SD.Tr) (x₁ : F.S)
    (hx₁ : algebraMap F.S y.ring x₁ ∈ SD.center)
    (hFT : FT.x = SD.Tr.toRing (algebraMap F.S y.ring x₁)) :
    𝒮.HasStalkFrameWith y'.stage y'.pt (RegularFrame.transport FT.toRegularFrame SD.e) := by
  obtain ⟨z, hr, hz⟩ : ∃ z, F.r = 1 ∧ ∀ i, F.z i = z := by
    obtain ⟨z, -, -, -, -, hr, hz, -⟩ := hF
    exact ⟨z, hr, hz⟩
  obtain ⟨z', c₀, hz', hβ, hc₀0, hzv, hdiv⟩ := FT.exists_tuple hr z hz x₁ hx₁ hFT
  subst h
  obtain ⟨t, xh⟩ := y'
  cases t with
  | zero => exact absurd rfl hne
  | succ s =>
    obtain ⟨hcenter, hhe⟩ := SD.real rfl hne
    have hQdef := eq_of_heq hcenter
    have he : SD.e.toRingHom.comp SD.Tr.toRing = ((𝒮.tHat.f s).stalkMap xh).hom := eq_of_heq hhe
    have hreg : IsRegularLocalRing SD.Tr.ring := IsRegularLocalRing.of_ringEquiv SD.e.symm
    exact 𝒮.hasStalkFrameWith_succ_of_frameTransform s xh hx F hF
      SD.center hQdef SD.Tr SD.e he
      FT.toRegularFrame z' c₀ hr hz'
      (by show Ideal.span {FT.β c₀} = _; rw [hβ]; exact FT.span_x)
      (fun j => by rw [hz j]; exact hzv) hc₀0 hdiv

set_option maxHeartbeats 400000 in
/-- `lem:IV.AB-4-frames` for `ℜ = (ℜ^{N,n}_I, U)`, along the printed route (pp. 300--301).  The paper:
"`{(J_j(t), S_t, Q_{t-1})}` is a permissible sequence of strict monoidal transforms of
`(J_j, S) = (J_j(0), S_0)` in the sense of § 9, Ch. III ... Therefore, `{(Ĵ_j(t), Ŝ_t, Q̂_{t-1})}` is
a permissible sequence of strict monoidal transforms of `(Ĵ_j, Ŝ) = (Ĵ_j(0), Ŝ_0)` for
`0 ≤ j ≤ β`.  For the case in which `ℜ = (ℜ^{N,n}_I, U)`, `(T; z)` is a `Ĵ_0`-stable regular frame of
`Ŝ = Ŝ_0`, and hence it admits a frame transform `(T_t; z_t)` in `Ŝ_t` for all `t (0 ≤ t ≤ s)`.
(See Remark 3, § 4 [sic: § 9], Ch. III.) We can choose these `z_t` of regular frames `(T_t; z_t)` of
`Ŝ_t` in such a way that `z_{t+1} = z_t/v_t` with the denominator `v_t ∈ T_t` for `t ≥ 0`."

In Lean: the sequence `Ŝ_0, …, Ŝ_s` (continued by trivial monoidal transforms) is
`TowerPoint.towerSequence`, permissible and residually separable algebraic with
`ν*`, `τ*` of `Ĵ_0(s)` those of `Ĵ_0` (`nuStar_t_tau_eq_of_cond`); the third assertion of Remark 3
(`remark3_frameTransform`) applied to the `Ĵ_0`-stable frame `(T; z)` gives the frames `(T_t; z_t)`,
each a frame transform of the previous one with denominator in the center (`FrameTransformAlong`,
`HasDenominatorsInCenters`); the induction on `t` carries `HasStalkFrameWith` for these frames
(`hasStalkFrameWith_of_stepData`). -/
theorem hasStalkFrame_of_cond_of_opn [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base xh)) (hopen : ∃ U, r = .opn U) :
    𝒮.HasStalkFrame s xh := by
  classical
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · subst hs0
    exact 𝒮.hasStalkFrame_zero xh hx
  obtain ⟨U, hU⟩ := hopen
  let y₀ : 𝒮.TowerPoint := ⟨s, xh⟩
  have hy₀ : y₀.Cond := hx
  -- the frame `(T; z)` of `Ŝ = Ŝ_0` (pp. 296--297)
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : RegularFrame (TowerPoint.chainPt y₀ 0).ring,
      𝒮.HasStalkFrameWith (TowerPoint.chainPt y₀ 0).stage (TowerPoint.chainPt y₀ 0).pt F₀ := by
    have key : ∀ y : 𝒮.TowerPoint, y.stage = 0 → y.Cond → 𝒮.HasStalkFrame y.stage y.pt := by
      rintro ⟨t, x⟩ (h : t = 0) hxc
      subst h
      exact 𝒮.hasStalkFrame_zero x hxc
    exact key _ (TowerPoint.stage_chainPt y₀ (Nat.zero_le _)) (TowerPoint.cond_chainPt hy₀ 0)
  -- "`(T; z)` is a `Ĵ_0`-stable regular frame of `Ŝ`"
  have hJst : F₀.IsJStable (TowerPoint.chainPt y₀ 0).ideal := by
    obtain ⟨z, m, ν, g, co, -, -, -, hFst, -⟩ := hF₀
    exact hFst U hU
  -- `ν*`, `τ*` of `Ĵ_0(k)` are those of `J_0` at `x₀` (condition (3))
  have hch : ∀ k, _ := fun k => 𝒮.nuStar_t_tau_eq_of_cond (TowerPoint.chainPt y₀ k).stage
    (TowerPoint.chainPt y₀ k).pt (TowerPoint.cond_chainPt hy₀ k) (Fin.last ℜ.β)
  -- Remark 3 (third assertion): "it admits a frame transform `(T_t; z_t)` in `Ŝ_t`"
  obtain ⟨c, hden⟩ := (remark3_frameTransform F₀ (TowerPoint.chainPt y₀ 0).ideal hJst).2.2
    (TowerPoint.towerSequence y₀ hy₀) (RingEquiv.refl _)
    (ideal_map_refl _).symm
    (TowerPoint.towerSequence_isPermissible y₀ hy₀)
    (TowerPoint.towerSequence_isResiduallySeparableAlgebraic y₀ hy₀) s hs0
    ((hch s).1.trans (hch 0).1.symm) ((hch s).2.1.trans (hch 0).2.1.symm)
    (fun a ha _ => ((hch s).2.2 a ha).trans ((hch 0).2.2 a ha).symm)
  -- by induction on `t`, the frames `(T_t; z_t)` are those of `HasStalkFrameWith`
  have hA : ∀ k, k ≤ s → 𝒮.HasStalkFrameWith (TowerPoint.chainPt y₀ k).stage
      (TowerPoint.chainPt y₀ k).pt (c.frame k) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [c.frame_zero]
      exact hF₀.transport_refl
    | succ k ih =>
      intro hk
      have hk' : k < s := hk
      obtain ⟨x₁, hx₁, hFT⟩ := hden k hk'
      rw [c.frame_succ k hk']
      exact hasStalkFrameWith_of_stepData (TowerPoint.chainPt y₀ k)
        (TowerPoint.chainPt y₀ (k + 1)) (TowerPoint.down_chainPt_succ y₀ hk')
        (by rw [TowerPoint.stage_chainPt y₀ hk]; omega) (TowerPoint.cond_chainPt hy₀ _)
        (TowerPoint.stepData y₀ hy₀ k) (c.frame k) (ih hk'.le) (c.step k hk') x₁ hx₁ hFT
  have hAs := hA s le_rfl
  have hps : TowerPoint.chainPt y₀ s = y₀ := TowerPoint.chainPt_of_le y₀ le_rfl
  have key : ∀ y : 𝒮.TowerPoint, y = y₀ → ∀ F : RegularFrame y.ring,
      𝒮.HasStalkFrameWith y.stage y.pt F → 𝒮.HasStalkFrame s xh := by
    rintro y rfl F hF
    exact ⟨F, hF⟩
  exact key _ hps _ hAs

set_option maxHeartbeats 400000 in
/-- The step `t → t + 1` of `lem:IV.AB-4-frames` for `ℜ = (ℜ^{N,n}_I, F)` at a point `x̂_{t+1}`
over `x̂_t ∈ B̂_t`: "We note that what we have seen above for the case in which `ℜ = (ℜ^{N,n}_I, U)`
can be trivially verified for the other case in which `ℜ = (ℜ^{N,n}_I, F)`.  Also in this case, we
choose `(T_t; z_t)` in the same way as above" (p. 300).

\textbf{Deviation from the paper (gap filled).}  The frame `(T; z)` is not `Ĵ_0`-stable in this
case, so Remark 3 does not apply, and the frame transform with a denominator `v_t ∈ T_t`
(`(v_t)Ŝ_{t+1} = Q̂_tŜ_{t+1}`, `z_{t+1} = z_t/v_t`) is obtained from the frame-transform criterion
of Ch. III § 8 and Nakayama's lemma (`RegularFrame.exists_frameTransform_of_mem_maximalIdeal`):
`z_{t+1}` is a non-unit because `x̂_{t+1} ∈ X̄_{t+1}` (`x_{t+1} ∈ F(t+1)`).  The rest is
`hasStalkFrameWith_succ_of_frameTransform`. -/
theorem hasStalkFrame_succ_of_mem_of_closed [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X (s + 1))
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) (s + 1) ((𝒮.c (s + 1)).base xh))
    (F₀ : Subscheme X) (hclosed : r = .closed F₀)
    (hF : (𝒮.c (s + 1)).base xh ∈ ((T.pre (s + 1)).strictTransform F₀).pts)
    (hmem : (𝒮.tHat.f s).base xh ∈ (𝒮.tHat.B s).pts)
    (h : 𝒮.HasStalkFrame s ((𝒮.tHat.f s).base xh)) : 𝒮.HasStalkFrame (s + 1) xh := by
  classical
  obtain ⟨F, hFw⟩ := h
  have hFw' := hFw
  obtain ⟨z, m, ν, g, co, hr, hz, hX, hFst, -⟩ := hFw
  -- the stage `s` at `x̂_s = f̂_s(x̂_{s+1})`
  have hc : (𝒮.c s).base ((𝒮.tHat.f s).base xh) = (T.f s).base ((𝒮.c (s + 1)).base xh) :=
    congrArg (fun φ => φ.base xh) (𝒮.c_comm s)
  have hxs : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base ((𝒮.tHat.f s).base xh)) := by
    rw [hc]; exact hS.cond_f_of_cond_succ s _ hx
  have hxB : (𝒮.c s).base ((𝒮.tHat.f s).base xh) ∈ (T.B s).pts := by
    have h1 := hmem
    rw [𝒮.B_hat s, Subscheme.pts_totalTransform_eq_preimage] at h1
    exact h1
  obtain ⟨hQprime, hQreg, hQperm, hzQ⟩ := 𝒮.isPermissibleCenter_and_mem_of_mem_B s _ hxs hxB
    F z hr hz hX hFst
  have hQne : (𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh) ≠ ⊤ := hQprime.ne_top
  -- `Ŝ_{s+1}` is a monoidal transform of `Ŝ_s` with center `Q̂_s`
  obtain ⟨T₁, e, he⟩ : ∃ (T₁ : MonoidalTransform ((𝒮.tHat.X s).presheaf.stalk
      ((𝒮.tHat.f s).base xh)) ((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh)))
      (e : T₁.ring ≃+* (𝒮.tHat.X (s + 1)).presheaf.stalk xh),
      e.toRingHom.comp T₁.toRing = ((𝒮.tHat.f s).stalkMap xh).hom :=
    (𝒮.tHat.monoidalTransformation s).exists_monoidalTransform_stalk xh
  have : IsRegularLocalRing T₁.ring := IsRegularLocalRing.of_ringEquiv e.symm
  -- `z_s/x_{R₁}`, the strict transform of `z_s`
  have hzmem : T₁.toRing z ∈ Ideal.span {T₁.xR} := by
    rw [T₁.span_xR_eq_map]; exact Ideal.mem_map_of_mem _ hzQ
  obtain ⟨ζ, hζ'⟩ := Ideal.mem_span_singleton'.mp hzmem
  have hζ : T₁.toRing z = T₁.xR * ζ := by rw [mul_comm]; exact hζ'.symm
  have hz2 : z ∉ maximalIdeal _ ^ 2 := F.extends_rsop.notMem_maximalIdeal_sq
    (Finset.mem_image.mpr ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, Finset.mem_univ _, hz _⟩)
  have hordz : Ideal.ordElem ((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh)) z = 1 :=
    Ideal.ordElem_eq_one_of_mem_of_notMem_sq hQne hzQ hz2
  have hζspan : Ideal.span {ζ} = strictTransformIdeal T₁ (Ideal.span {z}) :=
    (strictTransformIdeal_span_singleton_eq T₁ hQprime hQreg z ζ (by
      rw [hordz]; simpa using hζ.symm)).symm
  have hXst : (𝒮.xBar (s + 1)).stalkIdeal xh = Ideal.span {e ζ} := by
    have h1 : (𝒮.xBar (s + 1)).stalkIdeal xh =
        (strictTransformIdeal T₁ ((𝒮.xBar s).stalkIdeal ((𝒮.tHat.f s).base xh))).map e :=
      MonoidalTransformation.stalkIdeal_strictTransform_eq_map
        (𝒮.tHat.monoidalTransformation s) xh T₁ e he (Or.inl ⟨hQprime, hQreg⟩) (𝒮.xBar s)
    rw [h1, hX, ← hζspan, Ideal.map_span, Set.image_singleton]
  -- `z_{s+1} = z_s/v_s` is a non-unit: `x̂_{s+1} ∈ X̄_{s+1}` (closed case)
  have hζm : ζ ∈ maximalIdeal T₁.ring := by
    have hXF := 𝒮.xBar_eq_totalTransform_of_closed (s + 1) F₀ hclosed
    have hxX : xh ∈ (𝒮.xBar (s + 1)).pts := by
      rw [hXF, Subscheme.pts_totalTransform_eq_preimage]; exact hF
    rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, hXst] at hxX
    by_contra hcon
    apply hxX
    rw [Ideal.span_singleton_eq_top]
    exact (IsLocalRing.notMem_maximalIdeal.mp hcon).map e
  -- the frame transform `(T_{s+1}; z_{s+1})`, `z_{s+1} = z_s/v_s`, `v_s ∈ T_s`
  obtain ⟨F', z', c₀, hr', hz', hspan, hzv, hc₀0, hdiv⟩ :=
    RegularFrame.exists_frameTransform_of_mem_maximalIdeal F z hz hr _ hzQ T₁ ζ hζ hζm
  exact ⟨F'.transport e, 𝒮.hasStalkFrameWith_succ_of_frameTransform s xh hx F hFw' _ rfl T₁ e he
    F' z' c₀ hr' hz' hspan (fun j => by rw [hz j]; exact hzv) hc₀0 hdiv⟩

/-- `lem:IV.AB-4-frames` for `ℜ = (ℜ^{N,n}_I, F)`, by induction on `s` along the images `x̂_t`
of `x̂` ("by induction on `t`"): the images satisfy the conditions (1), (2), (3)
(`Standing.cond_f_of_cond_succ`) and lie on `F(t)`; the step is
`hasStalkFrame_succ_of_mem_of_closed` or `hasStalkFrame_succ_of_notMem` according as `x̂_t ∈ B̂_t`
or not. -/
theorem hasStalkFrame_of_cond_of_closed [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base xh))
    (F₀ : Subscheme X) (hclosed : r = .closed F₀)
    (hF : (𝒮.c s).base xh ∈ ((T.pre s).strictTransform F₀).pts) :
    𝒮.HasStalkFrame s xh := by
  induction s with
  | zero => exact 𝒮.hasStalkFrame_zero xh hx
  | succ s ih =>
    have hc : (𝒮.c s).base ((𝒮.tHat.f s).base xh) = (T.f s).base ((𝒮.c (s + 1)).base xh) :=
      congrArg (fun φ => φ.base xh) (𝒮.c_comm s)
    have hx' : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base ((𝒮.tHat.f s).base xh)) := by
      rw [hc]; exact hS.cond_f_of_cond_succ s _ hx
    have hF' : (𝒮.c s).base ((𝒮.tHat.f s).base xh) ∈ ((T.pre s).strictTransform F₀).pts := by
      have e : (T.pre (s + 1)).strictTransform F₀ = Subscheme.strictTransform
          (T.monoidalTransformation s) ((T.pre s).strictTransform F₀) :=
        Hironaka.MonoidalSuccession.strictTransform_snoc _ _ _ _
      have h1 := hF
      rw [e] at h1
      rw [hc]
      exact MonoidalTransformation.pts_strictTransform_subset (T.monoidalTransformation s) _ h1
    have hIH := ih _ hx' hF'
    by_cases hmem : (𝒮.tHat.f s).base xh ∈ (𝒮.tHat.B s).pts
    · exact 𝒮.hasStalkFrame_succ_of_mem_of_closed s xh hx F₀ hclosed hF hmem hIH
    · exact 𝒮.hasStalkFrame_succ_of_notMem s xh hmem hIH

/-- **`lem:IV.AB-4-frames`, the existence of the frames** `(T_s; z_s)` of `Ŝ_s` and the data
`g_{jk}(s)`, `g_{jki}(s)`, `J̄(s)_{x̂}` (pp. 300--302).  For `ℜ = (ℜ^{N,n}_I, U)` the frame transforms
come from the third assertion of Remark 3, Ch. III, as in the paper
(`hasStalkFrame_of_cond_of_opn`); for `ℜ = (ℜ^{N,n}_I, F)` ("trivially verified") see
`hasStalkFrame_of_cond_of_closed`. -/
theorem hasStalkFrame_of_cond [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base xh))
    (hF : ∀ F, r = .closed F → (𝒮.c s).base xh ∈ ((T.pre s).strictTransform F).pts) :
    𝒮.HasStalkFrame s xh := by
  have hcases : ∀ r' : Restriction X, (∃ F, r' = .closed F) ∨ ∃ U, r' = .opn U := by
    intro r'
    cases r' with
    | closed F => exact Or.inl ⟨F, rfl⟩
    | opn U => exact Or.inr ⟨U, rfl⟩
  rcases hcases r with ⟨F₀, hr⟩ | hopen
  · exact 𝒮.hasStalkFrame_of_cond_of_closed s xh hx F₀ hr (hF F₀ hr)
  · exact 𝒮.hasStalkFrame_of_cond_of_opn s xh hx hopen

end Frame

/-- **The frames `(T_s; z_s)` and the elements `g_{jk}(s)`, `g_{jki}(s)` at a point over `x̂_0`**
(proof of Lemma (AB.4), pp. 300–302), at one stage `s`.  Let `x̂ ∈ X̂_s` be such that
`x = c_s(x̂)` satisfies the conditions (1), (2), (3) of Lemma (AB.4) and, for
`ℜ = (ℜ^{N,n}_I, F)`, `x ∈ F(s)`.  The paper: "For the case in which `ℜ = (ℜ^{N,n}_I, U)`,
`(T; z)` is a `Ĵ_0`-stable regular frame of `Ŝ = Ŝ_0`, and hence it admits a frame transform
`(T_t; z_t)` in `Ŝ_t` for all `t (0 ≤ t ≤ s)`. (See Remark 3, § 4 [sic: § 9], Ch. III.) We can
choose these `z_t` of regular frames `(T_t; z_t)` of `Ŝ_t` in such a way that `z_{t+1} = z_t/v_t`
with the denominator `v_t ∈ T_t` for `t ≥ 0`. … `z_s` clearly generates the ideal of `X̄_s` in
`Ŝ_s`. We note that what we have seen above for the case in which `ℜ = (ℜ^{N,n}_I, U)` can be
trivially verified for the other case in which `ℜ = (ℜ^{N,n}_I, F)`" (p. 300); "then we get a
`Ĵ_j(t)`-stable standard base of `Ĵ_j(t)` of the form `(g_{j1}(t), …, g_{jm_j}(t))` … and we can
write `g_{jk}(t) = z_t^{ν_{jk}} + ∑_{i=1}^{ν_{jk}} g_{jki}(t) z_t^{ν_{jk}-i}`" (p. 301);
"`J̄(t)_{x̂_t} = (g_{jki}(t)^{b/i}) T̄_t` for `0 ≤ t ≤ s`" (p. 302).

Recorded at the stage `s`: a regular frame `(T_s; z_s)` of `Ŝ_s` (`F`, `r = 1`, `F.z = z`)
with `z_s` generating the ideal of `X̄_s` at `x̂`, `Ĵ_0(s)`-stable in the open case; for each
member `V_j(s)`, `W(s)` of the system, a `Ĵ_j(s)`-stable standard base `g_{jk}(s)` of
`Ĵ_j(s) = c_s⁻¹(V_j(s))_x̂` with `ν_{M}(g_{jk}(s)) = ν_{jk} = ν^{(k)}(J_j)` and
`g_{jk}(s) = z_s^{ν_{jk}} + ∑ g_{jki}(s) z_s^{ν_{jk}-i}`, `g_{jki}(s) ∈ T_s`; `b = ∏ ν_{jk}!`;
and, at the points of `X̄'_s` over `x̂`, the stalk of `J̄(s)` is generated by the images of the
`g_{jki}(s)^{b/i}`.

Formalization notes: the members of the system are indexed as in `datumSystem` (`W(s)` last);
"`x ∈ F(s)`" is the hypothesis under which `x̂ ∈ X̄_s` in the closed case (it holds for
`x ∈ B_s`, `B_s ⊆ F(s)`, as in Lemma (AB.4), and is the proviso of its Corollary); `J̄(s)` is
the paper's sheaf on `X̄'_s` only, so its stalk is described at the points of `X̄'_s`.

Paper misprint: "(See Remark 3, § 4, Ch. III.)" (p. 300); Remark 3 on frame
transforms is in § 9 of Ch. III (p. 263, `rem:III.9-3`).

The proof is `Frame.hasStalkFrame_of_cond`.  For `ℜ = (ℜ^{N,n}_I, U)` it is the paper's: the
`Ĵ_0`-stable frame `(T; z)` admits the frame transforms `(T_t; z_t)` of the third assertion of Remark 3
of Ch. III (`remark3_frameTransform`) along the sequence `{(Ĵ_0(t), Ŝ_t, Q̂_{t-1})}` of local rings of
the `X̂_t` at the images `x̂_t` of `x̂` (`Frame.TowerPoint.towerSequence`), and the induction on `t`
(`Frame.hasStalkFrameWith_of_stepData`) gives the elements `g_{jk}(t)`, `g_{jki}(t)` and the stalks
of `J̄(t)` (`Frame.hasStalkFrameWith_succ_of_frameTransform`).  For `ℜ = (ℜ^{N,n}_I, F)` ("trivially
verified", gap filled) see `Frame.hasStalkFrame_of_cond_of_closed`. -/
@[blueprint "lem:IV.AB-4-frames"
  (statement := /-- Notation as in \cref{def:IV.3-setup}, \cref{def:IV.3-frame},
    \cref{def:IV.3-construction}. Let $\hat x\in\hat X_s$ be such that $x=c_s(\hat x)$ satisfies
    the conditions (1), (2) and (3) of Lemma (AB.4) (\cref{lem:IV.AB-4-componentwise}) and, for
    $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$, $x\in F(s)$. Let $\hat S_s$ be the local
    ring of $\hat X_s$ at $\hat x$ and $\hat J_j(s)=J_j(s)\hat S_s$. Then there exist a regular
    frame $(T_s;z_s)$ of $\hat S_s$ (\cref{def:III.9}) and $\hat J_j(s)$-stable standard bases
    $(g_{j1}(s),\dots,g_{jm_j}(s))$ of $\hat J_j(s)$ (\cref{def:III.11}, \cref{def:III.3}) such
    that: $z_s$ generates the ideal of $\bar X_s$ in $\hat S_s$; for
    $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},U)$, $(T_s;z_s)$ is $\hat J_0(s)$-stable;
    $\nu_{\hat M_s}(g_{jk}(s))=\nu_{jk}=\nu^{(k)}(J_j)$, $b=\prod_j\prod_k\nu_{jk}!$, and
    $g_{jk}(s)=z_s^{\nu_{jk}}+\sum_{i=1}^{\nu_{jk}}g_{jki}(s)z_s^{\nu_{jk}-i}$ with
    $g_{jki}(s)\in T_s$; and $\bar J(s)_{\hat x}=(g_{jki}(s)^{b/i})\bar T_s$ in the local ring
    $\bar T_s$ of $\bar X_s$ at $\hat x$. (pp.~300--302.) (Formalization note (encoding): $\bar J(s)$
    is formed on all of $\bar X_s$, \cref{def:IV.3-construction}, so the last assertion is stated
    at every point of $\bar X_s$ over $\hat x$ and does not assume $\hat x\in\bar X_s'$; the
    paper's $\bar J(s)$ is its restriction to $\bar X_s'$.) -/)
  (proof := /-- The paper's argument (pp.~300--302): the images $x_t$ of $x$ satisfy (1), (2), (3)
    (\cref{lem:IV.3-thm3-consequence}); $\{(\hat J_j(t),\hat S_t,\hat Q_{t-1})\}$ is a permissible
    sequence of strict monoidal transforms of $(\hat J_j,\hat S)=(\hat J_j(0),\hat S_0)$
    (\cref{def:III.9-permissible-sequence}; Lemma (AB.2), \cref{lem:IV.AB-2}, and
    \cref{rem:III.5-1}); for $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},U)$ the $\hat J_0$-stable
    frame $(T;z)$ ``admits a frame transform $(T_t;z_t)$ in $\hat S_t$ for all $t$ $(0\le t\le s)$.
    (See Remark~3, \S4 [sic: \S9], Ch.~III)'', i.e.\ the frame transforms along the sequence of the
    third assertion of Remark~3 (\cref{rem:III.9-3}), with $z_{t+1}=z_t/v_t$, $v_t\in T_t$,
    $(v_t)\hat S_{t+1}=\hat Q_t\hat S_{t+1}$; then $g_{jk}(t+1)=g_{jk}(t)/v_t^{\nu_{jk}}$ and
    $g_{jki}(t+1)=g_{jki}(t)/v_t^i$ give $\hat J_j(t)$-stable standard bases
    (\cref{rem:III.9-2}); $\bar T_{t+1}$ is a monoidal transform of $\bar T_t$ with center
    $\bar Q_t$, $(\bar v_t)\bar T_{t+1}=\bar Q_t\bar T_{t+1}$ and $\bar J(t+1)_{\hat x_{t+1}}=
    (\bar v_t^{-b}\bar J(t)_{\hat x_t})\bar T_{t+1}$ (pp.~300--301).

    \textbf{Deviation from the paper (gap filled).} The paper gives these facts without proof.
    The formalization supplies them. The sequence $\hat S_0,\dots,\hat S_s$ (continued by trivial
    monoidal transforms) of the local rings of the $\hat X_t$ at the images $\hat x_t$ is built, with
    $\hat S_{t+1}$ a monoidal transform of $\hat S_t$ with center $\hat Q_t$ (the unit ideal at the
    points $\hat x_t\notin\hat B_t$: ``some trivial monoidal transforms'', p.~300), residually
    separable algebraic since both have dimension $N$, $\hat Q_t$ a permissible center for
    $\hat J_0(t)$, and $\nu^*$, $\tau^*$ of $\hat J_0(t)$ those of $\hat J_0$ (condition (3)): these
    are the hypotheses under which Remark~3 is applied. Its third assertion gives the frames
    $(T_t;z_t)$ with denominators $v_t$ the images of elements of the centers, and the induction on $t$
    carries these frames: the strict transforms $g_{jk}(t+1)$ form a standard base by Remark~2 of
    \S9 for one step, they are $\hat J_j(t+1)$-stable by Definition~11, and the stalk of
    $\bar J(t+1)=\bar f_t^{-1}(\bar J(t)):\bar f_t^{-1}(\bar B_t)^b$ is computed in the domain
    $\bar T_{t+1}$. For $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$ (``trivially verified'',
    p.~300) the frame $(T;z)$ is not $\hat J_0$-stable, so Remark~3 does not apply: the frame transform
    with denominator $v_t\in T_t$ is obtained from the frame-transform criterion of \S8, Ch.~III
    (\cref{lem:III.8-frame-transform-criterion}) and Nakayama's lemma ($z_{t+1}$ is a non-unit because
    $x_{t+1}\in F(t+1)$). -/)
  (proofUses := ["lem:IV.3-thm3-consequence", "lem:IV.AB-2", "rem:III.5-1", "rem:III.9-2",
    "rem:III.9-3", "def:III.11", "lem:III.8-frame-transform-criterion",
    "compat:blowup-stalk-monoidal-transform", "def:IV.3-frame", "def:IV.3-construction"])
  (latexEnv := "lemma")]
theorem Frame.exists_regularFrame_stalk_of_cond [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}}
    {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base xh))
    (hF : ∀ F, r = .closed F → (𝒮.c s).base xh ∈ ((T.pre s).strictTransform F).pts) :
    ∃ (F : RegularFrame ((𝒮.tHat.X s).presheaf.stalk xh)) (z : (𝒮.tHat.X s).presheaf.stalk xh)
      (m : Fin (ℜ.β + 1) → ℕ) (ν : ∀ j, Fin (m j) → ℕ)
      (g : ∀ j, Fin (m j) → (𝒮.tHat.X s).presheaf.stalk xh)
      (co : ∀ j k, Fin (ν j k) → F.S),
      F.r = 1 ∧ (∀ i, F.z i = z) ∧
      (𝒮.xBar s).stalkIdeal xh = Ideal.span {z} ∧
      (∀ U, r = .opn U → F.IsJStable
        ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal xh)) ∧
      (∀ j, IsStandardBase _
        ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh) (g j)) ∧
      (∀ j k, IsJStable ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh)
        (g j k)) ∧
      (∀ j k, Ideal.ordElem (maximalIdeal _) (g j k) = ν j k) ∧
      (∀ j k, haveI : IsRegularLocalRing (X.presheaf.stalk x₀) := hS.ambient.2.1 x₀
        (ν j k : ℕ∞) = nuI (X.presheaf.stalk x₀) ((datumSystem ℜ j).stalkIdeal x₀)
          (k : ℕ).succPNat) ∧
      𝒮.b = ∏ j, ∏ k, (ν j k).factorial ∧
      (∀ j k, g j k = z ^ ν j k + ∑ i : Fin (ν j k),
        algebraMap F.S _ (co j k i) * z ^ (ν j k - ((i : ℕ) + 1))) ∧
      ∀ xb : (𝒮.xBar s).toScheme, ∀ h : xh = (𝒮.xBar s).ι.base xb,
        (𝒮.jBar s).stalkIdeal xb = (Ideal.span {y | ∃ j k i,
          y = algebraMap F.S _ (co j k i) ^ (𝒮.b / ((i : ℕ) + 1))}).map
          (((𝒮.tHat.X s).presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫
            (𝒮.xBar s).ι.stalkMap xb).hom :=
  𝒮.hasStalkFrame_of_cond s xh hx hF

/-- The local computation of Lemma (AB.4) at `x̂` (pp. 300--302) for an arbitrary permissible center
`B'` at stage `s` containing `x = c_s(x̂)`: `z_s ∈ Q̂'` and `J̄(s)_{x̂} ⊆ Q̄'^b`, where `Q̂'` is the ideal
of `c_s⁻¹(B')` and `Q̄'` that of its trace on `X̄_s`.  The proof of Lemma (AB.4) uses of the center
`B_s` only that it is permissible for `(ℜ(s), r(s))`; for `B' = B_s` this is
`Frame.stalkIdeal_xBar_le_and_jBar_le_pow_of_cond`. -/
theorem Frame.stalkIdeal_xBar_le_and_jBar_le_pow_of_isPermissible [Hironaka.HironakaCitedResults.{u}]
    {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS) (s : ℕ) (B' : Subscheme (T.X s))
    (hB' : ((T.pre s).transformI ℜ).IsPermissible B')
    (hBF : ∀ F₁, r = .closed F₁ → B'.pts ⊆ ((T.pre s).strictTransform F₁).pts)
    (xh : 𝒮.tHat.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s ((𝒮.c s).base xh))
    (hxB : (𝒮.c s).base xh ∈ B'.pts) :
    (𝒮.xBar s).stalkIdeal xh ≤ (Subscheme.totalTransform (𝒮.c s) B').stalkIdeal xh ∧
      ∀ xb : (𝒮.xBar s).toScheme, (𝒮.xBar s).ι.base xb = xh →
        (𝒮.jBar s).stalkIdeal xb ≤
          ((Subscheme.totalTransform (𝒮.xBar s).ι
            (Subscheme.totalTransform (𝒮.c s) B')).stalkIdeal xb) ^ 𝒮.b := by
  classical
  obtain ⟨F, z, m, ν, g, co, hr, hz, hX, hFst, -, hgst, hord, -, hb, hsh, hJ⟩ :=
    𝒮.exists_regularFrame_stalk_of_cond s xh hx (fun F hF => hBF F hF hxB)
  obtain ⟨hQhprime, hQhreg, hQhperm, hzQ⟩ :=
    𝒮.isPermissibleCenter_and_mem_of_isPermissible s B' hB' hBF xh hx hxB F z hr hz hX hFst
  set α := ((𝒮.c s).stalkMap xh).hom with hαdef
  refine ⟨?_, fun xb hxbh => ?_⟩
  · rw [hX, Ideal.span_singleton_le_iff_mem]
    exact hzQ
  · have : CharZero (ResidueField ((𝒮.tHat.X s).presheaf.stalk xh)) := by
      have := hS.isAlgebraicScheme_X s
      exact (RingHom.charZero_iff (ResidueField.map α).injective).mp
        (charZero_residueField_stalk (T.X s) _)
    have hgQ : ∀ j k, g j k ∈ ((Subscheme.totalTransform (𝒮.c s) B').stalkIdeal xh) ^ ν j k :=
      fun j k =>
      Ideal.mem_pow_of_le_ordElem (by
        rw [IsJStable.ordElem_eq_of_isPermissibleCenter (hgst j k) _ (hQhperm j), hord])
    have hcoQ : ∀ j k (i : Fin (ν j k)), algebraMap F.S _ (co j k i) ∈
        ((Subscheme.totalTransform (𝒮.c s) B').stalkIdeal xh) ^ ((i : ℕ) + 1) := by
      intro j k i
      have h := RegularFrame.coeff_mem_comap_pow_of_mem_pow F z hz hr _ hQhreg hzQ (ν j k)
        (co j k) (by rw [← hsh]; exact hgQ j k) i
      exact Ideal.le_comap_pow _ _ h
    have hbB : (Subscheme.totalTransform (𝒮.xBar s).ι
        (Subscheme.totalTransform (𝒮.c s) B')).stalkIdeal xb =
        ((Subscheme.totalTransform (𝒮.c s) B').stalkIdeal xh).map
        (((𝒮.tHat.X s).presheaf.stalkCongr (Inseparable.of_eq hxbh.symm)).hom ≫
          (𝒮.xBar s).ι.stalkMap xb).hom := by
      rw [stalkIdeal_totalTransform, CommRingCat.hom_comp, ← Ideal.map_map,
        stalkIdeal_map_stalkCongr _ hxbh.symm]
    rw [hJ xb hxbh.symm, hbB, ← Ideal.map_pow]
    refine Ideal.map_mono (Ideal.span_le.mpr ?_)
    rintro y ⟨j, k, i, rfl⟩
    have hdvd : (i : ℕ) + 1 ∣ 𝒮.b := by
      rw [hb]
      exact ((Nat.dvd_factorial (Nat.succ_pos _) i.2).trans
        (Finset.dvd_prod_of_mem (fun k => (ν j k).factorial) (Finset.mem_univ k))).trans
          (Finset.dvd_prod_of_mem (fun j => ∏ k, (ν j k).factorial) (Finset.mem_univ j))
    have h := Ideal.pow_mem_pow (hcoQ j k i) (𝒮.b / ((i : ℕ) + 1))
    rwa [← pow_mul, Nat.mul_div_cancel' hdvd] at h

/-- The local computation in the proof of Lemma (AB.4) at the point `x̂` (pp. 300–302): if
`x ∈ B_s` satisfies (1), (2), (3) and `c_s(x̂) = x`, then the ideal of `X̄_s` at `x̂` is contained
in the ideal `Q̂_s` of `B̂_s` ("Since `Q_s` is a permissible center for `J_0(s)`, `Q̂_s` is such
for `Ĵ_0(s)`, and therefore we have `z_s ∈ Q̂_s`. This shows that `B̂_s` is contained in `X̄_s`
because `z_s` clearly generates the ideal of `X̄_s` in `Ŝ_s`", p. 300), and, at the points of
`X̄'_s` over `x̂`, `J̄(s)_x̂ ⊆ Q̄_s^b` ("The prime ideal `Q̂_s` of `B̄'_s` (i.e., that of `B̂_s`) in
`Ŝ_s` contains the element `z_s` of `Ŝ_s` and it is a permissible center for `Ĵ_j(s)`. It
follows that `g_{jk}(s) ∈ Q̂^{ν_{jk}}` … and `g_{jki}(s) ∈ Q̂_s^i` …. Therefore
`g_{jki}(s)^{b/i} ∈ Q̂_s^b` … or, equivalently, `Q̄_s^b ⊇ (g_{jki}(s)^{b/i}) T̄_s = J̄(s)_x̂`",
p. 302).

The proof follows the paper sentence by sentence, from the frames of
`Frame.exists_regularFrame_stalk_of_cond` (`lem:IV.AB-4-frames`).

\textbf{Deviation from the paper (gap filled).}
* "`Q̂_s` is such for `Ĵ_0(s)`": by Remark 1 of § 5, Ch. III (`isPermissibleCenter_map_iff`),
  `S_s → Ŝ_s` transforming a regular system of parameters into one (Lemma (AB.2)).
* "and therefore we have `z_s ∈ Q̂_s`": in the case `(ℜ^{N,n}_I, U)` by the first assertion of
  Remark 3, § 9, Ch. III (`remark3_frameTransform`) for the `Ĵ_0(s)`-stable frame `(T_s; z_s)`;
  in the case `(ℜ^{N,n}_I, F)` ("trivially verified") because `B_s ⊆ F(s)` (Definition 6) and
  `z_s` generates the ideal of `X̄_s = c_s⁻¹(F(s))` (`lem:IV.3-construction-facts`).
* "It follows that `g_{jk}(s) ∈ Q̂^{ν_{jk}}`": `lem:IV.AB-4-stable-order`; "and
  `g_{jki}(s) ∈ Q̂_s^i`": `RegularFrame.coeff_mem_comap_pow_of_mem_pow`; `i ∣ b` since
  `b = ∏ ν_{jk}!`.
* The bound on `J̄(s)` is stated at every point of `X̄_s` over `x̂` (the paper writes "the
  stalk `J̄(s)_x` of `J̄(s)` at `x`" [sic: `x̂`], p. 301, where `J̄(s)` is its sheaf on `X̄'_s`);
  in Lean `J̄(s)` is formed on all of `X̄_s` by the same formulas (`def:IV.3-construction`), and
  the argument at `x̂` never uses `X'_s`, so the first assertion of Lemma (AB.4) ("we have only
  to show the second assertion, assuming the first", p. 299) is not needed here. -/
@[blueprint "lem:IV.AB-4-stalk"
  (statement := /-- Notation as in \cref{def:IV.3-setup}, \cref{def:IV.3-frame},
    \cref{def:IV.3-construction}. If $x\in B_s$ satisfies the conditions (1), (2), (3) of Lemma
    (AB.4) (\cref{lem:IV.AB-4-componentwise}) and $\hat x\in\hat X_s$ is such that
    $c_s(\hat x)=x$, then the ideal of
    $\bar X_s$ at $\hat x$ is contained in the ideal $\hat Q_s$ of $\hat B_s$ at $\hat x$
    (that is, $z_s\in\hat Q_s$), and
    $\bar J(s)_{\hat x}\subseteq\bar Q_s^b$ in the local ring $\bar T_s$ of $\bar X_s$ at
    $\hat x$. (The local computation of pp.~300--302.) (Formalization note (encoding): $\bar J(s)$
    is formed on all of $\bar X_s$, \cref{def:IV.3-construction}, so the bound is stated at every
    point of $\bar X_s$ over $\hat x$, without assuming $\hat x\in\bar X_s'$.) -/)
  (proof := /-- The paper's argument at $\hat x$ (pp.~300--302), with the frames
    $(T_s;z_s)$ and the elements $g_{jk}(s)$, $g_{jki}(s)$ of \cref{lem:IV.AB-4-frames}. Since
    $Q_s$ is a permissible center for $J_j(s)$ ($B_s$ is a permissible center for
    $\mathfrak R(s)$), $\hat Q_s=Q_s\hat S_s$ is such for $\hat J_j(s)=J_j(s)\hat S_s$
    (\cref{rem:III.5-1}, $S_s\to\hat S_s$ transforming a regular system of parameters into one,
    \cref{lem:IV.AB-2}). Therefore $z_s\in\hat Q_s$: for
    $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},U)$ because $(T_s;z_s)$ is $\hat J_0(s)$-stable
    (\cref{rem:III.9-3}, first assertion), for $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$
    because $B_s\subseteq F(s)$ and $z_s$ generates the ideal of $\bar X_s=c_s^{-1}(F(s))$
    (\cref{lem:IV.3-construction-facts}). As $z_s$ generates the ideal of $\bar X_s$ in
    $\hat S_s$, the ideal of $\bar X_s$ is contained in $\hat Q_s$. Next
    $g_{jk}(s)\in\hat Q_s^{\nu_{jk}}$ (\cref{lem:IV.AB-4-stable-order}), hence
    $g_{jki}(s)\in\hat Q_s^i$, so $g_{jki}(s)^{b/i}\in\hat Q_s^b$ ($i\mid b$), i.e.\
    $\bar Q_s^b\supseteq(g_{jki}(s)^{b/i})\bar T_s=\bar J(s)_{\hat x}$.

    \textbf{Deviation from the paper (gap filled).} The reasons for ``$\hat Q_s$ is such for
    $\hat J_0(s)$'', ``therefore we have $z_s\in\hat Q_s$'' (in both cases) and ``It follows
    that $g_{jk}(s)\in\hat Q_s^{\nu_{jk}}$'' are supplied as above; the bound on $\bar J(s)$
    is stated at every point of $\bar X_s$ over $\hat x$, $\bar J(s)$ being formed on all of
    $\bar X_s$ in Lean (the paper writes ``the stalk $\bar J(s)_x$ of $\bar J(s)$ at $x$''
    [sic: $\hat x$], p.~301, for its sheaf on $\bar X_s'$); the argument never uses $X_s'$. -/)
  (proofUses := ["lem:IV.AB-4-frames", "lem:IV.AB-4-stable-order", "lem:IV.AB-2",
    "rem:III.5-1", "rem:III.9-3", "lem:IV.3-construction-facts", "def:IV.3-construction"])
  (latexEnv := "lemma")]
theorem Frame.stalkIdeal_xBar_le_and_jBar_le_pow_of_cond [Hironaka.HironakaCitedResults.{u}]
    {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS) (s : ℕ) (x : T.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s x) (hxB : x ∈ (T.B s).pts)
    (xh : 𝒮.tHat.X s) (hxh : (𝒮.c s).base xh = x) :
    (𝒮.xBar s).stalkIdeal xh ≤ (𝒮.tHat.B s).stalkIdeal xh ∧
      ∀ xb : (𝒮.xBar s).toScheme, (𝒮.xBar s).ι.base xb = xh →
        (𝒮.jBar s).stalkIdeal xb ≤ ((𝒮.bBarOn s).stalkIdeal xb) ^ 𝒮.b := by
  classical
  subst hxh
  have hBperm := isPermissible_transformI_of_isPermissibleI_snoc (T.pre s) (T.B s)
    (T.monoidalTransformation s) ℜ (hS.permissible (s + 1)).isPermissibleI
  have hBF : ∀ F, r = .closed F → (T.B s).pts ⊆ ((T.pre s).strictTransform F).pts := by
    intro F₁ hF₁
    subst hF₁
    exact (isPermissibleClosed_transformI_of_isPermissibleIClosed_snoc (T.pre s) (T.B s)
      (T.monoidalTransformation s) ℜ F₁ (hS.permissible (s + 1))).2.trans
        Set.inter_subset_right
  obtain ⟨h1, h2⟩ := 𝒮.stalkIdeal_xBar_le_and_jBar_le_pow_of_isPermissible s (T.B s) hBperm hBF xh hx hxB
  rw [𝒮.B_hat s]
  exact ⟨h1, fun xb hxb => by
    have := h2 xb hxb
    simpa only [bBarOn, 𝒮.B_hat s] using this⟩

/-- A point of maximal local dimension is closed: if `dim_y Z ≤ N` for all `y` and `dim_x Z = N`, then
`x` has no proper specialization (the local ring at `x` is the localization of that at a
specialization `y` at a prime `P ≠ 𝔪`, so `dim_x = ht P < ht 𝔪 = dim_y ≤ N`).  The paper uses this
without comment: condition (1) of Lemma (AB.4) makes `x` a closed point ("the closed point `x` of
`X_s`", p. 302). -/
theorem isClosed_singleton_of_dimAt_eq {Z : Scheme.{u}} [IsLocallyNoetherian Z] {N : ℕ}
    (hle : ∀ y : Z, Z.dimAt y ≤ N) {x : Z} (hx : Z.dimAt x = N) : IsClosed ({x} : Set Z) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  by_contra hne
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  have hrange : x ∈ Set.range (Z.fromSpecStalk y) := by
    rw [Scheme.range_fromSpecStalk]; exact hxy
  obtain ⟨P, rfl⟩ := hrange
  have hPm : P ≠ closedPoint (Z.presheaf.stalk y) := by
    intro h
    apply hne
    rw [h]
    exact (Z.fromSpecStalk_closedPoint (x := y)).symm
  have h1 := ringKrullDim_stalk_fromSpecStalk y P
  have h2 : P.asIdeal < maximalIdeal (Z.presheaf.stalk y) := by
    refine lt_of_le_of_ne (le_maximalIdeal P.isPrime.ne_top) fun h => hPm ?_
    exact PrimeSpectrum.ext (by simpa [closedPoint] using h)
  have : P.asIdeal.IsPrime := P.isPrime
  have h3 : P.asIdeal.height < (maximalIdeal (Z.presheaf.stalk y)).height :=
    Ideal.height_strict_mono_of_isPrime h2
  have h4 : ringKrullDim (Z.presheaf.stalk y) = (maximalIdeal (Z.presheaf.stalk y)).height :=
    (IsLocalRing.maximalIdeal_height_eq_ringKrullDim).symm
  have h5 := hle y
  unfold Scheme.dimAt at h5 hx
  rw [h1] at hx
  rw [h4] at h5
  have h6 : ((maximalIdeal (Z.presheaf.stalk y)).height : WithBot ℕ∞) ≤ (N : WithBot ℕ∞) := h5
  have h7 : (P.asIdeal.height : WithBot ℕ∞) = (N : WithBot ℕ∞) := hx
  have h8 : (P.asIdeal.height : WithBot ℕ∞) < (maximalIdeal (Z.presheaf.stalk y)).height := by
    exact_mod_cast h3
  rw [h7] at h8
  exact absurd (h8.trans_le h6) (lt_irrefl _)

/-- A point `x` of `X_s` satisfying (1), (2), (3) of Lemma (AB.4) lies on `W(s)`: "Hence, by the
condition (3) on `x`, we have `x ∈ W(s) − U(s)`" (p. 302): `ν^{(1)}` of the ideal of `W(s)` at `x`
is that of `W` at `x_0`, which is at least one as `x_0 ∈ W`; so the ideal is not the unit ideal. -/
theorem Standing.mem_pts_sys_last_of_cond {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    (hS : Standing N n ℜ P r T x₀) (s : ℕ) (x : T.X s)
    (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s x) :
    x ∈ (T.sys ℜ s (Fin.last ℜ.β)).pts := by
  classical
  have hx0 := hS.ambient.2.1 x₀
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx0
  have hW0 : x₀ ∈ ℜ.W.pts := by
    have h := hS.mem_wStar
    cases r with
    | closed F => exact h.1
    | opn U => exact h.1
  obtain ⟨-, -, hxs, hν, -⟩ := hx
  have : IsRegularLocalRing ((T.X s).presheaf.stalk x) := hxs
  by_contra hxW
  have htop : (T.sys ℜ s (Fin.last ℜ.β)).stalkIdeal x = ⊤ :=
    Subscheme.stalkIdeal_eq_top_of_notMem_pts hxW
  have h1 := congrArg (fun f : Lex (ℕ+ → ℕ∞) => ofLex f 1) (hν (Fin.last ℜ.β))
  simp only [nuStarSystemAt, Subscheme.nuStarAt, nuStar, ofLex_toLex, htop] at h1
  have hle : (datumSystem ℜ (Fin.last ℜ.β)).stalkIdeal x₀ ≤ maximalIdeal _ := by
    have : x₀ ∈ (datumSystem ℜ (Fin.last ℜ.β)).pts := by
      simpa [datumSystem] using hW0
    exact stalkIdeal_le_maximalIdeal_of_mem_pts _ this
  have e1 : 1 ≤ nuI (X.presheaf.stalk x₀) ((datumSystem ℜ (Fin.last ℜ.β)).stalkIdeal x₀) 1 := by
    rw [(nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen _ _).1.1]
    refine le_iInf₂ fun f hf => ?_
    have : f ∈ maximalIdeal _ ^ 1 := by simpa using hle hf
    exact_mod_cast Ideal.le_ordElem this
  rw [← h1] at e1
  have h0 := (nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen ((T.X s).presheaf.stalk x)
    (⊤ : Ideal ((T.X s).presheaf.stalk x))).1.2
  rw [Ideal.nu_top_eq_zero] at h0
  rw [h0] at e1
  exact absurd e1 (by simp)

/-- Normal flatness along a maximal ideal: the graded pieces are modules over the field `A/𝔪`. -/
theorem isNormallyFlatAlongIdeal_of_isMaximal {A : Type u} [CommRing A] (m : Ideal A)
    [m.IsMaximal] : IsNormallyFlatAlongIdeal m := fun p => by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  infer_instance

/-- The stalk at `y` of the reduced structure on the closed point `{y}` is the maximal ideal. -/
theorem stalkIdeal_ofClosed_singleton_eq_maximalIdeal {Y : Scheme.{u}} (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    (Subscheme.ofClosed ⟨{y}, hy⟩).stalkIdeal y = maximalIdeal (Y.presheaf.stalk y) := by
  have hcl : (⟨{y}, hy⟩ : TopologicalSpace.Closeds Y) = ⟨closure {y}, isClosed_closure⟩ := by
    ext z; simp [hy.closure_eq]
  rw [hcl]
  obtain ⟨⟨U, hU⟩, hyU⟩ := Subscheme.exists_affineOpen_mem y
  replace hU : IsAffineOpen U := hU
  replace hyU : y ∈ U := hyU
  set q := hU.primeIdealOf ⟨y, hyU⟩
  have hq : hU.fromSpec q = y := hU.fromSpec_primeIdealOf ⟨y, hyU⟩
  have hst := Subscheme.compStalk_stalkIdeal_ofClosed_closure hU hyU q
  rw [hq] at hst
  rw [hst]
  let _ := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hyU⟩ : U)
  have := hU.isLocalization_stalk ⟨y, hyU⟩
  exact IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal (Y.presheaf.stalk y)

/-- "Then we see that the monoidal transformation of `X_s` with center `x` is permissible"
(p. 302): the reduced closed point `{x}` of an algebraic non-singular scheme `Y` is a permissible
center for a type I datum `ℜ` on `Y` as soon as `x` lies on the principal subscheme `W`: it is
non-singular and irreducible; `(E; V_1, …, V_β, W; {x})` is a datum; and it is resolved at `x`
(`{x}` is simple; each `V_j` and `W` is normally flat along the closed point `x`, the graded
pieces being modules over the residue field; `E` has only normal crossings with `{x}`, the ideal
of `{x}` being the maximal ideal, generated by the whole regular system of parameters).  The paper
gives no argument. -/
theorem _root_.Hironaka.DatumI.Raw.isPermissible_ofClosed_singleton {Y : Scheme.{u}} [IsAlgebraicScheme Y]
    (hY : Y.IsNonsingular) {ℜ : DatumI.Raw Y} (hℜ : ℜ.IsDatum) {x : Y}
    (hcl : IsClosed ({x} : Set Y)) (hxW : x ∈ ℜ.W.pts) :
    ℜ.IsPermissible (Subscheme.ofClosed ⟨{x}, hcl⟩) := by
  classical
  set B : Subscheme Y := Subscheme.ofClosed ⟨{x}, hcl⟩ with hBdef
  have hBpts : B.pts = {x} := Subscheme.pts_ofClosed _
  have hxB : x ∈ B.pts := by rw [hBpts]; rfl
  have hBred : B.IsReduced := Subscheme.ofClosed_isReduced _
  have hmax : B.stalkIdeal x = maximalIdeal (Y.presheaf.stalk x) :=
    stalkIdeal_ofClosed_singleton_eq_maximalIdeal x hcl
  have : IsRegularLocalRing (Y.presheaf.stalk x) := hY x
  have hsimple : B.IsSimpleAt x := by
    refine ⟨hxB, ?_⟩
    rw [hmax]
    let _ : Field (Y.presheaf.stalk x ⧸ maximalIdeal (Y.presheaf.stalk x)) := Ideal.Quotient.field _
    infer_instance
  have hBns : B.IsNonsingular := by
    refine Subscheme.isNonsingular_of_stalk_quot B fun y hy => ?_
    rw [hBpts] at hy
    obtain rfl : y = x := hy
    exact hsimple.2
  have hBW : B.pts ⊆ ℜ.W.pts := by rw [hBpts]; simpa using hxW
  refine ⟨Or.inr ⟨hBns, Subscheme.isIrreducible_of_pts _ (by rw [hBpts]; exact isIrreducible_singleton)⟩,
    DatumI.Raw.isDatum_extendBy hℜ hBred hBW, ?_⟩
  intro y hy
  have hy' : y = x := by
    have : y ∈ (ℜ.extendBy B).W.pts := hy
    simpa [DatumI.Raw.extendBy, hBpts] using this
  subst hy'
  have hVx : ∀ j, y ∈ (ℜ.V j).pts := fun j =>
    pts_subset_of_isContainedIn (hℜ.2.2.2.2 j) hxW
  refine ⟨hsimple, fun j => ?_, ?_⟩
  · -- normal flatness along the closed point
    have hVj : y ∈ ((ℜ.extendBy B).V j).pts := by
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa [DatumI.Raw.extendBy] using hxW
      · simpa [DatumI.Raw.extendBy] using hVx i
    have hBV : B.IsContainedIn ((ℜ.extendBy B).V j) :=
      Subscheme.isContainedIn_of_pts_subset hBred (by rw [hBpts]; simpa using hVj)
    show Subscheme.IsNormallyFlatAlongAt' ((ℜ.extendBy B).V j) B y
    rw [Subscheme.isNormallyFlatAlongAt'_iff _ _ hBV]
    refine ⟨hxB, ?_⟩
    have hVne : ((ℜ.extendBy B).V j).stalkIdeal y ≠ ⊤ :=
      Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hVj
    have : IsLocalRing (Y.presheaf.stalk y ⧸ ((ℜ.extendBy B).V j).stalkIdeal y) :=
      isLocalRing_quotient_of_le (le_maximalIdeal hVne)
    rw [hmax, IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    exact isNormallyFlatAlongIdeal_of_isMaximal _
  · -- `E` has only normal crossings with the closed point
    obtain ⟨z, hz, hcomp, -⟩ := hℜ.2.2.1 y
    exact ⟨z, hz, hcomp, z, subset_rfl, by show B.stalkIdeal y = _; rw [hmax, hz.1]⟩

/-- At a point of an irreducible component `C` of a non-singular subscheme `D`, `C_p = D_p`. -/
theorem _root_.Hironaka.Subscheme.stalkIdeal_eq_of_mem_irreducibleComponents_of_isNonsingular
    {Y : Scheme.{u}}
    {D C : Subscheme Y} (hD : D.IsNonsingular) (hC : C ∈ D.irreducibleComponents) {p : Y}
    (hp : p ∈ C.pts) : C.stalkIdeal p = D.stalkIdeal p := by
  have hpD : p ∈ D.pts := Subscheme.pts_subset_of_mem_irreducibleComponents hC hp
  have hP := Subscheme.isPrime_stalkIdeal_of_isNonsingular hD hpD
  have hq := Subscheme.stalkIdeal_mem_minimalPrimes hC hp
  exact le_antisymm (hq.2 ⟨hP, le_rfl⟩ hq.1.2) hq.1.2

/-- The local part of the containment of Lemma (AB.4). -/
theorem Frame.isContainedIn_xBar_of_mem_irreducibleComponents [Hironaka.HironakaCitedResults.{u}]
    {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS) (s : ℕ)
    (x : T.X s) (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s x) (hxB : x ∈ (T.B s).pts)
    (xh : 𝒮.tHat.X s) (hxh : (𝒮.c s).base xh = x) (C : Subscheme (𝒮.tHat.X s))
    (hC : C ∈ (𝒮.tHat.B s).irreducibleComponents) (hxhC : xh ∈ C.pts) :
    C.IsContainedIn (𝒮.xBar s) := by
  have hBns : (𝒮.tHat.B s).IsNonsingular := 𝒮.isNonsingular_B (hS.ambient.2.1 x₀)
    hS.isNonsingular_X hS.isNonsingular_B s
  have h0 := (𝒮.stalkIdeal_xBar_le_and_jBar_le_pow_of_cond s x hx hxB xh hxh).1
  rw [← Subscheme.stalkIdeal_eq_of_mem_irreducibleComponents_of_isNonsingular hBns hC hxhC] at h0
  obtain ⟨Z, hZ, rfl⟩ := hC
  have hZpts : (Subscheme.ofClosed Z).pts = (Z : Set (𝒮.tHat.X s)) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  have hZirr : IsIrreducible (Z : Set (𝒮.tHat.X s)) := hZ.1.1
  have hxhZ : xh ∈ (Z : Set (𝒮.tHat.X s)) := hZpts ▸ hxhC
  set η := hZirr.genericPoint with hη
  have hgen : closure ({η} : Set (𝒮.tHat.X s)) = Z := by
    rw [hη, hZirr.genericPoint_closure_eq, Z.isClosed.closure_eq]
  have hηxh : η ⤳ xh := by
    rw [specializes_iff_mem_closure, hgen]
    exact hxhZ
  have hηZ : η ∈ (Z : Set (𝒮.tHat.X s)) := by
    rw [← hgen]; exact subset_closure rfl
  -- `η` lies on `X̄_s`
  have hηX : η ∈ (𝒮.xBar s).pts := by
    rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top]
    intro htop
    have h1 := Subscheme.stalkIdeal_eq_map_stalkSpecializes (𝒮.xBar s) hηxh
    have h2 := Subscheme.stalkIdeal_eq_map_stalkSpecializes (Subscheme.ofClosed Z) hηxh
    have h3 : (𝒮.xBar s).stalkIdeal η ≤ (Subscheme.ofClosed Z).stalkIdeal η := by
      rw [h1, h2]; exact Ideal.map_mono h0
    rw [htop, top_le_iff] at h3
    exact Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp (hZpts ▸ hηZ) h3
  have hsub : (Z : Set (𝒮.tHat.X s)) ⊆ (𝒮.xBar s).pts := by
    rw [← hgen]
    exact (closure_minimal (Set.singleton_subset_iff.mpr hηX) (𝒮.xBar s).support.isClosed)
  have hle : 𝒮.xBar s ≤ Subscheme.ofClosed Z :=
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp hsub
  exact fun U => hle U

/-- If `D_y` is prime and `D_η` is the maximal ideal of `O_η` for a generization `η ⤳ y`, then
`D_y` is the prime of `O_y` corresponding to `η`. -/
private theorem comap_maximalIdeal_stalkSpecializes_eq {Y : Scheme.{u}} (D : Subscheme Y)
    {η y : Y} (h : η ⤳ y) [(D.stalkIdeal y).IsPrime]
    (hη : D.stalkIdeal η = IsLocalRing.maximalIdeal (Y.presheaf.stalk η)) :
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk η)).comap (Y.presheaf.stalkSpecializes h).hom =
      D.stalkIdeal y := by
  let := (Y.presheaf.stalkSpecializes h).hom.toAlgebra
  have hloc := isLocalization_stalkSpecializes_of_specializes h
  have hmap : D.stalkIdeal η = (D.stalkIdeal y).map (algebraMap _ (Y.presheaf.stalk η)) :=
    Subscheme.stalkIdeal_eq_map_stalkSpecializes D h
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

/-- The local part of the bound `J̄(s) ⊆ P(B̄'_s)^b` of Lemma (AB.4), at a point `x̄` of `X̄_s`
over the component `C` of `B̂_s` through `x̂` at which `X̄_s` is non-singular.  (For the printed
construction `X̄_s` is non-singular at the points of `X̄'_s`, `lem:IV.3-construction-facts`; for
the corrected one at the points of `X̄*'_s`, `Hironaka.Ch4.ComponentwiseConstruction`.  The first
assertion of (AB.4), `x ∈ X'_s`, is not used: `J̄(s)` is formed on all of `X̄_s`.) -/
theorem Frame.jBar_le_pow_of_mem_irreducibleComponents [Hironaka.HironakaCitedResults.{u}]
    {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS) (s : ℕ)
    (x : T.X s) (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s x) (hxB : x ∈ (T.B s).pts)
    (xh : 𝒮.tHat.X s) (hxh : (𝒮.c s).base xh = x)
    (C : Subscheme (𝒮.tHat.X s)) (hC : C ∈ (𝒮.tHat.B s).irreducibleComponents)
    (hxhC : xh ∈ C.pts) (xb : (𝒮.xBar s).toScheme)
    (hreg : IsRegularLocalRing ((𝒮.xBar s).toScheme.presheaf.stalk xb))
    (hxbC : (𝒮.xBar s).ι.base xb ∈ C.pts) :
    (𝒮.jBar s).stalkIdeal xb ≤ ((𝒮.bBarOn s).stalkIdeal xb) ^ 𝒮.b := by
  classical
  set ι := (𝒮.xBar s).ι
  have hBns : (𝒮.tHat.B s).IsNonsingular := 𝒮.isNonsingular_B (hS.ambient.2.1 x₀)
    hS.isNonsingular_X hS.isNonsingular_B s
  have hCX := 𝒮.isContainedIn_xBar_of_mem_irreducibleComponents s x hx hxB xh hxh C hC hxhC
  have hCeq : ∀ p ∈ C.pts, C.stalkIdeal p = (𝒮.tHat.B s).stalkIdeal p := fun p hp =>
    Subscheme.stalkIdeal_eq_of_mem_irreducibleComponents_of_isNonsingular hBns hC hp
  -- `B̄ = ι⁻¹(B̂)` agrees with `ι⁻¹(C)` over `C`
  have hDeq : ∀ q : (𝒮.xBar s).toScheme, ι.base q ∈ C.pts →
      (𝒮.bBarOn s).stalkIdeal q = (Subscheme.totalTransform ι C).stalkIdeal q := fun q hq => by
    show (Subscheme.totalTransform ι (𝒮.tHat.B s)).stalkIdeal q = _
    rw [stalkIdeal_totalTransform, stalkIdeal_totalTransform, hCeq _ hq]
  -- the generic point of `C`
  obtain ⟨Z, hZ, rfl⟩ := hC
  have hZpts : (Subscheme.ofClosed Z).pts = (Z : Set (𝒮.tHat.X s)) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  have hZirr : IsIrreducible (Z : Set (𝒮.tHat.X s)) := hZ.1.1
  set η := hZirr.genericPoint with hη
  have hgen : IsGenericPoint η (Z : Set (𝒮.tHat.X s)) := by
    have := hZirr.isGenericPoint_genericPoint_closure
    rwa [Z.isClosed.closure_eq] at this
  -- `η` lies on `X̄_s`: `η = ι(η̄)`
  have hCsub : (Z : Set (𝒮.tHat.X s)) ⊆ (𝒮.xBar s).pts := by
    rw [← hZpts]
    intro p hp
    rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top] at hp ⊢
    exact fun htop => hp (top_le_iff.mp
      (htop ▸ Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hCX p))
  obtain ⟨ηb, hηb⟩ : η ∈ Set.range ι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hCsub hgen.mem
  have hind := ι.isClosedEmbedding.isInducing
  have hspec : ∀ q : (𝒮.xBar s).toScheme, ι.base q ∈ (Z : Set (𝒮.tHat.X s)) → ηb ⤳ q := by
    intro q hq
    rw [← hind.specializes_iff, hηb]
    exact hgen.specializes hq
  -- the point `x̄_0` of `X̄_s` over `x̂`
  obtain ⟨xb₀, hxb₀⟩ : xh ∈ Set.range ι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hCsub (hZpts ▸ hxhC)
  have hcore := (𝒮.stalkIdeal_xBar_le_and_jBar_le_pow_of_cond s x hx hxB xh hxh).2 xb₀ hxb₀
  -- at `η̄`: `J̄(s)_η̄ ⊆ B̄_η̄^b`
  have h0 : ηb ⤳ xb₀ := hspec xb₀ (by rw [hxb₀]; exact hZpts ▸ hxhC)
  have hη_le : (𝒮.jBar s).stalkIdeal ηb ≤ ((𝒮.bBarOn s).stalkIdeal ηb) ^ 𝒮.b := by
    rw [Subscheme.stalkIdeal_eq_map_stalkSpecializes (𝒮.jBar s) h0,
      Subscheme.stalkIdeal_eq_map_stalkSpecializes (𝒮.bBarOn s) h0, ← Ideal.map_pow]
    exact Ideal.map_mono hcore
  -- at `x̄`: localization at the prime `ι⁻¹(C)_x̄`
  have hxbZ : ι.base xb ∈ (Z : Set (𝒮.tHat.X s)) := hZpts ▸ hxbC
  have h1 : ηb ⤳ xb := hspec xb hxbZ
  set D := Subscheme.totalTransform ι (Subscheme.ofClosed Z)
  obtain ⟨τ, -⟩ := Subscheme.exists_quotEquiv_totalTransform (𝒮.xBar s) (Subscheme.ofClosed Z)
    hCX xb
  have hregq : IsRegularLocalRing ((𝒮.xBar s).toScheme.presheaf.stalk xb ⧸ D.stalkIdeal xb) := by
    have h2 := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hBns
      (Subscheme.pts_subset_of_mem_irreducibleComponents ⟨Z, hZ, rfl⟩ hxbC)
    rw [← hCeq _ hxbC] at h2
    exact IsRegularLocalRing.of_ringEquiv τ
  have hprime : (D.stalkIdeal xb).IsPrime := by
    have := isDomain_of_isRegularLocalRing
      ((𝒮.xBar s).toScheme.presheaf.stalk xb ⧸ D.stalkIdeal xb)
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  have hgen' : IsGenericPoint (ι.base ηb) (Z : Set (𝒮.tHat.X s)) := hηb ▸ hgen
  have hηbC : ι.base ηb ∈ (Subscheme.ofClosed Z).pts := hZpts ▸ hgen'.mem
  have hCη : (Subscheme.ofClosed Z).stalkIdeal (ι.base ηb) = maximalIdeal _ :=
    Subscheme.stalkIdeal_eq_maximalIdeal_of_isGenericPoint (Subscheme.ofClosed_isReduced Z)
      (hZpts ▸ hZirr) (hZpts ▸ hgen')
  have hDη : D.stalkIdeal ηb = maximalIdeal _ := by
    have hsurj := ι.stalkMap_surjective ηb
    show (Subscheme.totalTransform ι (Subscheme.ofClosed Z)).stalkIdeal ηb = _
    rw [stalkIdeal_totalTransform, hCη]
    apply le_antisymm
    · exact Ideal.map_le_iff_le_comap.mpr fun a ha => map_nonunit _ a ha
    · intro a ha
      obtain ⟨c, rfl⟩ := hsurj a
      refine Ideal.mem_map_of_mem _ ?_
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
      exact fun hc => ha (hc.map _)
  have := hprime
  have hp := comap_maximalIdeal_stalkSpecializes_eq D h1 hDη
  let := ((𝒮.xBar s).toScheme.presheaf.stalkSpecializes h1).hom.toAlgebra
  have hloc := isLocalization_stalkSpecializes_of_specializes h1
  set p' := (maximalIdeal ((𝒮.xBar s).toScheme.presheaf.stalk ηb)).comap
    ((𝒮.xBar s).toScheme.presheaf.stalkSpecializes h1).hom with hp'
  intro f hf
  have hfη : algebraMap _ ((𝒮.xBar s).toScheme.presheaf.stalk ηb) f ∈
      (𝒮.jBar s).stalkIdeal ηb := by
    rw [Subscheme.stalkIdeal_eq_map_stalkSpecializes _ h1]
    exact Ideal.mem_map_of_mem _ hf
  have hfη' := hη_le hfη
  rw [hDeq ηb hηbC, Subscheme.stalkIdeal_eq_map_stalkSpecializes D h1, ← Ideal.map_pow] at hfη'
  obtain ⟨⟨a, s'⟩, hs⟩ :=
    (IsLocalization.mem_map_algebraMap_iff p'.primeCompl _).mp hfη'
  rw [← map_mul] at hs
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists p'.primeCompl _).mp hs
  have hmem : ((c : _) * s') * f ∈ (D.stalkIdeal xb) ^ 𝒮.b := by
    rw [show (c : (𝒮.xBar s).toScheme.presheaf.stalk xb) * s' * f = c * (f * s') by ring, hc]
    exact Ideal.mul_mem_left _ _ a.2
  have hcs : ((c : _) * s' : (𝒮.xBar s).toScheme.presheaf.stalk xb) ∉ D.stalkIdeal xb := by
    rw [← hp]
    exact (p'.primeCompl.mul_mem c.2 s'.2 :)
  rw [hDeq xb hxbC]
  exact mem_pow_of_mul_mem_pow_of_isRegularLocalRing_quotient (D.stalkIdeal xb) hregq 𝒮.b _ f
    hcs hmem

/-- The local version of the second assertion of Lemma (AB.4), on the irreducible component `C` of
`B̂_s` through `x̂` (which is also its connected component through `x̂`, `B̂_s` being non-singular):
`C ⊆ X̄_s` and `J̄(s) ⊆ P(B̄_s)^b` at the points of `X̄'_s` over `C`.  The paper assumes here the
first assertion `x ∈ X'_s` ("we have only to show the second assertion, assuming the first",
p. 299); it is not needed, since `J̄(s)` is formed on all of `X̄_s` and the argument at `x̂` never
uses `X'_s` (`lem:IV.AB-4-stalk`), so it is not a hypothesis of the Lean statement.

\textbf{Deviation from the paper (gap filled).} The paper proves the containments at `x̂` and
extends them to `B̂_s` and `B̄'_s` by the irreducibility of `B̂_s` ("Since `B̄'_s` is a
non-singular irreducible subscheme of `X̄'_s`, this suffices", p. 301), which is false in general.  The extension is carried out on `C`: the containment at `x̂`
localizes to the generic point of `C`, whose closure is `C`; for the bound on `J̄(s)`, the stalk
of `B̄_s` at a point of `X̄'_s` over `C` is a prime with regular quotient in the regular local
ring of `X̄'_s` there (`X̄'_s` is non-singular, `lem:IV.3-construction-facts`), so its powers are
primary (`mem_pow_of_mul_mem_pow_of_isRegularLocalRing_quotient`), and the bound at the generic
point of `C` gives it at every point. -/
@[blueprint "lem:IV.AB-4-local"
  (statement := /-- Notation as in \cref{def:IV.3-setup}, \cref{def:IV.3-frame},
    \cref{def:IV.3-construction}. If $x\in B_s$ satisfies the conditions (1), (2), (3) of Lemma
    (AB.4) (\cref{lem:IV.AB-4-componentwise}), $c_s(\hat x)=x$, and $C$ is the irreducible
    component of
    $\hat B_s$ through $\hat x$ (its connected component through $\hat x$, as $\hat B_s$ is
    non-singular), then $C\subseteq\bar X_s$ and $\bar J(s)\subseteq P(\bar B_s)^b$ at every
    point of $\bar X_s'$ lying over $C$. (Formalization note (encoding): the paper assumes here
    the first assertion $x\in X_s'$ of Lemma (AB.4), p.~299; it is not needed, $\bar J(s)$
    being formed on all of $\bar X_s$ and the argument at $\hat x$ never using $X_s'$,
    \cref{lem:IV.AB-4-stalk}.) -/)
  (proof := /-- By \cref{lem:IV.AB-4-stalk} at $\hat x$. The ideal of $\hat B_s$ at a point of
    $C$ is that of $C$ (it is prime, $\hat B_s$ being non-singular). The containment of the ideal of
    $\bar X_s$ in that of $C$ at $\hat x$ localizes to the generic point $\eta$ of $C$, so
    $\eta\in\bar X_s$ and $C=\overline{\{\eta\}}\subseteq\bar X_s$; $C$ being reduced,
    $C\subseteq\bar X_s$. Likewise $\bar J(s)\subseteq P(\bar B_s)^b$ localizes from $\hat x$
    to $\eta$; at a point $\bar y$ of $\bar X_s'$ over $C$ the stalk of $\bar B_s$ is a prime $Q$
    with regular quotient of the regular local ring of $\bar X_s'$ at $\bar y$, the local ring at
    $\eta$ is the localization at $Q$, and $Q^b$ is $Q$-primary
    (\cref{lem:regular-quotient-primary-powers}), whence the bound at $\bar y$.

    \textbf{Deviation from the paper (gap filled).} This is the paper's ``this suffices''
    (p.~301) for $C$ in place of $\hat B_s$, whose irreducibility is false in general (see
    \cref{lem:IV.AB-4-componentwise}). -/)
  (proofUses := ["lem:IV.AB-4-stalk", "lem:regular-quotient-primary-powers",
    "lem:IV.3-construction-facts"])
  (latexEnv := "lemma")]
theorem Frame.isContainedIn_xBar_and_jBar_le_pow_of_mem_irreducibleComponents [Hironaka.HironakaCitedResults.{u}]
    {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS) (s : ℕ)
    (x : T.X s) (hx : Cond N ℜ T x₀ (hS.ambient.2.1 x₀) s x) (hxB : x ∈ (T.B s).pts)
    (xh : 𝒮.tHat.X s) (hxh : (𝒮.c s).base xh = x)
    (C : Subscheme (𝒮.tHat.X s)) (hC : C ∈ (𝒮.tHat.B s).irreducibleComponents)
    (hxhC : xh ∈ C.pts) :
    C.IsContainedIn (𝒮.xBar s) ∧
      ∀ xb ∈ 𝒮.xBarPrime s, (𝒮.xBar s).ι.base xb ∈ C.pts →
        (𝒮.jBar s).stalkIdeal xb ≤ ((𝒮.bBarOn s).stalkIdeal xb) ^ 𝒮.b :=
  ⟨𝒮.isContainedIn_xBar_of_mem_irreducibleComponents s x hx hxB xh hxh C hC hxhC,
    fun xb hxb hxbC =>
      𝒮.jBar_le_pow_of_mem_irreducibleComponents s x hx hxB xh hxh C hC hxhC xb
        ((𝒮.xBar_eq_totalTransform_and_xbp_succ_eq_preimage s).2.2.2.1 xb hxb) hxbC⟩

/-- The height of an ideal does not drop under a flat extension (going down). -/
theorem height_le_height_map_of_flat {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [IsNoetherianRing A] [IsNoetherianRing B] (I : Ideal A) :
    I.height ≤ (I.map (algebraMap A B)).height := by
  rw [Ideal.height_eq_inf_minimalPrimes (I.map (algebraMap A B))]
  refine le_iInf₂ fun Q hQ => ?_
  have hQprime : Q.IsPrime := hQ.1.1
  have hIQ : I ≤ Q.comap (algebraMap A B) := Ideal.map_le_iff_le_comap.mp hQ.1.2
  have hlies : Q.LiesOver (Q.comap (algebraMap A B)) := ⟨rfl⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (R := A) (S := B)
    (Q.comap (algebraMap A B)) Q
  exact (Ideal.height_mono hIQ).trans (h ▸ le_self_add)

/-- The height of the stalk ideal of a subscheme does not drop at a generization: if `z` is the
point of `Z` given by a prime `Q` of `O_{Z,y}` then `ht D_y ≤ ht D_z` (the stalk at `z` is the
localization of the stalk at `y` at `Q`).  The paper's "codimension of `W` in `X` at `x_0`" is
compared with that at the generization `x'_0` of `x_0`. -/
theorem height_stalkIdeal_le_height_stalkIdeal_fromSpecStalk {Z : Scheme.{u}} (D : Subscheme Z)
    (y : Z) (Q : Spec (Z.presheaf.stalk y)) :
    (D.stalkIdeal y).height ≤ (D.stalkIdeal (Z.fromSpecStalk y Q)).height := by
  have h := stalkIdeal_comap_specMap_fromSpecStalk D y (Z.presheaf.stalk y) (𝟙 _) Q
  simp only [Spec.map_id, Category.id_comp, CommRingCat.hom_id, Ideal.map_id] at h
  have h2 := stalkIdeal_totalTransform (Z.fromSpecStalk y) D Q
  have := flat_fromSpecStalk Z y
  have hiso := isIso_stalkMap_of_flat_of_isPreimmersion (Z.fromSpecStalk y) Q
  let e := (asIso ((Z.fromSpecStalk y).stalkMap Q)).commRingCatIsoToRingEquiv
  have h3 : (Subscheme.totalTransform (Z.fromSpecStalk y) D).stalkIdeal Q =
      (D.stalkIdeal (Z.fromSpecStalk y Q)).map e := h2
  have e1 := RingEquiv.height_map e (D.stalkIdeal (Z.fromSpecStalk y Q))
  rw [← e1, ← h3]
  have h' : (Subscheme.totalTransform (Z.fromSpecStalk y) D).stalkIdeal Q =
      (((D.stalkIdeal y).map (algebraMap _ (Localization.AtPrime (show PrimeSpectrum (Z.presheaf.stalk y) from Q).asIdeal))).map
        (Spec.stalkIso (Z.presheaf.stalk y) Q).inv.hom) := h
  rw [h']
  have e2 := RingEquiv.height_map (Spec.stalkIso (Z.presheaf.stalk y) Q).symm.commRingCatIsoToRingEquiv
    ((D.stalkIdeal y).map (algebraMap _ (Localization.AtPrime (show PrimeSpectrum (Z.presheaf.stalk y) from Q).asIdeal)))
  have h4 := IsLocalization.height_under (show PrimeSpectrum (Z.presheaf.stalk y) from Q).asIdeal.primeCompl
    (A := Localization.AtPrime (show PrimeSpectrum (Z.presheaf.stalk y) from Q).asIdeal)
    ((D.stalkIdeal y).map (algebraMap _ (Localization.AtPrime (show PrimeSpectrum (Z.presheaf.stalk y) from Q).asIdeal)))
  refine le_trans ?_ (le_of_eq e2.symm)
  rw [← h4]
  exact Ideal.height_mono Ideal.le_comap_map

section HeightsAlongTower

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X}

/-- The heights of the stalk ideals of the strict transforms `V_j(s)` along `g_s : X_s → X_0` do
not drop (one step at a time, `MonoidalTransformation.height_stalkIdeal_le_strictTransform`; all
`X_s` are non-singular): p. 305, "It is clear that the codimension of `W(s)` in `X'_s` at `x'_s` is
at least equal to that of `W` in `X` at `x'_0`". -/
theorem Standing.height_stalkIdeal_sys_le (hS : Standing N n ℜ P r T x₀) (j : Fin (ℜ.β + 1)) :
    ∀ (s : ℕ) (y : T.X s),
      ((T.sys ℜ 0 j).stalkIdeal ((T.pre s).composite.base y)).height ≤
      ((T.sys ℜ s j).stalkIdeal y).height
  | 0, y => le_rfl
  | s + 1, y => by
    have hcomp : (T.pre (s + 1)).composite.base y =
        (T.pre s).composite.base ((T.f s).base y) :=
      congrArg (fun φ => φ.base y) (Tower.composite_pre_succ T s)
    have h1 := hS.height_stalkIdeal_sys_le j s ((T.f s).base y)
    have h2 := MonoidalTransformation.height_stalkIdeal_le_strictTransform
      (hS.isNonsingular_X s) (T.monoidalTransformation s) (T.sys ℜ s j) y
    have hsys : T.sys ℜ (s + 1) j =
        Subscheme.strictTransform (T.monoidalTransformation s) (T.sys ℜ s j) :=
      Hironaka.MonoidalSuccession.strictTransform_snoc _ _ _ _
    rw [hsys, hcomp]
    exact h1.trans h2

end HeightsAlongTower

section PermissibleCentersFlat

variable {R R' : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R']
  [IsLocalRing R'] [IsNoetherianRing R'] [Algebra R R'] [Module.Flat R R']
  [IsLocalHom (algebraMap R R')]

omit [IsNoetherianRing R'] in
/-- Descent of regularity of a quotient along a flat local homomorphism: if `R'/JR'` is regular,
so is `R/J` (the induced map `R/J → R'/JR'` is flat and local; footnote 3, p. 116, local ring
theory). -/
theorem isRegularLocalRing_quotient_of_isRegularLocalRing_quotient_map_of_flat [Hironaka.HironakaCitedResults.{u}] (J : Ideal R)
    (h : IsRegularLocalRing (R' ⧸ J.map (algebraMap R R'))) : IsRegularLocalRing (R ⧸ J) := by
  have hJ' : J.map (algebraMap R R') ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hJ : J ≠ ⊤ := fun hh => hJ' (by rw [hh, Ideal.map_top])
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (R ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  have : Module.Flat (R ⧸ J) (R' ⧸ J.map (algebraMap R R')) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R' J).toLinearEquiv
  have : IsLocalHom (algebraMap (R ⧸ J) (R' ⧸ J.map (algebraMap R R'))) :=
    isLocalHom_quotientMap_of_le_comap (algebraMap R R') J _ Ideal.le_comap_map
  exact isRegularLocalRing_of_flat_of_isRegularLocalRing (R := R ⧸ J)
    (R' := R' ⧸ J.map (algebraMap R R'))

omit [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing R'] [IsNoetherianRing R'] [IsLocalHom (algebraMap R R')] in
/-- Flat base change of a permissible center: if `P` is a permissible center for `J` in `R`, `R → R'`
is flat and `R'/PR'` is regular, then `PR'` is a permissible center for `JR'` (the normal flatness
passes to the flat extension; `PR'` is prime as `R'/PR'` is a regular local ring, hence a domain). -/
theorem isPermissibleCenter_map_of_isPermissibleCenter_of_isRegularLocalRing_quotient
    {J P : Ideal R} (hP : IsPermissibleCenter R J P)
    (hreg : IsRegularLocalRing (R' ⧸ P.map (algebraMap R R'))) :
    IsPermissibleCenter R' (J.map (algebraMap R R')) (P.map (algebraMap R R')) := by
  rcases hP with hP | ⟨-, hJP, -, hNF⟩
  · exact Or.inl (by rw [hP, Ideal.map_top])
  · refine Or.inr ⟨?_, Ideal.map_mono hJP, hreg, ?_⟩
    · have hdom : IsDomain (R' ⧸ P.map (algebraMap R R')) :=
        Transforms.isDomain_of_isRegularLocalRing _
      exact (Ideal.Quotient.isDomain_iff_prime _).mp hdom
    · exact isNormallyFlatAlongIdeal_mod_map_of_flat _ _ hNF

/-- Descent of a permissible center along a faithfully flat local homomorphism (Lemma 9 of Ch. II
§3, `isNormallyFlatAlongIdeal_map_iff`, and descent of regularity): if `PR'` is a permissible center
for `JR'` in `R'` and `P ≠ R`, then `P` is a permissible center for `J` in `R`. -/
theorem isPermissibleCenter_of_isPermissibleCenter_map_of_flat [Hironaka.HironakaCitedResults.{u}] {J P : Ideal R} (hP : P ≠ ⊤)
    (h : IsPermissibleCenter R' (J.map (algebraMap R R')) (P.map (algebraMap R R'))) :
    IsPermissibleCenter R J P := by
  have hff : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hP' : P.map (algebraMap R R') ≠ ⊤ := fun hh => hP (by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R') P, hh, Ideal.comap_top])
  rcases h with h | ⟨hprime, hJP, hreg, hNF⟩
  · exact absurd h hP'
  · refine Or.inr ⟨?_, ?_, ?_, ?_⟩
    · rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R') P]
      exact hprime.comap _
    · rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R') P,
        ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R') J]
      exact Ideal.comap_mono hJP
    · exact isRegularLocalRing_quotient_of_isRegularLocalRing_quotient_map_of_flat P hreg
    · have hJP0 : J ≤ P := by
        rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R') P,
          ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R') J]
        exact Ideal.comap_mono hJP
      exact (isNormallyFlatAlongIdeal_map_iff J P hJP0 hP).mpr hNF

end PermissibleCentersFlat

/-! ## Lemmas (AB.5) and (AB.6) (pp. 303–307) -/

namespace Frame

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}

/-- `ν^{(1)}(J) ≤ ν^{(k)}(J)` (the degrees of a standard base are monotone). -/
theorem nuI_one_le_nuI_succPNat {R : Type u} [CommRing R] [IsRegularLocalRing R] (J : Ideal R)
    (k : ℕ) : nuI R J 1 ≤ nuI R J k.succPNat := by
  obtain ⟨m, f, hf⟩ := exists_isStandardBase J
  obtain ⟨d, hd, hmono⟩ := hf.2.2.1
  have hbig := (nuI_eq_of_hasLemma1Properties R J _ hf.2).2
  by_cases hk : k < m
  · by_cases h0 : 0 < m
    · rw [show (1 : ℕ+) = (0 : ℕ).succPNat from rfl,
        ← ordElem_eq_nuI_of_isStandardBase J f hf ⟨0, h0⟩,
        ← ordElem_eq_nuI_of_isStandardBase J f hf ⟨k, hk⟩,
        ordElem_eq_of_isStandardBase_of_initialForm_mem_homogeneous J f hf d hd,
        ordElem_eq_of_isStandardBase_of_initialForm_mem_homogeneous J f hf d hd]
      exact_mod_cast hmono (Nat.zero_le k)
    · omega
  · rw [hbig k.succPNat (by simp [Nat.succPNat]; omega)]
    exact le_top

/-- **The frames at an arbitrary point of `X̄_s`** (proof of Lemma (AB.5), pp. 303--305):
the conclusion of the properties (1)--(6) of the proof at the image `x̂_s'` of an arbitrary point
`x̂'` of `Ū_s`.  It is `Frame.HasStalkFrame` without the `Ĵ_j(s)`- and `Ĵ_0(s)`-stability
clauses: at a point `x̂'` that is not over `x_0` the conditions (1)--(3) of Lemma (AB.4) are
not available, and the paper replaces the stability by (2)(a) (the initial forms of the
`g_{jk}(t)` generate `gr_M(Ĵ_j(t), Ŝ_t)`, i.e. `IsStandardBase`) and (2)(b)
(`ν_M(g_{jk}(t)) = ν_{jk}`), the latter obtained from `ν(J̄(t)_{x̂_t'}) ≥ b`.
The existence of these frames is `Frame.RemovalFamily.exists_hasGenericStalkFrame_of_b_le_nu`.

Formalization note (encoding): (2)(a) is stated as `grIdeal = span` of the initial forms of the
`g_{jk}(t)` rather than as `IsStandardBase`: after localization the system need not be a minimal
(standard) set of generators of `gr`, and the paper's (2)(a) only asserts generation. -/
@[blueprint "def:IV.AB-5-frame"
  (statement := /-- Notation as in the proof of \cref{lem:IV.AB-5}, at the image $\hat x_t'$ of a
    point $\hat x'$ of $\bar X_s$ (stage $t$): $\hat S_t$ is the local ring of $\hat X_t$ at
    $\hat x_t'$, $\bar T_t$ that of $\bar X_t$, $\hat J_j(t)=J_j(t)\hat S_t$. A \emph{generic
    stalk frame} at stage $t$ consists of a regular frame $(T_t;z_t)$ of $\hat S_t$ such that the
    kernel of $\hat S_t\to\bar T_t$ is generated by $z_t$ (property (1)), and elements
    $g_{jk}(t)\in\hat J_j(t)$ $(0\le j\le\beta$, $1\le k\le m_j)$ [the paper prints ``$(0\le j\ \beta$, $1\le k\le m_j)$'' (sic)] with: (2)(a) the initial
    forms of the $g_{jk}(t)$ in $\operatorname{gr}_{\hat M_t}(\hat S_t)$ generate
    $\operatorname{gr}_{\hat M_t}(\hat J_j(t),\hat S_t)$ (b)
    $\nu_{\hat M_t}(g_{jk}(t))=\nu_{jk}$ ($=\nu^{(k)}(J_j)$); (3)
    $g_{jk}(t)=z_t^{\nu_{jk}}+\sum_{i=1}^{\nu_{jk}}g_{jki}(t)z_t^{\nu_{jk}-i}$ with
    $g_{jki}(t)\in T_t$; (4) $\bar J(t)_{\hat x_t'}=(g_{jki}(t)^{b/i})\bar T_t$ (with
    $b=\prod\nu_{jk}!$). (Properties (5), (6), the denominators $v_t$ and the passage from $t$ to
    $t+1$, are part of the induction in \cref{lem:IV.AB-5-frame}.) (Formalization note: this is
    \texttt{HasStalkFrame} of \cref{lem:IV.AB-4-frames} without the $\hat J$-stability clauses,
    which are not available at a point not over $x_0$; the paper replaces them by (2)(a), (b).
    The clause (4) is stated at every point of $\bar X_t$ over $\hat x_t'$.) -/)
  (latexEnv := "definition")]
def HasGenericStalkFrame [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X s) : Prop :=
  ∃ (F : RegularFrame ((𝒮.tHat.X s).presheaf.stalk xh)) (z : (𝒮.tHat.X s).presheaf.stalk xh)
    (m : Fin (ℜ.β + 1) → ℕ) (ν : ∀ j, Fin (m j) → ℕ)
    (g : ∀ j, Fin (m j) → (𝒮.tHat.X s).presheaf.stalk xh)
    (co : ∀ j k, Fin (ν j k) → F.S),
    F.r = 1 ∧ (∀ i, F.z i = z) ∧
    (𝒮.xBar s).stalkIdeal xh = Ideal.span {z} ∧
    (∀ j k, g j k ∈ (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh) ∧
    (∀ j, grIdeal (maximalIdeal _)
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh) =
        Ideal.span (Set.range fun k => initialForm (maximalIdeal _) (g j k))) ∧
    (∀ j k, Ideal.ordElem (maximalIdeal _) (g j k) = ν j k) ∧
    (∀ j k, haveI : IsRegularLocalRing (X.presheaf.stalk x₀) := hS.ambient.2.1 x₀
      (ν j k : ℕ∞) = nuI (X.presheaf.stalk x₀) ((datumSystem ℜ j).stalkIdeal x₀)
        (k : ℕ).succPNat) ∧
    𝒮.b = ∏ j, ∏ k, (ν j k).factorial ∧
    (∀ j k, g j k = z ^ ν j k + ∑ i : Fin (ν j k),
      algebraMap F.S _ (co j k i) * z ^ (ν j k - ((i : ℕ) + 1))) ∧
    ∀ xb : (𝒮.xBar s).toScheme, ∀ h : xh = (𝒮.xBar s).ι.base xb,
      (𝒮.jBar s).stalkIdeal xb = (Ideal.span {y | ∃ j k i,
        y = algebraMap F.S _ (co j k i) ^ (𝒮.b / ((i : ℕ) + 1))}).map
        (((𝒮.tHat.X s).presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫
          (𝒮.xBar s).ι.stalkMap xb).hom

/-- `f̄_s` is a local isomorphism at the points off `B̂_s`. -/
theorem bijective_stalkMap_fBar_of_notMem [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ)
    (xb : (𝒮.xBar (s + 1)).toScheme)
    (hmem : (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) ∉ (𝒮.tHat.B s).pts) :
    Function.Bijective ((𝒮.fBar s).stalkMap xb).hom := by
  classical
  have hcomm : (𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb) =
      (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) :=
    (congrArg (fun φ => φ.base xb) (𝒮.fBar_comm s)).symm
  have hmem' : (𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb) ∉ (𝒮.tHat.B s).pts :=
    hcomm ▸ hmem
  have hexc : (𝒮.xBar (s + 1)).ι.base xb ∉ (𝒮.tHat.monoidalTransformation s).exceptional.pts := by
    rw [MonoidalTransformation.exceptional, Subscheme.pts_totalTransform_eq_preimage]
    exact hmem'
  have hreg := 𝒮.regShat
  let e : (𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb)) ≃+*
      (𝒮.tHat.X (s + 1)).presheaf.stalk ((𝒮.xBar (s + 1)).ι.base xb) :=
    RingEquiv.ofBijective ((𝒮.tHat.f s).stalkMap _).hom
      ((𝒮.tHat.monoidalTransformation s).bijective_stalkMap_of_notMem _ hmem')
  have hst : (𝒮.xBar (s + 1)).stalkIdeal ((𝒮.xBar (s + 1)).ι.base xb) =
      ((𝒮.xBar s).stalkIdeal ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb))).map e := by
    have h := MonoidalTransformation.strictTransform_stalkIdeal_of_notMem
      (𝒮.tHat.monoidalTransformation s) (𝒮.xBar s) hexc
    exact h.trans (stalkIdeal_totalTransform _ _ _)
  have key := 𝒮.stalkMap_fBar_comp_eq s xb hcomm
  set c1 := (((𝒮.tHat.X s).presheaf.stalkCongr (Inseparable.of_eq hcomm)).hom ≫
        (𝒮.xBar s).ι.stalkMap ((𝒮.fBar s).base xb)).hom with hc1
  have hc1s : Function.Surjective c1 := by
    rw [hc1, CommRingCat.hom_comp]
    exact ((𝒮.xBar s).ι.stalkMap_surjective _).comp
      (ConcreteCategory.bijective_of_isIso
        (((𝒮.tHat.X s).presheaf.stalkCongr (Inseparable.of_eq hcomm)).hom)).2
  have hRs : Function.Surjective (((𝒮.xBar (s + 1)).ι.stalkMap xb).hom.comp
      ((𝒮.tHat.f s).stalkMap ((𝒮.xBar (s + 1)).ι.base xb)).hom) :=
    ((𝒮.xBar (s + 1)).ι.stalkMap_surjective xb).comp e.surjective
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a0, rfl⟩ := hc1s a
    have h1 : ((𝒮.xBar (s + 1)).ι.stalkMap xb).hom
        (((𝒮.tHat.f s).stalkMap ((𝒮.xBar (s + 1)).ι.base xb)).hom a0) = 0 := by
      have := RingHom.congr_fun key a0
      simp only [RingHom.comp_apply] at this
      rw [← this]; exact ha
    have h2 : ((𝒮.tHat.f s).stalkMap ((𝒮.xBar (s + 1)).ι.base xb)).hom a0 ∈
        (𝒮.xBar (s + 1)).stalkIdeal ((𝒮.xBar (s + 1)).ι.base xb) := by
      rw [stalkIdeal_eq_ker_stalkMap]; exact h1
    rw [hst] at h2
    obtain ⟨w, hw, hwe⟩ := (Ideal.mem_map_iff_of_surjective _ e.surjective).mp h2
    have hw' : w = a0 := e.injective hwe
    subst hw'
    have h3 : ((𝒮.tHat.X s).presheaf.stalkCongr (Inseparable.of_eq hcomm)).hom.hom w ∈
        (𝒮.xBar s).stalkIdeal ((𝒮.xBar s).ι.base ((𝒮.fBar s).base xb)) := by
      rw [← stalkIdeal_map_stalkCongr (𝒮.xBar s) hcomm]
      exact Ideal.mem_map_of_mem _ hw
    rw [stalkIdeal_eq_ker_stalkMap] at h3
    exact h3
  · rw [← key] at hRs
    exact Function.Surjective.of_comp hRs

/-- "From the definition of `X'_s` and the assumption … we have `ν(J̄(t)_{x̂'_t}) ≥ b`" (p. 304), one step:
if `ν(J̄(s+1)_{xb}) ≥ b` then `ν(J̄(s)_{f̄_s xb}) ≥ b`.

\textbf{Deviation from the paper (gap filled).} Off `B̂_s` the map `f̄_s` is a local isomorphism and
`J̄(s+1)_{xb} = J̄(s)_{f̄_s xb}`; on `B̂_s - Bad_s`, `J̄(s) ⊆ P(B̄_s)^b ⊆ M^b`. -/
theorem RemovalFamily.le_nu_jBar_of_le_nu_succ [Hironaka.HironakaCitedResults.{u}] {𝒮 : Frame hS} (R : 𝒮.RemovalFamily) (s : ℕ)
    (xb : (𝒮.xBar (s + 1)).toScheme) (hxb : xb ∈ R.uBar (s + 1))
    (h : (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar (s + 1)).stalkIdeal xb)) :
    (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal ((𝒮.fBar s).base xb)) := by
  classical
  have hx := R.mem_diff_of_mem_uBar_succ s xb hxb
  by_cases hB : (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) ∈ (𝒮.tHat.B s).pts
  · have h1 := R.stalkIdeal_jBar_le s _ hx.1 ⟨hB, hx.2⟩
    refine Ideal.le_ord (h1.trans (Ideal.pow_right_mono ?_ _))
    show (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s)).stalkIdeal _ ≤ _
    rw [stalkIdeal_totalTransform]
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    have ha' := stalkIdeal_le_maximalIdeal_of_mem_pts _ hB ha
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha'
    exact fun hu => ha' (isUnit_of_map_unit _ _ hu)
  · have hbij := bijective_stalkMap_fBar_of_notMem 𝒮 s xb hB
    have hB' : (𝒮.bBarOn s).stalkIdeal ((𝒮.fBar s).base xb) = ⊤ := by
      show (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s)).stalkIdeal _ = ⊤
      rw [stalkIdeal_totalTransform, Subscheme.stalkIdeal_eq_top_of_notMem_pts hB, Ideal.map_top]
    have hst : (𝒮.jBar (s + 1)).stalkIdeal xb =
        ((𝒮.jBar s).stalkIdeal ((𝒮.fBar s).base xb)).map ((𝒮.fBar s).stalkMap xb).hom := by
      rw [jBar_succ, Subscheme.stalkIdeal_divPow_of_isLocallyPrincipal
        (𝒮.isLocallyPrincipal_totalTransform_fBar_bBarOn s), stalkIdeal_totalTransform,
        stalkIdeal_totalTransform, hB', Ideal.map_top, Ideal.top_pow, Submodule.top_coe,
        Submodule.colon_univ]
    rw [hst] at h
    let e := RingEquiv.ofBijective ((𝒮.fBar s).stalkMap xb).hom hbij
    rwa [show ((𝒮.fBar s).stalkMap xb).hom = (e : _ →+* _) from by ext x; rfl,
      LocSucc.nu_map_ringEquiv e] at h

/-- The image of a point of `X̄_{t+d}` in `X̄_t` under `f̄_t ∘ ⋯ ∘ f̄_{t+d-1}`. -/
def fBarIter (𝒮 : Frame hS) (t : ℕ) : ∀ d : ℕ, (𝒮.xBar (t + d)).toScheme →
    (𝒮.xBar t).toScheme
  | 0 => id
  | d + 1 => fun xb => fBarIter 𝒮 t d ((𝒮.fBar (t + d)).base xb)

/-- "From the definition of `X'_s` and the assumption that `ν(J̄(s)_{x̂'}) ≥ b` it is clear that
we have `ν(J̄(t)_{x̂'_t}) ≥ b` for all `t` (`0 ≤ t ≤ s`)" (p. 304), by induction on `s - t` from
`RemovalFamily.le_nu_jBar_of_le_nu_succ`; the images `x̂'_t` stay in `Ū_t`.

\textbf{Deviation from the paper (gap filled).} The paper says "it is clear". -/
theorem RemovalFamily.le_nu_jBar_fBarIter [Hironaka.HironakaCitedResults.{u}] {𝒮 : Frame hS} (R : 𝒮.RemovalFamily) (t : ℕ) :
    ∀ (d : ℕ) (xb : (𝒮.xBar (t + d)).toScheme), xb ∈ R.uBar (t + d) →
      (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar (t + d)).stalkIdeal xb) →
      fBarIter 𝒮 t d xb ∈ R.uBar t ∧
        (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar t).stalkIdeal (fBarIter 𝒮 t d xb))
  | 0, xb, hxb, h => ⟨hxb, h⟩
  | d + 1, xb, hxb, h => by
    have h1 := R.le_nu_jBar_of_le_nu_succ (t + d) xb hxb h
    have h2 : (𝒮.fBar (t + d)).base xb ∈ R.uBar (t + d) :=
      (R.mem_diff_of_mem_uBar_succ (t + d) xb hxb).1
    exact RemovalFamily.le_nu_jBar_fBarIter R t d _ h2 h1

/-- **The case `t = 0` of the frames (1)--(6) of the proof of Lemma (AB.5)** (p. 304) at the
image `x̂'_0` of a point `xb` of `X̄_0` with `ν(J̄(0)_{xb}) ≥ b`: "We first see that (1) for `t = 0`
is clear.  Let `g_{jk}(0) = g_{jk}` … and `g_{jki}(0) = g_{jki}`.  Then (3) and (4) are clear for
`t = 0`.  Next we want to show (a) and (b) of (2) for `t = 0`.  From the definition of `X'` and the
assumption that `ν(J̄(s)_{x̂'}) ≥ b` it is clear that we have `ν(J̄(t)_{x̂'_t}) ≥ b` for all `t` …
Therefore, in particular if `t = 0`, (b) of (2) follows from (3) and (4).  Since
`(g_{j1}(0), …, g_{jm_j}(0))` is a standard base of `Ĵ_j`, if `t = 0`, then (b) of (2) implies (a)
of (2) by Corollary 3 of Theorem 5, § 6, Ch. III."

The frame is the localization `(T_0; z)` of `(T; z)` at `P̂_0 ∩ T` (`RegularFrame.localizeAtPrime`),
moved to the stalk of `X̂_0` at `x̂'_0` along `Spec.stalkIso`.

\textbf{Deviation from the paper (gap filled).}  The paper's "(1) is clear", "(3) and (4) are
clear" and "(b) of (2) follows from (3) and (4)" are proved: the frame property by
`localizeAtPrime`; `(g_{jki}^{b/i}) ∈ M^b` gives `g_{jki} ∈ M_{S_p}^i` through
`S ∩ (M^{ks} + (z)) = M_S^{ks}` and the multiplicativity of `ν` in the regular local ring `S_p`
(`RegularFrame.mem_pow_of_pow_mem_pow_sup`); then (b) is `RegularFrame.ordElem_pow_add_sum_eq`,
and (a) is `cor:III.thm5-3c` in the complete ring `Ŝ` (`ordElem_and_grIdeal_localization_of_frame`).
The standard bases `g_{jk}` are first multiplied by the units `u_{jk}^{-1}` of [c] (p. 297). -/
theorem hasGenericStalkFrame_zero_and [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) [IsRegularLocalRing (Shat X x₀)]
    (xb : (𝒮.xBar 0).toScheme)
    (hν : (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar 0).stalkIdeal xb)) :
    𝒮.HasGenericStalkFrame 0 ((𝒮.xBar 0).ι.base xb) ∧
      ∀ j : Fin (ℜ.β + 1), ∃ (m' : ℕ) (g : Fin m' → Shat X x₀),
        IsStandardBase (Shat X x₀) (((datumSystem ℜ j).stalkIdeal x₀).map
          (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))) g ∧
        IsLocallyAdaptedSystem (Shat X x₀)
          (show PrimeSpectrum (Shat X x₀) from (𝒮.xBar 0).ι.base xb).asIdeal
          (((datumSystem ℜ j).stalkIdeal x₀).map
            (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))) g := by
  classical
  have hx0 := hS.ambient.2.1 x₀
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx0
  have := 𝒮.regShat
  obtain ⟨Fr, h1, hFz, -, hbst, m, g, v, ν, co, hstd, hst, hν0, hshape, hbprod, hjGen⟩ := 𝒮.frame
  set xh : 𝒮.tHat.X 0 := (𝒮.xBar 0).ι.base xb with hxh
  let Pr : PrimeSpectrum (Shat X x₀) := xh
  let Pi : Ideal (Shat X x₀) := Pr.asIdeal
  have : Pi.IsPrime := Pr.isPrime
  have hzP : 𝒮.z ∈ Pi := by
    have hmem : xh ∈ (𝒮.xBar 0).pts := Subscheme.mem_pts_ι (𝒮.xBar 0) xb
    have := (mem_pts_ofIdealTop_spec (CommRingCat.of (Shat X x₀)) (Ideal.span {𝒮.z}) xh).mp hmem
    exact this (Ideal.mem_span_singleton_self _)
  have hSerre : IsRegularLocalRing (Localization.AtPrime Pi) :=
    isRegularLocalRing_localization_of_isRegularLocalRing _ _
  have : IsRegularLocalRing ((𝒮.tHat.X 0).presheaf.stalk xh) :=
    Frame.instIsRegularLocalRingStalk 𝒮 0 xh
  let e : Localization.AtPrime Pi ≃+* (𝒮.tHat.X 0).presheaf.stalk xh :=
    (Spec.stalkIso (CommRingCat.of (Shat X x₀)) Pr).symm.commRingCatIsoToRingEquiv
  let α := algebraMap (X.presheaf.stalk x₀) (Shat X x₀)
  have hmaps : RingHom.MapsRSOP α := mapsRSOP_algebraMap_adicCompletion
  let σ := finRotate (ℜ.β + 1)
  have hσ : ∀ j, jSys ℜ x₀ (σ j) = (datumSystem ℜ j).stalkIdeal x₀ := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [σ, finRotate_last, jSys, Fin.cons_zero, datumSystem, Fin.snoc_last]
    · have : σ i.castSucc = i.succ :=
        Fin.ext (by rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last i).ne]; simp)
      rw [this]
      simp only [jSys, Fin.cons_succ, datumSystem, Fin.snoc_castSucc]
  have hFz' : ∀ i, Fr.z i = 𝒮.z := fun i => by
    rw [← hFz]; congr 1; exact Fin.ext (by have := i.2; omega)
  have hstd' : ∀ j, IsStandardBase (Shat X x₀) ((jSys ℜ x₀ j).map α)
      (fun k => ((v j k)⁻¹ : (Shat X x₀)ˣ) * g j k) := fun j =>
    IsStandardBase.of_unit_mul (hstd j) (fun k => (v j k)⁻¹) (fun _ => rfl)
  have hshape' : ∀ j k, ((v j k)⁻¹ : (Shat X x₀)ˣ) * g j k = 𝒮.z ^ ν j k +
      ∑ i : Fin (ν j k), algebraMap Fr.S (Shat X x₀) (co j k i) * 𝒮.z ^ (ν j k - ((i : ℕ) + 1)) :=
    fun j k => by rw [hshape j k, Units.inv_mul_cancel_left]
  have hord' : ∀ j k, Ideal.ordElem (maximalIdeal (Shat X x₀))
      (((v j k)⁻¹ : (Shat X x₀)ˣ) * g j k) = ν j k := fun j k => by
    rw [ordElem_eq_nuI_of_isStandardBase _ _ (hstd' j) k, ← nuI_map_eq_of_mapsRSOP α hmaps _ _,
      ← hν0 j k]
  let F1 := Fr.localizeAtPrime 𝒮.z h1 hFz' Pi hzP
  have hX0 : (𝒮.xBar 0).stalkIdeal xh = Ideal.span {e (algebraMap _ _ 𝒮.z)} := by
    have h2 := stalkIdeal_ofIdealTop_spec (CommRingCat.of (Shat X x₀)) (Ideal.span {𝒮.z}) Pr
    refine Eq.trans (show Subscheme.stalkIdeal (vZ X x₀ 𝒮.z) xh = _ from h2) ?_
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    rfl
  have hJbar : ∀ (xb' : (𝒮.xBar 0).toScheme) (h : xh = (𝒮.xBar 0).ι.base xb'),
      (𝒮.jBar 0).stalkIdeal xb' = (Ideal.span {y | ∃ j k i, y = algebraMap (F1.transport e).S
        ((𝒮.tHat.X 0).presheaf.stalk xh) ((algebraMap Fr.S (Localization.AtPrime
          (Pi.comap (algebraMap Fr.S (Shat X x₀)))) (co (σ j) k i) : F1.S)) ^
          (𝒮.b / ((i : ℕ) + 1))}).map
        (((𝒮.tHat.X 0).presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫
          (𝒮.xBar 0).ι.stalkMap xb').hom := by
    intro xb' h
    let O : Subscheme (𝒮.tHat.X 0) := Scheme.IdealSheafData.ofIdealTop ((Ideal.span 𝒮.jGen).map
      (Scheme.ΓSpecIso (CommRingCat.of (Shat X x₀))).inv.hom)
    have hO : Subscheme.stalkIdeal O xh =
        ((Ideal.span 𝒮.jGen).map (algebraMap (Shat X x₀) (Localization.AtPrime Pi))).map e :=
      stalkIdeal_ofIdealTop_spec (CommRingCat.of (Shat X x₀)) (Ideal.span 𝒮.jGen) Pr
    have hG : Ideal.span {y | ∃ j k i, y = algebraMap (F1.transport e).S
        ((𝒮.tHat.X 0).presheaf.stalk xh) ((algebraMap Fr.S (Localization.AtPrime
          (Pi.comap (algebraMap Fr.S (Shat X x₀)))) (co (σ j) k i) : F1.S)) ^
          (𝒮.b / ((i : ℕ) + 1))} =
        ((Ideal.span 𝒮.jGen).map (algebraMap (Shat X x₀) (Localization.AtPrime Pi))).map e := by
      have hloc' : ∀ c : Fr.S, (algebraMap (F1.transport e).S ((𝒮.tHat.X 0).presheaf.stalk xh))
          (algebraMap Fr.S (Localization.AtPrime (Pi.comap (algebraMap Fr.S (Shat X x₀)))) c :
            F1.S) =
          e (algebraMap (Shat X x₀) (Localization.AtPrime Pi) (algebraMap Fr.S (Shat X x₀) c)) :=
        fun c => congrArg e (Localization.localRingHom_to_map _ _ _ _ c)
      rw [Ideal.map_span, Ideal.map_span, hjGen]
      congr 1
      ext y
      constructor
      · rintro ⟨j, k, i, rfl⟩
        refine ⟨_, ⟨_, ⟨σ j, k, i, rfl⟩, rfl⟩, ?_⟩
        rw [map_pow, map_pow, hloc']
      · rintro ⟨_, ⟨_, ⟨j', k, i, rfl⟩, rfl⟩, rfl⟩
        obtain ⟨j, rfl⟩ := σ.surjective j'
        refine ⟨j, k, i, ?_⟩
        rw [map_pow, map_pow, hloc']
    show (Subscheme.totalTransform (𝒮.xBar 0).ι O).stalkIdeal xb' = _
    rw [stalkIdeal_totalTransform, Subscheme.stalkIdeal_eq_map_stalkCongr O h, hO, hG,
      CommRingCat.hom_comp, ← Ideal.map_coe e]
    exact Ideal.map_map _ _
  have hco : ∀ j k (i : Fin (ν j k)), algebraMap Fr.S
      (Localization.AtPrime (Pi.comap (algebraMap Fr.S (Shat X x₀)))) (co j k i) ∈
        maximalIdeal (Localization.AtPrime (Pi.comap (algebraMap Fr.S (Shat X x₀)))) ^
          ((i : ℕ) + 1) := by
    intro j' k i
    obtain ⟨j, rfl⟩ := σ.surjective j'
    have hbpos : 0 < 𝒮.b := by
      rw [hbprod]
      exact Finset.prod_pos fun j _ => Finset.prod_pos fun k _ => Nat.factorial_pos _
    have hdvd : (i : ℕ) + 1 ∣ 𝒮.b := by
      rw [hbprod]
      exact ((Nat.dvd_factorial (Nat.succ_pos _) i.2).trans
        (Finset.dvd_prod_of_mem (fun k => (ν (σ j) k).factorial) (Finset.mem_univ k))).trans
          (Finset.dvd_prod_of_mem (fun j => ∏ k, (ν j k).factorial) (Finset.mem_univ (σ j)))
    have hkpos : 0 < 𝒮.b / ((i : ℕ) + 1) := Nat.div_pos (Nat.le_of_dvd hbpos hdvd) (Nat.succ_pos _)
    have hzM : e (algebraMap _ _ 𝒮.z) ∈ maximalIdeal ((𝒮.tHat.X 0).presheaf.stalk xh) := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hu' : IsUnit (algebraMap (Shat X x₀) (Localization.AtPrime Pi) 𝒮.z) := by
        simpa using hu.map e.symm
      exact (mem_maximalIdeal _).mp
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Pi) Pi _).mpr hzP) hu'
    -- the stalk of `J̄(0)` at `x̂'` and `ν(J̄(0)) ≥ b`
    have hJ := hJbar xb rfl
    have hle := Ideal.le_pow_of_le_ord hν
    set φ := ((𝒮.xBar 0).ι.stalkMap xb).hom with hφ
    have hψ : (((𝒮.tHat.X 0).presheaf.stalkCongr (Inseparable.of_eq (rfl : xh = xh))).hom ≫
        (𝒮.xBar 0).ι.stalkMap xb).hom = φ := by
      ext x
      simp [TopCat.Presheaf.stalkCongr_hom, hφ]
    rw [hψ] at hJ
    have hφs : Function.Surjective φ := (𝒮.xBar 0).ι.stalkMap_surjective xb
    have hφker : RingHom.ker φ = Ideal.span {e (algebraMap _ _ 𝒮.z)} := by
      rw [← hX0]
      exact (stalkIdeal_eq_ker_stalkMap (𝒮.xBar 0) xb).symm
    have hmax : (maximalIdeal ((𝒮.tHat.X 0).presheaf.stalk xh)).map φ =
        maximalIdeal ((𝒮.xBar 0).toScheme.presheaf.stalk xb) :=
      map_maximalIdeal_of_surjective φ hφs
    have hmem : (algebraMap (F1.transport e).S ((𝒮.tHat.X 0).presheaf.stalk xh)
        ((algebraMap Fr.S (Localization.AtPrime (Pi.comap (algebraMap Fr.S (Shat X x₀))))
          (co (σ j) k i) : F1.S))) ^ (𝒮.b / ((i : ℕ) + 1)) ∈
        (maximalIdeal ((𝒮.tHat.X 0).presheaf.stalk xh)) ^ 𝒮.b ⊔
          Ideal.span {e (algebraMap _ _ 𝒮.z)} := by
      have h1 : φ ((algebraMap (F1.transport e).S ((𝒮.tHat.X 0).presheaf.stalk xh)
          ((algebraMap Fr.S (Localization.AtPrime (Pi.comap (algebraMap Fr.S (Shat X x₀))))
            (co (σ j) k i) : F1.S))) ^ (𝒮.b / ((i : ℕ) + 1))) ∈
          (𝒮.jBar 0).stalkIdeal xb := by
        rw [hJ]
        exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨σ.symm (σ j) |> fun _ => j, k, i, rfl⟩)
      have h2 := hle h1
      rw [← hmax, ← Ideal.map_pow] at h2
      have h3 := (Ideal.mem_comap).mpr h2
      rw [Ideal.comap_map_of_surjective _ hφs, ← RingHom.ker_eq_comap_bot, hφker] at h3
      exact h3
    refine RegularFrame.mem_pow_of_pow_mem_pow_sup (F1.transport e) (e (algebraMap _ _ 𝒮.z))
      rfl (fun _ => rfl) hzM _ hkpos ?_
    rwa [Nat.div_mul_cancel hdvd]
  have := hS.ambient.1
  have hchar : CharZero (ResidueField (Shat X x₀)) :=
    (RingHom.charZero_iff (ResidueField.map α).injective).mp (charZero_residueField_stalk X x₀)
  have hcomplete : IsAdicComplete (maximalIdeal (Shat X x₀)) (Shat X x₀) := by
    have h : IsAdicComplete (maximalIdeal (X.presheaf.stalk x₀)) (Shat X x₀) :=
      AdicCompletion.isAdicComplete (IsNoetherian.noetherian _)
    have h2 := curve_isAdicComplete_map (maximalIdeal (X.presheaf.stalk x₀)) (B := Shat X x₀)
    rwa [← AdicCompletion.maximalIdeal_eq_map] at h2
  have hmain : ∀ j, (∀ k, Ideal.ordElem (maximalIdeal (Localization.AtPrime Pi))
      (algebraMap (Shat X x₀) (Localization.AtPrime Pi)
        (((v (σ j) k)⁻¹ : (Shat X x₀)ˣ) * g (σ j) k)) = ν (σ j) k) ∧
      grIdeal (maximalIdeal (Localization.AtPrime Pi))
        (((jSys ℜ x₀ (σ j)).map α).map (algebraMap (Shat X x₀) (Localization.AtPrime Pi))) =
        Ideal.span (Set.range fun k => initialForm (maximalIdeal (Localization.AtPrime Pi))
          (algebraMap (Shat X x₀) (Localization.AtPrime Pi)
            (((v (σ j) k)⁻¹ : (Shat X x₀)ˣ) * g (σ j) k))) := fun j =>
    RegularFrame.ordElem_and_grIdeal_localization_of_frame Fr 𝒮.z h1 hFz' Pi hzP _ _ (hstd' (σ j))
      (ν (σ j)) (hord' (σ j)) (co (σ j)) (hshape' (σ j)) (hco (σ j))
  have hJ0 : ∀ j, (Subscheme.totalTransform (𝒮.c 0) (T.sys ℜ 0 j)).stalkIdeal xh =
      (((jSys ℜ x₀ (σ j)).map α).map (algebraMap (Shat X x₀) (Localization.AtPrime Pi))).map e := by
    intro j
    rw [hσ j, 𝒮.c_zero]
    exact stalkIdeal_comap_specMap_fromSpecStalk (T.sys ℜ 0 j) x₀ (CommRingCat.of (Shat X x₀))
      (CommRingCat.ofHom α) Pr
  have hadapt : ∀ j : Fin (ℜ.β + 1), ∃ (m' : ℕ) (g : Fin m' → Shat X x₀),
      IsStandardBase (Shat X x₀) (((datumSystem ℜ j).stalkIdeal x₀).map α) g ∧
      IsLocallyAdaptedSystem (Shat X x₀) Pi (((datumSystem ℜ j).stalkIdeal x₀).map α) g := by
    intro j
    have hs := hstd' (σ j)
    rw [hσ j] at hs
    refine ⟨m (σ j), fun k => ((v (σ j) k)⁻¹ : (Shat X x₀)ˣ) * g (σ j) k, hs, hs.1, hs.2.2.2.1, ?_⟩
    intro k
    rw [hord' (σ j) k, ← (hmain j).1 k, Localization.AtPrime.map_eq_maximalIdeal]
  refine And.intro ?_ hadapt
  refine ⟨F1.transport e, e (algebraMap _ _ 𝒮.z), fun j => m (σ j), fun j k => ν (σ j) k,
    fun j k => e (algebraMap _ _ (((v (σ j) k)⁻¹ : (Shat X x₀)ˣ) * g (σ j) k)),
    fun j k i => (algebraMap Fr.S (Localization.AtPrime (Pi.comap (algebraMap Fr.S (Shat X x₀))))
      (co (σ j) k i) : F1.S), rfl, fun i => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hX0
  · -- the `g_{jk}` lie in the stalk of `c_0⁻¹(V_j)`
    intro j k
    rw [hJ0 j]
    exact Ideal.mem_map_of_mem e (Ideal.mem_map_of_mem _ ((hstd' (σ j)).1 k))
  · -- (a) of (2) at `t = 0`
    intro j
    rw [hJ0 j]
    have h := grIdeal_map_eq_span_initialForm_of_bijective e.toRingHom e.bijective
      (maximalIdeal (Localization.AtPrime Pi))
      (((jSys ℜ x₀ (σ j)).map α).map (algebraMap (Shat X x₀) (Localization.AtPrime Pi)))
      (fun k => algebraMap (Shat X x₀) (Localization.AtPrime Pi)
        (((v (σ j) k)⁻¹ : (Shat X x₀)ˣ) * g (σ j) k)) (hmain j).2
    have hmax : Ideal.map e.toRingHom (maximalIdeal (Localization.AtPrime Pi)) =
        maximalIdeal ((𝒮.tHat.X 0).presheaf.stalk xh) :=
      (Ideal.map_coe e _).trans (IsLocalRing.map_ringEquiv_maximalIdeal e)
    rw [hmax] at h
    exact h
  · -- (b) of (2) at `t = 0`
    intro j k
    rw [ordElem_maximalIdeal_ringEquiv e]
    exact (hmain j).1 k
  · intro j k
    rw [hν0 (σ j) k, hσ j]
  · rw [hbprod]
    exact (Equiv.prod_comp σ (fun j => ∏ k, (ν j k).factorial)).symm
  · intro j k
    have hloc : ∀ c : Fr.S, Localization.localRingHom (Pi.comap (algebraMap Fr.S (Shat X x₀))) Pi
        (algebraMap Fr.S (Shat X x₀)) rfl
        (algebraMap Fr.S (Localization.AtPrime (Pi.comap (algebraMap Fr.S (Shat X x₀)))) c) =
        algebraMap (Shat X x₀) (Localization.AtPrime Pi) (algebraMap Fr.S (Shat X x₀) c) :=
      fun c => Localization.localRingHom_to_map _ _ _ _ c
    show e (algebraMap (Shat X x₀) (Localization.AtPrime Pi) _) = e (algebraMap _ _ 𝒮.z) ^ ν (σ j) k +
      ∑ i : Fin (ν (σ j) k), e (Localization.localRingHom (Pi.comap (algebraMap Fr.S (Shat X x₀))) Pi
        (algebraMap Fr.S (Shat X x₀)) rfl (algebraMap Fr.S
          (Localization.AtPrime (Pi.comap (algebraMap Fr.S (Shat X x₀)))) (co (σ j) k i))) *
        e (algebraMap _ _ 𝒮.z) ^ (ν (σ j) k - ((i : ℕ) + 1))
    simp only [hloc]
    rw [hshape' (σ j) k, map_add, map_pow, map_sum, map_add, map_pow, map_sum]
    simp only [map_mul, map_pow]
  · exact hJbar

theorem hasGenericStalkFrame_zero [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (xb : (𝒮.xBar 0).toScheme)
    (hν : (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar 0).stalkIdeal xb)) :
    𝒮.HasGenericStalkFrame 0 ((𝒮.xBar 0).ι.base xb) :=
  haveI := 𝒮.regShat
  (hasGenericStalkFrame_zero_and 𝒮 xb hν).1

/-- (i) of Lemma (AB.5), first assertion, from the frame: since `x_0 ∈ W`, `ν_{0k} > 0`, so the
standard base `g_{0k}(s)` of `Ĵ_0(s)` has no unit initial form and `Ĵ_0(s)` is a proper ideal, i.e.
`x̂_s' ∈ c_s⁻¹(W(s))` (p. 305: "since `x_0 ∈ W`, `ν_{0k} > 0` … so `Ĵ_0(s)` is contained in the maximal ideal").
\textbf{Deviation from the paper (gap filled):} the paper says `J_0(s)` is contained in the
maximal ideal; Lean obtains properness of `Ĵ_0(s)` from `ν^{(1)}(Ĵ_0(s)) = ν_M(g_{01}(s)) = ν_{01} > 0`
and `m = 0 ⇒ ν^{(1)} = ∞`. -/
theorem HasGenericStalkFrame.mem_pts_sys_last [Hironaka.HironakaCitedResults.{u}] {𝒮 : Frame hS} {s : ℕ} {xh : 𝒮.tHat.X s}
    (h : 𝒮.HasGenericStalkFrame s xh) (hW : x₀ ∈ ℜ.W.pts) :
    (𝒮.c s).base xh ∈ (T.sys ℜ s (Fin.last ℜ.β)).pts := by
  classical
  obtain ⟨F, z, m, ν, g, co, -, -, -, hmem, hgr, hord, hν, -, -, -⟩ := h
  have hx0 := hS.ambient.2.1 x₀
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx0
  have key : xh ∈ (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).pts := by
    rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top]
    set J := (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal xh
    have hle : (datumSystem ℜ (Fin.last ℜ.β)).stalkIdeal x₀ ≤ maximalIdeal _ := by
      have : x₀ ∈ (datumSystem ℜ (Fin.last ℜ.β)).pts := by
        simpa [datumSystem] using hW
      exact stalkIdeal_le_maximalIdeal_of_mem_pts _ this
    have e1 : 1 ≤ nuI (X.presheaf.stalk x₀) ((datumSystem ℜ (Fin.last ℜ.β)).stalkIdeal x₀) 1 := by
      rw [(nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen _ _).1.1]
      refine le_iInf₂ fun f hf => ?_
      have : f ∈ maximalIdeal _ ^ 1 := by simpa using hle hf
      exact_mod_cast Ideal.le_ordElem this
    have hspan := span_eq_of_span_initialForm_eq_grIdeal (maximalIdeal _)
      (maximalIdeal.isMaximal _).ne_top J (g (Fin.last ℜ.β)) (hmem _) (hgr _).symm
    have hJle : J ≤ maximalIdeal _ := by
      rw [← hspan, Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      have hpos : (1 : ℕ∞) ≤ ν (Fin.last ℜ.β) k := by
        rw [hν]
        exact e1.trans (nuI_one_le_nuI_succPNat _ _)
      have := Ideal.mem_pow_of_le_ordElem (I := maximalIdeal _) (f := g (Fin.last ℜ.β) k)
        (ν := 1) (by rw [hord]; exact_mod_cast hpos)
      simpa using this
    exact fun hJ => (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (hJ ▸ hJle))
  rw [Subscheme.pts_totalTransform_eq_preimage] at key
  exact key

/-- The map `O_{Y,p} → O_{D,y}` (`p = ι y`, read through `stalkCongr`) is surjective with kernel the
stalk of the ideal sheaf of `D`. -/
theorem surjective_and_ker_stalkCongr_stalkMap {Y : Scheme.{u}} (D : Subscheme Y)
    (y : D.toScheme) (p : Y) (h : p = D.ι.base y) :
    Function.Surjective ((Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫
      D.ι.stalkMap y).hom ∧
    RingHom.ker ((Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ D.ι.stalkMap y).hom =
      D.stalkIdeal p := by
  subst h
  have hc : ((Y.presheaf.stalkCongr (Inseparable.of_eq (rfl : D.ι.base y = D.ι.base y))).hom ≫
      D.ι.stalkMap y).hom = (D.ι.stalkMap y).hom := by
    ext x
    simp [TopCat.Presheaf.stalkCongr_hom]
  rw [hc]
  exact ⟨D.ι.stalkMap_surjective y, (stalkIdeal_eq_ker_stalkMap D y).symm⟩

/-- Finiteness of the integral closures of footnote 10 for the localizations of a ring `A`. -/
def FiniteIntegralClosureLocalizations (A : Type u) [CommRing A] : Prop :=
  ∀ (Q' Q'' : Ideal A) [Q'.IsPrime] [Q''.IsPrime], Q'' ≤ Q' →
    Module.Finite (Localization.AtPrime Q' ⧸ Q''.map (algebraMap A (Localization.AtPrime Q')))
      (integralClosure (Localization.AtPrime Q' ⧸ Q''.map (algebraMap A (Localization.AtPrime Q')))
        (FractionRing (Localization.AtPrime Q' ⧸
          Q''.map (algebraMap A (Localization.AtPrime Q')))))

/-- `Ĵ_j(s) ⊆ Q̂_s` at the points of `B̂_s`: the center `B_s` is permissible for the datum
`ℜ(s)` (p. 304, "`Ĵ_j(t) ⊆ Q̂_t`"). -/
theorem stalkIdeal_totalTransform_sys_le_stalkIdeal_B (𝒮 : Frame hS) (s : ℕ)
    (p0 : 𝒮.tHat.X s) (hmem' : p0 ∈ (𝒮.tHat.B s).pts) (j : Fin (ℜ.β + 1)) :
    (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal p0 ≤
      (𝒮.tHat.B s).stalkIdeal p0 := by
  have : IsRegularLocalRing ((T.X s).presheaf.stalk ((𝒮.c s).base p0)) := hS.isNonsingular_X s _
  have hBperm := isPermissible_transformI_of_isPermissibleI_snoc (T.pre s) (T.B s)
    (T.monoidalTransformation s) ℜ (hS.permissible (s + 1)).isPermissibleI
  have hxB : (𝒮.c s).base p0 ∈ (T.B s).pts := by
    have h1 := hmem'
    rw [𝒮.B_hat s, Subscheme.pts_totalTransform_eq_preimage] at h1
    exact h1
  have hQneT : (T.B s).stalkIdeal ((𝒮.c s).base p0) ≠ ⊤ :=
    Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hxB
  obtain ⟨j', hj'⟩ := exists_datumSystem_transformI_eq_sys ℜ T s j
  have hperm := DatumI.Raw.isPermissibleCenter_stalkIdeal_datumSystem hBperm
    ((𝒮.c s).base p0) j'
  rw [hj'] at hperm
  have hJP := (hperm.resolve_left hQneT).2.1
  rw [𝒮.B_hat s, stalkIdeal_totalTransform, stalkIdeal_totalTransform]
  exact Ideal.map_mono hJP

/-- `W(s) ⊆ V_j(s)`, i.e. `Ĵ_j(s) ⊆ Ĵ_0(s)` at every point: the datum has `W ⊆ V_j` and strict
transforms preserve inclusions. -/
theorem stalkIdeal_totalTransform_sys_castSucc_le_last (𝒮 : Frame hS) (s : ℕ)
    (y : 𝒮.tHat.X s) (j : Fin ℜ.β) :
    (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j.castSucc)).stalkIdeal y ≤
      (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal y := by
  have hWV : ℜ.W.IsContainedIn (ℜ.V j) := hS.isDatum.2.2.2.2 j
  have h := MonoidalSuccession.isContainedIn_strictTransform (T.pre s) hWV
  have hV : T.sys ℜ s j.castSucc = (T.pre s).strictTransform (ℜ.V j) := by
    show (T.pre s).strictTransform (datumSystem ℜ j.castSucc) = _
    simp only [datumSystem, Fin.snoc_castSucc]
  have hW : T.sys ℜ s (Fin.last ℜ.β) = (T.pre s).strictTransform ℜ.W := by
    show (T.pre s).strictTransform (datumSystem ℜ (Fin.last ℜ.β)) = _
    simp only [datumSystem, Fin.snoc_last]
  rw [hV, hW, stalkIdeal_totalTransform, stalkIdeal_totalTransform]
  exact Ideal.map_mono (Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn h _)

/-- "It follows that `x̂'_t` is a simple point of `c_t⁻¹(W(t))`" (p. 305), one step: if
`Ŝ_s/Ĵ_0(s)` is regular at `f̂_s(x̂'_{s+1})` and `x̂'_{s+1}` lies on `c_{s+1}⁻¹(W(s+1))`, then
`Ŝ_{s+1}/Ĵ_0(s+1)` is regular. -/
theorem isRegularLocalRing_quotient_sys_last_succ [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ)
    (xh : 𝒮.tHat.X (s + 1))
    (hreg : IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh) ⧸
      (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal
        ((𝒮.tHat.f s).base xh)))
    (hne : (Subscheme.totalTransform (𝒮.c (s + 1))
      (T.sys ℜ (s + 1) (Fin.last ℜ.β))).stalkIdeal xh ≠ ⊤) :
    IsRegularLocalRing ((𝒮.tHat.X (s + 1)).presheaf.stalk xh ⧸
      (Subscheme.totalTransform (𝒮.c (s + 1)) (T.sys ℜ (s + 1) (Fin.last ℜ.β))).stalkIdeal xh) := by
  classical
  have hsucc := 𝒮.totalTransform_c_sys_succ s (Fin.last ℜ.β)
  rw [hsucc] at hne ⊢
  have hB := 𝒮.isNonsingular_B (hS.ambient.2.1 x₀) hS.isNonsingular_X hS.isNonsingular_B s
  have hX := 𝒮.toCompletion.isNonsingular_tHat (hS.ambient.2.1 x₀) hS.isNonsingular_X
    hS.isNonsingular_B s
  refine MonoidalTransformation.isRegularLocalRing_quotient_stalkIdeal_strictTransform hX hB
    (𝒮.tHat.monoidalTransformation s) _ xh ?_ hreg ?_
  · by_cases hmem : (𝒮.tHat.f s).base xh ∈ (𝒮.tHat.B s).pts
    · exact 𝒮.stalkIdeal_totalTransform_sys_le_stalkIdeal_B s _ hmem _
    · have h0 := Subscheme.stalkIdeal_eq_top_of_notMem_pts hmem
      exact h0.symm ▸ le_top
  · exact Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr hne

/-- The step `t → t + 1` of the proof of Lemma (AB.5) at a point `x̂'_{t+1}` whose image `x̂'_t` is
not on `B̂_t` ("trivial monoidal transforms for which the centers `Q_t` are unit ideals",
p. 300): `f̂_t` is a local isomorphism there and the data are transported along
`Ŝ_t ≅ Ŝ_{t+1}`; the divisor `f̄_t⁻¹(B̄_t)` is trivial, so `J̄(t + 1)` is the inverse image of
`J̄(t)`.  (The generic version of `hasStalkFrame_succ_of_notMem`.) -/
theorem hasGenericStalkFrame_succ_of_notMem [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X (s + 1))
    (hmem : (𝒮.tHat.f s).base xh ∉ (𝒮.tHat.B s).pts)
    (h : 𝒮.HasGenericStalkFrame s ((𝒮.tHat.f s).base xh)) :
    𝒮.HasGenericStalkFrame (s + 1) xh := by
  classical
  obtain ⟨F, z, m, ν, g, co, hr, hz, hX, hgJ, hgr, hord, hν, hb, hsh, hJ⟩ := h
  have hexc : xh ∉ (𝒮.tHat.monoidalTransformation s).exceptional.pts := by
    rw [MonoidalTransformation.exceptional, Subscheme.pts_totalTransform_eq_preimage]
    exact hmem
  let e : (𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh) ≃+*
      (𝒮.tHat.X (s + 1)).presheaf.stalk xh :=
    RingEquiv.ofBijective ((𝒮.tHat.f s).stalkMap xh).hom
      ((𝒮.tHat.monoidalTransformation s).bijective_stalkMap_of_notMem xh hmem)
  -- off the center, the stalks of strict transforms are the images of the stalks
  have hst : ∀ V : Subscheme (𝒮.tHat.X s),
      (Subscheme.strictTransform (𝒮.tHat.monoidalTransformation s) V).stalkIdeal xh =
        (V.stalkIdeal ((𝒮.tHat.f s).base xh)).map e := by
    intro V
    rw [MonoidalTransformation.strictTransform_stalkIdeal_of_notMem _ V hexc]
    exact stalkIdeal_totalTransform _ _ _
  have hJs : ∀ j, (Subscheme.totalTransform (𝒮.c (s + 1)) (T.sys ℜ (s + 1) j)).stalkIdeal xh =
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal
        ((𝒮.tHat.f s).base xh)).map e := by
    intro j
    have := hst (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j))
    rw [𝒮.totalTransform_c_sys_succ s j]
    exact this
  refine ⟨F.transport e, e z, m, ν, fun j k => e (g j k), co, hr, fun i => ?_, ?_, ?_, ?_,
    fun j k => (ordElem_maximalIdeal_ringEquiv e (g j k)).trans (hord j k), hν, hb, ?_, ?_⟩
  · exact congrArg e (hz i)
  · have := hst (𝒮.xBar s)
    rw [hX, Ideal.map_span, Set.image_singleton] at this
    exact this
  · intro j k
    rw [hJs]
    exact Ideal.mem_map_of_mem e (hgJ j k)
  · intro j
    rw [hJs]
    have h1 := grIdeal_map_eq_span_initialForm_of_bijective e.toRingHom e.bijective
      (maximalIdeal ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh)))
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal ((𝒮.tHat.f s).base xh))
      (g j) (hgr j)
    have hmax : Ideal.map e.toRingHom (maximalIdeal ((𝒮.tHat.X s).presheaf.stalk
        ((𝒮.tHat.f s).base xh))) = maximalIdeal ((𝒮.tHat.X (s + 1)).presheaf.stalk xh) :=
      (Ideal.map_coe e _).trans (IsLocalRing.map_ringEquiv_maximalIdeal e)
    rw [hmax, show Ideal.map e.toRingHom ((Subscheme.totalTransform (𝒮.c s)
      (T.sys ℜ s j)).stalkIdeal ((𝒮.tHat.f s).base xh)) = Ideal.map e
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal ((𝒮.tHat.f s).base xh))
      from Ideal.map_coe e _] at h1
    exact h1
  · intro j k
    show e (g j k) = e z ^ ν j k + ∑ i : Fin (ν j k),
      e (algebraMap F.S _ (co j k i)) * e z ^ (ν j k - ((i : ℕ) + 1))
    rw [hsh j k, map_add, map_pow, map_sum]
    simp only [map_mul, map_pow]
  · intro xb' h'
    subst h'
    have hcomm : (𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb') =
        (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb') :=
      (congrArg (fun φ => φ.base xb') (𝒮.fBar_comm s)).symm
    have hIH := hJ _ hcomm
    have hBtop : (𝒮.tHat.B s).stalkIdeal ((𝒮.xBar s).ι.base ((𝒮.fBar s).base xb')) = ⊤ :=
      Subscheme.stalkIdeal_eq_top_of_notMem_pts (hcomm ▸ hmem)
    have hB : (𝒮.bBarOn s).stalkIdeal ((𝒮.fBar s).base xb') = ⊤ := by
      show (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s)).stalkIdeal _ = ⊤
      rw [stalkIdeal_totalTransform, hBtop, Ideal.map_top]
    rw [jBar_succ, Subscheme.stalkIdeal_divPow_of_isLocallyPrincipal
      (𝒮.isLocallyPrincipal_totalTransform_fBar_bBarOn s), stalkIdeal_totalTransform,
      stalkIdeal_totalTransform, hB, Ideal.map_top, Ideal.top_pow, Submodule.top_coe,
      Submodule.colon_univ, hIH, Ideal.map_map, 𝒮.stalkMap_fBar_comp_eq s xb' hcomm]
    have hG : {y | ∃ j k i, y = algebraMap (F.transport e).S
        ((𝒮.tHat.X (s + 1)).presheaf.stalk ((𝒮.xBar (s + 1)).ι.base xb')) (co j k i) ^
          (𝒮.b / ((i : ℕ) + 1))} =
        e '' {y | ∃ j k i, y = algebraMap F.S _ (co j k i) ^ (𝒮.b / ((i : ℕ) + 1))} := by
      ext y
      constructor
      · rintro ⟨j, k, i, rfl⟩
        exact ⟨_, ⟨j, k, i, rfl⟩, map_pow e _ _⟩
      · rintro ⟨_, ⟨j, k, i, rfl⟩, rfl⟩
        exact ⟨j, k, i, map_pow e _ _⟩
    erw [hG]
    rw [← Ideal.map_span, ← Ideal.map_coe e, Ideal.map_map]
    congr 1
    ext a
    simp [e, TopCat.Presheaf.stalkCongr_hom]
    rfl

/-- **The step `t → t + 1` of the proof of Lemma (AB.5)** (pp. 304--305) at a point `x̂'_{t+1}`
over a point of `B̂_t − Bad_t` (`xb ∈ Ū_{t+1}`, `ν(J̄(t+1)_{xb}) ≥ b`).

The paper: "Now, assuming that we have obtained `(T_t; z_t)` having the property (1) for some
`t > 0`, we claim that there exists `v_t ∈ T_t` such that `Q_t S_{t+1} = (v_t) S_{t+1}`.  (See (5).)
In fact, `S_{t+1}` is a monoidal transform of `S_t` with center `Q_t`, `Q_t` contains the kernel
`(z_t) S_t` of the canonical homomorphism `S_t → T_t` by the definition of `X'_{t+1}`, and
finally if `Q_t S_{t+1} = (w) S_{t+1}` for some `w ∈ Q_t` then `z_t w^{-1}` is not a unit in
`S_{t+1}` because `x'_{t+1} ∈ X'_{t+1}`" (p. 304), "(4) for `J̄(t)_{x̂'_t}` implies that
`g_{jki}(t)^{b/i}` is contained in the `b`th power of `Q̄_t`" and "Finally (a) of (2) follows (b)
of (2) for `g_{jk}(t+1)` … by Corollary 3 of Theorem 5, § 6, Ch. III, and by Theorem 5, § 6,
Ch. III, applied to a monoidal transform of `Ŝ_t` with center `Q̂_t` which is residually algebraic
over `S_t` and such that `S_{t+1}` is a localization of the transform" (p. 305).

In Lean (the generic version of `hasStalkFrame_succ_of_mem_of_closed`, without `Cond`):
* `z_t ∈ Q̂_t` from `RemovalFamily.stalkIdeal_xBar_le`; `Ĵ_j(t) ⊆ Q̂_t` from the permissibility of
  `B_t`; `g_{jki}(t) ∈ (Q̂_t ∩ T_t)^i` from `J̄(t) ⊆ P(B̄_t)^b`
  (`RegularFrame.mem_comap_pow_of_pow_mem_pow_sup_prime`), whence `ν_{Q̂}(g_{jk}(t)) = ν_{jk}`
  (`RegularFrame.ordElem_eq_of_coeff_mem_pow`);
* the frame transform `(T_{t+1}; z_{t+1} = z_t/v_t)` (`exists_frameTransform_of_mem_maximalIdeal`)
  in the stalk monoidal transform `T₁`, `z_t/v_t` a non-unit because `x̂'_{t+1} ∈ X̄_{t+1}`;
* (3), (4) for `t + 1` (the colon-ideal computation of `hasStalkFrame_succ_of_mem`) and (b) of (2)
  for `t + 1` from `ν(J̄(t+1)) ≥ b` (`RegularFrame.ordElem_pow_add_sum_eq`);
* (a) of (2) for `t + 1`: the closed-point refinement `T₂` of `T₁` with `T₁.ring` a localization of
  `T₂.ring` (`MonoidalTransform.exists_isResiduallySeparableAlgebraic_localization_equiv`), then
  `FrameStepLocal.isStandardBase_and_grIdeal_localization_of_strictTransform` (Theorem 5 and
  Corollary 3 (c)), transported along the localization and `e`
  (`MonoidalTransform.strictTransformIdeal_eq_map_of_comp_eq`).

\textbf{Deviation from the paper (gap filled).} The paper's Corollary 3 (b) is not applicable
here (see `lem:IV.AB-5-frame`), and "there exists `v_t`", "a frame transform", "(3), (4) for
`t + 1`" are proved.  The finiteness of the integral closures of footnote 10 for the ring `T₂.ring`
(needed by Corollary 3 (c)) is the hypothesis of the first component, supplied by
`finiteIntegralClosureLocalizations_monoidalTransform`.

*Second component* (p. 306): "Therefore, in view of (a) and (b) of (2), we can conclude by
Corollary 1 of Proposition 2, § 8, Ch. III that, if `Ĵ_0(t+1)` (a prime of `Ŝ_{t+1}` with
`Ŝ_{t+1}/Ĵ_0(t+1)` regular) is a permissible center for `Ĵ_j(t+1)` for some `j (1 ≦ j ≦ β)`, then
`Ĵ_0(t)` is a permissible center for `Ĵ_j(t)` for the same `j`."  In Lean this is
`isPermissibleCenter_of_isPermissibleCenter_strictTransformIdeal` (Corollary 1 for the stalk
transform `T₁`, `Compat/PermissibleCenterDescent.lean`) with `R = Ŝ_t`, `J = Ĵ_j(t)`, `P = Ĵ_0(t)`,
`Q = Q̂_t`, `f = g_{jk}(t)`, `g = unit · g_{jk}(t+1)`: (iii) is `ν_Q̂(g_{jk}(t)) = ν_{jk}`
(`hordQ`),
(iv) is (a) of (2) at `t`, (vi) is (b) of (2) at `t+1`, `P ≤ Q` and `J ≤ P` are
`stalkIdeal_totalTransform_sys_le_stalkIdeal_B` and
`stalkIdeal_totalTransform_sys_castSucc_le_last`, and `Ĵ_0(t+1) ≠ Ŝ_{t+1}` makes the strict
transform of `P` proper.

\textbf{Deviation from the paper (gap filled).} The hypotheses of Corollary 1 are checked one by
one (`P ≤ Q` from the permissibility of `B_t`, `J ≤ P` from `W ⊆ V_j`, `P ≠ Q`, the choice of
`g_{jk}(t+1)` as the strict transform of `g_{jk}(t)` up to a unit, `Q̂_t`-order equal to
`M`-order), and the regularity of `Ŝ_t/Ĵ_0(t)` is a hypothesis
(`isRegularLocalRing_quotient_sys_last_succ` supplies it along the chain). -/
theorem RemovalFamily.hasGenericStalkFrame_succ_and_isPermissibleCenter_of_mem [Hironaka.HironakaCitedResults.{u}]
    {𝒮 : Frame hS} (R : 𝒮.RemovalFamily)
    (s : ℕ) (xb : (𝒮.xBar (s + 1)).toScheme) (hxb : xb ∈ R.uBar (s + 1))
    (hν : (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar (s + 1)).stalkIdeal xb))
    (hmem : (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) ∈ (𝒮.tHat.B s).pts)
    (h : 𝒮.HasGenericStalkFrame s ((𝒮.xBar s).ι.base ((𝒮.fBar s).base xb))) :
    ((∀ [IsDomain ((𝒮.tHat.X s).presheaf.stalk
        ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb)))]
      (T₂ : MonoidalTransform ((𝒮.tHat.X s).presheaf.stalk
        ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb)))
        ((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb)))),
        FiniteIntegralClosureLocalizations T₂.ring) →
      𝒮.HasGenericStalkFrame (s + 1) ((𝒮.xBar (s + 1)).ι.base xb)) ∧
    (IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk
        ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb)) ⧸
        (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal
          ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb))) →
      (Subscheme.totalTransform (𝒮.c (s + 1)) (T.sys ℜ (s + 1) (Fin.last ℜ.β))).stalkIdeal
        ((𝒮.xBar (s + 1)).ι.base xb) ≠ ⊤ →
      ∀ j : Fin ℜ.β,
        IsPermissibleCenter ((𝒮.tHat.X (s + 1)).presheaf.stalk ((𝒮.xBar (s + 1)).ι.base xb))
          ((Subscheme.totalTransform (𝒮.c (s + 1)) (T.sys ℜ (s + 1) j.castSucc)).stalkIdeal
            ((𝒮.xBar (s + 1)).ι.base xb))
          ((Subscheme.totalTransform (𝒮.c (s + 1))
            (T.sys ℜ (s + 1) (Fin.last ℜ.β))).stalkIdeal ((𝒮.xBar (s + 1)).ι.base xb)) →
        IsPermissibleCenter ((𝒮.tHat.X s).presheaf.stalk
            ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb)))
          ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j.castSucc)).stalkIdeal
            ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb)))
          ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal
            ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb)))) := by
  classical
  set xh : 𝒮.tHat.X (s + 1) := (𝒮.xBar (s + 1)).ι.base xb with hxh
  have hcomm : (𝒮.tHat.f s).base xh = (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) :=
    (congrArg (fun φ => φ.base xb) (𝒮.fBar_comm s)).symm
  have hdiff := R.mem_diff_of_mem_uBar_succ s xb hxb
  have hbad : (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) ∉ R.bad s := hdiff.2
  have h' : 𝒮.HasGenericStalkFrame s ((𝒮.tHat.f s).base xh) := by rw [hcomm]; exact h
  have hmem' : (𝒮.tHat.f s).base xh ∈ (𝒮.tHat.B s).pts := by rw [hcomm]; exact hmem
  set p0 := (𝒮.tHat.f s).base xh with hp0
  obtain ⟨F, z, m, ν, g, co, hr, hz, hX, hgJ, hgr, hord, hν0, hb, hsh, hJ⟩ := h'
  have hB : (𝒮.tHat.B s).IsNonsingular := 𝒮.isNonsingular_B (hS.ambient.2.1 x₀)
    hS.isNonsingular_X hS.isNonsingular_B s
  have hQprime := Subscheme.isPrime_stalkIdeal_of_isNonsingular hB hmem'
  have hQreg := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hB hmem'
  have hQne : (𝒮.tHat.B s).stalkIdeal p0 ≠ ⊤ := hQprime.ne_top
  have hregA : IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk p0) :=
    Frame.instIsRegularLocalRingStalk 𝒮 s p0
  have hdomA : IsDomain ((𝒮.tHat.X s).presheaf.stalk p0) := isDomain_of_isRegularLocalRing _
  have hcharA : CharZero (ResidueField ((𝒮.tHat.X s).presheaf.stalk p0)) := by
    have := hS.isAlgebraicScheme_X s
    exact (RingHom.charZero_iff (ResidueField.map
      ((𝒮.c s).stalkMap p0).hom).injective).mp (charZero_residueField_stalk (T.X s) _)
  -- `z ∈ Q̂_s` ("off `Bad_s`, `B̂_s ⊆ X̄_s`": the field of the family)
  have hzQ : z ∈ (𝒮.tHat.B s).stalkIdeal p0 := by
    have h1 := R.stalkIdeal_xBar_le s ((𝒮.xBar s).ι.base ((𝒮.fBar s).base xb)) ⟨hmem, hbad⟩
    rw [← hcomm] at h1
    have hzX : z ∈ (𝒮.xBar s).stalkIdeal p0 := by
      rw [hX]; exact Ideal.mem_span_singleton_self z
    exact h1 hzX
  -- `Ĵ_j(s) ⊆ Q̂_s`
  have hJQ : ∀ j, (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal p0 ≤
      (𝒮.tHat.B s).stalkIdeal p0 := fun j =>
    𝒮.stalkIdeal_totalTransform_sys_le_stalkIdeal_B s p0 hmem' j
  have hdvd : ∀ j k (i : Fin (ν j k)), (i : ℕ) + 1 ∣ 𝒮.b := by
    intro j k i
    rw [hb]
    exact ((Nat.dvd_factorial (Nat.succ_pos _) i.2).trans
      (Finset.dvd_prod_of_mem (fun k => (ν j k).factorial) (Finset.mem_univ k))).trans
        (Finset.dvd_prod_of_mem (fun j => ∏ k, (ν j k).factorial) (Finset.mem_univ j))
  have hbpos : 0 < 𝒮.b := by
    rw [hb]; exact Finset.prod_pos fun j _ => Finset.prod_pos fun k _ => Nat.factorial_pos _
  -- "`g_{jki}(s)^{b/i} ∈ Q̂_s^b + (z)`", hence "`g_{jki}(s) ∈ (Q̂_s ∩ T_s)^i`"
  have hcoQ : ∀ j k (i : Fin (ν j k)), co j k i ∈
      (((𝒮.tHat.B s).stalkIdeal p0).comap (algebraMap F.S _)) ^ ((i : ℕ) + 1) := by
    intro j k i
    have hIH := hJ _ hcomm
    obtain ⟨hψs, hψk⟩ := surjective_and_ker_stalkCongr_stalkMap (𝒮.xBar s)
      ((𝒮.fBar s).base xb) p0 hcomm
    have hBb : (𝒮.bBarOn s).stalkIdeal ((𝒮.fBar s).base xb) =
        ((𝒮.tHat.B s).stalkIdeal p0).map
          (((𝒮.tHat.X s).presheaf.stalkCongr (Inseparable.of_eq hcomm)).hom ≫
            (𝒮.xBar s).ι.stalkMap ((𝒮.fBar s).base xb)).hom := by
      show (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s)).stalkIdeal _ = _
      rw [stalkIdeal_totalTransform, CommRingCat.hom_comp, ← Ideal.map_map,
        stalkIdeal_map_stalkCongr _ hcomm]
    have hle := R.stalkIdeal_jBar_le s ((𝒮.fBar s).base xb) hdiff.1 ⟨hmem, hbad⟩
    have hy : (((𝒮.tHat.X s).presheaf.stalkCongr (Inseparable.of_eq hcomm)).hom ≫
        (𝒮.xBar s).ι.stalkMap ((𝒮.fBar s).base xb)).hom
        (algebraMap F.S _ (co j k i) ^ (𝒮.b / ((i : ℕ) + 1))) ∈
        (𝒮.jBar s).stalkIdeal ((𝒮.fBar s).base xb) := by
      rw [hIH]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, k, i, rfl⟩)
    have hy2 := hle hy
    rw [hBb, ← Ideal.map_pow] at hy2
    have hy3 := (Ideal.mem_comap).mpr hy2
    rw [Ideal.comap_map_of_surjective _ hψs, ← RingHom.ker_eq_comap_bot, hψk, hX] at hy3
    refine RegularFrame.mem_comap_pow_of_pow_mem_pow_sup_prime F z hr hz _ hQreg hzQ _
      (Nat.div_pos (Nat.le_of_dvd hbpos (hdvd j k i)) (Nat.succ_pos _)) ?_
    rwa [Nat.div_mul_cancel (hdvd j k i)]
  -- "`ν_{Q̂}(g_{jk}(s)) = ν_{jk}`"
  have hordQ : ∀ j k, Ideal.ordElem ((𝒮.tHat.B s).stalkIdeal p0) (g j k) = ν j k := by
    intro j k
    have h1 := RegularFrame.ordElem_eq_of_coeff_mem_pow F z _ hzQ (ν j k) (co j k) (hcoQ j k)
      (by rw [← hsh j k]; exact hord j k)
    rw [hsh j k]; exact h1
  have hgQ : ∀ j k, g j k ∈ ((𝒮.tHat.B s).stalkIdeal p0) ^ ν j k := fun j k =>
    Ideal.mem_pow_of_le_ordElem (hordQ j k).ge
  -- `Ŝ_{s+1}` is a monoidal transform of `Ŝ_s` with center `Q̂_s`
  have hregX : IsRegularLocalRing ((𝒮.tHat.X (s + 1)).presheaf.stalk xh) :=
    Frame.instIsRegularLocalRingStalk 𝒮 (s + 1) xh
  have hdomX : IsDomain ((𝒮.tHat.X s).presheaf.stalk
      ((𝒮.tHat.monoidalTransformation s).f.base xh)) := isDomain_of_isRegularLocalRing _
  obtain ⟨T₁, e, he⟩ : ∃ (T₁ : MonoidalTransform ((𝒮.tHat.X s).presheaf.stalk p0)
      ((𝒮.tHat.B s).stalkIdeal p0))
      (e : T₁.ring ≃+* (𝒮.tHat.X (s + 1)).presheaf.stalk xh),
      e.toRingHom.comp T₁.toRing = ((𝒮.tHat.f s).stalkMap xh).hom :=
    (𝒮.tHat.monoidalTransformation s).exists_monoidalTransform_stalk xh
  have hregT : IsRegularLocalRing T₁.ring := IsRegularLocalRing.of_ringEquiv e.symm
  have hJ1 : ∀ j, (Subscheme.totalTransform (𝒮.c (s + 1)) (T.sys ℜ (s + 1) j)).stalkIdeal xh =
      (strictTransformIdeal T₁ ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal
        p0)).map e := by
    intro j
    rw [𝒮.totalTransform_c_sys_succ s j]
    exact MonoidalTransformation.stalkIdeal_strictTransform_eq_map
      (𝒮.tHat.monoidalTransformation s) xh T₁ e he (Or.inl ⟨hQprime, hQreg⟩) _
  -- `z_s/x_{R₁}`, the strict transform of `z_s`
  have : ((𝒮.tHat.B s).stalkIdeal p0).IsPrime := hQprime
  have : IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk p0 ⧸ (𝒮.tHat.B s).stalkIdeal p0) := hQreg
  have hzmem : T₁.toRing z ∈ Ideal.span {T₁.xR} := by
    rw [T₁.span_xR_eq_map]; exact Ideal.mem_map_of_mem _ hzQ
  obtain ⟨ζ, hζ'⟩ := Ideal.mem_span_singleton'.mp hzmem
  have hζ : T₁.toRing z = T₁.xR * ζ := by rw [mul_comm]; exact hζ'.symm
  have hz2 : z ∉ maximalIdeal _ ^ 2 := F.extends_rsop.notMem_maximalIdeal_sq
    (Finset.mem_image.mpr ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, Finset.mem_univ _, hz _⟩)
  have hordz : Ideal.ordElem ((𝒮.tHat.B s).stalkIdeal p0) z = 1 :=
    Ideal.ordElem_eq_one_of_mem_of_notMem_sq hQne hzQ hz2
  have hζspan : Ideal.span {ζ} = strictTransformIdeal T₁ (Ideal.span {z}) :=
    (strictTransformIdeal_span_singleton_eq T₁ hQprime hQreg z ζ (by
      rw [hordz]; simpa using hζ.symm)).symm
  have hXst : (𝒮.xBar (s + 1)).stalkIdeal xh = Ideal.span {e ζ} := by
    have h1 : (𝒮.xBar (s + 1)).stalkIdeal xh =
        (strictTransformIdeal T₁ ((𝒮.xBar s).stalkIdeal p0)).map e :=
      MonoidalTransformation.stalkIdeal_strictTransform_eq_map
        (𝒮.tHat.monoidalTransformation s) xh T₁ e he (Or.inl ⟨hQprime, hQreg⟩) (𝒮.xBar s)
    rw [h1, hX, ← hζspan, Ideal.map_span, Set.image_singleton]
  -- `z_{s+1} = z_s/v_s` is a non-unit: `x̂'_{s+1} ∈ X̄_{s+1}`
  have hζm : ζ ∈ maximalIdeal T₁.ring := by
    have hxX : xh ∈ (𝒮.xBar (s + 1)).pts := Subscheme.mem_pts_ι (𝒮.xBar (s + 1)) xb
    rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, hXst] at hxX
    by_contra hcon
    apply hxX
    rw [Ideal.span_singleton_eq_top]
    exact (IsLocalRing.notMem_maximalIdeal.mp hcon).map e
  -- the frame transform `(T_{s+1}; z_{s+1})`, `z_{s+1} = z_s/v_s`
  obtain ⟨F', z', c₀, hr', hz', hspan, hzv, hc₀0, hdiv⟩ :=
    RegularFrame.exists_frameTransform_of_mem_maximalIdeal F z hz hr _ hzQ T₁ ζ hζ hζm
  set v := algebraMap F'.S T₁.ring c₀ with hvdef
  have hdomT := isDomain_of_isRegularLocalRing T₁.ring
  have hxR0 : T₁.xR ≠ 0 := fun h0 => T₁.x_ne_zero (T₁.toRing_injective (by
    rw [map_zero]; exact h0))
  obtain ⟨u, hu⟩ : Associated T₁.xR v := Ideal.span_singleton_eq_span_singleton.mp
    (T₁.span_xR_eq_map.trans hspan.symm)
  choose c' hc' using fun j k (i : Fin (ν j k)) => hdiv ((i : ℕ) + 1) (co j k i) (hcoQ j k i)
  set g' : ∀ j, Fin (m j) → T₁.ring := fun j k => z' ^ ν j k + ∑ i : Fin (ν j k),
    algebraMap F'.S _ (c' j k i) * z' ^ (ν j k - ((i : ℕ) + 1)) with hg'def
  have hTg : ∀ j k, T₁.toRing (g j k) = v ^ ν j k * g' j k := by
    intro j k
    rw [hsh j k, map_add, map_pow, map_sum, hzv, mul_pow, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hzv, hc' j k i, mul_pow]
    have hi : (i : ℕ) + 1 ≤ ν j k := i.2
    have : v ^ ν j k = v ^ ((i : ℕ) + 1) * v ^ (ν j k - ((i : ℕ) + 1)) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    ring
  have hg'span : ∀ j k, Ideal.span {g' j k} = strictTransformIdeal T₁ (Ideal.span {g j k}) := by
    intro j k
    rw [strictTransformIdeal_span_singleton_eq T₁ hQprime hQreg (g j k)
      ((u : T₁.ring) ^ ν j k * g' j k) (by
        rw [hordQ j k, ENat.toNat_natCast, hTg j k, ← hu, mul_pow]; ring)]
    exact (Ideal.span_singleton_mul_left_unit (u.isUnit.pow _) _).symm
  have hζz' : Ideal.span {ζ} = Ideal.span {z'} := by
    refine (Ideal.span_singleton_eq_span_singleton.mpr ⟨u, ?_⟩).symm
    apply mul_left_cancel₀ hxR0
    rw [← hζ, hzv, ← hu]; ring
  have hJbar1 : ∀ (xb' : (𝒮.xBar (s + 1)).toScheme) (h' : xh = (𝒮.xBar (s + 1)).ι.base xb'),
      (𝒮.jBar (s + 1)).stalkIdeal xb' = (Ideal.span {y | ∃ j k i, y = algebraMap (F'.transport e).S
        ((𝒮.tHat.X (s + 1)).presheaf.stalk xh) (c' j k i) ^ (𝒮.b / ((i : ℕ) + 1))}).map
        (((𝒮.tHat.X (s + 1)).presheaf.stalkCongr (Inseparable.of_eq h')).hom ≫
          (𝒮.xBar (s + 1)).ι.stalkMap xb').hom := by
    intro xb' h'
    obtain rfl : xb' = xb := (𝒮.xBar (s + 1)).ι.isClosedEmbedding.injective h'.symm
    have hcomm : (𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb') =
        (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb') :=
      (congrArg (fun φ => φ.base xb') (𝒮.fBar_comm s)).symm
    have hIH := hJ _ hcomm
    have hBb : (𝒮.bBarOn s).stalkIdeal ((𝒮.fBar s).base xb') =
        ((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb'))).map
          (((𝒮.tHat.X s).presheaf.stalkCongr (Inseparable.of_eq hcomm)).hom ≫
            (𝒮.xBar s).ι.stalkMap ((𝒮.fBar s).base xb')).hom := by
      show (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s)).stalkIdeal _ = _
      rw [stalkIdeal_totalTransform, CommRingCat.hom_comp, ← Ideal.map_map,
        stalkIdeal_map_stalkCongr _ hcomm]
    rw [jBar_succ, Subscheme.stalkIdeal_divPow_of_isLocallyPrincipal
      (𝒮.isLocallyPrincipal_totalTransform_fBar_bBarOn s), stalkIdeal_totalTransform,
      stalkIdeal_totalTransform, hIH, hBb, Ideal.map_map, Ideal.map_map,
      𝒮.stalkMap_fBar_comp_eq s xb' hcomm, ← he]
    obtain ⟨ψ', hψ'⟩ : ∃ ψ' : T₁.ring →+* (𝒮.xBar (s + 1)).toScheme.presheaf.stalk xb',
        ψ' = ((𝒮.xBar (s + 1)).ι.stalkMap xb').hom.comp e.toRingHom := ⟨_, rfl⟩
    have hcompφ : ((𝒮.xBar (s + 1)).ι.stalkMap xb').hom.comp (e.toRingHom.comp T₁.toRing) =
        ψ'.comp T₁.toRing := by rw [hψ']; rfl
    -- `b = ∏ ν_{jk}!` is divisible by every `i ≤ ν_{jk}`
    have hdvd : ∀ j k (i : Fin (ν j k)), (i : ℕ) + 1 ∣ 𝒮.b := by
      intro j k i
      rw [hb]
      exact ((Nat.dvd_factorial (Nat.succ_pos _) i.2).trans
        (Finset.dvd_prod_of_mem (fun k => (ν j k).factorial) (Finset.mem_univ k))).trans
          (Finset.dvd_prod_of_mem (fun j => ∏ k, (ν j k).factorial) (Finset.mem_univ j))
    -- "`(g_{jki}(s)^{b/i})/v_s^b = g_{jki}(s + 1)^{b/i}`"
    have hGT : (Ideal.span {y | ∃ j k i,
        y = algebraMap F.S _ (co j k i) ^ (𝒮.b / ((i : ℕ) + 1))}).map T₁.toRing =
        Ideal.span (Set.range fun p : (Σ j, Σ k : Fin (m j), Fin (ν j k)) =>
          v ^ 𝒮.b * algebraMap F'.S _ (c' p.1 p.2.1 p.2.2) ^ (𝒮.b / ((p.2.2 : ℕ) + 1))) := by
      have key : ∀ j k (i : Fin (ν j k)), T₁.toRing (algebraMap F.S _ (co j k i) ^
          (𝒮.b / ((i : ℕ) + 1))) = v ^ 𝒮.b * algebraMap F'.S _ (c' j k i) ^
            (𝒮.b / ((i : ℕ) + 1)) := by
        intro j k i
        rw [map_pow, hc' j k i, mul_pow, ← pow_mul, Nat.mul_div_cancel' (hdvd j k i), mul_comm]
      rw [Ideal.map_span]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨j, k, i, hx⟩, hy⟩
        exact ⟨⟨j, k, i⟩, by rw [← hy, hx, key]⟩
      · rintro ⟨⟨j, k, i⟩, hy⟩
        exact ⟨_, ⟨j, k, i, rfl⟩, by rw [key]; exact hy⟩
    -- the local ring `T̄_{s+1}` of `X̄_{s+1}` is a domain, and `v̄_s ≠ 0` in it
    have hXst' : (𝒮.xBar (s + 1)).stalkIdeal ((𝒮.xBar (s + 1)).ι.base xb') =
        Ideal.span {e z'} := by
      have h1 := congrArg (Ideal.map e) hζz'
      rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at h1
      rw [hXst]
      exact h1
    have hker : RingHom.ker ((𝒮.xBar (s + 1)).ι.stalkMap xb').hom = Ideal.span {e z'} := by
      rw [← stalkIdeal_eq_ker_stalkMap, hXst']
    have hrange : Set.range F'.z = {z'} := by
      ext a
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩; exact hz' j
      · rintro rfl
        exact ⟨⟨0, by rw [hr']; exact Nat.one_pos⟩, hz' _⟩
    have hq := F'.quot_bijective
    rw [hrange] at hq
    have := RegularFrame.isDomain_S F'
    have hprime : (Ideal.span {z'}).IsPrime := by
      have : IsDomain (T₁.ring ⧸ Ideal.span {z'}) :=
        (RingEquiv.ofBijective _ hq).symm.injective.isDomain
          ((RingEquiv.ofBijective _ hq).symm : T₁.ring ⧸ Ideal.span {z'} →+* F'.S)
      exact (Ideal.Quotient.isDomain_iff_prime _).mp this
    have hprime' : (Ideal.span {e z'}).IsPrime := by
      have := Ideal.map_isPrime_of_equiv e (I := Ideal.span {z'})
      rwa [Ideal.map_span, Set.image_singleton] at this
    have hdomD : IsDomain ((𝒮.xBar (s + 1)).toScheme.presheaf.stalk xb') := by
      have : IsDomain ((𝒮.tHat.X (s + 1)).presheaf.stalk ((𝒮.xBar (s + 1)).ι.base xb') ⧸
          RingHom.ker ((𝒮.xBar (s + 1)).ι.stalkMap xb').hom) := by
        rw [hker]; exact (Ideal.Quotient.isDomain_iff_prime _).mpr hprime'
      let φ := RingHom.quotientKerEquivOfSurjective ((𝒮.xBar (s + 1)).ι.stalkMap_surjective xb')
      exact Function.Injective.isDomain φ.symm φ.symm.injective
    have hv0 : ψ' v ≠ 0 := by
      intro h0
      have h1 : e v ∈ RingHom.ker ((𝒮.xBar (s + 1)).ι.stalkMap xb').hom := by
        rw [hψ'] at h0; exact h0
      rw [hker, Ideal.mem_span_singleton'] at h1
      obtain ⟨a, ha⟩ := h1
      have h2 : v ∈ Ideal.span {z'} := by
        rw [Ideal.mem_span_singleton']
        refine ⟨e.symm a, e.injective ?_⟩
        rw [map_mul, RingEquiv.apply_symm_apply, ha]
      apply hc₀0
      apply hq.1
      rw [RingHom.comp_apply, RingHom.comp_apply, map_zero, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h2
    have h1 : Ideal.map (ψ'.comp T₁.toRing) (Ideal.span {y | ∃ j k i,
        y = algebraMap F.S _ (co j k i) ^ (𝒮.b / ((i : ℕ) + 1))}) =
        Ideal.span (Set.range fun p : (Σ j, Σ k : Fin (m j), Fin (ν j k)) =>
          ψ' v ^ 𝒮.b * ψ' (algebraMap F'.S _ (c' p.1 p.2.1 p.2.2)) ^
            (𝒮.b / ((p.2.2 : ℕ) + 1))) := by
      refine (Ideal.map_map T₁.toRing ψ').symm.trans ((congrArg (Ideal.map ψ') hGT).trans ?_)
      rw [Ideal.map_span, ← Set.range_comp]
      refine congrArg Ideal.span (congrArg Set.range (funext fun p => ?_))
      simp only [Function.comp_apply, map_mul, map_pow]
    have h2 : Ideal.map (ψ'.comp T₁.toRing)
        ((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb'))) =
        Ideal.span {ψ' v} := by
      refine (Ideal.map_map T₁.toRing ψ').symm.trans ?_
      rw [← hspan, Ideal.map_span, Set.image_singleton]
    have key : Submodule.colon (Ideal.map (ψ'.comp T₁.toRing) (Ideal.span {y | ∃ j k i,
        y = algebraMap F.S _ (co j k i) ^ (𝒮.b / ((i : ℕ) + 1))}))
        ((Ideal.map (ψ'.comp T₁.toRing) ((𝒮.tHat.B s).stalkIdeal
          ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb'))) ^ 𝒮.b : Ideal _) : Set _) =
        Ideal.span (Set.range fun p : (Σ j, Σ k : Fin (m j), Fin (ν j k)) =>
          ψ' (algebraMap F'.S _ (c' p.1 p.2.1 p.2.2)) ^ (𝒮.b / ((p.2.2 : ℕ) + 1))) := by
      rw [h1, h2]
      exact Ideal.colon_span_range_mul_pow (ψ' v) hv0 𝒮.b _
    rw [hcompφ]
    refine key.trans ?_
    rw [Ideal.map_span]
    refine congrArg Ideal.span ?_
    ext y
    constructor
    · rintro ⟨⟨j, k, i⟩, hy⟩
      refine ⟨_, ⟨j, k, i, rfl⟩, ?_⟩
      rw [← hy, hψ']
      simp [TopCat.Presheaf.stalkCongr_hom]
      rfl
    · rintro ⟨x, ⟨j, k, i, hx⟩, hy⟩
      refine ⟨⟨j, k, i⟩, ?_⟩
      rw [← hy, hx, hψ']
      simp [TopCat.Presheaf.stalkCongr_hom]
      rfl
  have hXst' : (𝒮.xBar (s + 1)).stalkIdeal xh = Ideal.span {e z'} := by
    have h1 := congrArg (Ideal.map e) hζz'
    rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at h1
    rw [hXst]; exact h1
  have hz'M : e z' ∈ maximalIdeal ((𝒮.tHat.X (s + 1)).presheaf.stalk xh) := by
    have h1 : z' ∈ Ideal.span {ζ} := hζz' ▸ Ideal.mem_span_singleton_self z'
    have h2 : z' ∈ maximalIdeal T₁.ring :=
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hζm)) (by simpa using h1)
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (mem_maximalIdeal _).mp h2 (by simpa using hu.map e.symm)
  -- "(b) of (2) for `g_{jk}(s+1)`": `g_{jki}(s+1) ∈ M_{S_{s+1}}^i` from `ν(J̄(s+1)) ≥ b`
  have hc'M : ∀ j k (i : Fin (ν j k)), c' j k i ∈ maximalIdeal F'.S ^ ((i : ℕ) + 1) := by
    intro j k i
    have hkpos : 0 < 𝒮.b / ((i : ℕ) + 1) :=
      Nat.div_pos (Nat.le_of_dvd hbpos (hdvd j k i)) (Nat.succ_pos _)
    have hJ' := hJbar1 xb rfl
    have hle := Ideal.le_pow_of_le_ord hν
    set φ := ((𝒮.xBar (s + 1)).ι.stalkMap xb).hom with hφ
    have hψ : (((𝒮.tHat.X (s + 1)).presheaf.stalkCongr (Inseparable.of_eq (rfl : xh = xh))).hom ≫
        (𝒮.xBar (s + 1)).ι.stalkMap xb).hom = φ := by
      ext x
      simp [TopCat.Presheaf.stalkCongr_hom, hφ]
    rw [hψ] at hJ'
    have hφs : Function.Surjective φ := (𝒮.xBar (s + 1)).ι.stalkMap_surjective xb
    have hφker : RingHom.ker φ = Ideal.span {e z'} := by
      rw [← hXst']
      exact (stalkIdeal_eq_ker_stalkMap (𝒮.xBar (s + 1)) xb).symm
    have hmax : (maximalIdeal ((𝒮.tHat.X (s + 1)).presheaf.stalk xh)).map φ =
        maximalIdeal ((𝒮.xBar (s + 1)).toScheme.presheaf.stalk xb) :=
      map_maximalIdeal_of_surjective φ hφs
    have hmem : (algebraMap (F'.transport e).S ((𝒮.tHat.X (s + 1)).presheaf.stalk xh)
        (c' j k i)) ^ (𝒮.b / ((i : ℕ) + 1)) ∈
        (maximalIdeal ((𝒮.tHat.X (s + 1)).presheaf.stalk xh)) ^ 𝒮.b ⊔ Ideal.span {e z'} := by
      have h1 : φ ((algebraMap (F'.transport e).S ((𝒮.tHat.X (s + 1)).presheaf.stalk xh)
          (c' j k i)) ^ (𝒮.b / ((i : ℕ) + 1))) ∈ (𝒮.jBar (s + 1)).stalkIdeal xb := by
        rw [hJ']
        exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, k, i, rfl⟩)
      have h2 := hle h1
      rw [← hmax, ← Ideal.map_pow] at h2
      have h3 := (Ideal.mem_comap).mpr h2
      rw [Ideal.comap_map_of_surjective _ hφs, ← RingHom.ker_eq_comap_bot, hφker] at h3
      exact h3
    refine RegularFrame.mem_pow_of_pow_mem_pow_sup (F'.transport e) (e z') hr' (fun i => ?_)
      hz'M (c' j k i) hkpos ?_
    · exact congrArg e (hz' i)
    · rwa [Nat.div_mul_cancel (hdvd j k i)]
  have hb' : ∀ j k, Ideal.ordElem (maximalIdeal ((𝒮.tHat.X (s + 1)).presheaf.stalk xh))
      (e (g' j k)) = ν j k := by
    intro j k
    have := RegularFrame.ordElem_pow_add_sum_eq (F'.transport e) (e z') hr'
      (fun i => congrArg e (hz' i)) (ν j k) (c' j k) (hc'M j k)
    rw [hg'def]
    simp only [map_add, map_pow, map_sum, map_mul]
    exact this
  refine ⟨?_, ?_⟩
  swap
  · -- "in view of (a) and (b) of (2), we can conclude by Corollary 1 of Proposition 2, § 8,
    -- Ch. III that, if `Ĵ_0(t+1)` is a permissible center for `Ĵ_j(t+1)`, then `Ĵ_0(t)` is
    -- a permissible center for `Ĵ_j(t)`" (p. 306)
    intro hregP hne1 j hperm
    have hdomP : IsDomain ((𝒮.tHat.X s).presheaf.stalk p0 ⧸
        (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal p0) :=
      isDomain_of_isRegularLocalRing _
    have hPprime := (Ideal.Quotient.isDomain_iff_prime _).mp hdomP
    have hlocT : IsLocalHom T₁.toRing := ⟨fun a ha => by
      have h1 : IsUnit (e (T₁.toRing a)) := ha.map e
      have h2 : e (T₁.toRing a) = ((𝒮.tHat.f s).stalkMap xh).hom a := by
        rw [← he]; rfl
      rw [h2] at h1
      exact isUnit_of_map_unit ((𝒮.tHat.f s).stalkMap xh).hom a h1⟩
    have hperm₁ : IsPermissibleCenter T₁.ring
        (strictTransformIdeal T₁ ((Subscheme.totalTransform (𝒮.c s)
          (T.sys ℜ s j.castSucc)).stalkIdeal p0))
        (strictTransformIdeal T₁ ((Subscheme.totalTransform (𝒮.c s)
          (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal p0)) := by
      refine (isPermissibleCenter_map_ringEquiv_iff e _ _).mp ?_
      rw [← hJ1, ← hJ1]
      exact hperm
    have hne : strictTransformIdeal T₁ ((Subscheme.totalTransform (𝒮.c s)
        (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal p0) ≠ ⊤ := fun h0 => hne1 (by
      rw [hJ1, h0, Ideal.map_top])
    have hu0 : ∀ n : ℕ, Ideal.ordElem (maximalIdeal T₁.ring) ((u : T₁.ring) ^ n) = 0 := fun n => by
      refine le_antisymm (Ideal.ordElem_le_of_notMem (m := 0) ?_) bot_le
      rw [zero_add, pow_one]
      exact fun hm => (mem_maximalIdeal _).mp hm (u.isUnit.pow _)
    exact isPermissibleCenter_of_isPermissibleCenter_strictTransformIdeal
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j.castSucc)).stalkIdeal p0)
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal p0)
      ((𝒮.tHat.B s).stalkIdeal p0) (hJQ (Fin.last ℜ.β))
      (𝒮.stalkIdeal_totalTransform_sys_castSucc_le_last s p0 j)
      (g j.castSucc) (hgJ j.castSucc)
      (fun k => (hord j.castSucc k).trans (hordQ j.castSucc k).symm) (hgr j.castSucc).symm
      T₁ hne (ν j.castSucc) (fun k => (hordQ j.castSucc k).symm)
      (fun k => (u : T₁.ring) ^ ν j.castSucc k * g' j.castSucc k)
      (fun k => by
        show T₁.xR ^ ν j.castSucc k * ((u : T₁.ring) ^ ν j.castSucc k * g' j.castSucc k) = _
        rw [hTg, ← hu, mul_pow]; ring)
      (fun k => by
        rw [Hironaka.ordElem_mul_maximalIdeal, hu0, zero_add, ← ordElem_maximalIdeal_ringEquiv e]
        exact hb' j.castSucc k)
      hperm₁
  intro hfin
  -- (a) of (2) at `t + 1`: Theorem 5 for a closed-point transform, then Corollary 3 (c)
  have hP0 : (𝒮.tHat.B s).stalkIdeal p0 ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨T₁.x, T₁.x_mem, T₁.x_ne_zero⟩
  obtain ⟨T₂, Q₁, hQ₁, L, hxeq, hsep, hLc⟩ :=
    MonoidalTransform.exists_isResiduallySeparableAlgebraic_localization_equiv
      ((𝒮.tHat.B s).stalkIdeal p0) T₁
  obtain ⟨hregT2, hlocT2, hxT2⟩ :=
    MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map T₂ hQprime hP0 hQreg
  let lam : T₂.ring →+* T₁.ring := L.toRingHom.comp (algebraMap T₂.ring (Localization.AtPrime Q₁))
  have hlam : ∀ a, lam (T₂.toRing a) = T₁.toRing a := hLc
  have hstrict : ∀ J, strictTransformIdeal T₁ J = (strictTransformIdeal T₂ J).map lam :=
    fun J => MonoidalTransform.strictTransformIdeal_eq_map_of_comp_eq _ T₁ T₂ lam hlam J
  have hmemg : ∀ j k, g' j k ∈ strictTransformIdeal T₁
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal p0) := by
    intro j k
    have h5 : g' j k ∈ Ideal.span {g' j k} := Ideal.mem_span_singleton_self _
    rw [hg'span j k] at h5
    refine (?_ : strictTransformIdeal T₁ (Ideal.span {g j k}) ≤ strictTransformIdeal T₁
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal p0)) h5
    unfold strictTransformIdeal
    refine Ideal.span_mono ?_
    rintro y ⟨x, hx, f, hf, ν', hν', hy⟩
    exact ⟨x, hx, f, (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hgJ j k))) hf, ν', hν',
      hy⟩
  have hfinT2 : FiniteIntegralClosureLocalizations T₂.ring := hfin T₂
  have hgrnew : ∀ j, grIdeal (maximalIdeal ((𝒮.tHat.X (s + 1)).presheaf.stalk xh))
      ((Subscheme.totalTransform (𝒮.c (s + 1)) (T.sys ℜ (s + 1) j)).stalkIdeal xh) =
      Ideal.span (Set.range fun k => initialForm
        (maximalIdeal ((𝒮.tHat.X (s + 1)).presheaf.stalk xh)) (e (g' j k))) := by
    intro j
    rw [hJ1 j]
    obtain ⟨m', σ, -, hσ⟩ := exists_isStandardBase_comp _ ((Subscheme.totalTransform (𝒮.c s)
      (T.sys ℜ s j)).stalkIdeal p0) (g j) (hgJ j) (hgr j).symm
    -- the elements `g_{jk}(s+1)` of the closed-point transform
    have hgc : ∀ k, ∃ y : T₂.ring, T₂.toRing T₂.x ^ ν j k * y = T₂.toRing (g j k) := by
      intro k
      have hmemx : T₂.toRing (g j k) ∈ Ideal.span {T₂.xR ^ ν j k} := by
        rw [← Ideal.span_singleton_pow, hxT2, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ (hgQ j k)
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmemx
      exact ⟨y, by rw [mul_comm]; exact hy⟩
    choose gc hgc using hgc
    -- `L(gc) = u^ν g'`
    have hLg : ∀ k, L (algebraMap T₂.ring (Localization.AtPrime Q₁) (gc k)) =
        (u : T₁.ring) ^ ν j k * g' j k := by
      intro k
      have e1 : T₁.xR ^ ν j k * lam (gc k) = T₁.toRing (g j k) := by
        have := congrArg lam (hgc k)
        rw [map_mul, map_pow, hlam, hlam, hxeq] at this
        exact this
      apply mul_left_cancel₀ (pow_ne_zero (ν j k) hxR0)
      show T₁.xR ^ ν j k * lam (gc k) = _
      rw [e1, hTg j k, ← hu, mul_pow]
      ring
    -- orders in the localization at `Q₁`
    have hloc : ∀ i : Fin m', Ideal.ordElem (maximalIdeal (Localization.AtPrime Q₁))
        (algebraMap T₂.ring (Localization.AtPrime Q₁) (gc (σ i))) = ν j (σ i) := by
      intro i
      rw [← ordElem_maximalIdeal_ringEquiv L, hLg (σ i), mul_comm,
        Hironaka.ordElem_mul_maximalIdeal]
      have hu0 : Ideal.ordElem (maximalIdeal T₁.ring) ((u : T₁.ring) ^ ν j (σ i)) = 0 := by
        refine le_antisymm (Ideal.ordElem_le_of_notMem (m := 0) ?_) bot_le
        rw [zero_add, pow_one]
        exact fun hm => (mem_maximalIdeal _).mp hm (u.isUnit.pow _)
      rw [hu0, add_zero, ← ordElem_maximalIdeal_ringEquiv e]
      exact hb' j (σ i)
    have hcore := FrameStepLocal.isStandardBase_and_grIdeal_localization_of_strictTransform
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal p0)
      ((𝒮.tHat.B s).stalkIdeal p0) (hJQ j) T₂ hsep T₂.x T₂.x_mem hxT2.symm
      (g j ∘ σ) (fun i => ν j (σ i)) (fun i => gc (σ i))
      (fun i => (hord j (σ i)).symm) (fun i => hgc (σ i)) hσ
      (fun i => (hordQ j (σ i)).trans (hord j (σ i)).symm) Q₁ hloc hfinT2
    obtain ⟨-, -, -, hgrL⟩ := hcore
    set J := (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal p0 with hJdef
    have h2 := grIdeal_map_eq_span_initialForm_of_bijective L.toRingHom L.bijective
      (maximalIdeal (Localization.AtPrime Q₁))
      ((strictTransformIdeal T₂ J).map (algebraMap T₂.ring (Localization.AtPrime Q₁)))
      (fun i => algebraMap T₂.ring (Localization.AtPrime Q₁) (gc (σ i))) hgrL
    have hmaxL : Ideal.map L.toRingHom (maximalIdeal (Localization.AtPrime Q₁)) =
        maximalIdeal T₁.ring :=
      (Ideal.map_coe L _).trans (IsLocalRing.map_ringEquiv_maximalIdeal L)
    have hmapL : Ideal.map L.toRingHom
        ((strictTransformIdeal T₂ J).map (algebraMap T₂.ring (Localization.AtPrime Q₁))) =
        strictTransformIdeal T₁ J := by
      rw [Ideal.map_map, hstrict J]
    rw [hmaxL, hmapL] at h2
    have h3 : grIdeal (maximalIdeal T₁.ring) (strictTransformIdeal T₁ J) = Ideal.span
        (Set.range fun i : Fin m' => initialForm (maximalIdeal T₁.ring) (g' j (σ i))) := by
      rw [h2]
      have hu := span_range_initialForm_mul_units (maximalIdeal T₁.ring)
        (fun i : Fin m' => g' j (σ i)) (fun i => u ^ ν j (σ i))
      rw [← hu]
      congr 2
      funext i
      show initialForm _ (L (algebraMap T₂.ring (Localization.AtPrime Q₁) (gc (σ i)))) = _
      rw [hLg (σ i), mul_comm]
      rfl
    have h4 := grIdeal_map_eq_span_initialForm_of_bijective e.toRingHom e.bijective
      (maximalIdeal T₁.ring) (strictTransformIdeal T₁ J) (fun i : Fin m' => g' j (σ i)) h3
    have hmaxE : Ideal.map e.toRingHom (maximalIdeal T₁.ring) =
        maximalIdeal ((𝒮.tHat.X (s + 1)).presheaf.stalk xh) :=
      (Ideal.map_coe e _).trans (IsLocalRing.map_ringEquiv_maximalIdeal e)
    rw [hmaxE, show Ideal.map e.toRingHom (strictTransformIdeal T₁ J) =
      Ideal.map e (strictTransformIdeal T₁ J) from Ideal.map_coe e _] at h4
    refine le_antisymm ?_ ?_
    · rw [h4]
      exact Ideal.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨σ i, rfl⟩)
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      exact Ideal.subset_span ⟨e (g' j k), Ideal.mem_map_of_mem e (hmemg j k), rfl⟩
  refine ⟨F'.transport e, e z', m, ν, fun j k => e (g' j k), c', hr',
    fun i => congrArg e (hz' i), hXst', ?_, hgrnew, hb', hν0, hb, ?_, hJbar1⟩
  · intro j k
    rw [hJ1 j]
    exact Ideal.mem_map_of_mem e (hmemg j k)
  · intro j k
    show e (g' j k) = e z' ^ ν j k + ∑ i : Fin (ν j k),
      e (algebraMap F'.S _ (c' j k i)) * e z' ^ (ν j k - ((i : ℕ) + 1))
    simp only [hg'def, map_add, map_pow, map_sum, map_mul]

/-- The step `t → t + 1` of the proof of Lemma (AB.5) (first component of
`RemovalFamily.hasGenericStalkFrame_succ_and_isPermissibleCenter_of_mem`). -/
theorem RemovalFamily.hasGenericStalkFrame_succ_of_mem [Hironaka.HironakaCitedResults.{u}] {𝒮 : Frame hS} (R : 𝒮.RemovalFamily)
    (s : ℕ) (xb : (𝒮.xBar (s + 1)).toScheme) (hxb : xb ∈ R.uBar (s + 1))
    (hν : (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar (s + 1)).stalkIdeal xb))
    (hmem : (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) ∈ (𝒮.tHat.B s).pts)
    (hfin : ∀ [IsDomain ((𝒮.tHat.X s).presheaf.stalk
        ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb)))]
      (T₂ : MonoidalTransform ((𝒮.tHat.X s).presheaf.stalk
        ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb)))
        ((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb)))),
        FiniteIntegralClosureLocalizations T₂.ring)
    (h : 𝒮.HasGenericStalkFrame s ((𝒮.xBar s).ι.base ((𝒮.fBar s).base xb))) :
    𝒮.HasGenericStalkFrame (s + 1) ((𝒮.xBar (s + 1)).ι.base xb) :=
  (R.hasGenericStalkFrame_succ_and_isPermissibleCenter_of_mem s xb hxb hν hmem h).1 hfin

/-- **Gap in the paper (incomplete citation, p. 305).**  Corollary 3 (c) of Theorem 5, Ch. III,
used for `t ≥ 1` in the proof of Lemma (AB.5), needs the finiteness of the integral closures of
footnote 10 for the localizations of the monoidal transforms `R_1` of the non-complete local rings
`Ŝ_t` of the schemes `X̂_t`; the paper does not verify it.

It follows from the finiteness of integral closures for essentially finite type algebras over a
complete noetherian local ring (`Hironaka.finite_integralClosure_of_essFiniteType`, the classical
result of Nagata on the finiteness of the integral closure over Nagata rings): `X̂_s → X̂_0 =
Spec Ŝ` is locally of finite type (a composite of monoidal transformations, which are proper),
`Ŝ` is complete (`isAdicComplete_maximalIdeal_adicCompletion`), and the ring `R_1` of the monoidal
transform is essentially of finite type over `Ŝ`
(`finite_integralClosure_localization_quotient_of_stalk_monoidalTransform`).  This is the
single remaining input of the helper: the statement of the finiteness result is in
`Hironaka/Compat/NagataFinite.lean`. -/
theorem finiteIntegralClosureLocalizations_monoidalTransform [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ)
    (xh : 𝒮.tHat.X (s + 1))
    [IsDomain ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh))]
    (T₂ : MonoidalTransform ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh))
      ((𝒮.tHat.B s).stalkIdeal ((𝒮.tHat.f s).base xh))) :
    FiniteIntegralClosureLocalizations T₂.ring := by
  intro Q' Q'' _ _ h
  have hx0 := hS.ambient.2.1 x₀
  have hregS : IsRegularLocalRing (X.presheaf.stalk x₀) := hx0
  have hregHat := 𝒮.regShat
  have : IsAdicComplete (maximalIdeal (Shat X x₀)) (Shat X x₀) :=
    isAdicComplete_maximalIdeal_adicCompletion (X.presheaf.stalk x₀)
  have : IsLocallyNoetherian (xHat0 X x₀) := isLocallyNoetherian_xHat0 hx0
  -- the structure morphism `g : X̂_s ⟶ X̂_0 = Spec Ŝ`, locally of finite type
  let g : 𝒮.tHat.X s ⟶ Spec (CommRingCat.of (Shat X x₀)) := (𝒮.tHat.pre s).composite
  have hg : LocallyOfFiniteType g := by
    have := MonoidalSuccession.isProper_composite (𝒮.tHat.pre s)
    exact inferInstanceAs (LocallyOfFiniteType (𝒮.tHat.pre s).composite)
  exact finite_integralClosure_localization_quotient_of_stalk_monoidalTransform (S := Shat X x₀)
    g ((𝒮.tHat.f s).base xh) T₂ Q' Q'' h

theorem RemovalFamily.hasGenericStalkFrame_succ [Hironaka.HironakaCitedResults.{u}] {𝒮 : Frame hS} (R : 𝒮.RemovalFamily) (s : ℕ)
    (xb : (𝒮.xBar (s + 1)).toScheme) (hxb : xb ∈ R.uBar (s + 1))
    (hν : (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar (s + 1)).stalkIdeal xb))
    (h : 𝒮.HasGenericStalkFrame s ((𝒮.xBar s).ι.base ((𝒮.fBar s).base xb))) :
    𝒮.HasGenericStalkFrame (s + 1) ((𝒮.xBar (s + 1)).ι.base xb) := by
  classical
  have hcomm : (𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb) =
      (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) :=
    (congrArg (fun φ => φ.base xb) (𝒮.fBar_comm s)).symm
  by_cases hmem : (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) ∈ (𝒮.tHat.B s).pts
  · exact R.hasGenericStalkFrame_succ_of_mem s xb hxb hν hmem
      (fun {_} T₂ => 𝒮.finiteIntegralClosureLocalizations_monoidalTransform s _ T₂) h
  · refine 𝒮.hasGenericStalkFrame_succ_of_notMem s _ (by rw [hcomm]; exact hmem) ?_
    rw [hcomm]; exact h

/-- **The frames (1)--(6) of the proof of Lemma (AB.5)** (pp. 303--305) at the image `x̂'` of a
point `xb ∈ Ū_s` with `ν(J̄(s)_{xb}) ≥ b`.  By induction on `s`: the case `s = 0` is
`hasGenericStalkFrame_zero`, the descent `ν(J̄(t)_{x̂'_t}) ≥ b` is
`RemovalFamily.le_nu_jBar_of_le_nu_succ`, and the step `t → t + 1` is
`RemovalFamily.hasGenericStalkFrame_succ`, which uses the finiteness of the integral closures of
footnote 10, `finiteIntegralClosureLocalizations_monoidalTransform` (it rests on the classical
finiteness result `finite_integralClosure_of_essFiniteType` of `Compat/NagataFinite.lean`). -/
@[blueprint "lem:IV.AB-5-frame"
  (statement := /-- Notation as in \cref{lem:IV.AB-5}. Let $\hat x'$ be a point of $\bar U_s$
    (\cref{lem:IV.3-construction-facts-generic}) with $\nu(\bar J(s)_{\hat x'})\ge b$. Then
    there exist regular frames $(T_t;z_t)$ of $\hat S_t$ $(0\le t\le s)$, elements
    $g_{jk}(t)\in\hat J_j(t)$ and $v_t\in T_t$ with (1)--(6) of the proof of \cref{lem:IV.AB-5}
    (p.~304); in particular the generic stalk frame of \cref{def:IV.AB-5-frame} exists at stage
    $s$. -/)
  (proof := /-- The paper's induction on $t$ (pp.~304--305). For $t=0$ (proved in Lean): $(T_0;z)$
    with $T_0$ the localization of $T$ at $\hat P_0\cap T$ (\cref{def:IV.AB-5-frame-localization};
    $z\in\hat P_0$ since $\hat x_0'\in\bar X_0$), $g_{jk}(0)=g_{jk}$, $g_{jki}(0)=g_{jki}$; (b) of
    (2) from (3), (4) and $\nu(\bar J(0)_{\hat x_0'})\ge b$ (\cref{lem:IV.AB-5-frame-order}), then
    (a) by Corollary~3 of Theorem~5, \S6, assertion~(c) (\cref{cor:III.thm5-3c}) in the complete
    ring $\hat S$ with $Q=\hat P_0$. Step (proved in Lean, modulo the finiteness of the integral closures of footnote~10 for the
    rings of the transforms, see the Remark below): $\hat Q_t\ni z_t$ and
    $\hat Q_t$ permissible for $\hat J_j(t)$ by Corollary~3 (a) with $Q=\hat Q_t$; a monoidal
    transform $R_1$ of $\hat S_t$ with center $\hat Q_t$, residually separable algebraic, of which
    $\hat S_{t+1}$ is a localization at a prime $Q_1$; the frame transform with
    $z_{t+1}=z_t/v_t$, $g_{jk}(t+1)=g_{jk}(t)/v_t^{\nu_{jk}}$; (2)(a) at $t+1$ by Theorem~5
    (\cref{thm:III.5}) for $R_1$ and then Corollary~3 (c) (\cref{cor:III.thm5-3c}) for the
    localization at $Q_1$.

    \textbf{Deviation from the paper (gap filled).} ``From the definition of $X'_s$ and the
    assumption that $\nu(\bar J(s)_{\hat x'})\ge b$ it is clear that we have
    $\nu(\bar J(t)_{\hat x_t'})\ge b$ for all $t$'' (p.~304) is proved in Lean from the fields of
    the removal family (\cref{lem:IV.3-construction-facts-generic}): off $\hat B_t$ the map
    $\bar f_t$ is a local isomorphism; on $\hat B_t-\mathrm{Bad}_t$, $\bar J(t)\subseteq
    \bar Q_t^b$. Likewise ``(1) for $t=0$ is clear'', ``(3) and (4) are clear for $t=0$'' and
    ``(b) of (2) follows from (3) and (4)'' are proved (\cref{def:IV.AB-5-frame-localization},
    \cref{lem:IV.AB-5-frame-order}).

    \textbf{Remark (incomplete citation in the paper).} The paper obtains (a) of (2) at
    $t+1$ ``by Corollary~3 of Theorem~5, \S6, Ch.~III, and by Theorem~5 \dots applied to a monoidal
    transform of $\hat S_t$ with center $\hat Q_t$ which is residually algebraic over $S_t$ and
    such that $S_{t+1}$ is a localization of the transform'' (p.~305). This is not an instance of Corollary~3 (b), which needs
    $P\supsetneq Q$ with $Q_1\cap R=Q$ (here $Q_1\cap\hat S_t$ is the maximal ideal, which is not
    contained in the center), but of Theorem~5 followed by Corollary~3 (c) for the localization at
    $Q_1$; the hypothesis of (c) (a prime $\hat Q$ of the completion of the ring of the
    transform with $\hat Q\hat R_{\hat Q}=Q_1\hat R_{\hat Q}$, or finiteness of the integral
    closures of footnote~10) is not verified in the paper for $t\ge1$, where the rings are not
    complete. It holds because these rings are localizations of algebras of finite type over the
    complete ring $\hat S$ (Nagata: the integral closure of a domain essentially of finite type over a
    complete noetherian local ring is finite over it); in Lean this is the helper
    \texttt{finiteIntegralClosureLocalizations\_monoidalTransform}, proved from
    \cref{lem:IV.AB-5-nagata-monoidal-transform} (the structure morphism $\hat X_s\to\hat X_0=
    \operatorname{Spec}\hat S$ is locally of finite type, and $\hat S$ is complete), whose only input
    is the finiteness result \cref{lem:IV.AB-5-nagata-finite}. -/)
  (proofUses := ["cor:III.thm5-3c", "cor:III.thm5-3a", "thm:III.5", "def:IV.AB-5-frame",
    "lem:IV.3-construction-facts-generic", "rem:III.9-3", "def:IV.AB-5-frame-localization",
    "lem:IV.AB-5-frame-order", "lem:IV.AB-5-nagata-monoidal-transform"])
  (latexEnv := "lemma")]
theorem RemovalFamily.exists_hasGenericStalkFrame_of_b_le_nu [Hironaka.HironakaCitedResults.{u}] {𝒮 : Frame hS}
    (R : 𝒮.RemovalFamily) (s : ℕ) (xb : (𝒮.xBar s).toScheme) (hxb : xb ∈ R.uBar s)
    (hν : (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal xb)) :
    𝒮.HasGenericStalkFrame s ((𝒮.xBar s).ι.base xb) := by
  induction s with
  | zero => exact hasGenericStalkFrame_zero 𝒮 xb hν
  | succ s ih =>
    have h1 := R.le_nu_jBar_of_le_nu_succ s xb hxb hν
    have h2 : (𝒮.fBar s).base xb ∈ R.uBar s := (R.mem_diff_of_mem_uBar_succ s xb hxb).1
    exact R.hasGenericStalkFrame_succ s xb hxb hν (ih _ h2 h1)

/-- p. 305: "(Observe that a suitably reordered subsystem of `(g_{01}(s), …, g_{0m}(s))` is a
standard base of `Ĵ_0(s)`.)": if the initial forms of elements `g_1, …, g_m` of an ideal `J` of a
regular local ring generate `gr_M(J, R)`, then a suitably reordered subsystem of `(g_1, …, g_m)` is a
standard base of `J` (Definition 3, p. 208): sort the `g_k` by the degrees of their initial forms and
discard every member whose initial form lies in the ideal generated by those of its predecessors
(`exists_isStandardBase_comp_of_prefix`).

\textbf{Deviation from the paper (gap filled).} The paper says only "Observe". -/
@[blueprint "lem:IV.AB-5-ii-standard-subsystem"
  (statement := /-- Let $R$ be a regular local ring, $J$ an ideal of $R$ and $g_1,\dots,g_m\in J$
    elements whose initial forms generate $\operatorname{gr}_{\mathfrak M}(J,R)$. Then a suitably
    reordered subsystem of $(g_1,\dots,g_m)$ is a standard base of $J$ (\cref{def:III.3}). (The
    parenthetical remark of p.~305: ``Observe that a suitably reordered subsystem of
    $(g_{01}(s),\dots,g_{0m}(s))$ is a standard base of $\hat J_0(s)$.'' Formalization note
    (encoding): ``a suitably reordered subsystem'' is a subfamily $(g_{\sigma(1)},\dots,
    g_{\sigma(m')})$ for an injective $\sigma$.) -/)
  (proof := /-- Sort the $g_k$ by the degrees of their (homogeneous) initial forms, so that the
    degrees are non-decreasing, and discard every member whose initial form lies in the ideal
    generated by the initial forms of its predecessors. The remaining initial forms still generate
    $\operatorname{gr}_{\mathfrak M}(J,R)$ (each discarded one lies in the ideal generated by the
    earlier ones, by induction), have non-decreasing degrees, and each lies outside the ideal
    generated by its predecessors, which is (i), (ii), (iii) of Lemma~1 (\cref{lem:III.1}).
    \textbf{Deviation from the paper (gap filled).} The paper says only ``Observe''. -/)
  (proofUses := ["def:III.3"])
  (latexEnv := "lemma")]
theorem _root_.Hironaka.exists_injective_isStandardBase_comp {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (J : Ideal R) {m : ℕ} (g : Fin m → R) (hgJ : ∀ k, g k ∈ J)
    (hgr : grIdeal (maximalIdeal R) J =
      Ideal.span (Set.range fun k => initialForm (maximalIdeal R) (g k))) :
    ∃ (m' : ℕ) (σ : Fin m' → Fin m), Function.Injective σ ∧ IsStandardBase R J (g ∘ σ) := by
  classical
  choose d hd using fun k => initialForm_mem_homogeneous_aux' (maximalIdeal R) (g k)
  have hgen : Ideal.span (Set.range fun l => initialForm (maximalIdeal R) ((g ∘ Tuple.sort d) l)) =
      grIdeal (maximalIdeal R) J := by
    rw [hgr]
    show Ideal.span (Set.range ((fun k => initialForm (maximalIdeal R) (g k)) ∘ Tuple.sort d)) = _
    rw [(Tuple.sort d).surjective.range_comp]
  obtain ⟨m', σ, -, hσ, -, hstd⟩ := exists_isStandardBase_comp_of_prefix J (g ∘ Tuple.sort d)
    (fun l => hgJ _) hgen (d ∘ Tuple.sort d) (fun l => hd _) (Tuple.monotone_sort d)
    (p := 0) (Nat.zero_le _) (fun l hl => absurd hl (Nat.not_lt_zero _))
  exact ⟨m', Tuple.sort d ∘ σ, (Tuple.sort d).injective.comp hσ.injective, hstd⟩

/-- The height of the stalk ideal of `V_j(s)` at `x'_s = c_s(x̂)` is at most that of the stalk ideal
of `Ĵ_j(s) = c_s⁻¹(V_j(s))` at `x̂` (`S_s → Ŝ_s` is flat, so heights of ideals do not drop under
the extension: going down).  The paper passes from `J_0(s)` to `Ĵ_0(s)` here without comment. -/
theorem height_stalkIdeal_sys_le_totalTransform [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (j : Fin (ℜ.β + 1)) (s : ℕ)
    (xh : 𝒮.tHat.X s) :
    ((T.sys ℜ s j).stalkIdeal ((𝒮.c s).base xh)).height ≤
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal xh).height := by
  have hflat : Flat (𝒮.c s) := 𝒮.toCompletion.flat_c (hS.ambient.2.1 x₀) s
  have : IsRegularLocalRing ((T.X s).presheaf.stalk ((𝒮.c s).base xh)) := hS.isNonsingular_X s _
  have : IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk xh) := 𝒮.instIsRegularLocalRingStalk s xh
  let _ : Algebra ((T.X s).presheaf.stalk ((𝒮.c s).base xh)) ((𝒮.tHat.X s).presheaf.stalk xh) :=
    ((𝒮.c s).stalkMap xh).hom.toAlgebra
  have : Module.Flat ((T.X s).presheaf.stalk ((𝒮.c s).base xh)) ((𝒮.tHat.X s).presheaf.stalk xh) :=
    Flat.stalkMap (𝒮.c s) xh
  rw [stalkIdeal_totalTransform]
  exact height_le_height_map_of_flat (B := (𝒮.tHat.X s).presheaf.stalk xh) _

/-- (ii) of Lemma (AB.5) from the frame (p. 305), along the printed argument.

"If `W` is singular at `x_0`, then the number of those indices `k` with `ν_{0k} = 1` is less than
codimension of `W` in `X(= X_0 = X'_0)` at `x_0`.  Here, by the codimension we mean the minimum of the
codimensions of irreducible components of `W` in `X` at `x_0`.  It is clear that the codimension of
`W(s)` in `W'_s` [sic; `X'_s` is meant] at `x'_s` is at least equal to that of `W` in `X` at `x_0`.
Therefore, in view of (a) and (b) of (2) for `Ĵ_0(s)` and `g_{0k}(s)` `(1 ≤ k ≤ m_0)`, we see that
`W(s)` is singular at the point `x' = x'_s`.  (Observe that a suitably reordered subsystem of
`(g_{01}(s), …, g_{0m}(s))` is a standard base of `Ĵ_0(s)`.)" (p. 305)

The Lean proof follows the sentences, with the local rings `S = O_{X,x_0}`, `S_s = O_{X_s,x'_s}`
(the heights of `J_0`, `J_0(s)` are the codimensions of the paper) and `Ŝ_s`:
* the `ν_{0k} = ν^{(k)}(J_0)` are the orders of a standard base of `J_0` in `S` (Lemma 1) and `S/J_0` is
  not regular (`W` singular at `x_0`), so the number of `k` with `ν_{0k} = 1` is `< ht J_0`
  (`card_order_one_lt_height_of_not_isRegularLocalRing_quotient`);
* "It is clear that the codimension of `W(s)` ... is at least equal to that of `W` in `X` at `x_0`":
  `ht J_0` at `x_0` is at most `ht J_0` at the generization `x'_0 = g_s(x'_s)`
  (`height_stalkIdeal_le_height_stalkIdeal_fromSpecStalk`), which is at most `ht J_0(s)` at `x'_s`
  (`Standing.height_stalkIdeal_sys_le`: one monoidal transformation at a time,
  `MonoidalTransformation.height_stalkIdeal_le_strictTransform`);
* "Therefore, in view of (a) and (b) of (2)": `ht J_0(s) ≤ ht Ĵ_0(s)` (`S_s → Ŝ_s` is flat,
  `height_stalkIdeal_sys_le_totalTransform`); the number of `k` with `ν_{0k} = 1` is the number of
  `g_{0k}(s)` of order one ((b) of (2): `ν_{0k}` is the order of `g_{0k}(s)` and the count does not
  increase from `t = 0` to `t = s`), and the initial forms generate `gr(Ĵ_0(s))` ((a) of (2)); "(Observe
  that a suitably reordered subsystem of `(g_{01}(s), …, g_{0m}(s))` is a standard base of
  `Ĵ_0(s)`.)": such a subsystem is extracted (`exists_injective_isStandardBase_comp`), it has at most
  as many members of order one as the whole system, and the count criterion
  (`not_isRegularLocalRing_quotient_of_card_order_one_lt_height`) applied to it gives that
  `Ŝ_s/Ĵ_0(s)` is not regular;
* so `S_s/J_0(s)` is not regular: regularity of `S_s/J_0(s)` would give that of `Ŝ_s/Ĵ_0(s)`
  (class 𝔅, `isRegularLocalRing_quotient_stalk_totalTransform_of_isPullback_completion`).

\textbf{Gaps filled.} "It is clear that the codimension of `W(s)` ... at least equal" (proved, one
step `MonoidalTransformation.height_stalkIdeal_le_strictTransform`, iterated; with the comparison
between `x_0` and its generization `x'_0`; the paper prints `W'_s` for `X'_s`); the passage from
`S_s/J_0(s)` and `ht J_0(s)` to `Ŝ_s/Ĵ_0(s)` and `ht Ĵ_0(s)`, which the paper makes without
comment (going down for the flat map `S_s → Ŝ_s`, and class 𝔅).  The parenthetical "(Observe that a
suitably reordered subsystem ... is a standard base of `Ĵ_0(s)`.)" is proved
(`exists_injective_isStandardBase_comp`) and used as printed, to apply the count criterion to a
standard base of `Ĵ_0(s)`. -/
theorem RemovalFamily.not_isSimpleAt_strictTransform_of_b_le_nu [Hironaka.HironakaCitedResults.{u}] {𝒮 : Frame hS}
    (R : 𝒮.RemovalFamily) (s : ℕ) (xb : (𝒮.xBar s).toScheme) (hxb : xb ∈ R.uBar s)
    (hν : (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal xb))
    (h : 𝒮.HasGenericStalkFrame s ((𝒮.xBar s).ι.base xb)) :
    ¬ ℜ.W.IsSimpleAt x₀ →
      ¬ ((T.pre s).strictTransform ℜ.W).IsSimpleAt ((𝒮.cBar s).base xb) := by
  classical
  intro hsing hsimple
  have hx0 := hS.ambient.2.1 x₀
  have hregS : IsRegularLocalRing (X.presheaf.stalk x₀) := hx0
  have hW0 : x₀ ∈ ℜ.W.pts := by
    have h := hS.mem_wStar
    cases r with
    | closed F => exact h.1
    | opn U => exact h.1
  have hnreg : ¬ IsRegularLocalRing (X.presheaf.stalk x₀ ⧸ ℜ.W.stalkIdeal x₀) :=
    fun hr => hsing ⟨hW0, hr⟩
  -- "If `W` is singular at `x_0`, then the number of those indices `k` with `ν_{0k} = 1` is less
  -- than codimension of `W` in `X` at `x_0`" (a standard base of `J_0` in `S`)
  have hJ0ne : ℜ.W.stalkIdeal x₀ ≠ ⊤ := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hW0
  obtain ⟨mS, gS, hstdS⟩ := exists_isStandardBase (ℜ.W.stalkIdeal x₀)
  have hK1 := card_order_one_lt_height_of_not_isRegularLocalRing_quotient hJ0ne gS hstdS hnreg
  -- the frame data at stage `s`, for the member `W(s)` (the last index of the system)
  set xh : 𝒮.tHat.X s := (𝒮.xBar s).ι.base xb with hxh
  have hmem_s : (𝒮.c s).base xh ∈ (T.sys ℜ s (Fin.last ℜ.β)).pts :=
    h.mem_pts_sys_last hW0
  have hJs_ne : (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal xh
      ≠ ⊤ := by
    rw [← Subscheme.mem_pts_iff_stalkIdeal_ne_top, Subscheme.pts_totalTransform_eq_preimage]
    exact hmem_s
  obtain ⟨F, z, m', ν', g', co', hr, hz, hX, hgJ, hgr, hord, hν0', hb, hsh, hJ⟩ := h
  -- the orders `ν_{0k} = 1`: the counts at stages `s` and `0`
  have hordS : ∀ k, (Ideal.ordElem (maximalIdeal ((𝒮.tHat.X s).presheaf.stalk xh))
      (g' (Fin.last ℜ.β) k) = 1) ↔
      nuI (X.presheaf.stalk x₀) (ℜ.W.stalkIdeal x₀) (k : ℕ).succPNat = 1 := by
    intro k
    rw [hord (Fin.last ℜ.β) k]
    have := hν0' (Fin.last ℜ.β) k
    simp only [datumSystem, Fin.snoc_last] at this
    rw [← this]
  have hbigS : ∀ k : ℕ, nuI (X.presheaf.stalk x₀) (ℜ.W.stalkIdeal x₀) k.succPNat = 1 →
      k < mS := by
    intro k hk
    by_contra hlt
    push Not at hlt
    obtain ⟨-, hbig⟩ := nuI_eq_of_hasLemma1Properties (X.presheaf.stalk x₀) _ _ hstdS.2
    have h2 := hbig k.succPNat (by simpa [Nat.succPNat] using Nat.lt_succ_of_le hlt)
    rw [hk] at h2
    exact absurd h2 (by simp)
  -- "the number of those indices `k` with `ν_{0k} = 1`" does not increase from `t = 0` to `t = s`
  have hcard : (Finset.univ.filter fun k : Fin (m' (Fin.last ℜ.β)) =>
      Ideal.ordElem (maximalIdeal ((𝒮.tHat.X s).presheaf.stalk xh))
        (g' (Fin.last ℜ.β) k) = 1).card ≤
      (Finset.univ.filter fun k : Fin mS => Ideal.ordElem (maximalIdeal (X.presheaf.stalk x₀))
        (gS k) = 1).card := by
    rw [← Finset.card_map Fin.valEmbedding, ← Finset.card_map (Fin.valEmbedding (n := mS))]
    refine Finset.card_le_card ?_
    intro n hn
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply] at hn ⊢
    obtain ⟨k, hk, rfl⟩ := hn
    have hk' := (hordS k).mp hk
    refine ⟨⟨k, hbigS k hk'⟩, ?_, rfl⟩
    rw [ordElem_eq_nuI_of_isStandardBase _ _ hstdS, hk']
  -- `x'_0 = c_0(x̂'_0)` and the pull-back square
  have : IsAlgebraicScheme X := hS.ambient.1
  have : IsHironakaBase (X.presheaf.stalk x₀) := isHironakaBase_stalk X x₀
  have : IsLocallyNoetherian X := (IsAlgebraicScheme.isNoetherian X).toIsLocallyNoetherian
  have hpr : IsProper (T.pre s).composite := Hironaka.MonoidalSuccession.isProper_composite _
  have hH : IsPullback (𝒮.c s) (𝒮.tHat.pre s).composite (T.pre s).composite
      (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))) ≫
        X.fromSpecStalk x₀) := by
    have := 𝒮.isPullback s
    rw [𝒮.c_zero] at this
    exact this
  -- heights, in the local rings of the schemes `X`, `X_s` and then of `X̂_s`:
  -- `ht J_0 ≤ ht J_0(x'_0) ≤ ht J_0(s) ≤ ht Ĵ_0(s)`
  have hht : (ℜ.W.stalkIdeal x₀).height ≤
      ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal xh).height := by
    let Q0 : Spec (X.presheaf.stalk x₀) :=
      (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀)))).base
        ((𝒮.tHat.pre s).composite.base xh)
    have hpt : (T.pre s).composite.base ((𝒮.c s).base xh) = X.fromSpecStalk x₀ Q0 := by
      have := congrArg (fun φ => φ.base xh) hH.w
      exact this
    have hsys0 : T.sys ℜ 0 (Fin.last ℜ.β) = ℜ.W := by
      show (T.pre 0).strictTransform (datumSystem ℜ (Fin.last ℜ.β)) = ℜ.W
      simp only [datumSystem, Fin.snoc_last]
      rfl
    have H1 := height_stalkIdeal_le_height_stalkIdeal_fromSpecStalk ℜ.W x₀ Q0
    have H2 := hS.height_stalkIdeal_sys_le (Fin.last ℜ.β) s ((𝒮.c s).base xh)
    have H3 := 𝒮.height_stalkIdeal_sys_le_totalTransform (Fin.last ℜ.β) s xh
    rw [hpt, hsys0] at H2
    exact H1.trans (H2.trans H3)
  -- K2: `Ŝ_s/Ĵ_0(s)` is singular
  have hhat : ¬ IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk xh ⧸
      (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal xh) := by
    -- "(Observe that a suitably reordered subsystem of `(g_{01}(s), …, g_{0m}(s))` is a standard
    -- base of `Ĵ_0(s)`.)": the count criterion is applied to that standard base
    obtain ⟨mm, σ, hσ, hstd⟩ := exists_injective_isStandardBase_comp _ (g' (Fin.last ℜ.β))
      (hgJ (Fin.last ℜ.β)) (hgr (Fin.last ℜ.β))
    have hcard'' : (Finset.univ.filter fun k : Fin mm =>
        Ideal.ordElem (maximalIdeal ((𝒮.tHat.X s).presheaf.stalk xh))
          (g' (Fin.last ℜ.β) (σ k)) = 1).card ≤
        (Finset.univ.filter fun k : Fin (m' (Fin.last ℜ.β)) =>
        Ideal.ordElem (maximalIdeal ((𝒮.tHat.X s).presheaf.stalk xh))
          (g' (Fin.last ℜ.β) k) = 1).card :=
      Finset.card_le_card_of_injOn σ (fun k hk => by simpa using hk) hσ.injOn
    refine not_isRegularLocalRing_quotient_of_card_order_one_lt_height hJs_ne
      (g' (Fin.last ℜ.β) ∘ σ) hstd.1 hstd.2.2.2.1 ?_
    exact lt_of_le_of_lt (Nat.cast_le.mpr (hcard''.trans hcard)) (lt_of_lt_of_le hK1 hht)
  -- K5: class 𝔅, (ii)
  have hsysW : T.sys ℜ s (Fin.last ℜ.β) = (T.pre s).strictTransform ℜ.W := by
    show (T.pre s).strictTransform (datumSystem ℜ (Fin.last ℜ.β)) = _
    simp only [datumSystem, Fin.snoc_last]
  rw [hsysW] at hhat
  exact hhat (isRegularLocalRing_quotient_stalk_totalTransform_of_isPullback_completion x₀
    (T.pre s).composite (𝒮.c s) (𝒮.tHat.pre s).composite hH ((T.pre s).strictTransform ℜ.W) xh
    hsimple.2)

/-- Normal flatness of `P` modulo `J` is invariant under a ring isomorphism `B ≃+* A` carrying
`J_B, P_B` to `J_A, P_A`. -/
theorem isNormallyFlatAlongIdeal_mod_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : B ≃+* A) (JB PB : Ideal B) (JA PA : Ideal A) (hJ : JA = JB.map e) (hP : PA = PB.map e)
    (h : IsNormallyFlatAlongIdeal (PA.map (Ideal.Quotient.mk JA))) :
    IsNormallyFlatAlongIdeal (PB.map (Ideal.Quotient.mk JB)) := by
  subst hJ hP
  let e2 : B ⧸ JB ≃+* A ⧸ JB.map e := Ideal.quotientEquiv JB (JB.map e) e rfl
  refine isNormallyFlatAlongIdeal_of_ringEquiv e2.symm _ _ ?_ h
  have key : ((e2.symm : A ⧸ JB.map e →+* B ⧸ JB).comp
      (Ideal.Quotient.mk (JB.map e))).comp (e : B →+* A) = Ideal.Quotient.mk JB := by
    ext a
    exact (RingEquiv.symm_apply_eq e2).mpr rfl
  have hc : Ideal.map e PB = Ideal.map (e : B →+* A) PB := Ideal.map_coe e PB
  rw [Ideal.map_map, hc, Ideal.map_map]
  have h2 : Ideal.map (((e2.symm : A ⧸ JB.map e →+* B ⧸ JB).comp
      (Ideal.Quotient.mk (JB.map e))).comp (e : B →+* A)) PB = Ideal.map (Ideal.Quotient.mk JB) PB := by
    rw [key]
  exact h2

/-- The stalk of `c_0⁻¹(V)` at a point of `X̂_0 = Spec Ŝ`, through `Spec.stalkIso`. -/
theorem stalkIdeal_totalTransform_c0_stalkIso {X : Scheme.{u}} (x₀ : X) (V : Subscheme X)
    (P₀ : xHat0 X x₀) :
    (Subscheme.totalTransform (c0 X x₀) V).stalkIdeal P₀ =
      ((((V.stalkIdeal x₀).map (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))).map
        (algebraMap (Shat X x₀)
          (Localization.AtPrime (show PrimeSpectrum (Shat X x₀) from P₀).asIdeal))).map
        (Spec.stalkIso (CommRingCat.of (Shat X x₀)) (show PrimeSpectrum (Shat X x₀) from P₀)).inv.hom) :=
  stalkIdeal_comap_specMap_fromSpecStalk V x₀ (CommRingCat.of (Shat X x₀))
    (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))) P₀

/-- Class 𝔅 at the closed point: if `S/D_{x_0}` is regular then so is `Ŝ/D_{x_0}Ŝ` (`(K5)` for
`Y = X`, `c = c_0`). -/
theorem isRegularLocalRing_shat_quotient_map_of_isRegularLocalRing_quotient [Hironaka.HironakaCitedResults.{u}]
    {X : Scheme.{u}} [IsAlgebraicScheme X] (x₀ : X) (hx : X.IsSimpleAt x₀) (D : Subscheme X)
    (hD : IsRegularLocalRing (X.presheaf.stalk x₀ ⧸ D.stalkIdeal x₀)) :
    haveI : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
    IsRegularLocalRing (Shat X x₀ ⧸ (D.stalkIdeal x₀).map
      (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))) := by
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  have : IsHironakaBase (X.presheaf.stalk x₀) := isHironakaBase_stalk X x₀
  have hH : IsPullback (c0 X x₀) (𝟙 (xHat0 X x₀)) (𝟙 X) (Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))) ≫ X.fromSpecStalk x₀) :=
    IsPullback.of_vert_isIso ⟨by simp [c0]⟩
  have hreg : IsRegularLocalRing (X.presheaf.stalk ((c0 X x₀).base (xhat0 X x₀ hx)) ⧸
      D.stalkIdeal ((c0 X x₀).base (xhat0 X x₀ hx))) := by
    rw [c0_apply_xhat0]; exact hD
  have h := isRegularLocalRing_quotient_stalk_totalTransform_of_isPullback_completion x₀
    (𝟙 X) (c0 X x₀) (𝟙 (xHat0 X x₀)) hH D (xhat0 X x₀ hx) hreg
  rw [stalkIdeal_totalTransform_c0_xhat0 hx D] at h
  let κ : Shat X x₀ ≃+* (xHat0 X x₀).presheaf.stalk (xhat0 X x₀ hx) :=
    (stalkClosedPointIso (CommRingCat.of (Shat X x₀))).symm.commRingCatIsoToRingEquiv
  have e2 := Ideal.quotientEquiv ((D.stalkIdeal x₀).map
    (algebraMap (X.presheaf.stalk x₀) (Shat X x₀)))
    (((D.stalkIdeal x₀).map (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))).map
      (stalkClosedPointIso (CommRingCat.of (Shat X x₀))).inv.hom) κ rfl
  have h' : IsRegularLocalRing ((Spec (CommRingCat.of (Shat X x₀))).presheaf.stalk
      (closedPoint (Shat X x₀)) ⧸ ((D.stalkIdeal x₀).map
        (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))).map
          (stalkClosedPointIso (CommRingCat.of (Shat X x₀))).inv.hom) := h
  exact IsRegularLocalRing.of_ringEquiv e2.symm

/-- "To prove (iii), we assume that `x_0` is a simple point of `W`.  It follows that `x̂'_t` is a
simple point of `c_t⁻¹(W(t))`, `0 ≦ t ≦ s`" (p. 305), the case `t = 0`: if `x_0` is a simple
point of `W` then `Ŝ/Ĵ_0` is regular (class 𝔅, `isRegularLocalRing_shat_quotient_map_of_isRegularLocalRing_quotient`),
and the local ring of `c_0⁻¹(W)` at a point `ŷ` of `X̂_0 = Spec Ŝ` over which it is non-empty is the
localization of `Ŝ/Ĵ_0` at the prime `ŷ` (Serre: a localization of a regular local ring is regular).

\textbf{Deviation from the paper (gap filled).} The paper's "It follows that" is proved here:
regularity of `Ŝ/Ĵ_0` (class 𝔅) and Serre's theorem (footnote 9, p. 243, a cited leaf) for the
generization `x̂'_0`; the steps `t → t + 1` are `isRegularLocalRing_quotient_sys_last_succ`. -/
theorem isRegularLocalRing_quotient_sys_last_zero [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (hsimple : ℜ.W.IsSimpleAt x₀)
    (y : 𝒮.tHat.X 0)
    (hne : (Subscheme.totalTransform (𝒮.c 0) (T.sys ℜ 0 (Fin.last ℜ.β))).stalkIdeal y ≠ ⊤) :
    IsRegularLocalRing ((𝒮.tHat.X 0).presheaf.stalk y ⧸
      (Subscheme.totalTransform (𝒮.c 0) (T.sys ℜ 0 (Fin.last ℜ.β))).stalkIdeal y) := by
  classical
  have hx0 := hS.ambient.2.1 x₀
  have hregS : IsRegularLocalRing (X.presheaf.stalk x₀) := hx0
  have hregHat := 𝒮.regShat
  let Pr : PrimeSpectrum (Shat X x₀) := y
  let Pi : Ideal (Shat X x₀) := Pr.asIdeal
  have : Pi.IsPrime := Pr.isPrime
  let α := algebraMap (X.presheaf.stalk x₀) (Shat X x₀)
  have hhaveAlg : IsAlgebraicScheme X := hS.ambient.1
  let e : Localization.AtPrime Pi ≃+* (𝒮.tHat.X 0).presheaf.stalk y :=
    (Spec.stalkIso (CommRingCat.of (Shat X x₀)) Pr).symm.commRingCatIsoToRingEquiv
  have hsysW : T.sys ℜ 0 (Fin.last ℜ.β) = ℜ.W := by
    show (T.pre 0).strictTransform (datumSystem ℜ (Fin.last ℜ.β)) = ℜ.W
    simp only [datumSystem, Fin.snoc_last]
    rfl
  have hJW : (Subscheme.totalTransform (𝒮.c 0) (T.sys ℜ 0 (Fin.last ℜ.β))).stalkIdeal y =
      ((((ℜ.W.stalkIdeal x₀).map α).map (algebraMap (Shat X x₀) (Localization.AtPrime Pi))).map e) := by
    rw [𝒮.c_zero, hsysW]
    exact stalkIdeal_totalTransform_c0_stalkIso x₀ ℜ.W y
  have hJWP : (ℜ.W.stalkIdeal x₀).map α ≤ Pi := by
    by_contra hnle
    obtain ⟨a, haJ, haP⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
    apply hne
    rw [hJW]
    have hunit : IsUnit (algebraMap (Shat X x₀) (Localization.AtPrime Pi) a) :=
      IsLocalization.map_units _ (⟨a, haP⟩ : Pi.primeCompl)
    have : ((ℜ.W.stalkIdeal x₀).map α).map (algebraMap (Shat X x₀) (Localization.AtPrime Pi)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ haJ) hunit
    rw [this, Ideal.map_top]
  have hregW : IsRegularLocalRing (Shat X x₀ ⧸ (ℜ.W.stalkIdeal x₀).map α) :=
    isRegularLocalRing_shat_quotient_map_of_isRegularLocalRing_quotient x₀ hx0 ℜ.W hsimple.2
  obtain ⟨e2⟩ := nonempty_localization_quotient_equiv ((ℜ.W.stalkIdeal x₀).map α) Pi hJWP
  have : (Ideal.map (Ideal.Quotient.mk ((ℜ.W.stalkIdeal x₀).map α)) Pi).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]; exact hJWP)
  have hreg := isRegularLocalRing_localization_of_isRegularLocalRing
    (Shat X x₀ ⧸ (ℜ.W.stalkIdeal x₀).map α)
    (Ideal.map (Ideal.Quotient.mk ((ℜ.W.stalkIdeal x₀).map α)) Pi)
  refine IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime
      (Ideal.map (Ideal.Quotient.mk ((ℜ.W.stalkIdeal x₀).map α)) Pi)) ?_
  exact e2.symm.trans (Ideal.quotientEquiv _ _ e hJW)

/-- `Ŝ_s/Ĵ_0(s)` is a regular local ring at the point `ŷ` of `X̂_s` ("`ŷ` is a simple point of
`c_s⁻¹(W(s))`", p. 305). -/
def IsRegularSysLast (𝒮 : Frame hS) (s : ℕ) (y : 𝒮.tHat.X s) : Prop :=
  IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk y ⧸
    (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal y)

/-- `Ĵ_0(s)` is a permissible center for `Ĵ_j(s)` in `Ŝ_s` at the point `ŷ` of `X̂_s`
(`V_j(s)` is indexed by `j.castSucc`, `W(s)` by `Fin.last`). -/
def IsPermissibleSys (𝒮 : Frame hS) (s : ℕ) (y : 𝒮.tHat.X s) (j : Fin ℜ.β) : Prop :=
  IsPermissibleCenter ((𝒮.tHat.X s).presheaf.stalk y)
    ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j.castSucc)).stalkIdeal y)
    ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal y)

/-- Off the center `B̂_s`, `f̂_s` is a local isomorphism and `Ĵ_0(s+1)` is a permissible center
for `Ĵ_j(s+1)` at `ŷ` iff `Ĵ_0(s)` is one for `Ĵ_j(s)` at `f̂_s(ŷ)` ("trivial monoidal transforms
for which the centers `Q_t` are unit ideals", p. 300). -/
theorem isPermissibleSys_succ_iff_of_notMem [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ) (xh : 𝒮.tHat.X (s + 1))
    (hmem : (𝒮.tHat.f s).base xh ∉ (𝒮.tHat.B s).pts) (j : Fin ℜ.β) :
    𝒮.IsPermissibleSys (s + 1) xh j ↔ 𝒮.IsPermissibleSys s ((𝒮.tHat.f s).base xh) j := by
  unfold IsPermissibleSys
  rw [𝒮.totalTransform_c_sys_succ s j.castSucc, 𝒮.totalTransform_c_sys_succ s (Fin.last ℜ.β)]
  have h1 : IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk ((𝒮.tHat.f s).base xh)) :=
    Frame.instIsRegularLocalRingStalk 𝒮 s _
  have h2 : IsRegularLocalRing ((𝒮.tHat.monoidalTransformation s).X'.presheaf.stalk xh) :=
    Frame.instIsRegularLocalRingStalk 𝒮 (s + 1) xh
  exact isPermissibleCenter_stalkIdeal_strictTransform_iff_of_notMem
    (𝒮.tHat.monoidalTransformation s) _ _ xh hmem

/-- The point `x̂'_s` of `X̄_s` over which the frames live lies on `c_s⁻¹(W(s))` (this is (i) of
Lemma (AB.5)): `Ĵ_0(s) ≠ Ŝ_s`. -/
theorem RemovalFamily.stalkIdeal_totalTransform_sys_last_ne_top [Hironaka.HironakaCitedResults.{u}] {𝒮 : Frame hS}
    (R : 𝒮.RemovalFamily) (hW0 : x₀ ∈ ℜ.W.pts) (s : ℕ) (xb : (𝒮.xBar s).toScheme)
    (hxb : xb ∈ R.uBar s) (hν : (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal xb)) :
    (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s (Fin.last ℜ.β))).stalkIdeal
      ((𝒮.xBar s).ι.base xb) ≠ ⊤ := by
  have hgen := R.exists_hasGenericStalkFrame_of_b_le_nu s xb hxb hν
  have := hgen.mem_pts_sys_last hW0
  rw [← Subscheme.mem_pts_iff_stalkIdeal_ne_top, Subscheme.pts_totalTransform_eq_preimage]
  exact this

/-- `J_0(t)` is a permissible center for `J_j(t)` in `S_t`, the local ring of `X_t` at
`x'_t = c_t(x̂)` (`V_j(t)` is indexed by `j.castSucc`, `W(t)` by `Fin.last`): the statement of p. 305
before the passage to `Ŝ_t`. -/
def IsPermissibleSysS (𝒮 : Frame hS) (t : ℕ) (y : 𝒮.tHat.X t) (j : Fin ℜ.β) : Prop :=
  IsPermissibleCenter ((T.X t).presheaf.stalk ((𝒮.c t).base y))
    ((T.sys ℜ t j.castSucc).stalkIdeal ((𝒮.c t).base y))
    ((T.sys ℜ t (Fin.last ℜ.β)).stalkIdeal ((𝒮.c t).base y))

/-- The stalk map `S_t → Ŝ_t` at `x̂` is flat and local. -/
theorem flat_isLocalHom_stalkMap_c (𝒮 : Frame hS) (t : ℕ) (y : 𝒮.tHat.X t) :
    letI : Algebra ((T.X t).presheaf.stalk ((𝒮.c t).base y)) ((𝒮.tHat.X t).presheaf.stalk y) :=
      ((𝒮.c t).stalkMap y).hom.toAlgebra
    Module.Flat ((T.X t).presheaf.stalk ((𝒮.c t).base y)) ((𝒮.tHat.X t).presheaf.stalk y) ∧
      IsLocalHom (algebraMap ((T.X t).presheaf.stalk ((𝒮.c t).base y))
        ((𝒮.tHat.X t).presheaf.stalk y)) := by
  have hflat : Flat (𝒮.c t) := 𝒮.toCompletion.flat_c (hS.ambient.2.1 x₀) t
  exact ⟨Flat.stalkMap (𝒮.c t) y, inferInstanceAs (IsLocalHom ((𝒮.c t).stalkMap y).hom)⟩

/-- The first half of "Since `Ŝ_{t+1}` (resp. `Ŝ_t`) is faithfully flat over `S_{t+1}` (resp.
`S_t`), it follows by Lemma 9 of §3, Ch. II ..." (p. 305), upwards: if `J_0(t)` is a permissible
center for `J_j(t)` in `S_t` and `Ŝ_t/Ĵ_0(t)` is regular, then `Ĵ_0(t)` is a permissible center for
`Ĵ_j(t)` in `Ŝ_t`. -/
theorem isPermissibleSys_of_isPermissibleSysS [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (t : ℕ) (y : 𝒮.tHat.X t)
    (j : Fin ℜ.β) (hreg : 𝒮.IsRegularSysLast t y) (hP : 𝒮.IsPermissibleSysS t y j) :
    𝒮.IsPermissibleSys t y j := by
  have : IsRegularLocalRing ((T.X t).presheaf.stalk ((𝒮.c t).base y)) := hS.isNonsingular_X t _
  have : IsRegularLocalRing ((𝒮.tHat.X t).presheaf.stalk y) := 𝒮.instIsRegularLocalRingStalk t y
  let _ : Algebra ((T.X t).presheaf.stalk ((𝒮.c t).base y)) ((𝒮.tHat.X t).presheaf.stalk y) :=
    ((𝒮.c t).stalkMap y).hom.toAlgebra
  obtain ⟨hfl, hloc⟩ := 𝒮.flat_isLocalHom_stalkMap_c t y
  unfold IsPermissibleSys
  rw [stalkIdeal_totalTransform, stalkIdeal_totalTransform]
  unfold IsRegularSysLast at hreg
  rw [stalkIdeal_totalTransform] at hreg
  exact isPermissibleCenter_map_of_isPermissibleCenter_of_isRegularLocalRing_quotient hP hreg

/-- The second half, downwards: if `Ĵ_0(t)` is a permissible center for `Ĵ_j(t)` in `Ŝ_t` and the
point `x'_t` lies on `W(t)`, then `J_0(t)` is a permissible center for `J_j(t)` in `S_t` (Lemma 9
of Ch. II §3: faithful flatness of `S_t → Ŝ_t`; the regularity of `S_t/J_0(t)` descends along the
flat local homomorphism). -/
theorem isPermissibleSysS_of_isPermissibleSys [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (t : ℕ) (y : 𝒮.tHat.X t)
    (j : Fin ℜ.β) (hne : (T.sys ℜ t (Fin.last ℜ.β)).stalkIdeal ((𝒮.c t).base y) ≠ ⊤)
    (hP : 𝒮.IsPermissibleSys t y j) : 𝒮.IsPermissibleSysS t y j := by
  have : IsRegularLocalRing ((T.X t).presheaf.stalk ((𝒮.c t).base y)) := hS.isNonsingular_X t _
  have : IsRegularLocalRing ((𝒮.tHat.X t).presheaf.stalk y) := 𝒮.instIsRegularLocalRingStalk t y
  let _ : Algebra ((T.X t).presheaf.stalk ((𝒮.c t).base y)) ((𝒮.tHat.X t).presheaf.stalk y) :=
    ((𝒮.c t).stalkMap y).hom.toAlgebra
  obtain ⟨hfl, hloc⟩ := 𝒮.flat_isLocalHom_stalkMap_c t y
  unfold IsPermissibleSys at hP
  rw [stalkIdeal_totalTransform, stalkIdeal_totalTransform] at hP
  exact isPermissibleCenter_of_isPermissibleCenter_map_of_flat hne hP

/-- From the regularity of `Ŝ_t/Ĵ_0(t)` ("`x̂'_t` is a simple point of `c_t⁻¹(W(t))`") and the normal
flatness of `V_j(t)` along `W(t)` at `x'_t`, `J_0(t)` is a permissible center for `J_j(t)` in `S_t`:
the stage `t = s` of the descent of (iii) (p. 305). -/
theorem isPermissibleSysS_of_isNormallyFlatAlongAt' [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (t : ℕ) (y : 𝒮.tHat.X t)
    (j : Fin ℜ.β) (hreg : 𝒮.IsRegularSysLast t y)
    (hNF : Subscheme.IsNormallyFlatAlongAt' (T.sys ℜ t j.castSucc) (T.sys ℜ t (Fin.last ℜ.β))
      ((𝒮.c t).base y)) : 𝒮.IsPermissibleSysS t y j := by
  have hWV : (T.sys ℜ t (Fin.last ℜ.β)).IsContainedIn (T.sys ℜ t j.castSucc) := by
    have h := MonoidalSuccession.isContainedIn_strictTransform (T.pre t) (hS.isDatum.2.2.2.2 j)
    have hV : T.sys ℜ t j.castSucc = (T.pre t).strictTransform (ℜ.V j) := by
      show (T.pre t).strictTransform (datumSystem ℜ j.castSucc) = _
      simp only [datumSystem, Fin.snoc_castSucc]
    have hW : T.sys ℜ t (Fin.last ℜ.β) = (T.pre t).strictTransform ℜ.W := by
      show (T.pre t).strictTransform (datumSystem ℜ (Fin.last ℜ.β)) = _
      simp only [datumSystem, Fin.snoc_last]
    rw [hV, hW]
    exact h
  have : IsRegularLocalRing ((T.X t).presheaf.stalk ((𝒮.c t).base y)) := hS.isNonsingular_X t _
  have : IsRegularLocalRing ((𝒮.tHat.X t).presheaf.stalk y) := 𝒮.instIsRegularLocalRingStalk t y
  let _ : Algebra ((T.X t).presheaf.stalk ((𝒮.c t).base y)) ((𝒮.tHat.X t).presheaf.stalk y) :=
    ((𝒮.c t).stalkMap y).hom.toAlgebra
  obtain ⟨hfl, hloc⟩ := 𝒮.flat_isLocalHom_stalkMap_c t y
  unfold IsRegularSysLast at hreg
  rw [stalkIdeal_totalTransform] at hreg
  have hregS := isRegularLocalRing_quotient_of_isRegularLocalRing_quotient_map_of_flat _ hreg
  have hdom : IsDomain ((T.X t).presheaf.stalk ((𝒮.c t).base y) ⧸
      (T.sys ℜ t (Fin.last ℜ.β)).stalkIdeal ((𝒮.c t).base y)) :=
    Transforms.isDomain_of_isRegularLocalRing _
  exact Or.inr ⟨(Ideal.Quotient.isDomain_iff_prime _).mp hdom,
    Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hWV _, hregS,
    ((Subscheme.isNormallyFlatAlongAt'_iff _ _ hWV _).mp hNF).2⟩

/-- `Ŝ_t/Ĵ_0(t)` regular implies that `x'_t` lies on `W(t)`: `J_0(t) ≠ S_t`. -/
theorem IsRegularSysLast.stalkIdeal_ne_top {𝒮 : Frame hS} {t : ℕ} {y : 𝒮.tHat.X t}
    (hreg : 𝒮.IsRegularSysLast t y) :
    (T.sys ℜ t (Fin.last ℜ.β)).stalkIdeal ((𝒮.c t).base y) ≠ ⊤ := by
  intro h
  have hreg' : IsRegularLocalRing ((𝒮.tHat.X t).presheaf.stalk y ⧸
    (Subscheme.totalTransform (𝒮.c t) (T.sys ℜ t (Fin.last ℜ.β))).stalkIdeal y) := hreg
  have hne : (Subscheme.totalTransform (𝒮.c t) (T.sys ℜ t (Fin.last ℜ.β))).stalkIdeal y ≠ ⊤ :=
    Ideal.Quotient.nontrivial_iff.mp inferInstance
  rw [stalkIdeal_totalTransform, h, Ideal.map_top] at hne
  exact hne rfl

/-- **The backward induction of the proof of (iii)** (pp. 305--306), through the rings `S_t`: for
`x̂'_s` the image of a point of `Ū_s` with `ν(J̄(s)_{x̂'}) ≥ b`, and `x_0` a simple point of `W`, the
ring `Ŝ_s/Ĵ_0(s)` is regular and, if `J_0(s)` is a permissible center for `J_j(s)` in `S_s`, then so
is `J_0(0)` for `J_j(0)` in `S_0` at a point `x̂'_0` of `X̄_0` with `ν(J̄(0)_{x̂'_0}) ≥ b`.

The step `t + 1 → t`, in the order of p. 306: "Therefore, in view of (a) and (b) of (2), we can
conclude by Corollary 1 of Proposition 2, § 8, Ch. III that, if `Ĵ_0(t+1)` (which is a prime ideal in
`Ŝ_{t+1}` such that `Ŝ_{t+1}/Ĵ_0(t+1)` is regular) is a permissible center for `Ĵ_j(t+1)` for some `j`,
then `Ĵ_0(t)` ... is a permissible center for `Ĵ_j(t)` for the same `j`.  Since `Ŝ_{t+1}` (resp. `Ŝ_t`)
is faithfully flat over `S_{t+1}` (resp. `S_t`), it follows by Lemma 9 of § 3, Ch. II that, if
`J_0(t+1)` is a permissible center for `J_j(t+1)` for some `j`, then `J_0(t)` is such for `J_j(t)`."
Here `J_0(t+1)` permissible in `S_{t+1}` gives `Ĵ_0(t+1)` permissible in `Ŝ_{t+1}`
(`isPermissibleSys_of_isPermissibleSysS`); Corollary 1 of Proposition 2 is
`hasGenericStalkFrame_succ_and_isPermissibleCenter_of_mem` (on `B̂_t`) and
`isPermissibleSys_succ_iff_of_notMem` (off `B̂_t`); and `Ĵ_0(t)` permissible in `Ŝ_t` gives `J_0(t)`
permissible in `S_t` (`isPermissibleSysS_of_isPermissibleSys`). -/
theorem RemovalFamily.isRegularSysLast_and_exists_isPermissibleSysS_zero [Hironaka.HironakaCitedResults.{u}] {𝒮 : Frame hS}
    (R : 𝒮.RemovalFamily) (hsimple : ℜ.W.IsSimpleAt x₀) :
    ∀ (s : ℕ) (xb : (𝒮.xBar s).toScheme), xb ∈ R.uBar s →
      (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal xb) →
      𝒮.IsRegularSysLast s ((𝒮.xBar s).ι.base xb) ∧
        ∀ j : Fin ℜ.β, 𝒮.IsPermissibleSysS s ((𝒮.xBar s).ι.base xb) j →
          ∃ xb0 : (𝒮.xBar 0).toScheme, xb0 ∈ R.uBar 0 ∧
            (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar 0).stalkIdeal xb0) ∧
            𝒮.IsPermissibleSysS 0 ((𝒮.xBar 0).ι.base xb0) j := by
  classical
  intro s
  induction s with
  | zero =>
    intro xb hxb hν
    have hne := R.stalkIdeal_totalTransform_sys_last_ne_top hsimple.1 0 xb hxb hν
    exact ⟨𝒮.isRegularLocalRing_quotient_sys_last_zero hsimple _ hne,
      fun j hp => ⟨xb, hxb, hν, hp⟩⟩
  | succ s ih =>
    intro xb hxb hν
    have hx := R.mem_diff_of_mem_uBar_succ s xb hxb
    have hν' := R.le_nu_jBar_of_le_nu_succ s xb hxb hν
    obtain ⟨hreg, hdesc⟩ := ih ((𝒮.fBar s).base xb) hx.1 hν'
    have hgen := R.exists_hasGenericStalkFrame_of_b_le_nu s ((𝒮.fBar s).base xb) hx.1 hν'
    have hne1 := R.stalkIdeal_totalTransform_sys_last_ne_top hsimple.1 (s + 1) xb hxb hν
    have hcomm : (𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb) =
        (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) :=
      (congrArg (fun φ => φ.base xb) (𝒮.fBar_comm s)).symm
    have hreg' : 𝒮.IsRegularSysLast s ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb)) := by
      rw [hcomm]; exact hreg
    have hreg1 : 𝒮.IsRegularSysLast (s + 1) ((𝒮.xBar (s + 1)).ι.base xb) :=
      𝒮.isRegularLocalRing_quotient_sys_last_succ s _ hreg' hne1
    refine ⟨hreg1, fun j hS1 => ?_⟩
    -- `J_0(s+1)` permissible in `S_{s+1}` gives `Ĵ_0(s+1)` permissible in `Ŝ_{s+1}`
    have hp : 𝒮.IsPermissibleSys (s + 1) ((𝒮.xBar (s + 1)).ι.base xb) j :=
      𝒮.isPermissibleSys_of_isPermissibleSysS (s + 1) _ j hreg1 hS1
    -- Corollary 1 of Proposition 2, § 8, Ch. III: `Ĵ_0(s)` is permissible in `Ŝ_s`
    have hp'' : 𝒮.IsPermissibleSys s ((𝒮.xBar s).ι.base ((𝒮.fBar s).base xb)) j := by
      by_cases hmem : (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) ∈ (𝒮.tHat.B s).pts
      · obtain ⟨-, hD⟩ := R.hasGenericStalkFrame_succ_and_isPermissibleCenter_of_mem s xb hxb hν
          hmem hgen
        have hp' : 𝒮.IsPermissibleSys s ((𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb)) j :=
          hD hreg' hne1 j hp
        rw [hcomm] at hp'
        exact hp'
      · have hmem' : (𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb) ∉ (𝒮.tHat.B s).pts := by
          rw [hcomm]; exact hmem
        have hp' := (𝒮.isPermissibleSys_succ_iff_of_notMem s _ hmem' j).mp hp
        rw [hcomm] at hp'
        exact hp'
    -- and `J_0(s)` is permissible in `S_s` (Lemma 9)
    exact hdesc j (𝒮.isPermissibleSysS_of_isPermissibleSys s _ j hreg.stalkIdeal_ne_top hp'')

/-- (A3) The case `t = 0` of (iii): if `Ĵ_0(0)` is a permissible center for `Ĵ_j(0)` at the point
`x̂'_0` of `X̄_0`, then `V_j` is normally flat along `W` at `x_0` (p. 306: "`V_j` is normally flat
along `W` at `x_0` if and only if the same is true at `x_0'`.  (See Corollary 2 of Proposition 2,
§ 8, Ch. III.)").

\textbf{Deviation from the paper (gap filled).} The paper cites Corollary 2 of Proposition 2 for
the equivalence "`V_j` is normally flat along `W` at `x_0` iff the same is true at `x'_0`", where
`x'_0 = c_0(x̂'_0)` is a generization of `x_0` in `X = X_0`.  Lean proves the implication needed
(from the point `x̂'_0` of `Spec Ŝ` to `x_0`): Corollary 2 of Proposition 2 (`cor:III.prop2-2`,
`isNormallyFlatAlongIdeal_of_localization`) in the complete ring `Ŝ`, for the prime `P̂_0` of
`x̂'_0`, the adapted system `g` of `Ĵ_j` at `x̂'_0` (the properties (i), (ii) come from the base
case `hasGenericStalkFrame_zero_and`), then the descent `Ŝ → S` of normal flatness (Lemma 9 of
Ch. II § 3, `isNormallyFlatAlongIdeal_map_iff`).  The paper's step "`V_j` is normally flat at `x'_0`" is
`Ŝ`-level here and never passes through `S` at `x'_0`. -/
theorem isNormallyFlatAlongAt'_of_isPermissibleCenter_zero [Hironaka.HironakaCitedResults.{u}] {𝒮 : Frame hS}
    (xb : (𝒮.xBar 0).toScheme) (hν : (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar 0).stalkIdeal xb))
    (hsimple : ℜ.W.IsSimpleAt x₀) (j : Fin ℜ.β)
    (hperm : IsPermissibleCenter ((𝒮.tHat.X 0).presheaf.stalk ((𝒮.xBar 0).ι.base xb))
      ((Subscheme.totalTransform (𝒮.c 0) (T.sys ℜ 0 j.castSucc)).stalkIdeal
        ((𝒮.xBar 0).ι.base xb))
      ((Subscheme.totalTransform (𝒮.c 0) (T.sys ℜ 0 (Fin.last ℜ.β))).stalkIdeal
        ((𝒮.xBar 0).ι.base xb))) :
    Subscheme.IsNormallyFlatAlongAt' (ℜ.V j) ℜ.W x₀ := by
  classical
  have hx0 := hS.ambient.2.1 x₀
  have hregS : IsRegularLocalRing (X.presheaf.stalk x₀) := hx0
  have hregHat := 𝒮.regShat
  have hW0 : x₀ ∈ ℜ.W.pts := by
    have h := hS.mem_wStar
    cases r with
    | closed F => exact h.1
    | opn U => exact h.1
  obtain ⟨hgen, hadapt⟩ := hasGenericStalkFrame_zero_and 𝒮 xb hν
  set xh : 𝒮.tHat.X 0 := (𝒮.xBar 0).ι.base xb with hxh
  let Pr : PrimeSpectrum (Shat X x₀) := xh
  let Pi : Ideal (Shat X x₀) := Pr.asIdeal
  have : Pi.IsPrime := Pr.isPrime
  let α := algebraMap (X.presheaf.stalk x₀) (Shat X x₀)
  obtain ⟨m', g, hstd, hadaptj⟩ := hadapt j.castSucc
  have hVj : (datumSystem ℜ j.castSucc) = ℜ.V j := by simp [datumSystem]
  have hW : (datumSystem ℜ (Fin.last ℜ.β)) = ℜ.W := by simp [datumSystem]
  rw [hVj] at hstd hadaptj
  have hhaveAlg : IsAlgebraicScheme X := hS.ambient.1
  let e : Localization.AtPrime Pi ≃+* (𝒮.tHat.X 0).presheaf.stalk xh :=
    (Spec.stalkIso (CommRingCat.of (Shat X x₀)) Pr).symm.commRingCatIsoToRingEquiv
  have hsysW : T.sys ℜ 0 (Fin.last ℜ.β) = ℜ.W := by
    show (T.pre 0).strictTransform (datumSystem ℜ (Fin.last ℜ.β)) = ℜ.W
    simp only [datumSystem, Fin.snoc_last]
    rfl
  have hsysV : T.sys ℜ 0 j.castSucc = ℜ.V j := by
    show (T.pre 0).strictTransform (datumSystem ℜ j.castSucc) = ℜ.V j
    simp only [datumSystem, Fin.snoc_castSucc]
    rfl
  -- the stalk ideals of `c_0⁻¹(W)` and `c_0⁻¹(V_j)` at `x̂'_0`
  have hJW : (Subscheme.totalTransform (𝒮.c 0) (T.sys ℜ 0 (Fin.last ℜ.β))).stalkIdeal xh =
      ((((ℜ.W.stalkIdeal x₀).map α).map (algebraMap (Shat X x₀) (Localization.AtPrime Pi))).map e) := by
    rw [𝒮.c_zero, hsysW]
    exact stalkIdeal_totalTransform_c0_stalkIso x₀ ℜ.W xh
  have hJV : (Subscheme.totalTransform (𝒮.c 0) (T.sys ℜ 0 j.castSucc)).stalkIdeal xh =
      ((((ℜ.V j).stalkIdeal x₀).map α).map (algebraMap (Shat X x₀) (Localization.AtPrime Pi))).map e := by
    rw [𝒮.c_zero, hsysV]
    exact stalkIdeal_totalTransform_c0_stalkIso x₀ (ℜ.V j) xh
  have hWV : ℜ.W.IsContainedIn (ℜ.V j) := hS.isDatum.2.2.2.2 j
  have hne : (Subscheme.totalTransform (𝒮.c 0) (T.sys ℜ 0 (Fin.last ℜ.β))).stalkIdeal xh ≠ ⊤ := by
    have := hgen.mem_pts_sys_last hW0
    rw [← Subscheme.mem_pts_iff_stalkIdeal_ne_top, Subscheme.pts_totalTransform_eq_preimage]
    exact this
  have hJWP : (ℜ.W.stalkIdeal x₀).map α ≤ Pi := by
    by_contra hnle
    obtain ⟨a, haJ, haP⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
    apply hne
    rw [hJW]
    have hunit : IsUnit (algebraMap (Shat X x₀) (Localization.AtPrime Pi) a) :=
      IsLocalization.map_units _ (⟨a, haP⟩ : Pi.primeCompl)
    have : ((ℜ.W.stalkIdeal x₀).map α).map (algebraMap (Shat X x₀) (Localization.AtPrime Pi)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ haJ) hunit
    rw [this, Ideal.map_top]
  obtain ⟨hPprime, hJleA, hregA, hNFA⟩ := hperm.resolve_left hne
  -- normal flatness in `Ŝ_P`
  have hNFR : IsNormallyFlatAlongIdeal
      ((((ℜ.W.stalkIdeal x₀).map α).map (algebraMap (Shat X x₀) (Localization.AtPrime Pi))).map
        (Ideal.Quotient.mk ((((ℜ.V j).stalkIdeal x₀).map α).map
          (algebraMap (Shat X x₀) (Localization.AtPrime Pi))))) := by
    exact isNormallyFlatAlongIdeal_mod_of_ringEquiv e _ _ _ _ hJV hJW hNFA
  have hregW : IsRegularLocalRing (Shat X x₀ ⧸ (ℜ.W.stalkIdeal x₀).map α) :=
    isRegularLocalRing_shat_quotient_map_of_isRegularLocalRing_quotient x₀ hx0 ℜ.W hsimple.2
  have hdom : IsDomain (Shat X x₀ ⧸ (ℜ.W.stalkIdeal x₀).map α) := isDomain_of_isRegularLocalRing _
  have hJWprime : ((ℜ.W.stalkIdeal x₀).map α).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  have hJVW : ((ℜ.V j).stalkIdeal x₀).map α ≤ (ℜ.W.stalkIdeal x₀).map α :=
    Ideal.map_mono (Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hWV x₀)
  have hcharS : CharZero (ResidueField (Shat X x₀)) :=
    (RingHom.charZero_iff (ResidueField.map α).injective).mp (charZero_residueField_stalk X x₀)
  have hcor := isNormallyFlatAlongIdeal_of_localization (Shat X x₀) Pi
    (((ℜ.V j).stalkIdeal x₀).map α) (hJVW.trans hJWP) g hadaptj ((ℜ.W.stalkIdeal x₀).map α) hJWP
    hJVW hNFR
  have hFF := faithfullyFlat_adicCompletion_maximalIdeal (X.presheaf.stalk x₀)
  have hWne : ℜ.W.stalkIdeal x₀ ≠ ⊤ := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hW0
  have hdesc := (isNormallyFlatAlongIdeal_map_iff (R := X.presheaf.stalk x₀) (R' := Shat X x₀)
    ((ℜ.V j).stalkIdeal x₀) (ℜ.W.stalkIdeal x₀)
    (Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hWV x₀) hWne).mpr hcor
  exact (Subscheme.isNormallyFlatAlongAt'_iff (ℜ.V j) ℜ.W hWV x₀).mpr ⟨hW0, hdesc⟩

/-- (iii) of Lemma (AB.5) (p. 306): if `x_0` is a simple point of `W` and `V_j` is not normally
flat along `W` at `x_0`, then `V_j(s)` is not normally flat along `W(s)` at `x'_s = c_s(x̂')`.

"To prove (iii), we assume that `x_0` is a simple point of `W`.  It follows that `x̂'_t` is a
simple point of `c_t⁻¹(W(t))`, for `0 ≦ t ≦ s`.  Since `x̂'_t ∈ X̂'_t` for all `t`, by the definition of
`X̂'_t`, we have `z_t ∈ Q̂_t` and `J̄(t)_{x'_t} ⊆ Q̄_t^b` ...  Therefore `ν_Q̂(g_{jk}(t)) = ν_{jk}`.
Therefore, in view of (a) and (b) of (2), we can conclude by Corollary 1 of Proposition 2, § 8,
Ch. III that, if `Ĵ_0(t+1)` ... is a permissible center for `Ĵ_j(t+1)` for some `j`, then `Ĵ_0(t)`
... is a permissible center for `Ĵ_j(t)` for the same `j`.  Since `Ŝ_{t+1}` (resp. `Ŝ_t`) is
faithfully flat over `S_{t+1}` (resp. `S_t`), it follows by Lemma 9 of § 3, Ch. II that, if
`J_0(t+1)` is a permissible center for `J_j(t+1)`, then `J_0(t)` is such for `J_j(t)`.  In other
words, if `V_j(t+1)` is normally flat along `W(t+1)` at `x'_{t+1}` for some `j`, then `V_j(t)` is so
along `W(t)` at `x'_t`.  On the other hand, `V_j` is normally flat along `W` at `x_0` iff the same
is true at `x'_0`.  (See Corollary 2 of Proposition 2, § 8, Ch. III.)  The assertion (iii)
follows." (pp. 305--306.)

Lean (the contrapositive, step by step through the rings `S_t`, as printed): normal flatness of
`V_j(s)` along `W(s)` at `x'_s` gives that `J_0(s)` is a permissible center for `J_j(s)` in `S_s`
(`isPermissibleSysS_of_isNormallyFlatAlongAt'`; the regularity of `S_s/J_0(s)` descends from the
regular `Ŝ_s/Ĵ_0(s)`, "It follows that `x̂'_t` is a simple point of `c_t⁻¹(W(t))`").  Then
`RemovalFamily.isRegularSysLast_and_exists_isPermissibleSysS_zero` runs the step `t+1 → t` of the
paper at every `t` (to `Ŝ_{t+1}`, Corollary 1 of Proposition 2 in `Ŝ`, back to `S_t` by Lemma 9) and
gives that `J_0(0)` is a permissible center for `J_j(0)` at `x'_0`.  The last step is Corollary 2 of
Proposition 2 (`isNormallyFlatAlongAt'_of_isPermissibleCenter_zero`).

\textbf{Gaps filled.} (1) "It follows that `x̂'_t` is a simple point of `c_t⁻¹(W(t))`" is proved
(`isRegularLocalRing_quotient_sys_last_zero`, `isRegularLocalRing_quotient_sys_last_succ`).  (2) The
two uses of "faithfully flat ... Lemma 9": `J_0(t)` permissible in `S_t` gives `Ĵ_0(t)` permissible in
`Ŝ_t` (flat base change of the normal flatness, `Ŝ_t/Ĵ_0(t)` regular by (1)), and conversely
(`isPermissibleSys_of_isPermissibleSysS`, `isPermissibleSysS_of_isPermissibleSys`: Lemma 9 for the
normal flatness, and the descent of the regularity of `S_t/J_0(t)` along the flat local homomorphism
`S_t → Ŝ_t`, local ring theory, footnote 3, p. 116).  (3) Corollary 2 of Proposition 2 is applied in
`Ŝ`, where the frame data at `t = 0` (a `J_j`-stable standard base of `Ĵ_j`, hypotheses of the
corollary) are given, at the prime `P̂_0`, and its output is descended to `S` by Lemma 9; of
the equivalence "normally flat at `x_0` iff at `x'_0`" only `x'_0 ⇒ x_0` is used. -/
theorem RemovalFamily.not_isNormallyFlatAlongAt_strictTransform_of_b_le_nu [Hironaka.HironakaCitedResults.{u}] {𝒮 : Frame hS}
    (R : 𝒮.RemovalFamily) (s : ℕ) (xb : (𝒮.xBar s).toScheme) (hxb : xb ∈ R.uBar s)
    (hν : (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal xb)) :
    ℜ.W.IsSimpleAt x₀ → ∀ j, ¬ Subscheme.IsNormallyFlatAlongAt' (ℜ.V j) ℜ.W x₀ →
      ¬ Subscheme.IsNormallyFlatAlongAt' ((T.pre s).strictTransform (ℜ.V j))
        ((T.pre s).strictTransform ℜ.W) ((𝒮.cBar s).base xb) := by
  intro hsimple j hj hNF
  obtain ⟨hreg, hdesc⟩ := R.isRegularSysLast_and_exists_isPermissibleSysS_zero hsimple s xb hxb hν
  have hsysV : T.sys ℜ s j.castSucc = (T.pre s).strictTransform (ℜ.V j) := by
    show (T.pre s).strictTransform (datumSystem ℜ j.castSucc) = _
    simp only [datumSystem, Fin.snoc_castSucc]
  have hsysW : T.sys ℜ s (Fin.last ℜ.β) = (T.pre s).strictTransform ℜ.W := by
    show (T.pre s).strictTransform (datumSystem ℜ (Fin.last ℜ.β)) = _
    simp only [datumSystem, Fin.snoc_last]
  have hNF' : Subscheme.IsNormallyFlatAlongAt' (T.sys ℜ s j.castSucc)
      (T.sys ℜ s (Fin.last ℜ.β)) ((𝒮.c s).base ((𝒮.xBar s).ι.base xb)) := by
    rw [hsysV, hsysW]; exact hNF
  -- at `t = s`: `V_j(s)` normally flat along `W(s)` at `x'_s` is `J_0(s)` permissible for `J_j(s)`
  have hp := 𝒮.isPermissibleSysS_of_isNormallyFlatAlongAt' s _ j hreg hNF'
  obtain ⟨xb0, hxb0, hν0, hp0⟩ := hdesc j hp
  -- at `t = 0`: back to `Ŝ`, then Corollary 2 of Proposition 2 and Lemma 9
  have hne0 := R.stalkIdeal_totalTransform_sys_last_ne_top hsimple.1 0 xb0 hxb0 hν0
  have hreg0 := 𝒮.isRegularLocalRing_quotient_sys_last_zero hsimple _ hne0
  have hp0' := 𝒮.isPermissibleSys_of_isPermissibleSysS 0 _ j hreg0 hp0
  exact hj (isNormallyFlatAlongAt'_of_isPermissibleCenter_zero xb0 hν0 hsimple j hp0')

end Frame

/-- **Lemma (AB.5)** (p. 303) for an arbitrary open family with removals `U_s`
(`Frame.RemovalFamily`), with `Ū_s = U_s ∩ X̄_s` in place of `X̄'_s`: the printed lemma is the
instance `U_s = X̂'_s` (`Frame.cbar_mem_strictTransform_and_not_isSimpleAt_of_b_le_nu`), and the
corrected construction of `Hironaka.Ch4.ComponentwiseConstruction` is the instance
`U_s = X̂*'_s`.  The paper's proof applies verbatim: of the open subschemes it
uses only that a point of `Ū_{t+1}` lies over a point of `Ū_t` which is either not on `B̂_t` or on
`B̂_t − Bad_t`, where `B̂_t ⊆ X̄_t` and `J̄(t) ⊆ P(B̄_t)^b` (the fields of `RemovalFamily`); this
is exactly the dichotomy [g]/[h] "from the definition of `X'_s`" (p. 304). -/
@[blueprint "lem:IV.AB-5-generic"
  (statement := /-- Notation as in \cref{lem:IV.AB-5}, for an arbitrary open family with
    removals $U_s\subseteq\hat X_s$ (\cref{lem:IV.3-construction-facts-generic}), with
    $\bar U_s=U_s\cap\bar X_s$ in place of $\bar X_s'$: let $\hat x'$ be any point of
    $\bar U_s$ and $x'=c_s(\hat x')$, and suppose $\nu(\bar J(s)_{\hat x'})\ge b$. Then (i),
    (ii), (iii) of \cref{lem:IV.AB-5} hold. (Formalization note: the printed Lemma (AB.5) is the
    instance $U_s=\hat X_s'$; the corrected construction of
    \cref{def:IV.3-construction-componentwise} is the instance $U_s=\hat X_s^{*\prime}$.) -/)
  (proof := /-- The proof of \cref{lem:IV.AB-5} applies verbatim: of the open subschemes it
    uses only that the image $\hat x_t'$ of $\hat x'$ in $\bar U_t$ is either not on $\hat B_t$
    or on $\hat B_t-\mathrm{Bad}_t$, where $z_t\in\hat Q_t$ and
    $\bar J(t)_{\hat x_t'}\subseteq\bar Q_t^b$ (the defining properties of the family), which is
    the dichotomy ``from the definition of $X_s'$'' of p.~304. The frames (1)--(6) are
    \cref{lem:IV.AB-5-frame} (generic stalk frames, \cref{def:IV.AB-5-frame}); (i) is derived
    from them, and (ii), (iii) are the Lean helpers
    \texttt{not\_isSimpleAt\_strictTransform\_of\_b\_le\_nu} and
    \texttt{not\_isNormallyFlatAlongAt\_strictTransform\_of\_b\_le\_nu}.

    \textbf{Deviation from the paper (gap filled), (i).} The paper (p.~305): ``Since $x_0$ is a
    point of $W$, we have $\nu_{0k}>0$ for $1\le k\le m_0$. Hence (a) and (b) of (2) for
    $\hat J_0(s)$ and $g_{0k}(s)$ for $1\le k\le m_0$ imply that $\hat J_0(s)$ is contained in the
    maximal ideal of $\hat S_s$, and hence $J_0(s)$ contained in the maximal ideal of $S_s$. This
    means that $x'=x_s'\in W(s)$, namely (i).'' Lean proves that $\hat J_0(s)$ is a proper ideal
    (if it were the unit ideal, $\nu^{(1)}(\hat J_0(s))=0$, whereas $\nu^{(1)}=\infty$ if
    $m_0=0$ and $\nu^{(1)}=\nu_{M}(g_{01}(s))=\nu_{01}>0$ otherwise) and transfers this to
    $x'$ through $c_s^{-1}(W(s))$ (a point lies on the total transform iff its image lies on
    $W(s)$). For $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$, $x'\in F(s)$ follows
    directly from $\bar X_s=c_s^{-1}(F(s))$.

    \textbf{Gap filled, (ii), along the printed argument.} The paper (p.~305): ``If $W$ is singular
    at $x_0$, then the number of those indices $k$ with $\nu_{0k}=1$ is less than codimension of $W$
    in $X$ at $x_0$ \dots\ It is clear that the codimension of $W(s)$ in $W_s'$ [sic; $X_s'$ is
    meant] at $x_s'$ is at least equal to that of $W$ in $X$ at $x_0$. Therefore, in view of (a) and
    (b) of (2) for $\hat J_0(s)$ and $g_{0k}(s)$ $(1\le k\le m_0)$, we see that $W(s)$ is singular
    at the point $x'=x_s'$.'' Lean follows these sentences, the codimension being the height of the
    ideal in the local ring ($S=\mathcal O_{X,x_0}$, $S_s=\mathcal O_{X_s,x_s'}$; the minimum of the
    codimensions of the irreducible components). The numbers $\nu_{0k}=\nu^{(k)}(J_0)$ are the orders
    of a standard base of $J_0$ in $S$ and $S/J_0$ is not regular, so the number of indices with
    $\nu_{0k}=1$ is smaller than $\operatorname{ht}J_0$. The height of $J_0$ at $x_0$ is at most that
    at its generization $x_0'=g_s(x_s')$ (a localization), which is at most $\operatorname{ht}J_0(s)$
    at $x_s'$ (the strict transforms along the $s$ monoidal transformations of non-singular schemes,
    one at a time), and $\operatorname{ht}J_0(s)\le\operatorname{ht}\hat J_0(s)$ since $S_s\to\hat S_s$
    is flat. By (a), (b) of (2) the initial forms of the $g_{0k}(s)$ generate $\operatorname{gr}\hat
    J_0(s)$ and their number of order one is at most that of $\nu_{0k}=1$, so $\hat S_s/\hat J_0(s)$
    is not regular; regularity of $S_s/J_0(s)$ would give that of $\hat S_s/\hat J_0(s)$ (class
    $\mathfrak B$, base change along $c_s$). The paper's parenthetical ``(Observe that a suitably
    reordered subsystem of $(g_{01}(s),\dots,g_{0m}(s))$ is a standard base of $\hat J_0(s)$.)'' is
    proved (\cref{lem:IV.AB-5-ii-standard-subsystem}) and used as printed: the count criterion
    (\cref{lem:IV.AB-5-ii-criterion}) is applied to that standard base, whose number of members of
    order one is at most the number of $g_{0k}(s)$ of order one.

    \textbf{Gap filled, (iii), along the printed argument.} The paper (pp.~305--306) asserts
    ``It follows that $\hat x_t'$ is a simple point of $c_t^{-1}(W(t))$, $0\le t\le s$'' (proved: for
    $t=0$ class $\mathfrak B$ and Serre's theorem for the generization $\hat x_0'$; for $t\to t+1$
    the strict transform of a regular $W(t)\supseteq B_t$). Then, at every step $t+1\to t$ in the
    order of the paper: $J_0(t+1)$ permissible in $S_{t+1}$ gives $\hat J_0(t+1)$ permissible in
    $\hat S_{t+1}$ (faithful flatness, Lemma~9 of Ch.~II \S3, with the regularity of $\hat S_{t+1}/
    \hat J_0(t+1)$), then ``Corollary~1 of Proposition~2, \S8, Ch.~III'' (\cref{cor:III.prop2-1})
    applied to the stalk monoidal transform, with $g_{jk}(t+1)=g_{jk}(t)/v_t^{\nu_{jk}}$ (up to a
    unit), gives $\hat J_0(t)$ permissible in $\hat S_t$, and Lemma~9 gives $J_0(t)$ permissible in
    $S_t$ (the regularity of $S_t/J_0(t)$ descends along the flat local homomorphism $S_t\to\hat
    S_t$). At $t=s$ normal flatness of $V_j(s)$ along $W(s)$ at $x_s'$ gives $J_0(s)$ permissible
    for $J_j(s)$ in $S_s$; at $t=0$ one uses Corollary~2 of Proposition~2 (\cref{cor:III.prop2-2})
    in the complete ring $\hat S$, where the frame data of the hypotheses are given, and descends
    by Lemma~9; only the implication ``normally flat at $\hat x_0'$ implies normally flat at $x_0$''
    of the paper's equivalence is used. -/)
  (proofUses := ["cor:III.thm5-3a", "thm:III.5", "lem:II.3-9",
    "lem:IV.3-construction-facts-generic", "def:IV.AB-5-frame", "lem:IV.AB-5-frame",
    "cor:III.prop2-1", "cor:III.prop2-2", "lem:regular-localization-serre",
    "lem:IV.AB-5-ii-criterion", "lem:IV.AB-5-ii-standard-subsystem"])
  (latexEnv := "lemma")]
theorem Frame.RemovalFamily.cbar_mem_strictTransform_and_not_isSimpleAt_of_b_le_nu [Hironaka.HironakaCitedResults.{u}] {N n : ℕ}
    {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
    {𝒮 : Frame hS} (R : 𝒮.RemovalFamily) (s : ℕ) (xb : (𝒮.xBar s).toScheme)
    (hxb : xb ∈ R.uBar s)
    (hν : (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal xb)) :
    (𝒮.cBar s).base xb ∈ ((T.pre s).strictTransform ℜ.W).pts ∧
    (∀ F, r = .closed F → (𝒮.cBar s).base xb ∈ ((T.pre s).strictTransform F).pts) ∧
    (¬ ℜ.W.IsSimpleAt x₀ →
      ¬ ((T.pre s).strictTransform ℜ.W).IsSimpleAt ((𝒮.cBar s).base xb)) ∧
    (ℜ.W.IsSimpleAt x₀ → ∀ j, ¬ Subscheme.IsNormallyFlatAlongAt' (ℜ.V j) ℜ.W x₀ →
      ¬ Subscheme.IsNormallyFlatAlongAt' ((T.pre s).strictTransform (ℜ.V j))
        ((T.pre s).strictTransform ℜ.W) ((𝒮.cBar s).base xb)) := by
  have hgen := R.exists_hasGenericStalkFrame_of_b_le_nu s xb hxb hν
  have hW0 : x₀ ∈ ℜ.W.pts := by
    have h := hS.mem_wStar
    cases r with
    | closed F => exact h.1
    | opn U => exact h.1
  have hi := hgen.mem_pts_sys_last hW0
  have hi' : (𝒮.cBar s).base xb ∈ ((T.pre s).strictTransform ℜ.W).pts := by
    have hi2 : (𝒮.c s).base ((𝒮.xBar s).ι.base xb) ∈
        ((T.pre s).strictTransform ℜ.W).pts := by
      simpa [Tower.sys, succSystem, datumSystem] using hi
    exact hi2
  refine ⟨hi', fun F hF => ?_,
    R.not_isSimpleAt_strictTransform_of_b_le_nu s xb hxb hν hgen,
    R.not_isNormallyFlatAlongAt_strictTransform_of_b_le_nu s xb hxb hν⟩
  have h1 := Subscheme.mem_pts_ι (𝒮.xBar s) xb
  have e : (𝒮.xBar s).pts =
      (Subscheme.totalTransform (𝒮.c s) ((T.pre s).strictTransform F)).pts :=
    congrArg (fun D => D.pts) (𝒮.xBar_eq_totalTransform_of_closed s F hF)
  rw [e, Subscheme.pts_totalTransform_eq_preimage] at h1
  exact h1

/-- **Lemma (AB.5)** (p. 303).  `x̂'` is a point of `X̄'_s` (a point of the scheme `X̄_s` lying
in the open subset `X̄'_s`), and `x' = c_s(x̂')`; `ν(J̄(s)_{x̂'})` is the order of the stalk of
`J̄(s)` in the local ring of `X̄'_s` at `x̂'` (Ch. I, p. 165).

In Lean: the instance `U_s = X̂'_s` (`Frame.removalFamily`) of the lemma for an arbitrary open
family with removals, `Frame.RemovalFamily.cbar_mem_strictTransform_and_not_isSimpleAt_of_b_le_nu`
(`lem:IV.AB-5-generic`). -/
@[blueprint "lem:IV.AB-5"
  (statement := /-- \textbf{Lemma (AB.5).} Notation as in \cref{def:IV.3-setup},
    \cref{def:IV.3-frame}, \cref{def:IV.3-construction}. Let $\hat x'$ be any point of
    $\bar X_s'$ and $x'=c_s(\hat x')\in X_s'$. Suppose $\nu(\bar J(s)_{\hat x'})\ge b$
    (\cref{def:order-nu}). Then we have that:
    \begin{enumerate}
      \item[(i)] $x'$ is a point of $W(s)$. (Hence, for the case in which
        $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$, we have $x'\in W(s)\cap F(s)$.)
      \item[(ii)] If $W$ is singular at the point $x_0$, then $W(s)$ is also singular at $x'$.
      \item[(iii)] If $V_j$ for some $j$ $(1\le j\le\beta)$ is not normally flat along $W$ at
        $x_0$, then $V_j(s)$ for the same $j$ is not normally flat along $W(s)$ at $x'$,
        provided $x_0$ is a simple point of $W$ (\cref{def:0.1-normally-flat-at}).
    \end{enumerate}
    (p.~303.) -/)
  (proof := /-- Let $\hat x_t'$ (resp.\ $x_t'$) be the image of $\hat x'$ in $\bar X_t'$
    (resp.\ of $x'$ in $X_t'$), so that $x_t'=c_t(\hat x_t')$; let $S_t$, $\hat S_t$, $\bar T_t$
    be the local rings of $X_t'$ at $x_t'$, $\hat X_t'$ at $\hat x_t'$, $\bar X_t'$ at
    $\hat x_t'$, $Q_t$ the ideal of $B_t$ in $S_t$, $\hat Q_t=Q_t\hat S_t$ the ideal of
    $\hat B_t=c_t^{-1}(B_t)$, $J_j(t)$ the ideal of $V_j(t)$ $(1\le j\le\beta)$ and $J_0(t)$ that
    of $W(t)$ in $S_t$, and $\hat J_j(t)=J_j(t)\hat S_t$. Clearly $x_0$ (resp.\ $\hat x_0$) is a
    specialization of $x_0'$ (resp.\ $\hat x_0'$), so $S_0=S_{P_0}$ and
    $\hat S_0=\hat S_{\hat P_0}$ for prime ideals $P_0$, $\hat P_0$; since $\hat x_0'\in\bar X_0'$
    we have $z\in\hat P_0$, and with $T_0$ the localization of $T$ at $\hat P_0\cap T$,
    $(T_0;z)$ is a regular frame of $\hat S_0$; $\bar J(0)_{\hat x_0'}=(g_{jki}^{b/i})\bar T_0$.
    One proves, by induction on $t$, that there exist regular frames $(T_t;z_t)$ of
    $\hat S_t$ $(0\le t\le s)$, elements $g_{jk}(t)\in\hat J_j(t)$ and $v_t\in T_t$ with:
    (1) $(T_0;z_0)=(T_0;z)$ and $z_t$ generates the kernel of $\hat S_t\to\bar T_t$;
    (2) $g_{jk}(0)=g_{jk}$ and (a) the initial forms of the $g_{jk}(t)$ generate
    $\operatorname{gr}_{\hat M_t}(\hat J_j(t),\hat S_t)$, (b)
    $\nu_{\hat M_t}(g_{jk}(t))=\nu_{jk}$ $(=\nu^{(k)}(\hat J_j)=\nu^{(k)}(J_j))$;
    (3) $g_{jk}(t)=z_t^{\nu_{jk}}+\sum_{i=1}^{\nu_{jk}}g_{jki}(t)z_t^{\nu_{jk}-i}$ with
    $g_{jki}(t)\in T_t$; (4) $\bar J(t)_{\hat x_t'}=(g_{jki}(t)^{b/i})\bar T_t$;
    (5) $(v_t)\hat S_{t+1}=\hat Q_t\hat S_{t+1}$ and $z_{t+1}=z_t/v_t$;
    (6) $g_{jk}(t+1)=g_{jk}(t)/v_t^{\nu_{jk}}$. From the definition of $X_s'$ and
    $\nu(\bar J(s)_{\hat x'})\ge b$ we have $\nu(\bar J(t)_{\hat x_t'})\ge b$ for all $t$, which
    gives (b) of (2) from (3), (4), and then (a) of (2) by Corollary~3 of Theorem~5, \S6,
    Ch.~III (\cref{cor:III.thm5-3a}); the inductive step uses that $\hat S_{t+1}$ is a monoidal
    transform of $\hat S_t$ with center $\hat Q_t\supseteq(z_t)\hat S_t$, the frame transform
    $(T_{t+1};z_{t+1})$ with $z_{t+1}=z_t/v_t$, (4) for $\bar J(t)$ (whence
    $g_{jki}(t)^{b/i}\in\hat Q_t^b$, and one sets $g_{jki}(t+1)=g_{jki}(t)v_t^{-i}$), and
    Theorem~5, \S6, Ch.~III (\cref{thm:III.5}).
    (i): since $x_0\in W$, $\nu_{0k}>0$ for $1\le k\le m_0$, so by (2) $\hat J_0(s)$, hence
    $J_0(s)$, is contained in the maximal ideal; this means $x'=x_s'\in W(s)$. (ii): if $W$ is
    singular at $x_0$, the number of indices $k$ with $\nu_{0k}=1$ is less than the
    codimension of $W$ in $X$ at $x_0$ (the minimum of the codimensions of its irreducible
    components); the codimension of $W(s)$ at $x_s'$ is at least that of $W$ at $x_0$, so by
    (a), (b) of (2) for $\hat J_0(s)$ (a suitably reordered subsystem of the $g_{0k}(s)$ being
    a standard base of $\hat J_0(s)$), $W(s)$ is singular at $x'=x_s'$. (iii): assume $x_0$ is
    a simple point of $W$; then $\hat x_t'$ is a simple point of $c_t^{-1}(W(t))$, and since
    $\hat x_t'\in\hat X_t'$, $z_t\in\hat Q_t$ and $\bar J(t)_{\hat x_t'}\subseteq\bar Q_t^b$ for
    all $t$; by (3), (4), $\nu_{\hat Q}(g_{jk}(t))=\nu_{jk}$. By (a), (b) of (2) and
    Corollary~1 of Proposition~2, \S8, Ch.~III, if $\hat J_0(t+1)$ is a permissible center for
    $\hat J_j(t+1)$ then $\hat J_0(t)$ is one for $\hat J_j(t)$; by faithful flatness and
    Lemma~9, \S3, Ch.~II (\cref{lem:II.3-9}) the same holds for $J_0(t+1)$, $J_j(t+1)$ and
    $J_0(t)$, $J_j(t)$: if $V_j(t+1)$ is normally flat along $W(t+1)$ at $x_{t+1}'$ then
    $V_j(t)$ is so along $W(t)$ at $x_t'$. Finally, $V_j$ is normally flat along $W$ at $x_0$
    if and only if the same is true at $x_0'$ (Corollary~2 of Proposition~2, \S8, Ch.~III).
    The assertion (iii) follows. \textsc{q.e.d.}

    (Formalization note: in Lean this is the instance $U_s=\hat X_s'$ of
    \cref{lem:IV.AB-5-generic}, the lemma for an arbitrary open family with removals; the
    parenthetical observation of (ii) is \cref{lem:IV.AB-5-ii-standard-subsystem}, used to apply
    the count criterion \cref{lem:IV.AB-5-ii-criterion} to a standard base of $\hat J_0(s)$.) -/)
  (proofUses := ["cor:III.thm5-3a", "thm:III.5", "lem:II.3-9", "lem:IV.AB-5-generic",
    "lem:IV.AB-5-ii-standard-subsystem"])
  (latexEnv := "lemma")]
theorem Frame.cbar_mem_strictTransform_and_not_isSimpleAt_of_b_le_nu [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
    (𝒮 : Frame hS) (s : ℕ) (xb : (𝒮.xBar s).toScheme) (hxb : xb ∈ 𝒮.xBarPrime s)
    (hν : (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal xb)) :
    (𝒮.cBar s).base xb ∈ ((T.pre s).strictTransform ℜ.W).pts ∧
    (∀ F, r = .closed F → (𝒮.cBar s).base xb ∈ ((T.pre s).strictTransform F).pts) ∧
    (¬ ℜ.W.IsSimpleAt x₀ →
      ¬ ((T.pre s).strictTransform ℜ.W).IsSimpleAt ((𝒮.cBar s).base xb)) ∧
    (ℜ.W.IsSimpleAt x₀ → ∀ j, ¬ Subscheme.IsNormallyFlatAlongAt' (ℜ.V j) ℜ.W x₀ →
      ¬ Subscheme.IsNormallyFlatAlongAt' ((T.pre s).strictTransform (ℜ.V j))
        ((T.pre s).strictTransform ℜ.W) ((𝒮.cBar s).base xb)) :=
  𝒮.removalFamily.cbar_mem_strictTransform_and_not_isSimpleAt_of_b_le_nu s xb hxb hν

end AB

end

end Hironaka
