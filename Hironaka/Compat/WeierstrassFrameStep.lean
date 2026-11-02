/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch3.JStability
public import Hironaka.Compat.CoefficientField
public import Hironaka.Compat.TauZSystem
public import Hironaka.Compat.FrameChain
public import Hironaka.Compat.WeierstrassDatum
public import Hironaka.Compat.WeierstrassFrameTransform
public import Hironaka.Compat.WeierstrassChoice
public import Hironaka.Compat.WeierstrassDatumBaseChange
public import Hironaka.Compat.WeierstrassAdaptedModel
public import Hironaka.Compat.WeierstrassInitialForm
public import Hironaka.Compat.WeierstrassAdaptedCoordinates
public import Hironaka.Compat.WeierstrassLinearTerm
public import Hironaka.Compat.WeierstrassNormalization
public import Hironaka.Statements

/-!
# Lemma 25 (pp. 269--272): the structure of its proof (Weierstrass frames)

The proof of Lemma 25 in the paper has three parts:

1. the **choice of `w`** (p. 270): a regular frame `(S; z)` of `R`, a regular frame `(S₀; w)` of `S`
   such that `w` lies in `T*` of `f` and the coefficient `h_Ā` of `f` has the Weierstrass shape
   (`exists_weierstrassDatum` of `WeierstrassChoice.lean`: Cohen, Weierstrass preparation, a
   linear change of the `x₁, …, x_t` and the substitution `x₁ ↦ x₁ + e⁻¹ p₁'`);
2. the **reformulated statement** (pp. 270--271) with its facts (a), (b), (c)(i)--(iii) for one
   monoidal transform: (a) `weierstrassStep_mem`, (c)(i) `weierstrassStep_frames`, (c)(iii)
   `weierstrassStep_shape` (all proved), (c)(ii) `weierstrassStep_tau` (via the printed reduction
   `weierstrassStepTau_of_rational` to the case of an algebraically closed residue field, proved
   with the base change of `Compat/WeierstrassDatumBaseChange.lean`, and the comparison of initial
   forms `weierstrassStepTau_rational`, proved with the adapted coordinates and polynomial
   models of `Compat/WeierstrassAdaptedCoordinates.lean`, the two "we may assume" normalizations
   of `Compat/WeierstrassNormalization.lean` (by Lemma 24, and `L₁ = ⋯ = L_τ = 0`), the shape of
   the initial forms of `Compat/WeierstrassInitialForm.lean`, `exists_lift` and
   `eq_zero_of_aeval_add_of_coeff` ("`eL = 0`, hence `L = 0`", p. 273)); the facts are assembled
   as printed, with the hypotheses (1)--(4), in `weierstrassDatum_facts` (whose proof goes through
   the internal one-step form `weierstrassStep_next`, the hypotheses (1), (2) entering through
   their consequences at the indices `ᾱ = 0, 1` of a one-step sequence);
3. the sentence "one can easily see that, if we prove these facts, then the proof of the lemma is
   completed" (p. 271), the induction along a permissible sequence
   (`WeierstrassDatum.isJTauZStable_snoc`, in `Compat/WeierstrassSequence.lean`), which applies
   `weierstrassDatum_facts` at each stage; the hypotheses (1), (2) at the stage `β + 1` follow
   from those at `β` by the transitivity of stability along one step
   (`Compat/StageStability.lean`), which the paper uses without comment.

`exists_isJTauZStable_snoc_aux` (in `Compat/WeierstrassSequence.lean`) assembles Lemma 25 from them.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section Statements

attribute [local instance] RegularFrame.isDomain_S

/-- **The facts (a), (b), (c) of the reformulation of Lemma 25** (pp. 270--271), for one monoidal
transform `R₁` of `R` with a regular center `P`.  Let `(S; z₁, …, z_r)` be a regular frame of `R`,
`(S₀; w)` a regular frame of `S` and `f ∈ R`, with (3) `w` in the span `T*` of
`(f)` and (4) the Weierstrass shape of the coefficient `h_Ā` of `f`.  Suppose `P ⊇ (z₁, …, z_r)R`
and `ν_P(f) = ν_M(f)` (these are the consequences of (1) `(z)` being `J`-stable and (2) `f` being
`(J, τ_{(z)})`-stable at the index `ᾱ = 0`).  Then (a) `w ∈ P` (with `(b)`, `ν_P(f) = ν`, the
hypothesis).  Suppose moreover that `(S; z)` admits a frame transform `(S₁; z₁/x, …, z_r/x)` in `R₁`
with denominator `x` and that the strict transform `f̄ = x^{-ν} f` satisfies `ν_{M₁}(f̄) = ν` and
`τ_{(z/x)}(f̄) = τ_{(z)}(f)` (the consequences of (1), (2) at the index `ᾱ = 1`, when
`ν*(J₁) = ν*(J)` and `τ*(J₁) = τ*(J)`).  Then (c) there is `y ∈ P ∩ S₀` with `(y)R₁ = PR₁` such
that (i) `(S; z)` has a frame transform in `R₁` with denominator `y` and `(S₀; w)` has a frame
transform `(S₀₁; w/y)` in `S₁` with denominator `y`, and for `f̄ = y^{-ν} f`, (ii) `w̄ = w/y`
lies in `T*` of `(f̄)` for `z̄ = z/y` and `τ_{(z̄,w̄)}(f̄) = τ_{(z,w)}(f)`, and (iii) `f̄` has the
shape (4) for the frames `(S₁; z̄)`, `(S₀₁; w̄)`.

Deviation from the paper (the hypotheses (1), (2) of the reformulation are used only through their
consequences listed above, which is what the induction along a sequence supplies; and (3) is read
through `T*`). -/
def WeierstrassStepMem : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero (ResidueField R)]
    (D : WeierstrassDatum R) (f : R), D.InTauStar f → D.HasShape f →
    ∀ (P : Ideal R) [P.IsPrime] [IsRegularLocalRing (R ⧸ P)],
      D.F.idealZ ≤ P → Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f → D.wR ∈ P

/-- The part (c)(i) of the facts of the reformulation of Lemma 25 (see `WeierstrassStepMem`): the
existence of `y ∈ P ∩ S₀` with `(y)R₁ = PR₁`, of the frame transform of `(S; z)` in `R₁` with
denominator `y` and of the frame transform of `(S₀; w)` in `S₁` with denominator `y`. -/
def WeierstrassStepFrames : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero (ResidueField R)]
    (D : WeierstrassDatum R) (f : R), D.InTauStar f → D.HasShape f →
    ∀ (P : Ideal R) [P.IsPrime] [IsRegularLocalRing (R ⧸ P)],
      D.F.idealZ ≤ P → Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f →
      ∀ (T : MonoidalTransform R P) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring],
        RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing →
        ∀ (FT : D.F.FrameTransform T) (ν : ℕ), (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) f →
        ∀ f₁ : T.ring, FT.x ^ ν * f₁ = T.toRing f →
          Ideal.ordElem (maximalIdeal T.ring) f₁ = ν →
          ∃ (y : D.F0.S) (FT' : D.F.FrameTransform T) (FT0 : D.F0.FrameTransform FT'.TS),
            algebraMap D.F.S R (algebraMap D.F0.S D.F.S y) ∈ P ∧
            FT'.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)) ∧
            FT0.x = FT'.TS.toRing (algebraMap D.F0.S D.F.S y)

/-- The part (c)(iii) of the facts of the reformulation of Lemma 25 (see `WeierstrassStepMem`,
p. 271: "(iii) of (c) is clear"): `f̄ = y^{-ν} f` has the shape (4) for the frames `(S₁; z̄)`,
`(S₀₁; w̄)`.  (The hypothesis `ν_{M₁}(f̄) = ν` is the one of (c): `ν*(J₁) = ν*(J)`; the shape (4)
asks for `|Ā| + e = ν_{M₁}(f̄)`.) -/
def WeierstrassStepShape : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero (ResidueField R)]
    (D : WeierstrassDatum R) (f : R), D.InTauStar f → D.HasShape f →
    ∀ (P : Ideal R) [P.IsPrime] [IsRegularLocalRing (R ⧸ P)],
      D.F.idealZ ≤ P → Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f →
      ∀ (T : MonoidalTransform R P) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring],
        ∀ (ν : ℕ), (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) f →
          ∀ (y : D.F0.S) (FT' : D.F.FrameTransform T) (FT0 : D.F0.FrameTransform FT'.TS),
            algebraMap D.F.S R (algebraMap D.F0.S D.F.S y) ∈ P →
            FT'.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)) →
            FT0.x = FT'.TS.toRing (algebraMap D.F0.S D.F.S y) →
            ∀ f₂ : T.ring, FT'.x ^ ν * f₂ = T.toRing f →
              Ideal.ordElem (maximalIdeal T.ring) f₂ = ν → (D.transform FT' FT0).HasShape f₂

/-- The part (c)(ii) of the facts of the reformulation of Lemma 25 (see `WeierstrassStepMem`): for
the frame transforms of (c)(i), `w̄` lies in `T*` of `f̄` for `z̄` and
`τ_{(z̄,w̄)}(f̄) = τ_{(z,w)}(f)`. -/
def WeierstrassStepTau : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero (ResidueField R)]
    (D : WeierstrassDatum R) (f : R), D.InTauStar f → D.HasShape f →
    ∀ (P : Ideal R) [P.IsPrime] [IsRegularLocalRing (R ⧸ P)],
      D.F.idealZ ≤ P → Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f →
      ∀ (T : MonoidalTransform R P) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring],
        RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing →
        ∀ (FT : D.F.FrameTransform T) (ν : ℕ), (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) f →
        ∀ f₁ : T.ring, FT.x ^ ν * f₁ = T.toRing f →
          Ideal.ordElem (maximalIdeal T.ring) f₁ = ν →
          tauZ T.ring FT.w (fun _ : Fin 1 => f₁) = tauZ R D.F.z (fun _ : Fin 1 => f) →
          ∀ (y : D.F0.S) (FT' : D.F.FrameTransform T) (FT0 : D.F0.FrameTransform FT'.TS),
            algebraMap D.F.S R (algebraMap D.F0.S D.F.S y) ∈ P →
            FT'.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)) →
            FT0.x = FT'.TS.toRing (algebraMap D.F0.S D.F.S y) →
            ∀ f₂ : T.ring, FT'.x ^ ν * f₂ = T.toRing f →
              (D.transform FT' FT0).InTauStar f₂ ∧
              tauZ T.ring (Fin.snoc FT'.w (D.transform FT' FT0).wR : Fin (D.F.r + 1) → T.ring)
                  (fun _ : Fin 1 => f₂) =
                tauZ R (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) (fun _ : Fin 1 => f)

/-- The part (c)(ii) of the facts of the reformulation of Lemma 25 in the case to which the paper
reduces it ("As in the proof of Lemma 22, the proof of (ii) of (c) can be reduced to the case in
which the residue field `k` of `S₀` is algebraically closed, so that `R₁` is residually rational
over `R`", p. 271): `R` complete with algebraically closed residue field. -/
def WeierstrassStepTauRational : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero (ResidueField R)]
    [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]
    (D : WeierstrassDatum R) (f : R), D.InTauStar f → D.HasShape f →
    ∀ (P : Ideal R) [P.IsPrime] [IsRegularLocalRing (R ⧸ P)],
      D.F.idealZ ≤ P → Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f →
      ∀ (T : MonoidalTransform R P) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring],
        RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing →
        ∀ (FT : D.F.FrameTransform T) (ν : ℕ), (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) f →
        ∀ f₁ : T.ring, FT.x ^ ν * f₁ = T.toRing f →
          Ideal.ordElem (maximalIdeal T.ring) f₁ = ν →
          tauZ T.ring FT.w (fun _ : Fin 1 => f₁) = tauZ R D.F.z (fun _ : Fin 1 => f) →
          ∀ (y : D.F0.S) (FT' : D.F.FrameTransform T) (FT0 : D.F0.FrameTransform FT'.TS),
            algebraMap D.F.S R (algebraMap D.F0.S D.F.S y) ∈ P →
            FT'.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)) →
            FT0.x = FT'.TS.toRing (algebraMap D.F0.S D.F.S y) →
            ∀ f₂ : T.ring, FT'.x ^ ν * f₂ = T.toRing f →
              (D.transform FT' FT0).InTauStar f₂ ∧
              tauZ T.ring (Fin.snoc FT'.w (D.transform FT' FT0).wR : Fin (D.F.r + 1) → T.ring)
                  (fun _ : Fin 1 => f₂) =
                tauZ R (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) (fun _ : Fin 1 => f)

end Statements

section ShapeAux

attribute [local instance] RegularFrame.isDomain_S

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

open Classical in
/-- **(iii) of (c) in the reformulation of Lemma 25** (p. 271: "(iii) of (c) is clear"):
`h̄_Ā = h_Ā y^{-e} = ū(w̄^e + p̄₂w̄^{e-2} + ⋯ + p̄_e)` with `p̄_j = y^{-j}p_j ∈ S₀₁`.

Gap filled (not detailed in the paper): `y^{-e}(w^e + p₂w^{e-2} + ⋯ + p_e)` is an element of `S₁`
(`w^e + ⋯ + p_e ∈ Q^e`, `Q = P ∩ S`, `QS₁ = yS₁`), and its expansion coefficients in the frame
transform `(S₀₁; w̄)` of `(S₀; w)` are `y^{-j}p_j`, which are therefore elements of `S₀₁`
(`RegularFrame.FrameTransform.expCoeff_div` for the frame `(S₀; w)` of `S`). -/
theorem WeierstrassDatum.hasShape_transform_of [IsDomain R] (D : WeierstrassDatum R) {f : R}
    {A : Fin D.F.r →₀ ℕ} {e : ℕ} {u : D.F.S} {p : ℕ → D.F0.S} (hu : IsUnit u)
    (hdeg : ((A.degree + e : ℕ) : ℕ∞) = Ideal.ordElem (maximalIdeal R) f)
    (hcoef : D.F.expCoeff f A = u * (D.w ^ e + ∑ j ∈ Finset.Icc 2 e,
      algebraMap D.F0.S D.F.S (p j) * D.w ^ (e - j)))
    {P : Ideal R} [P.IsPrime] (hz : D.F.idealZ ≤ P)
    (hP : Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f)
    {T : MonoidalTransform R P} [IsRegularLocalRing T.ring] {ν : ℕ}
    (hν : (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) f)
    {y : D.F0.S} (FT' : D.F.FrameTransform T) (FT0 : D.F0.FrameTransform FT'.TS)
    (hx : FT'.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)))
    (hx0 : FT0.x = FT'.TS.toRing (algebraMap D.F0.S D.F.S y))
    {f₂ : T.ring} (hf₂ : FT'.x ^ ν * f₂ = T.toRing f)
    (hord₂ : Ideal.ordElem (maximalIdeal T.ring) f₂ = ν) :
    ∃ (u' : (D.transform FT' FT0).F.S) (p' : ℕ → (D.transform FT' FT0).F0.S), IsUnit u' ∧
      ((A.degree + e : ℕ) : ℕ∞) = Ideal.ordElem (maximalIdeal T.ring) f₂ ∧
      (D.transform FT' FT0).F.expCoeff f₂ A = u' * ((D.transform FT' FT0).w ^ e +
        ∑ j ∈ Finset.Icc 2 e, algebraMap (D.transform FT' FT0).F0.S (D.transform FT' FT0).F.S
          (p' j) * (D.transform FT' FT0).w ^ (e - j)) := by
  have : IsRegularLocalRing FT'.TS.ring := FT'.isRegular
  have : IsRegularLocalRing FT0.TS.ring := FT0.isRegular
  have : IsDomain FT'.TS.ring := Transforms.isDomain_of_isRegularLocalRing _
  set yS : D.F.S := algebraMap D.F0.S D.F.S y with hyS
  set Q : Ideal D.F.S := P.comap (algebraMap D.F.S R) with hQ
  set Wp : D.F.S := D.w ^ e + ∑ j ∈ Finset.Icc 2 e,
    algebraMap D.F0.S D.F.S (p j) * D.w ^ (e - j) with hWp
  set x1 : FT'.TS.ring := FT'.TS.toRing yS with hx1
  have hνe : ν = A.degree + e := by
    have : ((A.degree + e : ℕ) : ℕ∞) = (ν : ℕ∞) := hdeg.trans hν.symm
    exact_mod_cast this.symm
  have hWpQ : Wp ∈ Q ^ e := D.weierstrassPoly_mem_pow hu hdeg hcoef hz hP
  -- `x1 ≠ 0`
  have hFTx0 : FT'.x ≠ 0 := by
    intro h0
    have hxT : T.toRing T.x ∈ Ideal.span {FT'.x} := by
      rw [FT'.span_x]; exact Ideal.mem_map_of_mem _ T.x_mem
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hxT
    exact T.x_ne_zero (MonoidalTransform.toRing_injective T (hxT.trans (map_zero _).symm))
  have hyS0 : yS ≠ 0 := by
    intro h0
    apply hFTx0
    rw [hx, h0, map_zero, map_zero]
  have hx10 : x1 ≠ 0 := by
    intro h0
    exact hyS0 (MonoidalTransform.toRing_injective FT'.TS (h0.trans (map_zero _).symm))
  -- `w^e + ⋯ + p_e = (y)^e · W̄` in `S₁`
  obtain ⟨Wb, hWb⟩ : ∃ Wb : FT'.TS.ring, FT0.x ^ e * Wb = FT'.TS.toRing Wp := by
    have hmem : FT'.TS.toRing Wp ∈ (Q ^ e).map FT'.TS.toRing := Ideal.mem_map_of_mem _ hWpQ
    rw [Ideal.map_pow, ← FT0.span_x, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  -- the coefficients `p̄_j` of `W̄` in the frame `(S₀₁; w̄)`
  set i0 : Fin D.F0.r := Fin.cast D.rank_eq_one.symm 0 with hi0
  set pb : ℕ → FT0.TS.ring := fun j =>
    FT0.toRegularFrame.expCoeff Wb (Finsupp.single i0 (e - j)) with hpb
  have hrel : ∀ j ∈ Finset.Icc 2 e, FT'.TS.toRing (algebraMap D.F0.S D.F.S (p j)) =
      x1 ^ j * FT0.β (pb j) := by
    intro j hj
    have hjle : j ≤ e := (Finset.mem_Icc.mp hj).2
    have hdiv := FT0.expCoeff_div y hx0 Wp Wb e hWb (Finsupp.single i0 (e - j))
    rw [Finsupp.degree_single, D.expCoeff_weierstrassPoly e p hj] at hdiv
    have hdiv' := congrArg FT0.β hdiv
    have hβy : FT0.β (FT0.TS.toRing y) = x1 := by
      have := RingHom.congr_fun FT0.canonical.comm y
      exact this
    have hβp : FT0.β (FT0.TS.toRing (p j)) = FT'.TS.toRing (algebraMap D.F0.S D.F.S (p j)) :=
      RingHom.congr_fun FT0.canonical.comm (p j)
    rw [map_mul, map_mul, map_pow, map_pow, hβy, hβp] at hdiv'
    have h3 : x1 ^ (e - j) * (x1 ^ j * FT0.β (pb j) -
        FT'.TS.toRing (algebraMap D.F0.S D.F.S (p j))) = 0 := by
      have : x1 ^ e = x1 ^ (e - j) * x1 ^ j := by rw [← pow_add]; congr 1; omega
      rw [mul_sub, ← mul_assoc, ← this]
      rw [sub_eq_zero]
      exact hdiv'
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h (pow_ne_zero _ hx10)
    · exact (sub_eq_zero.mp h).symm
  have hTSw : FT'.TS.toRing D.w = x1 * FT0.w i0 := by
    have h := FT0.mul_w i0
    rw [D.z0_eq i0, hx0] at h
    exact h.symm
  set wb : FT'.TS.ring := FT0.w i0 with hwb
  set Wbar : FT'.TS.ring := wb ^ e + ∑ j ∈ Finset.Icc 2 e, FT0.β (pb j) * wb ^ (e - j)
    with hWbar
  have hTWp : FT'.TS.toRing Wp = x1 ^ e * Wbar := by
    rw [hWp, map_add, map_pow, hTSw, mul_pow, map_sum, hWbar, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjle : j ≤ e := (Finset.mem_Icc.mp hj).2
    rw [map_mul, map_pow, hTSw, hrel j hj, mul_pow]
    have : x1 ^ e = x1 ^ j * x1 ^ (e - j) := by rw [← pow_add]; congr 1; omega
    rw [this]; ring
  refine ⟨FT'.TS.toRing u, pb, hu.map _, ?_, ?_⟩
  · show ((A.degree + e : ℕ) : ℕ∞) = _
    rw [hord₂, hνe]
  · have hdiv := FT'.expCoeff_div yS hx f f₂ ν hf₂ A
    rw [hcoef, map_mul, hTWp] at hdiv
    show FT'.toRegularFrame.expCoeff f₂ A = FT'.TS.toRing u * Wbar
    apply mul_left_cancel₀ (pow_ne_zero ν hx10)
    rw [hdiv, hνe, pow_add]
    ring

/-- **(iii) of (c) in the reformulation of Lemma 25** (p. 271: "(iii) of (c) is clear"): `f̄` has
the shape (4) for the frames `(S₁; z̄)`, `(S₀₁; w̄)`; see `WeierstrassDatum.hasShape_transform_of`
(which also exposes that `Ā` and `e` are those of `f`). -/
theorem WeierstrassDatum.hasShape_transform [IsDomain R] (D : WeierstrassDatum R) {f : R}
    (hShape : D.HasShape f) {P : Ideal R} [P.IsPrime] (hz : D.F.idealZ ≤ P)
    (hP : Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f)
    {T : MonoidalTransform R P} [IsRegularLocalRing T.ring] {ν : ℕ}
    (hν : (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) f)
    {y : D.F0.S} (FT' : D.F.FrameTransform T) (FT0 : D.F0.FrameTransform FT'.TS)
    (hx : FT'.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)))
    (hx0 : FT0.x = FT'.TS.toRing (algebraMap D.F0.S D.F.S y))
    {f₂ : T.ring} (hf₂ : FT'.x ^ ν * f₂ = T.toRing f)
    (hord₂ : Ideal.ordElem (maximalIdeal T.ring) f₂ = ν) :
    (D.transform FT' FT0).HasShape f₂ := by
  obtain ⟨A, e, u, p, hu, he, hdeg, hcoef⟩ := hShape
  obtain ⟨u', p', hu', hdeg', hcoef'⟩ :=
    D.hasShape_transform_of hu hdeg hcoef hz hP hν FT' FT0 hx hx0 hf₂ hord₂
  exact ⟨A, e, u', p', hu', he, hdeg', hcoef'⟩


/-- Two denominators `x`, `x'` of the same monoidal transform (`(x)R₁ = (x')R₁ = PR₁`) give the same
order to the quotients: if `xᵛ f₁ = x'ᵛ f₂` then `ν_{M₁}(f₁) = ν_{M₁}(f₂)` (the quotients differ by the
unit `(x'/x)ᵛ`). -/
theorem MonoidalTransform.ordElem_eq_of_mul_pow_eq [IsDomain R] {P : Ideal R} [P.IsPrime]
    (T : MonoidalTransform R P) [IsRegularLocalRing T.ring] {x x' : T.ring}
    (hx : Ideal.span {x} = P.map T.toRing) (hx' : Ideal.span {x'} = P.map T.toRing) {ν : ℕ}
    {f₁ f₂ : T.ring} (h : x ^ ν * f₁ = x' ^ ν * f₂) :
    Ideal.ordElem (maximalIdeal T.ring) f₁ = Ideal.ordElem (maximalIdeal T.ring) f₂ := by
  have : IsDomain T.ring := Transforms.isDomain_of_isRegularLocalRing _
  have hx0 : x ≠ 0 := by
    intro h0
    have hxT : T.toRing T.x ∈ Ideal.span {x} := by
      rw [hx]; exact Ideal.mem_map_of_mem _ T.x_mem
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hxT
    exact T.x_ne_zero (MonoidalTransform.toRing_injective T (hxT.trans (map_zero _).symm))
  obtain ⟨u, hu⟩ : Associated x x' :=
    Ideal.span_singleton_eq_span_singleton.mp (hx.trans hx'.symm)
  have h2 : f₁ = (u : T.ring) ^ ν * f₂ := by
    apply mul_left_cancel₀ (pow_ne_zero ν hx0)
    rw [h, ← hu, mul_pow]
    ring
  rw [h2, Ideal.ordElem_isUnit_mul _ (u.isUnit.pow ν)]

end ShapeAux

section Facts

attribute [local instance] RegularFrame.isDomain_S

/-- Part (a) of the facts of the reformulation of Lemma 25 (`WeierstrassStepMem`, p. 271): see
`WeierstrassDatum.wR_mem_of_hasShape` (Lemma 22 for the frame `(S₀; w)` of `S`). -/
theorem weierstrassStep_mem [Hironaka.HironakaCitedResults.{u}] : WeierstrassStepMem.{u} := by
  intro R _ _ _ _ D f _ h4 P _ _ hz hP
  exact D.wR_mem_of_hasShape h4 hz hP

/-- Part (c)(i) of the facts of the reformulation: `y ∈ P ∩ S₀` generating `PR₁` (Nakayama, once
`w̄ = w/x ∈ M₁` by Lemma 24); see `WeierstrassDatum.exists_frameTransforms`. -/
theorem weierstrassStep_frames [Hironaka.HironakaCitedResults.{u}] : WeierstrassStepFrames.{u} := by
  intro R _ _ _ _ D f hTau hShape P _ _ hz hP T _ _ _ FT ν hν f₁ hf₁ hord₁
  exact D.exists_frameTransforms hTau hz (D.wR_mem_of_hasShape hShape hz hP) hP T FT hν hf₁ hord₁

/-- Part (c)(iii) of the facts of the reformulation: `h̄_Ā = h_Ā y^{-e}`, `p̄_j = y^{-j} p_j`
(p. 271: "(iii) of (c) is clear"). -/
theorem weierstrassStep_shape : WeierstrassStepShape.{u} := by
  intro R _ _ _ _ D f hTau hShape P _ _ hz hP T _ _ ν hν y FT' FT0 hyP hx hx0 f₂ hf₂ hord₂
  exact D.hasShape_transform hShape hz hP hν FT' FT0 hx hx0 hf₂ hord₂

/-- **The reduction of (ii) of (c) to `R` complete and the residue field algebraically closed**
(p. 271: "As in the proof of Lemma 22, the proof of (ii) of (c) can be reduced to the case in which
the residue field `k` of `S₀` is algebraically closed, so that `R₁` is residually rational over
`R`"; p. 270: "as in Lemma 20, we may assume that `S` and `R` are complete").

Printed route: `S̃₀` is the complete regular local ring with algebraically closed residue field of
Lemma 22 (`CompleteSepClosedExtension` of `S₀`; in characteristic `0` separably closed is
algebraically closed), `S̃ = S̃₀⟦w⟧` and `R̃ = S̃⟦z₁, …, z_r⟧` (`RegularFrame.baseChange`, applied
twice, p. 254), `R̃₁` the canonical lift of `R₁` (`BaseChangeLift`, p. 254), the frame transforms of
`(S̃; z)` in `R̃₁` and of `(S̃₀; w)` in `S̃₁` are the lifts of those of `R₁` with denominator the
image of `y` (`FrameTransform.exists_baseChange`, `exists_baseChange_inner`).  The case of
`WeierstrassStepTauRational` is then applied to the base changed datum.

Deviation from the paper (gap filled).  The paper states the reduction without proof.  Lean checks
(`weierstrassStepTau_of_rational`): the datum and `f` pass to `R̃` (the shape (4) by
`expCoeff_baseChangeHom`, the condition (3) by `grMapMax_mem_tauZSubmoduleStar`:
`WeierstrassDatum.hasShape_baseChange`, `inTauStar_baseChange`); `P̃ = PR̃` is prime with `R̃/P̃`
regular, `(z) ⊆ P̃` and `ν_{P̃}(f) = ν_{M̃}(f)`, the order of an element does not change
(`ordElem_map_of_mapsRSOP`); `R̃₁` is regular and residually rational over `R̃` (`S̃₀` has an
algebraically closed residue field), hence separable algebraic; the quotient `f̃₂ = β(f₂)` has the
same order `ν` and `τ_{(z̃/ỹ)}(f̃₂) = τ_{(z)}(f)` (`tauZ_map`, the invariance of `τ` under `β` and
`α`).  The hypothesis on `τ` is stated for a frame transform `FT` with an arbitrary denominator
`x`, the conclusion for the one with denominator `y`; both denominators generate `PR₁`, so they
differ by a unit, and `τ` is unchanged (`tauZ_congr_of_associated`).  The conclusion descends to
`R₁` as follows: the equality of the `τ_{(z̄,w̄)}` is the equality of `tauZ_map` twice, and `w̄ ∈ T*`
is recovered from `τ_{(z̄,w̄)}(f̄) = τ_{(z̄)}(f̄) - 1` with `τ_{(z̄)}(f̄) = τ_{(z)}(f) ≥ 1`
(`initialForm_mem_tauZSubmoduleStar_of_tauZ_snoc`, `WeierstrassDatum.one_le_tauZ`); faithful
flatness of `R → R̃` is not needed.  No new leaf. -/
theorem weierstrassStepTau_of_rational [Hironaka.HironakaCitedResults.{u}] (h : WeierstrassStepTauRational.{u}) :
    WeierstrassStepTau.{u} := by
  classical
  intro R _ _ _ _ D f hTau hShape P _ _ hz hP T _ _ hsep FT ν hν f₁ hf₁ hord₁ hτ y FT' FT0 hyP
    hx' hx0' f₂ hf₂
  have : IsRegularLocalRing FT'.TS.ring := FT'.isRegular
  have : IsRegularLocalRing FT0.TS.ring := FT0.isRegular
  have : IsDomain T.ring := Transforms.isDomain_of_isRegularLocalRing _
  -- Step A: `(FT, f₁)` replaced by `(FT', f₂)`
  have hFTx0 : FT'.x ≠ 0 := by
    intro h0
    have hxT : T.toRing T.x ∈ Ideal.span {FT'.x} := by
      rw [FT'.span_x]; exact Ideal.mem_map_of_mem _ T.x_mem
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hxT
    exact T.x_ne_zero (MonoidalTransform.toRing_injective T (hxT.trans (map_zero _).symm))
  have hord₂ : Ideal.ordElem (maximalIdeal T.ring) f₂ = ν :=
    (T.ordElem_eq_of_mul_pow_eq FT'.span_x FT.span_x (hf₂.trans hf₁.symm)).trans hord₁
  obtain ⟨ε, hε⟩ : Associated FT'.x FT.x :=
    Ideal.span_singleton_eq_span_singleton.mp (FT'.span_x.trans FT.span_x.symm)
  have hwass : ∀ j, Associated (FT.w j) (FT'.w j) := fun j => ⟨ε, by
    apply mul_left_cancel₀ hFTx0
    calc FT'.x * (FT.w j * ε) = (FT'.x * ε) * FT.w j := by ring
      _ = FT.x * FT.w j := by rw [hε]
      _ = T.toRing (D.F.z j) := FT.mul_w j
      _ = FT'.x * FT'.w j := (FT'.mul_w j).symm⟩
  have hfass : Associated f₁ f₂ := ⟨ε ^ ν, by
    apply mul_left_cancel₀ (pow_ne_zero ν hFTx0)
    calc FT'.x ^ ν * (f₁ * ↑(ε ^ ν)) = (FT'.x * ε) ^ ν * f₁ := by simp only [Units.val_pow_eq_pow_val]; ring
      _ = FT.x ^ ν * f₁ := by rw [hε]
      _ = T.toRing f := hf₁
      _ = FT'.x ^ ν * f₂ := hf₂.symm⟩
  have hτ₂ : tauZ T.ring FT'.w (fun _ : Fin 1 => f₂) = tauZ R D.F.z (fun _ : Fin 1 => f) :=
    (tauZ_congr_of_associated FT.w FT'.w f₁ f₂ hwass hfass).symm.trans hτ
  -- Step B: the base change `S₀ → S̃₀`, `S → S̃ = S̃₀⟦w⟧`, `R → R̃ = S̃⟦z⟧`
  obtain ⟨E⟩ := CompleteSepClosedExtension.nonempty D.F0.S
  have ha := D.F0.mapsRSOP_baseChangeHom E.hom E.mapsRSOP
  have hasep := D.F0.isResiduallySeparableAlgebraic_baseChangeHom E.hom
    E.isResiduallySeparableAlgebraic
  have hα := D.F.mapsRSOP_baseChangeHom (D.F0.baseChangeHom E.hom) ha
  have hsepα := D.F.isResiduallySeparableAlgebraic_baseChangeHom (D.F0.baseChangeHom E.hom) hasep
  have hsepα' := hsepα.isResiduallySeparable
  obtain ⟨L⟩ := BaseChangeLift.nonempty hα T
  obtain ⟨hPp, hPq⟩ := RingHom.MapsRSOP.isPrime_map_and_isRegularLocalRing_quotient hα
    (inferInstance : P.IsPrime) inferInstance
  have := hPp
  have := hPq
  have := L.isRegularLocalRing hα
  have := L.isLocalHom_toRing
  have hβ := L.mapsRSOP_β hα hsepα
  have hsepβ := (L.isResiduallySeparableAlgebraic_β hα hsepα).isResiduallySeparable
  have : IsSepClosed (ResidueField E.ring) := E.isSepClosed
  have : IsAdicComplete (maximalIdeal E.ring) E.ring := E.isAdicComplete
  have : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin D.F0.r) E.ring))
      (MvPowerSeries (Fin D.F0.r) E.ring) := D.F0.isAdicComplete_baseChange (S' := E.ring)
  have : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin D.F.r) (MvPowerSeries (Fin D.F0.r) E.ring)))
      (MvPowerSeries (Fin D.F.r) (MvPowerSeries (Fin D.F0.r) E.ring)) :=
    D.F.isAdicComplete_baseChange (S' := MvPowerSeries (Fin D.F0.r) E.ring)
  have : IsSepClosed (ResidueField (MvPowerSeries (Fin D.F0.r) E.ring)) :=
    D.F0.isSepClosed_residueField_baseChange (S' := E.ring)
  have hsc : IsSepClosed (ResidueField (MvPowerSeries (Fin D.F.r) (MvPowerSeries (Fin D.F0.r) E.ring))) :=
    D.F.isSepClosed_residueField_baseChange (S' := MvPowerSeries (Fin D.F0.r) E.ring)
  have : CharZero (ResidueField (MvPowerSeries (Fin D.F.r) (MvPowerSeries (Fin D.F0.r) E.ring))) :=
    (RingHom.charZero_iff (ResidueField.map
      (D.F.baseChangeHom (D.F0.baseChangeHom E.hom))).injective).mp inferInstance
  have : IsAlgClosed (ResidueField (MvPowerSeries (Fin D.F.r) (MvPowerSeries (Fin D.F0.r) E.ring))) :=
    IsSepClosed.isAlgClosed_of_perfectField _
  have hsepT' : RingHom.IsResiduallySeparableAlgebraic L.T'.toRing :=
    RingHom.isResiduallySeparableAlgebraic_of_isResiduallyRational _
      (L.isResiduallyRational hα hsc hsep)
  -- Step C: the lifts of the frame transforms
  have h7 : P.map T.toRing = Ideal.span {T.toRing (algebraMap D.F.S R
      (algebraMap D.F0.S D.F.S y))} := by rw [← hx', FT'.span_x]
  obtain ⟨FT'', hFT''x, hFT''w⟩ := RegularFrame.FrameTransform.exists_baseChange ha L FT'
    (algebraMap D.F0.S D.F.S y) hyP h7 hx'
  obtain ⟨FT0'', hFT0''x, hFT0''w⟩ := RegularFrame.FrameTransform.exists_baseChange_inner
    E.mapsRSOP L FT' y hyP hx' FT0 hx0' FT'' hFT''x
  have hFT''w' : FT''.w = fun j => L.β (FT'.w j) := funext hFT''w
  have hCy : algebraMap E.ring (MvPowerSeries (Fin D.F0.r) E.ring) (E.hom y) =
      D.F0.baseChangeHom E.hom (algebraMap D.F0.S D.F.S y) := by
    rw [D.F0.baseChangeHom_algebraMap E.hom y, algebraMap_mvPowerSeries_eq_C]
  have hxβ : FT''.x = L.β FT'.x := by
    rw [hFT''x, L.toRing_algebraMap_baseChange, hx']
  -- Step D: the case of an algebraically closed residue field, for the base changed data
  have key := h (MvPowerSeries (Fin D.F.r) (MvPowerSeries (Fin D.F0.r) E.ring))
    (D.baseChange E.ring) (D.F.baseChangeHom (D.F0.baseChangeHom E.hom) f)
    (D.inTauStar_baseChange E.hom E.mapsRSOP E.isResiduallySeparableAlgebraic hTau)
    (D.hasShape_baseChange E.hom E.mapsRSOP hShape)
    (P.map (D.F.baseChangeHom (D.F0.baseChangeHom E.hom)))
    (by
      rw [RegularFrame.idealZ, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have hj := Ideal.mem_map_of_mem (D.F.baseChangeHom (D.F0.baseChangeHom E.hom))
        (hz (Ideal.subset_span ⟨j, rfl⟩ : D.F.z j ∈ D.F.idealZ))
      rw [D.F.baseChangeHom_z' (D.F0.baseChangeHom E.hom) j] at hj
      exact hj)
    (by rw [ordElem_map_ideal_of_mapsRSOP _ hα P, hP, ordElem_map_of_mapsRSOP _ hα])
    L.T' hsepT' FT'' ν (hν.trans (ordElem_map_of_mapsRSOP _ hα f).symm) (L.β f₂)
    (by
      rw [hxβ, ← map_pow, ← map_mul, hf₂, L.toRing_baseChangeHom])
    ((ordElem_map_of_mapsRSOP L.β hβ f₂).trans hord₂)
    (by
      rw [hFT''w']
      have e1 := tauZ_map L.β hβ hsepβ FT'.w (fun _ : Fin 1 => f₂)
      have e2 := RegularFrame.tauZ_baseChangeHom (F := D.F) ha hasep (fun _ : Fin 1 => f)
      exact e1.trans (hτ₂.trans e2.symm))
    (E.hom y) FT'' FT0''
    (by
      have := D.F.algebraMap_mem_map_baseChangeHom (a := D.F0.baseChangeHom E.hom)
        (algebraMap D.F0.S D.F.S y) hyP
      rwa [← hCy] at this)
    (hFT''x.trans (by rw [← hCy]; rfl))
    hFT0''x (L.β f₂) (by
      rw [hxβ, ← map_pow, ← map_mul, hf₂, L.toRing_baseChangeHom])
  obtain ⟨-, hkey⟩ := key
  -- Step E: descent of the conclusion
  have hwβ : ((D.baseChange E.ring).transform FT'' FT0'').wR = L.β (D.transform FT' FT0).wR :=
    hFT0''w _
  have hb : tauZ T.ring (Fin.snoc FT'.w (D.transform FT' FT0).wR : Fin (D.F.r + 1) → T.ring)
        (fun _ : Fin 1 => f₂) =
      tauZ R (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) (fun _ : Fin 1 => f) := by
    have e1 := tauZ_map L.β hβ hsepβ
      (Fin.snoc FT'.w (D.transform FT' FT0).wR : Fin (D.F.r + 1) → T.ring)
      (fun _ : Fin 1 => f₂)
    have e2 := tauZ_map (D.F.baseChangeHom (D.F0.baseChangeHom E.hom)) hα hsepα'
      (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) (fun _ : Fin 1 => f)
    have c1 : (fun j => L.β ((Fin.snoc FT'.w (D.transform FT' FT0).wR :
        Fin (D.F.r + 1) → T.ring) j)) =
        (Fin.snoc FT''.w ((D.baseChange E.ring).transform FT'' FT0'').wR :
          Fin (D.F.r + 1) → _) := by
      refine (Fin.comp_snoc (L.β : T.ring → L.T'.ring) FT'.w (D.transform FT' FT0).wR).trans ?_
      rw [hFT''w', hwβ]
      rfl
    have c2 : (fun j => D.F.baseChangeHom (D.F0.baseChangeHom E.hom) ((Fin.snoc D.F.z D.wR :
        Fin (D.F.r + 1) → R) j)) =
        (Fin.snoc (D.baseChange E.ring).F.z (D.baseChange E.ring).wR : Fin (D.F.r + 1) → _) := by
      refine (Fin.comp_snoc (D.F.baseChangeHom (D.F0.baseChangeHom E.hom)) D.F.z D.wR).trans ?_
      have hz' : (D.F.baseChangeHom (D.F0.baseChangeHom E.hom) ∘ D.F.z) =
          (D.baseChange E.ring).F.z := funext fun j => D.F.baseChangeHom_z' _ j
      rw [hz', D.baseChangeHom_wR E.hom]
    rw [c1] at e1
    rw [c2] at e2
    exact e1.symm.trans (hkey.trans e2)
  refine ⟨?_, hb⟩
  have h1 := D.one_le_tauZ hTau
  have h2 := tauZ_snoc_eq_sub_one_of_mem D.F.z (fun _ : Fin 1 => f) D.wR hTau
  exact initialForm_mem_tauZSubmoduleStar_of_tauZ_snoc (z := FT'.w)
    (D.transform FT' FT0).injective_snoc (D.transform FT' FT0).extendsToRSOP_snoc
    (fun _ : Fin 1 => f₂) (hτ₂ ▸ h1) (hb.trans (h2.trans (by rw [hτ₂])))

section TauRational

attribute [local instance] Ideal.Quotient.field

open MvPolynomial

/-- **(ii) of (c) of the reformulation of Lemma 25 when `R` is complete with algebraically closed
residue field** (pp. 271--273), the case to which `weierstrassStepTau_of_rational` reduces it.

Printed route, step by step:
1. "Let us choose a minimal base `(y₁, ⋯, y_i)` of `Q₀` in such a way that `y = y_i` and
   `ȳ_j = y_j/y ∈ M₁` for `1 ≤ j ≤ i − 1`" (p. 271): `WeierstrassDatum.exists_adaptedCoords`
   (`R₁` is residually rational over `R`, its residue field being algebraic over the algebraically
   closed `k`).
2. "Lemma 24 shows that, if `τ = τ_{(z)}(f) − 1` (`= τ_{(z,w)}(f)`), there exist `τ` independent
   linear combinations of `y₁, ⋯, y_{i−1}` with coefficients in `S₀` which form a regular system of
   `τ_{(z,w)}`-parameters of `R` for `f`.  Therefore, we may assume that `(w, y₁, ⋯, y_τ)` is a
   regular system of `τ_{(z)}`-parameters of `R` for `f` (`τ ≤ i − 1`)" (pp. 271--272):
   `AdaptedCoords.exists_tauNormalized` (Lemma 24: `AdaptedCoords.tauStar_le_sup`), the new
   coordinates being `AdaptedCoords.recoord C 0`.
3. "Let `b = i − 1`.  Let us choose a regular system of parameters `(y₁, ⋯, y_b, y, x₁, ⋯, x_a)`
   of `S₀`.  Then […] `gr_M(R) = k[Z, W, Y₁, ⋯, Y_b, Y, X₁, ⋯, X_a]` […],
   `gr_{M₁}(R₁) = k[Z̄, W̄, Ȳ₁, ⋯, Ȳ_b, Y, X₁, ⋯, X_a]`" (p. 272): `AdaptedCoords.modelR`,
   `AdaptedCoords.modelT`.
4. "`φ` is a form only in `Z₁, ⋯, Z_r, W, Y₁, ⋯, Y_τ`, and
   `φ̄ = φ(Z̄₁, ⋯, Z̄_r, W̄, Ȳ₁, ⋯, Ȳ_τ) + φ̄*` with `φ̄* ∈ (Y, X₁, ⋯, X_a) gr_{M₁}(R₁)`" (p. 272):
   the first part from step 2 (`φ ∈ k[T] ⊆ k[Z, W, Y₁, …, Y_τ]`), the second from
   `AdaptedCoords.forms`.
5. "By the assumption (2), we can find a system of linear forms `(L, L₁, ⋯, L_τ)` in
   `Y, X₁, ⋯, X_a` with coefficients in `k` such that
   `φ̄ = φ(Z̄₁, ⋯, Z̄_r, W̄ + L, Ȳ₁ + L₁, ⋯, Ȳ_τ + L_τ)`" (p. 272): `exists_lift`, the
   assumption (2) entering as `τ_{(z̄)}(f̄) = τ_{(z)}(f)`, i.e. the equality of the dimensions of
   the two spaces `T*`.
6. "We can find linear combinations `v₁, ⋯, v_τ` of `y, x₁, ⋯, x_a` with coefficients in `S₀` such
   that `L_j` is the initial form of `v_j` […].  We may replace `y_j` by `y_j + v_j y` for
   `1 ≤ j ≤ τ` without affecting any of the assumptions on `(y₁, ⋯, y_b)` in the above argument, so
   that we may assume that `L₁ = ⋯ = L_τ = 0`.  We then have
   `φ̄ = φ(Z̄₁, ⋯, Z̄_r, W̄ + L, Ȳ₁, ⋯, Ȳ_τ)`" (p. 272): `AdaptedCoords.exists_shift` (the
   coordinates `AdaptedCoords.recoord 1 v`; the picture of `gr_M(R)` is unchanged, that of `gr_{M₁}(R₁)` is
   composed with `Ȳ_j ↦ Ȳ_j + L_j`).
7. "Hence `φ̄` is of the form `φ̄ = ψ̄ + cZ̄^Ā(W̄^e + λ̄₂W̄^{e-2} + ⋯ + λ̄_e)`" (p. 272), "On the
   other hand, `φ` is of the form `φ = ψ + cZ^Ā(W^e + λ₂W^{e-2} + ⋯ + λ_e)`" (p. 273):
   `IsAdaptedModel.initialForm_coeff` for `f` and, with the shape (4) of `f̄`
   (`WeierstrassDatum.hasShape_transform_of`, the same `Ā` and `e`), for `f̄`.
8. "Therefore the equality `φ̄ = φ(Z̄₁, ⋯, Z̄_r, W̄ + L, Ȳ₁, ⋯, Ȳ_τ)` implies […]. It follows that
   `eL = 0`, hence `L = 0`.  Thus `φ̄ = φ(Z̄₁, ⋯, Z̄_r, W̄, Ȳ₁, ⋯, Ȳ_τ)`" (p. 273):
   `eq_zero_of_aeval_add_of_coeff`.
9. "It follows that `(w̄)` can be extended to a regular system of `τ_{(z̄)}`-parameters of `R₁` for
   `f̄`, and that `τ_{(z̄,w̄)}(f̄) = τ_{(z w)}(f) (= τ)`" (p. 273): `φ̄` and `φ` being the same
   polynomial, the two spaces `T` (`SemiModel.singleton_minimal`) and hence the two spaces `T*`
   correspond; so `(w̄, ȳ₁, …, ȳ_τ)` is a regular system of `τ_{(z̄)}`-parameters of `R₁` for `f̄`
   (`AdaptedCoords.span_eq_of_modelT_pull_eq`), and the ranks of the two `T*` are equal. -/
theorem weierstrassStepTau_rational [Hironaka.HironakaCitedResults.{u}] : WeierstrassStepTauRational.{u} := by
  classical
  intro R _ _ _ _ _ _ D f hTau hShape P _ _ hz hP T _ _ hsep FT ν hν f₁ hf₁ hord₁ hτ y FT' FT0 hyP
    hx' hx0' f₂ hf₂
  have : IsRegularLocalRing FT'.TS.ring := FT'.isRegular
  have : IsRegularLocalRing FT0.TS.ring := FT0.isRegular
  have : IsDomain T.ring := Transforms.isDomain_of_isRegularLocalRing _
  -- Step A: `(FT, f₁)` replaced by `(FT', f₂)` (as in `weierstrassStepTau_of_rational`)
  have hFTx0 : FT'.x ≠ 0 := by
    intro h0
    have hxT : T.toRing T.x ∈ Ideal.span {FT'.x} := by
      rw [FT'.span_x]; exact Ideal.mem_map_of_mem _ T.x_mem
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hxT
    exact T.x_ne_zero (MonoidalTransform.toRing_injective T (hxT.trans (map_zero _).symm))
  have hord₂ : Ideal.ordElem (maximalIdeal T.ring) f₂ = ν :=
    (T.ordElem_eq_of_mul_pow_eq FT'.span_x FT.span_x (hf₂.trans hf₁.symm)).trans hord₁
  obtain ⟨ε, hε⟩ : Associated FT'.x FT.x :=
    Ideal.span_singleton_eq_span_singleton.mp (FT'.span_x.trans FT.span_x.symm)
  have hwass : ∀ j, Associated (FT.w j) (FT'.w j) := fun j => ⟨ε, by
    apply mul_left_cancel₀ hFTx0
    calc FT'.x * (FT.w j * ε) = (FT'.x * ε) * FT.w j := by ring
      _ = FT.x * FT.w j := by rw [hε]
      _ = T.toRing (D.F.z j) := FT.mul_w j
      _ = FT'.x * FT'.w j := (FT'.mul_w j).symm⟩
  have hfass : Associated f₁ f₂ := ⟨ε ^ ν, by
    apply mul_left_cancel₀ (pow_ne_zero ν hFTx0)
    calc FT'.x ^ ν * (f₁ * ↑(ε ^ ν)) = (FT'.x * ε) ^ ν * f₁ := by
          simp only [Units.val_pow_eq_pow_val]; ring
      _ = FT.x ^ ν * f₁ := by rw [hε]
      _ = T.toRing f := hf₁
      _ = FT'.x ^ ν * f₂ := hf₂.symm⟩
  have hτ₂ : tauZ T.ring FT'.w (fun _ : Fin 1 => f₂) = tauZ R D.F.z (fun _ : Fin 1 => f) :=
    (tauZ_congr_of_associated FT.w FT'.w f₁ f₂ hwass hfass).symm.trans hτ
  -- Step B: `R₁` is residually rational over `R`
  have hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing := by
    let _ := (ResidueField.map T.toRing).toAlgebra
    have hsep' : Algebra.IsSeparable (ResidueField R) (ResidueField T.ring) := hsep
    have : Algebra.IsAlgebraic (ResidueField R) (ResidueField T.ring) := inferInstance
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField R)
      (K := ResidueField T.ring)).2
  obtain ⟨ρ, hρ⟩ := exists_residueEquiv hrat
  set K := T.ring ⧸ maximalIdeal T.ring with hK
  have : CharZero K := by
    have : CharZero (R ⧸ maximalIdeal R) := inferInstanceAs (CharZero (ResidueField R))
    exact (RingHom.charZero_iff (ρ : K →+* R ⧸ maximalIdeal R).injective).mpr this
  -- Step 1 (p. 271): the minimal base `(y₁, …, y_b, y)` of `Q₀` with `ȳ_j ∈ M₁`
  obtain ⟨t, s, ⟨c₀⟩⟩ := D.exists_adaptedCoords hrat y FT' FT0 hyP hx' hx0'
  -- Step 2 (pp. 271--272): Lemma 24; "we may assume that `(w, y₁, ⋯, y_τ)` is a regular system of
  -- `τ_{(z)}`-parameters of `R` for `f`"
  obtain ⟨C, hC, hτt, hnorm⟩ := c₀.exists_tauNormalized hTau hz hP hν hf₂ hord₂
  set c₁ := c₀.recoord C hC 0 (fun _ => zero_mem _) with hc₁
  set τ := tauZ R (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) (fun _ : Fin 1 => f) with hτdef
  set V : Set (Fin c₁.n) :=
    Set.range c₁.zwI ∪ Set.range (fun j : Fin τ => c₁.yI (Fin.castLE hτt j)) with hVdef
  have hVR : (c₁.modelR ρ).pull (tauZSubmoduleStar R D.F.z (fun _ : Fin 1 => f)) =
      Submodule.span K (X '' V) := c₁.modelR_pull_eq ρ hτt _ hnorm
  -- Step 3 (p. 272): the polynomial pictures `M`, `M₁` in these coordinates
  set M := c₁.modelR ρ with hMdef
  set M₁ := c₁.modelT with hM₁def
  have hM := c₁.isAdaptedModel ρ
  have hM₁ := c₁.isAdaptedModel_transform
  have hfP : f ∈ P ^ ν := Ideal.mem_pow_of_ordElem (hP.trans hν.symm)
  obtain ⟨hpU, hqp⟩ := c₁.forms ρ hρ ν f f₂ hfP hν.symm hord₂ hf₂
  set p := M.Φ.symm (initialForm (maximalIdeal R) f) with hpdef
  set q := M₁.Φ.symm (initialForm (maximalIdeal T.ring) f₂) with hqdef
  have hθ : killB (k := K) (fun v => v ∈ c₁.U) q = p := by
    have h1 : killB (k := K) (fun v => v ∈ c₁.U) q = projOut c₁.U q := rfl
    rw [h1, projOut_sub_of_mem_outIdeal c₁.U hqp, projOut_of_mem_supported c₁.U hpU]
  obtain ⟨hTp1, hpTp, hTpmin⟩ := M.singleton_minimal hM.graded f
  obtain ⟨hTq1, hqTq, -⟩ := M₁.singleton_minimal hM₁.graded f₂
  set Tp := M.pull (tauZSubmodule R (fun _ : Fin 1 => f)) with hTp
  set Tq := M₁.pull (tauZSubmodule T.ring (fun _ : Fin 1 => f₂)) with hTq
  set Zs : Submodule K (MvPolynomial (Fin c₁.n) K) :=
    Submodule.span K (MvPolynomial.X '' Set.range c₁.zI) with hZs
  have hZM : M.pull (Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm D.F.z))) = Zs :=
    M.pull_span_range (frameForm D.F.z) c₁.zI hM.Φ_X_zI
  have hZM₁ : M₁.pull (Submodule.span (T.ring ⧸ maximalIdeal T.ring)
      (Set.range (frameForm FT'.w))) = Zs :=
    M₁.pull_span_range (frameForm FT'.w) c₁.zI hM₁.Φ_X_zI
  have hStarP : M.pull (tauZSubmoduleStar R D.F.z (fun _ : Fin 1 => f)) = Tp ⊔ Zs := by
    unfold tauZSubmoduleStar
    rw [M.pull_sup, hZM]
  have hStarQ : M₁.pull (tauZSubmoduleStar T.ring FT'.w (fun _ : Fin 1 => f₂)) = Tq ⊔ Zs := by
    unfold tauZSubmoduleStar
    rw [M₁.pull_sup, hZM₁]
  -- "`φ` is a form only in `Z₁, ⋯, Z_r, W, Y₁, ⋯, Y_τ`"
  have hpV : p ∈ MvPolynomial.supported K V := by
    rw [MvPolynomial.supported_eq_adjoin_X]
    have h1 : Tp ≤ Submodule.span K (X '' V) := by
      rw [← hVR, hStarP]
      exact le_sup_left
    have h2 := Algebra.adjoin_mono (R := K) (SetLike.coe_subset_coe.mpr h1) hpTp
    rwa [Algebra.adjoin_span] at h2
  -- Step 5 (p. 272): "By the assumption (2), we can find […] `(L, L₁, ⋯, L_τ)`"
  have hdim : Module.finrank K (Tq ⊔ Zs : Submodule K (MvPolynomial (Fin c₁.n) K)) ≤
      Module.finrank K (Tp ⊔ Zs : Submodule K (MvPolynomial (Fin c₁.n) K)) := by
    rw [← hStarP, ← hStarQ, M.finrank_pull, M₁.finrank_pull]
    have h1 := finrank_tauZSubmoduleStar_eq D.F.z_injective D.F.extends_rsop
      (fun _ : Fin 1 => f)
    have h2 : Module.finrank (T.ring ⧸ maximalIdeal T.ring)
        (tauZSubmoduleStar T.ring FT'.w (fun _ : Fin 1 => f₂)) =
        tauZ T.ring FT'.w (fun _ : Fin 1 => f₂) + D.F.r :=
      finrank_tauZSubmoduleStar_eq (D.transform FT' FT0).F.z_injective
        (D.transform FT' FT0).F.extends_rsop (fun _ : Fin 1 => f₂)
    rw [h1, h2, hτ₂]
  have hZsA : Zs ≤ linSpan (k := K) {v | v ∈ c₁.U} :=
    Submodule.span_mono (Set.image_mono c₁.range_zI_subset_U)
  have hpA : p ∈ Algebra.adjoin K (MvPolynomial.X '' {v | v ∈ c₁.U} :
      Set (MvPolynomial (Fin c₁.n) K)) := by
    rw [← MvPolynomial.supported_eq_adjoin_X]
    exact hpU
  obtain ⟨ℓ, hℓB, hℓA, hℓz, hqℓ, -⟩ := exists_lift (isA := fun v => v ∈ c₁.U) p q hθ hpA Tp Tq
    Zs hTpmin hTq1 hqTq hZsA hdim
  -- Step 6 (p. 272): "We may replace `y_j` by `y_j + v_j y` for `1 ≤ j ≤ τ` […] so that we may
  -- assume that `L₁ = ⋯ = L_τ = 0`"
  obtain ⟨v, hv, hMR, hMT⟩ := c₁.exists_shift ρ hρ hτt ℓ hℓB
  set c₂ := c₁.recoord 1 isUnit_one v hv with hc₂
  set σ₂ := aeval (R := T.ring ⧸ maximalIdeal T.ring) (fun i => X i +
    if i ∈ Set.range (fun j : Fin τ => c₁.yI (Fin.castLE hτt j)) then ℓ i else 0) with hσ₂
  obtain ⟨ℓ₁, hℓ₁w, hℓ₁o⟩ : ∃ ℓ₁ : Fin c₁.n → type_of% (ℓ c₁.wI),
      ℓ₁ c₁.wI = ℓ c₁.wI ∧ ∀ i, i ≠ c₁.wI → ℓ₁ i = 0 :=
    ⟨fun i => if i = c₁.wI then ℓ c₁.wI else 0, ite_eq_left rfl, fun i h => ite_eq_right h⟩
  set p₂ := (c₂.modelR ρ).Φ.symm (initialForm (maximalIdeal R) f) with hp₂def
  set q₂ := c₂.modelT.Φ.symm (initialForm (maximalIdeal T.ring) f₂) with hq₂def
  have hp₂ : p₂ = p := congrArg (fun Φ => RingEquiv.symm Φ (initialForm (maximalIdeal R) f)) hMR
  have hσ₂q : σ₂ q₂ = q := M₁.Φ.injective
    (((hMT q₂).symm.trans (c₂.modelT.Φ.apply_symm_apply _)).trans (M₁.Φ.apply_symm_apply _).symm)
  have hσ₂inj : Function.Injective σ₂ := fun a b hab =>
    c₂.modelT.Φ.injective ((hMT a).trans ((congrArg M₁.Φ hab).trans (hMT b).symm))
  -- `σ₂` fixes the linear forms in `Y, X₁, …, X_a`
  have hσ₂B : ∀ t ∈ linSpan (k := K) {v | v ∉ c₁.U}, σ₂ t = t := by
    intro t ht
    refine Submodule.span_induction (p := fun t _ => σ₂ t = t) ?_ (by simp) ?_ ?_ ht
    · rintro _ ⟨i, hi, rfl⟩
      rw [hσ₂, aeval_X, ite_eq_right_of_eq_false _ _ (eq_false ?_), add_zero]
      rintro ⟨j, rfl⟩
      exact hi (c₁.yI_mem_U _)
    · intro a b _ _ ha hb
      rw [map_add, ha, hb]
    · intro r a _ ha
      rw [map_smul, ha]
  -- "We then have `φ̄ = φ(Z̄₁, ⋯, Z̄_r, W̄ + L, Ȳ₁, ⋯, Ȳ_τ)`"
  have hcomp : σ₂ (aeval (fun i => X i + ℓ₁ i) p) = aeval (fun i => X i + ℓ i) p := by
    have hV' : p ∈ Algebra.adjoin K (X '' V : Set (MvPolynomial (Fin c₁.n) K)) := by
      rw [← MvPolynomial.supported_eq_adjoin_X]; exact hpV
    have : Algebra.adjoin K (X '' V : Set (MvPolynomial (Fin c₁.n) K)) ≤
        AlgHom.equalizer (σ₂.comp (aeval (fun i => X i + ℓ₁ i))) (aeval (fun i => X i + ℓ i)) := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨i, hi, rfl⟩
      show σ₂ (aeval (fun i => X i + ℓ₁ i) (X i)) = aeval (fun i => X i + ℓ i) (X i)
      rw [aeval_X, aeval_X]
      rcases hi with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · -- `W ↦ W + L`
          rw [c₁.zwI_last, hℓ₁w, map_add, hσ₂B _ (hℓB _), hσ₂, aeval_X,
            ite_eq_right_of_eq_false _ _ (eq_false ?_), add_zero]
          rintro ⟨j, hj⟩
          have h1 : (c₁.yI (Fin.castLE hτt j)).val = c₁.wI.val := congrArg Fin.val hj
          rw [c₁.yI_val, c₁.wI_val] at h1
          omega
        · -- `Z_j ↦ Z_j`
          have hzw : c₁.zwI (Fin.castSucc j) ≠ c₁.wI := fun h => c₁.wI_notMem ⟨j, h⟩
          have hℓ0 : ℓ (c₁.zwI (Fin.castSucc j)) = 0 :=
            hℓz _ (Submodule.subset_span ⟨c₁.zI j, ⟨j, rfl⟩, rfl⟩)
          rw [hℓ₁o _ hzw, add_zero, hσ₂, aeval_X, hℓ0, add_zero,
            ite_eq_right_of_eq_false _ _ (eq_false ?_), add_zero]
          rintro ⟨k, hk⟩
          have h1 := congrArg Fin.val hk
          rw [c₁.yI_val, c₁.zwI_castSucc, c₁.zI_val] at h1
          have := j.2
          omega
      · -- `Ȳ_j ↦ Ȳ_j + L_j`
        have hyw : c₁.yI (Fin.castLE hτt j) ≠ c₁.wI := by
          intro h
          have h1 := congrArg Fin.val h
          rw [c₁.yI_val, c₁.wI_val] at h1
          omega
        rw [hℓ₁o _ hyw, add_zero, hσ₂, aeval_X, ite_eq_left ⟨j, rfl⟩]
    exact this hV'
  have hq₂ : q₂ = aeval (fun i => X i + ℓ₁ i) p₂ := by
    apply hσ₂inj
    rw [hσ₂q, hp₂, hcomp, hqℓ]
  -- Step 7 (pp. 272--273): the shapes of `φ` and `φ̄`
  obtain ⟨Ā, e, u, pj, hu, he, hdeg, hcoef⟩ := hShape
  obtain ⟨u', pj', hu', hdeg', hcoef'⟩ :=
    D.hasShape_transform_of hu hdeg hcoef hz hP hν FT' FT0 hx' hx0' hf₂ hord₂
  obtain ⟨hp₀, hpsupp⟩ := (c₂.isAdaptedModel ρ).initialForm_coeff hu he hdeg hcoef
  obtain ⟨-, hqsupp⟩ := c₂.isAdaptedModel_transform.initialForm_coeff hu' he hdeg' hcoef'
  have hp₀' : p₂.coeff (Finsupp.mapDomain c₁.zI Ā + Finsupp.single c₁.wI e) ≠ 0 := hp₀
  have hpsupp' : ∀ m ∈ p₂.support, (∀ j : Fin D.F.r, m (c₁.zI j) = Ā j) →
      m = Finsupp.mapDomain c₁.zI Ā + Finsupp.single c₁.wI e ∨ m c₁.wI + 2 ≤ e := hpsupp
  have hqsupp' : ∀ m ∈ q₂.support, (∀ j : Fin D.F.r, m (c₁.zI j) = Ā j) →
      m = Finsupp.mapDomain c₁.zI Ā + Finsupp.single c₁.wI e ∨ m c₁.wI + 2 ≤ e := hqsupp
  have hmd : ∀ j, (Finsupp.mapDomain c₁.zI Ā) (c₁.zI j) = Ā j := fun j =>
    Finsupp.mapDomain_apply_of_injective c₁.zI_injective Ā j
  have hmdw : ∀ i, i ∉ Set.range c₁.zI → (Finsupp.mapDomain c₁.zI Ā) i = 0 := by
    intro i hi
    rw [← Finsupp.notMem_support_iff]
    intro hmem
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
    exact hi ⟨j, hj⟩
  have hzpart : ∀ m : Fin c₁.n →₀ ℕ,
      (∀ i ∈ Set.range c₁.zI, m i = (Finsupp.mapDomain c₁.zI Ā) i) →
      ∀ j, m (c₁.zI j) = Ā j := fun m hm j => by
    rw [hm (c₁.zI j) ⟨j, rfl⟩, hmd]
  -- Step 8 (p. 273): "It follows that `eL = 0`, hence `L = 0`"
  have hℓw : ℓ₁ c₁.wI = 0 := by
    refine eq_zero_of_aeval_add_of_coeff (fun v => v ∈ c₁.U) (Set.range c₁.zI) c₁.wI c₁.wI_mem_U
      c₁.wI_notMem (fun i hi => c₁.range_zI_subset_U hi) ℓ₁ ?_ ?_ ?_ p₂ q₂ hq₂
      (Finsupp.mapDomain c₁.zI Ā) hmdw e he hp₀' ?_ ?_
    · intro i
      by_cases h : i = c₁.wI
      · rw [h, hℓ₁w]
        exact hℓB _
      · rw [hℓ₁o i h]
        exact zero_mem _
    · intro i hi
      refine hℓ₁o i ?_
      rintro rfl
      exact hi c₁.wI_mem_U
    · intro i hi
      refine hℓ₁o i ?_
      rintro rfl
      exact c₁.wI_notMem hi
    · exact fun m hm hmz => hpsupp' m hm (hzpart m hmz)
    · intro m hm hmz
      rcases hqsupp' m hm (hzpart m hmz) with h | h
      · rw [h, Finsupp.add_apply, hmdw c₁.wI c₁.wI_notMem, Finsupp.single_eq_same]
        omega
      · omega
  have hℓ₁0 : ∀ i, ℓ₁ i = 0 := by
    intro i
    by_cases h : i = c₁.wI
    · rw [h]
      exact hℓw
    · exact hℓ₁o i h
  -- "Thus `φ̄ = φ(Z̄₁, ⋯, Z̄_r, W̄, Ȳ₁, ⋯, Ȳ_τ)`"
  have hqp₂ : q₂ = p₂ := by
    rw [hq₂]
    simp only [hℓ₁0, add_zero]
    exact aeval_X_left_apply p₂
  -- Step 9 (p. 273): "It follows that `(w̄)` can be extended to a regular system of
  -- `τ_{(z̄)}`-parameters of `R₁` for `f̄`, and that `τ_{(z̄,w̄)}(f̄) = τ_{(z w)}(f) (= τ)`"
  obtain ⟨hTp1₂, hpTp₂, hTpmin₂⟩ := (c₂.modelR ρ).singleton_minimal (c₂.isAdaptedModel ρ).graded f
  obtain ⟨hTq1₂, hqTq₂, hTqmin₂⟩ :=
    c₂.modelT.singleton_minimal c₂.isAdaptedModel_transform.graded f₂
  have hTT : c₂.modelT.pull (tauZSubmodule T.ring (fun _ : Fin 1 => f₂)) =
      (c₂.modelR ρ).pull (tauZSubmodule R (fun _ : Fin 1 => f)) := by
    apply le_antisymm
    · refine hTqmin₂ _ hTp1₂ ?_
      rw [← hq₂def, hqp₂]
      exact hpTp₂
    · refine hTpmin₂ _ hTq1₂ ?_
      rw [← hp₂def, ← hqp₂]
      exact hqTq₂
  have hZM₂ : (c₂.modelR ρ).pull (Submodule.span (R ⧸ maximalIdeal R)
      (Set.range (frameForm D.F.z))) = Zs :=
    (c₂.modelR ρ).pull_span_range (frameForm D.F.z) c₁.zI (c₂.isAdaptedModel ρ).Φ_X_zI
  have hZM₁₂ : c₂.modelT.pull (Submodule.span (T.ring ⧸ maximalIdeal T.ring)
      (Set.range (frameForm FT'.w))) = Zs :=
    c₂.modelT.pull_span_range (frameForm FT'.w) c₁.zI c₂.isAdaptedModel_transform.Φ_X_zI
  have hpullR : (c₂.modelR ρ).pull (tauZSubmoduleStar R D.F.z (fun _ : Fin 1 => f)) =
      M.pull (tauZSubmoduleStar R D.F.z (fun _ : Fin 1 => f)) :=
    SemiModel.pull_eq_of_Φ_eq hMR _
  have hStar : c₂.modelT.pull (tauZSubmoduleStar T.ring FT'.w (fun _ : Fin 1 => f₂)) =
      Submodule.span K (X '' V) := by
    rw [← hVR, ← hpullR]
    unfold tauZSubmoduleStar
    rw [SemiModel.pull_sup, SemiModel.pull_sup, hTT, hZM₂, hZM₁₂]
  -- `(w̄, ȳ₁, ⋯, ȳ_τ)` is a regular system of `τ_{(z̄)}`-parameters of `R₁` for `f̄`
  have hparams := c₂.span_eq_of_modelT_pull_eq hτt _ hStar
  have hTau₁ : (D.transform FT' FT0).InTauStar f₂ := by
    show initialForm (maximalIdeal T.ring) (D.transform FT' FT0).wR ∈
      tauZSubmoduleStar T.ring FT'.w (fun _ : Fin 1 => f₂)
    rw [← hparams]
    refine Submodule.subset_span (Or.inl ⟨Fin.last D.F.r, ?_⟩)
    have h := (D.transform FT' FT0).frameForm_snoc_wR
    change frameForm (Fin.snoc FT'.w (D.transform FT' FT0).wR : Fin (D.F.r + 1) → T.ring) =
      Fin.snoc (frameForm FT'.w) (initialForm (maximalIdeal T.ring) (D.transform FT' FT0).wR)
      at h
    rw [h, Fin.snoc_last]
  refine ⟨hTau₁, ?_⟩
  have hrank : Module.finrank K (c₂.modelT.pull
        (tauZSubmoduleStar T.ring FT'.w (fun _ : Fin 1 => f₂))) =
      Module.finrank K (M.pull (tauZSubmoduleStar R D.F.z (fun _ : Fin 1 => f))) := by
    rw [hStar, hVR]
  rw [M.finrank_pull, c₂.modelT.finrank_pull] at hrank
  have e1 := tauZ_snoc_eq_sub_one_of_mem D.F.z (fun _ : Fin 1 => f) D.wR hTau
  have e2 := tauZ_snoc_eq_sub_one_of_mem FT'.w (fun _ : Fin 1 => f₂)
    (D.transform FT' FT0).wR hTau₁
  rw [e2, hτdef, e1]
  unfold tauZ
  rw [hrank]

end TauRational

theorem weierstrassStep_tau [Hironaka.HironakaCitedResults.{u}] : WeierstrassStepTau.{u} :=
  weierstrassStepTau_of_rational weierstrassStepTau_rational

end Facts

section Reformulation

attribute [local instance] RegularFrame.isDomain_S

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] in
/-- `T(w) = y · w̄`: with the denominators of (c)(i), the image of `w` in `R₁` is the denominator
times the image of `w̄ = w/y`. -/
theorem WeierstrassDatum.toRing_wR_eq_mul_transform (D : WeierstrassDatum R) {P : Ideal R}
    [P.IsPrime] {T : MonoidalTransform R P} [IsRegularLocalRing T.ring]
    (FT : D.F.FrameTransform T) (FT0 : D.F0.FrameTransform FT.TS) (y : D.F0.S)
    (hFT : FT.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)))
    (hFT0 : FT0.x = FT.TS.toRing (algebraMap D.F0.S D.F.S y)) :
    T.toRing D.wR = FT.x * (D.transform FT FT0).wR := by
  have hcomm : ∀ s : D.F.S, FT.β (FT.TS.toRing s) = T.toRing (algebraMap D.F.S R s) := fun s =>
    RingHom.congr_fun FT.canonical.comm s
  have hmul := FT0.mul_w (Fin.cast D.rank_eq_one.symm 0)
  show T.toRing (algebraMap D.F.S R D.w) = _
  rw [← hcomm]
  have h1 : FT.TS.toRing D.w = FT0.x * FT0.w (Fin.cast D.rank_eq_one.symm 0) := hmul.symm
  rw [h1, map_mul, hFT0, hcomm, hFT]
  rfl

open Classical in
/-- **One step of the facts (c) of the reformulation of Lemma 25**, with the hypotheses (1), (2)
used only through their consequences at the two indices `ᾱ = 0, 1`: given the datum `D`, `f` with
`w ∈ T*` and the shape (4), a prime center `P ⊇ (z)` with `ν_P(f) = ν = ν_M(f)`, a frame transform
`FT` of `(S; z)` in the residually separable algebraic monoidal transform `T`, and the quotient
`f₁ = x^{-ν} f` with `ν_{M₁}(f₁) = ν` and `τ_{(z̄)}(f₁) = τ_{(z)}(f)`, there are the denominator
`y ∈ S₀` and the frame transforms of (c)(i), and `f̄ = y^{-ν} f` satisfies (c)(ii) and (c)(iii).
This is the internal step of `weierstrassDatum_facts`, which states the facts with the hypotheses
(1), (2) as printed. -/
theorem weierstrassStep_next [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    [CharZero (ResidueField R)] (D : WeierstrassDatum R) (f : R) (hInTau : D.InTauStar f)
    (hShape : D.HasShape f) (P : Ideal R) [P.IsPrime] [IsRegularLocalRing (R ⧸ P)]
    (hzP : D.F.idealZ ≤ P) (hb : Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f)
    (T : MonoidalTransform R P) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing)
    (FT : D.F.FrameTransform T) (ν : ℕ) (hν : (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) f)
    (f₁ : T.ring) (hf₁ : FT.x ^ ν * f₁ = T.toRing f)
    (hord₁ : Ideal.ordElem (maximalIdeal T.ring) f₁ = ν)
    (hτ : tauZ T.ring FT.w (fun _ : Fin 1 => f₁) = tauZ R D.F.z (fun _ : Fin 1 => f)) :
    ∃ (y : D.F0.S) (FT' : D.F.FrameTransform T) (FT0 : D.F0.FrameTransform FT'.TS),
      algebraMap D.F.S R (algebraMap D.F0.S D.F.S y) ∈ P ∧
      FT'.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)) ∧
      FT0.x = FT'.TS.toRing (algebraMap D.F0.S D.F.S y) ∧
      (∀ j, FT'.w j ∈ maximalIdeal T.ring) ∧
      (D.transform FT' FT0).wR ∈ maximalIdeal T.ring ∧
      T.toRing D.wR = FT'.x * (D.transform FT' FT0).wR ∧
      ∃ f₂ : T.ring, FT'.x ^ ν * f₂ = T.toRing f ∧ Ideal.ordElem (maximalIdeal T.ring) f₂ = ν ∧
        (D.transform FT' FT0).TauParams f₂ ∧
        tauZ T.ring (Fin.snoc FT'.w (D.transform FT' FT0).wR : Fin (D.F.r + 1) → T.ring)
            (fun _ : Fin 1 => f₂) =
          tauZ R (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) (fun _ : Fin 1 => f) ∧
        (D.transform FT' FT0).HasShape f₂ := by
  obtain ⟨y, FT', FT0, hyP, hx', hx0'⟩ := weierstrassStep_frames R D f hInTau hShape P hzP hb T hsep
    FT ν hν f₁ hf₁ hord₁
  have hdiv : ∃ f₂ : T.ring, FT'.x ^ ν * f₂ = T.toRing f := by
    have hfP : f ∈ P ^ ν := Ideal.mem_pow_of_ordElem (hb.trans hν.symm)
    have hmem : T.toRing f ∈ (P ^ ν).map T.toRing := Ideal.mem_map_of_mem _ hfP
    rw [Ideal.map_pow, ← FT'.span_x, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  obtain ⟨f₂, hf₂⟩ := hdiv
  have hord₂ : Ideal.ordElem (maximalIdeal T.ring) f₂ = ν :=
    (T.ordElem_eq_of_mul_pow_eq FT'.span_x FT.span_x (hf₂.trans hf₁.symm)).trans hord₁
  have hT := weierstrassStep_tau R D f hInTau hShape P hzP hb T hsep FT ν hν f₁ hf₁ hord₁ hτ y FT'
    FT0 hyP hx' hx0' f₂ hf₂
  exact ⟨y, FT', FT0, hyP, hx', hx0', fun j => FT'.extends_rsop.mem_maximalIdeal
    (Finset.mem_image_of_mem _ (Finset.mem_univ j)), (D.transform FT' FT0).wR_mem,
    D.toRing_wR_eq_mul_transform FT' FT0 y hx' hx0', f₂, hf₂, hord₂,
    ((D.transform FT' FT0).inTauStar_iff_tauParams f₂).mp hT.1, hT.2,
    weierstrassStep_shape R D f hInTau hShape P hzP hb T ν hν y FT' FT0 hyP hx' hx0' f₂ hf₂ hord₂⟩

open Classical in
/-- **The reformulation of Lemma 25** (pp. 270--271), as printed: "Let `R` be a regular local ring
whose residue field has characteristic zero, `J` an ideal in `R`, `(S; z₁, …, z_r)` a regular frame
of `R` and `(S₀; w)` a regular frame of `S`.  Let `f` be an element of `R`.  Suppose:
(1) `(z₁, …, z_r)` is `J`-stable, i.e., `(S; z₁, …, z_r)` is `J`-stable, (2) `f` is
`(J, τ_{(z)})`-stable, (3) `(w)` can be extended to a regular system of `τ_{(z)}`-parameters of `R`
for `f`, and (4) `f` can be written in the form `f = g + u z^Ā (w^e + p₂ w^{e-2} + ⋯ + p_e)` where
`g = ∑_{A ≠ Ā} h_A z^A` with `h_A ∈ S`, `u` = a unit in `S`, `e = ν_M(f) − |Ā| > 0`, and `p_j ∈ S₀`
for `2 ≤ j ≤ e`.  Let `P` be any prime ideal in `R` which is a permissible center for `J`, `R₁` a
monoidal transform of `R` with center `P` which is residually algebraic (necessarily, separable
algebraic) over `R`, and `J₁` the strict transform of `J` in `R₁`.  We shall prove that
(a) `P ⊇ (z₁, …, z_r, w)R`, (b) `ν_P(f) = ν` (throughout, `ν` denotes `ν_M(f)`), (c) if
`ν*(J₁) = ν*(J)` and `τ*(J₁) = τ*(J)`, then there exists `y ∈ P ∩ S₀` such that `PR₁ = (y)R₁` and
such that: (i) `z̄_j = z_j/y` (`1 ≤ j ≤ r`) and `w̄ = w/y` are non-units in `R₁`, hence, `(S; z)`
admits a frame transform `(S₁; z̄)` in `R₁`, and `(S₀; w)` admits a frame transform `(S₀₁; w̄)` in
`S₁`, (ii) if `f̄ = y^{-ν} f`, then `(w̄)` can be extended to a regular system of
`τ_{(z̄)}`-parameters of `R₁` for `f̄` and `τ_{(z̄,w̄)}(f̄) = τ_{(z,w)}(f)`, and (iii) `f̄` can be
written in the same form as `f` in (4) where `(z,w)` and `(S,S₀)` are replaced by `(z̄,w̄)` and
`(S₁,S₀₁)` respectively."

(Formalization notes: the frame `(S₀; w)` of `S` is a `RegularFrame` with one element
(`WeierstrassDatum`); (4) is `HasShape`, stated through the canonical power series expansion of the
frame, which exists although `R` is not complete; "the frame transform with denominator `y`" is a
`FrameTransform` whose denominator is the image of `y ∈ S₀` in `R₁` (resp. in `S₁`), so that
`PR₁ = (y)R₁` is part of it; "`ν*(J₁) = ν*(J)` and `τ*(J₁) = τ*(J)`" are
`ν*`, `t` and `τ^{(a)}` equal as in Definition 12; (a), (b) are conclusions and `ν = ν_M(f)` is
carried by `hν`.)

Proof: derived from the helper lemmas `weierstrassStep_mem`, `weierstrassStep_frames` and
`weierstrassStep_tau`, which use hypotheses (1), (2) only through their consequences at the
indices `ᾱ = 0, 1` of the one-step sequence `R, R₁, R₁, …` (`idealZ ≤ P`, `ν_P(f) = ν`, the frame
transform of Remark 3, `ν_{M₁}(f̄) = ν` and `τ_{(z̄)}(f̄) = τ_{(z)}(f)`). -/
@[blueprint "lem:III.25-reformulated"
  (statement := /-- Let $R$ be a regular local ring whose residue field has characteristic zero, $J$
    an ideal in $R$, $(S;z_1,\dots,z_r)$ a regular frame of $R$ and $(S_0;w)$ a regular frame of
    $S$.
    Let $f$ be an element of $R$. Suppose: (1) $(z_1,\dots,z_r)$ is $J$-stable, (2) $f$ is
    $(J,\tau_{(z)})$-stable, (3) $(w)$ can be extended to a regular system of
    $\tau_{(z)}$-parameters of $R$ for $f$, and (4) $f$ can be written in the form
    $f=g+uz^{\bar A}(w^e+p_2w^{e-2}+\dots+p_e)$ where $g=\sum_{A\ne\bar A}h_Az^A$ with $h_A\in S$,
    $u$ a unit in $S$, $e=\nu_M(f)-|\bar A|>0$, and $p_j\in S_0$ for $2\le j\le e$. Let $P$ be any
    prime ideal in $R$ which is a permissible center for $J$, $R_1$ a monoidal transform of $R$ with
    center $P$ which is residually separable algebraic over $R$, and $J_1$ the strict transform of
    $J$ in $R_1$. Then (a) $P\supseteq(z_1,\dots,z_r,w)R$, (b) $\nu_P(f)=\nu$, (c) if
    $\nu^*(J_1)=\nu^*(J)$ and $\tau^*(J_1)=\tau^*(J)$, then there exists $y\in P\cap S_0$ such that
    $PR_1=(y)R_1$ and such that (i) $\bar z_j=z_j/y$ and $\bar w=w/y$ are non-units in $R_1$, hence
    $(S;z)$ admits a frame transform $(S_1;\bar z)$ in $R_1$ and $(S_0;w)$ admits a frame transform
    $(S_{01};\bar w)$ in $S_1$, (ii) if $\bar f=y^{-\nu}f$, then $(\bar w)$ can be extended to a
    regular system of $\tau_{(\bar z)}$-parameters of $R_1$ for $\bar f$ and
    $\tau_{(\bar z,\bar w)}(\bar f)=\tau_{(z,w)}(f)$, and (iii) $\bar f$ can be written in the same
    form as $f$ in (4) with $(z,w)$, $(S,S_0)$ replaced by $(\bar z,\bar w)$, $(S_1,S_{01})$.
    (Proof of Lemma 25, pp.~270--271.) -/)
  (proof := /-- Now (1) implies that $P\supseteq(z_1,\dots,z_r)R$. By (2), we have $\nu_P(f)=\nu$,
    and therefore by (4) we have $w^e+p_2w^{e-2}+\dots+p_e\in Q^e$ where $Q=P\cap S$; by Lemma 22
    $w\in Q\subseteq P$. For (c), $y\in Q_0=P\cap S_0$ exists with $(y)R_1=PR_1$ (Lemma 24 shows
    $w/y\in M_1$); (iii) is clear, and (ii) is shown by comparing the initial forms of $f$ and
    $\bar f$ (pp.~271--273). -/)
  (latexEnv := "lemma")]
theorem weierstrassDatum_facts [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    [CharZero (ResidueField R)] (J : Ideal R) (D : WeierstrassDatum R) (f : R)
    (h1 : D.F.IsJStable J) (h2 : IsJTauZStable J D.F.z f) (h3 : D.TauParams f)
    (h4 : D.HasShape f) (P : Ideal R) [P.IsPrime] (hP : IsPermissibleCenter R J P)
    (T : MonoidalTransform R P) [IsRegularLocalRing T.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing) :
    (D.F.idealZ ≤ P ∧ D.wR ∈ P) ∧
      (∀ ν : ℕ, (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) f → Ideal.ordElem P f = ν) ∧
      (nuStar T.ring (strictTransformIdeal T J) = nuStar R J →
        t T.ring (strictTransformIdeal T J) = t R J →
        (∀ a, 1 ≤ a → a ≤ t R J → tau T.ring (strictTransformIdeal T J) a = tau R J a) →
        ∃ (y : D.F0.S) (FT : D.F.FrameTransform T) (FT0 : D.F0.FrameTransform FT.TS),
          algebraMap D.F.S R (algebraMap D.F0.S D.F.S y) ∈ P ∧
          FT.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)) ∧
          FT0.x = FT.TS.toRing (algebraMap D.F0.S D.F.S y) ∧
          (∀ j, FT.w j ∈ maximalIdeal T.ring) ∧
          (D.transform FT FT0).wR ∈ maximalIdeal T.ring ∧
          T.toRing D.wR = FT.x * (D.transform FT FT0).wR ∧
          ∀ ν : ℕ, (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) f →
            ∃ f₂ : T.ring, FT.x ^ ν * f₂ = T.toRing f ∧
              (D.transform FT FT0).TauParams f₂ ∧
              tauZ T.ring (Fin.snoc FT.w (D.transform FT FT0).wR : Fin (D.F.r + 1) → T.ring)
                  (fun _ : Fin 1 => f₂) =
                tauZ R (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) (fun _ : Fin 1 => f) ∧
              (D.transform FT FT0).HasShape f₂) := by
  have hPtop : P ≠ ⊤ := (‹P.IsPrime›).ne_top
  obtain ⟨-, hJP, hreg, -⟩ := hP.resolve_left hPtop
  have : IsRegularLocalRing (R ⧸ P) := hreg
  have hzP : D.F.idealZ ≤ P := (remark3_frameTransform D.F J h1).1 P hP
  have hInTau : D.InTauStar f := (D.inTauStar_iff_tauParams f).mpr h3
  obtain ⟨ν₀, hν₀⟩ : ∃ ν : ℕ, (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) f := by
    obtain ⟨A, e, -, -, -, -, hdeg, -⟩ := h4
    exact ⟨A.degree + e, hdeg⟩
  have hperm := MonoidalSequence.ofStep_isPermissible T J hP
  have hsepS := MonoidalSequence.ofStep_isResiduallySeparableAlgebraic T J hsep
  have h0 := MonoidalSequence.nuStar_t_tau_zero J (MonoidalSequence.ofStep T J)
    (MonoidalSequence.ofStepEquiv T J) (MonoidalSequence.ofStep_ideal_zero T J)
  -- (b): `ν_P(f) = ν`, the case `ᾱ = 0` of Definition 13
  have hb : Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f :=
    (h2.2.2 (MonoidalSequence.ofStep T J) (MonoidalSequence.ofStepEquiv T J)
      (MonoidalSequence.ofStep_ideal_zero T J) hperm hsepS 0 h0.1 h0.2.1 h0.2.2
      (fun j => MonoidalSequence.ofStepEquiv T J (D.F.z j)) (fun j => rfl)
      (MonoidalSequence.ofStepEquiv T J f) rfl).2.1 hPtop
  refine ⟨⟨hzP, D.wR_mem_of_hasShape h4 hzP hb⟩, fun ν hν => hb.trans hν.symm, ?_⟩
  intro hnu ht htau
  obtain ⟨x, hxP, FT, hFT⟩ := (remark3_frameTransform D.F J h1).2.1 P hP T hsep hnu ht htau
  have hz1 : ∀ j, Ideal.ordElem P (D.F.z j) = 1 := fun j =>
    (ordElem_eq_of_isJStable_of_monoidalTransform (h1 j) hPtop T hP hsep).trans
      (ordElem_maximalIdeal_eq_one_of_mem_extendsToRSOP D.F.extends_rsop
        (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  -- division of `f` by the `ν`-th power of any denominator
  have hdiv : ∀ (FT' : D.F.FrameTransform T), ∃ f₁ : T.ring, FT'.x ^ ν₀ * f₁ = T.toRing f := by
    intro FT'
    have hfP : f ∈ P ^ ν₀ := Ideal.mem_pow_of_ordElem (hb.trans hν₀.symm)
    have hmem : T.toRing f ∈ (P ^ ν₀).map T.toRing := Ideal.mem_map_of_mem _ hfP
    rw [Ideal.map_pow, ← FT'.span_x, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  obtain ⟨f₁, hf₁⟩ := hdiv FT
  have hS := hperm.hasRegularCenters
  have hstrf : (MonoidalSequence.ofStep T J).IsStrictTransformElem
      (MonoidalSequence.ofStepEquiv T J) f 1 f₁ :=
    (MonoidalSequence.ofStep T J).isStrictTransformElem_succ_of_center_ne_top
      (MonoidalSequence.ofStepEquiv T J) hS (z := f) (n := 0)
      (g := MonoidalSequence.ofStepEquiv T J f) rfl hPtop (ν := ν₀)
      (by show Ideal.ordElem P f = ((ν₀ : ℕ) : ℕ∞); rw [hb, ← hν₀]) (x := FT.x) FT.span_x
      (w := f₁) hf₁
  have hstrz : ∀ j, (MonoidalSequence.ofStep T J).IsStrictTransformElem
      (MonoidalSequence.ofStepEquiv T J) (D.F.z j) 1 (FT.w j) := fun j => by
    have hw' : FT.x ^ 1 * FT.w j = T.toRing (D.F.z j) := by rw [pow_one]; exact FT.mul_w j
    exact (MonoidalSequence.ofStep T J).isStrictTransformElem_succ_of_center_ne_top
      (MonoidalSequence.ofStepEquiv T J) hS (z := D.F.z j) (n := 0)
      (g := MonoidalSequence.ofStepEquiv T J (D.F.z j)) rfl hPtop (ν := 1)
      (by show Ideal.ordElem P (D.F.z j) = ((1 : ℕ) : ℕ∞); rw [hz1 j]; rfl) (x := FT.x)
      FT.span_x (w := FT.w j) hw'
  have h1' := MonoidalSequence.ofStep_ideal_one T J
  have hstab := h2.2.2 (MonoidalSequence.ofStep T J) (MonoidalSequence.ofStepEquiv T J)
    (MonoidalSequence.ofStep_ideal_zero T J) hperm hsepS 1 (by rw [h1']; exact hnu)
    (by rw [h1']; exact ht) (by rw [h1']; exact htau) (fun j => FT.w j) hstrz f₁ hstrf
  have hord₁ : Ideal.ordElem (maximalIdeal T.ring) f₁ = ν₀ := hstab.1.trans hν₀.symm
  have hτ : tauZ T.ring FT.w (fun _ : Fin 1 => f₁) = tauZ R D.F.z (fun _ : Fin 1 => f) :=
    hstab.2.2
  obtain ⟨y, FT', FT0, hyP, hx', hx0', hjM, hwM, hmul, f₂, hf₂, -, hT, hτ', hsh⟩ :=
    weierstrassStep_next D f hInTau h4 P hzP hb T hsep FT ν₀ hν₀ f₁ hf₁ hord₁ hτ
  refine ⟨y, FT', FT0, hyP, hx', hx0', hjM, hwM, hmul, fun ν hν => ?_⟩
  obtain rfl : ν = ν₀ := by exact_mod_cast hν.trans hν₀.symm
  exact ⟨f₂, hf₂, hT, hτ', hsh⟩

end Reformulation

end Hironaka
