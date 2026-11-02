/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch3.FrameTransforms
public import Hironaka.Compat.StrictTransformRegular
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Compat.SingularStandardBase
public import Hironaka.Statements

/-!
# Permissible centers along monoidal transforms and flat base change (Ch. IV §3, pp. 305-306)

General cores of the proof of Lemma (AB.5) (iii) (pp. 305-306).  The paper (p. 305): "To
prove (iii), we assume that x_0 is a simple point of W. It follows that x̂'_t is a simple point of
c_t⁻¹(W(t)), for 0 ≦ t ≦ s." and "Therefore, in view of (a) and (b) of (2), we can conclude by
Corollary 1 of Proposition 2, § 8, Ch. III that, if Ĵ_0(t + 1) (which is a prime ideal in Ŝ_{t+1}
such that Ŝ_{t+1}/Ĵ_0(t + 1) is regular) is a permissible center for Ĵ_j(t + 1) for some
j(1 ≦ j ≦ β), then Ĵ_0(t) (which is a prime ideal in Ŝ_t such that Ŝ_t/Ĵ_0(t) is regular) is a
permissible center for Ĵ_j(t) for the same j. Since Ŝ_{t+1} (resp. Ŝ_t) is faithfully flat over
S_{t+1} (resp. S_t), it follows by Lemma 9 of § 3, Ch. II that, if J_0(t + 1) is a permissible
center for J_j(t + 1) for some j(1 ≦ j ≦ β), then J_0(t) is such for J_j(t) for the same j."

* Core 1: the backward step, a wrapper of Corollary 1 of Proposition 2 for the stalk transform;
* Core 2: off the center the stalk (and its permissible centers) are unchanged;
* Core 3: regularity of the strict transform of a regular `W ⊇ B` at a point of it;
* Core 4: base change of a permissible center along a flat local map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Hironaka

universe u

noncomputable section

section Core4

/-- **Core 4** Base change of a permissible center along a flat map of regular local rings, when
the base-changed center has regular quotient.

Paper (p. 305): "Since Ŝ_{t+1} (resp. Ŝ_t) is faithfully flat over S_{t+1} (resp. S_t), it
follows by Lemma 9 of § 3, Ch. II that, if J_0(t + 1) is a permissible center for J_j(t + 1) for
some j(1 ≦ j ≦ β), then J_0(t) is such for J_j(t) for the same j."

Deviation from the paper (gap filled): the paper applies Lemma 9 (faithful flatness) in both
directions at every stage.  The route here needs only this direction (from `S` to `Ŝ`, at
`t = s`), where flatness suffices (`isNormallyFlatAlongIdeal_mod_map_of_flat`), the regularity of
the quotient by the extended center being a hypothesis (it is the parenthetical "such that
`Ŝ_t/Ĵ_0(t)` is regular" of the paper, supplied by `lem:IV.AB-5-ii-class-A-quotient`); primality
of `P R'` follows from that regularity.  The other direction is
`isNormallyFlatAlongIdeal_map_iff` (Remark 1, p. 226).
-/
@[blueprint "lem:IV.AB-5-iii-flat-base-change"
  (statement := /-- Let $R\to R'$ be a flat homomorphism of regular local rings, $P$ a permissible
    center for an ideal $J$ of $R$ (\cref{def:III.8}) such that $R'/PR'$ is regular. Then $PR'$ is
    a permissible center for $JR'$. (p.~305: ``Since $\hat S_{t+1}$ (resp.\ $\hat S_t$) is
    faithfully flat over $S_{t+1}$ (resp.\ $S_t$), it follows by Lemma~9 of \S3, Ch.~II
    \dots''.) -/)
  (proof := /-- If $P=R$, then $PR'=R'$. Otherwise $PR'$ is prime because $R'/PR'$ is regular
    local, hence a domain; $JR'\subseteq PR'$; the quotient is regular by hypothesis, and
    normal flatness along $PR'$ modulo $JR'$ follows from that along $P$ modulo $J$ by flat
    base change (\cref{def:normally-flat-ideal}). \textbf{Deviation from the paper (gap
    filled).} The paper applies Lemma~9 in both directions; flatness suffices for this one. -/)
  (proofUses := ["def:III.8", "def:normally-flat-ideal"])
  (latexEnv := "lemma")]
theorem isPermissibleCenter_map_of_flat {R R' : Type u} [CommRing R] [CommRing R']
    [IsRegularLocalRing R] [IsRegularLocalRing R'] [Algebra R R'] [Module.Flat R R']
    (J P : Ideal R) (hP : IsPermissibleCenter R J P)
    (hP' : IsRegularLocalRing (R' ⧸ P.map (algebraMap R R'))) :
    IsPermissibleCenter R' (J.map (algebraMap R R')) (P.map (algebraMap R R')) := by
  by_cases hPtop : P = ⊤
  · left; rw [hPtop, Ideal.map_top]
  · right
    have hdom : IsDomain (R' ⧸ P.map (algebraMap R R')) :=
      Transforms.isDomain_of_isRegularLocalRing _
    have hprime : (P.map (algebraMap R R')).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp hdom
    obtain ⟨-, hJP, -, hnf⟩ := hP.resolve_left hPtop
    exact ⟨hprime, Ideal.map_mono hJP, hP', isNormallyFlatAlongIdeal_mod_map_of_flat P J hnf⟩

end Core4

section Core2

/-- Normal flatness of `P` modulo `J` is invariant under a ring isomorphism. -/
theorem isNormallyFlatAlongIdeal_mod_map_ringEquiv_iff {R R' : Type u} [CommRing R] [CommRing R']
    (e : R ≃+* R') (J P : Ideal R) :
    IsNormallyFlatAlongIdeal ((P.map e).map (Ideal.Quotient.mk (J.map e))) ↔
      IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)) := by
  let e2 : R ⧸ J ≃+* R' ⧸ J.map e := Ideal.quotientEquiv J (J.map e) e rfl
  have key : (P.map (Ideal.Quotient.mk J)).map (e2 : R ⧸ J →+* R' ⧸ J.map e) =
      (P.map e).map (Ideal.Quotient.mk (J.map e)) := by
    have h2 := Ideal.map_map (e : R →+* R') (Ideal.Quotient.mk (J.map e)) (I := P)
    rw [Ideal.map_map, ← Ideal.map_coe e P, h2]
    congr 1
  constructor
  · intro h
    refine isNormallyFlatAlongIdeal_of_ringEquiv e2.symm _ _ ?_ h
    rw [← key, Ideal.map_map]
    convert Ideal.map_id _ using 2
    ext a
    simp
  · exact isNormallyFlatAlongIdeal_of_ringEquiv e2 _ _ key

/-- A ring isomorphism carries permissible centers to permissible centers. -/
theorem isPermissibleCenter_map_ringEquiv_iff {R R' : Type u} [CommRing R] [CommRing R']
    [IsRegularLocalRing R] [IsRegularLocalRing R'] (e : R ≃+* R') (J P : Ideal R) :
    IsPermissibleCenter R' (J.map e) (P.map e) ↔ IsPermissibleCenter R J P := by
  unfold IsPermissibleCenter
  rw [map_ringEquiv_eq_top_iff e P]
  refine or_congr_right ?_
  have hc : ∀ I : Ideal R, Ideal.map e I = Ideal.map (e : R →+* R') I := fun I =>
    (Ideal.map_coe e I).symm
  have hprime : (P.map e).IsPrime ↔ P.IsPrime := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h' : (Ideal.comap (e : R →+* R') (Ideal.map e P)).IsPrime := Ideal.comap_isPrime _ _
      rwa [hc P, Ideal.comap_map_of_bijective (f := (e : R →+* R')) e.bijective] at h'
    · have := h
      exact Ideal.map_isPrime_of_equiv e
  have hle : J.map e ≤ P.map e ↔ J ≤ P := by
    refine ⟨fun h => ?_, Ideal.map_mono⟩
    have h1 := Ideal.comap_mono (f := (e : R →+* R')) h
    rw [hc J, hc P, Ideal.comap_map_of_bijective (f := (e : R →+* R')) e.bijective,
      Ideal.comap_map_of_bijective (f := (e : R →+* R')) e.bijective] at h1
    exact h1
  have hreg : IsRegularLocalRing (R' ⧸ P.map e) ↔ IsRegularLocalRing (R ⧸ P) := by
    let e1 : R ⧸ P ≃+* R' ⧸ P.map e := Ideal.quotientEquiv P (P.map e) e rfl
    exact ⟨fun _ => IsRegularLocalRing.of_ringEquiv e1.symm,
      fun _ => IsRegularLocalRing.of_ringEquiv e1⟩
  rw [hprime, hle, hreg, isNormallyFlatAlongIdeal_mod_map_ringEquiv_iff e J P]

/-- **Core 2** Off the center the stalk of `X'` at `y` is that of `X` at `f y`, with the same
permissible centers.

Paper (p. 305): the proof of (iii) goes through the monoidal transforms `Ŝ_{t+1}` of `Ŝ_t` and
applies Corollary 1 of Proposition 2, which requires the point to lie on the center; the points
`x̂'_{t+1}` off the center `B̂_t` are not discussed.

Deviation from the paper (gap filled): at a point off the center `f` is an isomorphism of stalks
(`bijective_stalkMap_of_notMem`, which needs the stalk of `X` to be regular, hence the instance
arguments), the stalk ideals of the strict transforms are the images of those of `V`, `W`, and
permissibility is invariant under a ring isomorphism.
-/
@[blueprint "lem:IV.AB-5-iii-off-center"
  (statement := /-- Let $f\colon X'\to X$ be a monoidal transformation with center $B$, $V,W$
    subschemes of $X$, $y\in X'$ with $f(y)\notin B$ and $\mathcal O_{X,f(y)}$ regular (hence
    $\mathcal O_{X',y}$). Then the stalk ideal of the strict transform of $W$ is a permissible
    center for that of $V$ at $y$ iff $W_{f(y)}$ is one for $V_{f(y)}$. (The case of points off
    the center in the induction of \S\,(AB.5) (iii), p.~305.) -/)
  (proof := /-- By \cref{compat:blowup-local-iso}, $\mathcal O_{X,f(y)}\to\mathcal O_{X',y}$ is
    an isomorphism, and off the exceptional subscheme the stalk ideal of the strict transform is
    that of the total transform, the image of $V_{f(y)}$. The conditions of \cref{def:III.8}
    (primality, containment, regularity of the quotient, normal flatness) are invariant under
    a ring isomorphism. \textbf{Deviation from the paper (gap filled).} The paper does not treat
    points off the center. -/)
  (proofUses := ["compat:blowup-local-iso", "def:III.8"])
  (latexEnv := "lemma")]
theorem isPermissibleCenter_stalkIdeal_strictTransform_iff_of_notMem
    {X : Scheme.{u}} {B : Subscheme X} (t : MonoidalTransformation X B) (V W : Subscheme X)
    (y : t.X') (hy : t.f y ∉ B.pts)
    [IsRegularLocalRing (X.presheaf.stalk (t.f y))] [IsRegularLocalRing (t.X'.presheaf.stalk y)] :
    IsPermissibleCenter (t.X'.presheaf.stalk y) ((Subscheme.strictTransform t V).stalkIdeal y)
        ((Subscheme.strictTransform t W).stalkIdeal y) ↔
      IsPermissibleCenter (X.presheaf.stalk (t.f y)) (V.stalkIdeal (t.f y))
        (W.stalkIdeal (t.f y)) := by
  let e : X.presheaf.stalk (t.f y) ≃+* t.X'.presheaf.stalk y :=
    RingEquiv.ofBijective (t.f.stalkMap y).hom (t.bijective_stalkMap_of_notMem y hy)
  have hyE : y ∉ t.exceptional.pts := by
    rw [MonoidalTransformation.pts_exceptional]; exact hy
  have hI : ∀ V : Subscheme X, (Subscheme.strictTransform t V).stalkIdeal y =
      (V.stalkIdeal (t.f y)).map e := by
    intro V
    rw [MonoidalTransformation.strictTransform_stalkIdeal_of_notMem t V hyE,
      stalkIdeal_totalTransform]
    rfl
  rw [hI V, hI W]
  exact isPermissibleCenter_map_ringEquiv_iff e _ _

end Core2

section Core3

/-- **Core 3** Regularity of the strict transform of `W ⊇ B` at a point of it.

Paper (p. 305): "It follows that x̂'_t is a simple point of c_t⁻¹(W(t)), for 0 ≦ t ≦ s."

Deviation from the paper (gap filled; statement made precise): the paper gives no proof.  The
statement needs the hypothesis `hy`, that `y` lies on the strict transform: otherwise the stalk
ideal is `⊤` and the quotient is the zero ring (for instance for `W = B` near `t.f y`, where the
strict transform is empty).  With `hy`, Lean identifies the strict transform of `W` with the
blow-up of `W` along `B ∩ W` and applies the regularity of the monoidal transform of a regular
local ring along a regular center (Ch. III §2); the hypothesis `W_x ≤ B_x` is automatic if
`t.f y ∉ B.pts`.
-/
@[blueprint "lem:IV.AB-5-iii-regular-strict-transform"
  (statement := /-- Let $f\colon X'\to X$ be a monoidal transformation with non-singular center
    $B$ of a non-singular scheme $X$, $W$ a subscheme of $X$ with $W_{f(y)}\subseteq B_{f(y)}$ and
    $\mathcal O_{X,f(y)}/W_{f(y)}$ regular, and $y$ a point of the strict transform $W'$ of $W$.
    Then $\mathcal O_{X',y}/W'_y$ is regular. (p.~305: ``It follows that $\hat x'_t$ is a simple
    point of $c_t^{-1}(W(t))$, for $0\le t\le s$.'') -/)
  (proof := /-- The strict transform $W'$ is the monoidal transformation of $W$ with center
    $B\cap W$ (\cref{lem:strict-transform-is-blowup}); apply
    \cref{lem:IV.3-strict-transform-regular} at a point of $W'$ over $f(y)$. If $f(y)\notin B$
    then $W_{f(y)}\subseteq B_{f(y)}=\mathcal O_{X,f(y)}$ trivially. \textbf{Deviation from the
    paper (gap filled).} The paper gives no proof; the hypothesis that $y$ lies on $W'$ is
    needed (otherwise the quotient is the zero ring). -/)
  (proofUses := ["lem:IV.3-strict-transform-regular", "lem:strict-transform-is-blowup"])
  (latexEnv := "lemma")]
theorem MonoidalTransformation.isRegularLocalRing_quotient_stalkIdeal_strictTransform [Hironaka.HironakaCitedResults.{u}]
    {X : Scheme.{u}} (hX : X.IsNonsingular) {B : Subscheme X} (hB : B.IsNonsingular)
    (t : MonoidalTransformation X B) (W : Subscheme X) (y : t.X')
    (hBW : W.stalkIdeal (t.f y) ≤ B.stalkIdeal (t.f y))
    (hreg : IsRegularLocalRing (X.presheaf.stalk (t.f y) ⧸ W.stalkIdeal (t.f y)))
    (hy : y ∈ (Subscheme.strictTransform t W).pts) :
    IsRegularLocalRing (t.X'.presheaf.stalk y ⧸ (Subscheme.strictTransform t W).stalkIdeal y) := by
  have _ := hX
  obtain ⟨q, hq⟩ := Subscheme.exists_ι_eq_of_mem_pts (Subscheme.strictTransform t W) hy
  have hle : Subscheme.totalTransform t.f W ≤ Subscheme.strictTransform t W :=
    le_sSup fun _ _ => rfl
  let fb : (Subscheme.strictTransform t W).toScheme ⟶ W.toScheme :=
    Scheme.IdealSheafData.subschemeMap (Subscheme.strictTransform t W) W t.f
      (Scheme.IdealSheafData.le_map_iff_comap_le.mpr hle)
  have hfb : fb ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have hpt : W.ι (fb q) = t.f y := by
    rw [← hq, ← Scheme.Hom.comp_apply, hfb, Scheme.Hom.comp_apply]
  have hW : IsRegularLocalRing (W.toScheme.presheaf.stalk (fb q)) :=
    (isRegularLocalRing_quotient_stalk_iff W (fb q) hpt).mp hreg
  have hB' : W.ι (fb q) ∈ B.pts →
      W.stalkIdeal (W.ι (fb q)) ≤ B.stalkIdeal (W.ι (fb q)) ∧
        IsRegularLocalRing (X.presheaf.stalk (W.ι (fb q)) ⧸ B.stalkIdeal (W.ι (fb q))) := by
    intro hmem
    rw [hpt] at hmem ⊢
    exact ⟨hBW, Subscheme.isRegularLocalRing_quotient_of_isNonsingular hB hmem⟩
  have hreg' := (t.isRegularLocalRing_stalk_and_exceptional_strictTransform W fb hfb q hB').1
  exact (isRegularLocalRing_quotient_stalk_iff (Subscheme.strictTransform t W) q hq).mpr hreg'

end Core3

section Core1

/-- **Core 1** The backward step: Corollary 1 of Proposition 2 for a stalk transform.

Paper (p. 305): "Therefore, in view of (a) and (b) of (2), we can conclude by Corollary 1 of
Proposition 2, § 8, Ch. III that, if Ĵ_0(t + 1) (which is a prime ideal in Ŝ_{t+1} such that
Ŝ_{t+1}/Ĵ_0(t + 1) is regular) is a permissible center for Ĵ_j(t + 1) for some j(1 ≦ j ≦ β), then
Ĵ_0(t) (which is a prime ideal in Ŝ_t such that Ŝ_t/Ĵ_0(t) is regular) is a permissible center
for Ĵ_j(t) for the same j."

Deviation from the paper (gap filled): Corollary 1 (`cor:III.prop2-1`) has the hypotheses `Q ≠ P`,
the prime `P₁` with `P₁ ∩ R = P`, and the element `x` with `QR₁ = (x)R₁`, none of which the paper
verifies here.  Lean takes `P₁` to be the strict transform of `P` (`hne`: the point `x̂'_{t+1}`
lies on it), which is prime with `P₁ ∩ R = P` (`isPrime_strictTransformIdeal_and_comap_eq`), `x`
to be the element of the transform, and `Q ≠ P` because `x ∈ Q`, `x ∉ P` (the strict transform is
proper); "residue field perfect of the same characteristic" is `CharZero (ResidueField R)`.  The
corollary itself is `isPermissibleCenter_of_perfectField_residueField`, proved in Ch. III.
-/
@[blueprint "lem:IV.AB-5-iii-center-descent"
  (statement := /-- Let $R$ be a regular local domain whose residue field has characteristic zero,
    $J\subseteq P\subseteq Q$ ideals with $P,Q$ prime, $R/P$ and $R/Q$ regular, and
    $(f_k)$ elements of $J$ with $\nu_M(f_k)=\nu_Q(f_k)$ whose initial forms generate
    $\operatorname{gr}_M(J,R)$. Let $R_1$ be a monoidal transform of $R$ with center $Q$ (a local
    homomorphism, $R_1$ regular), $x$ its element, $P_1$ the strict transform of $P$, assumed
    proper, $J_1$ that of $J$, $\nu_k=\nu_Q(f_k)$ and $g_k$ with $x^{\nu_k}g_k=f_k$ and
    $\nu_{M_1}(g_k)=\nu_k$. If $P_1$ is a permissible center for $J_1$, then $P$ is a permissible
    center for $J$. (p.~305: ``we can conclude by Corollary 1 of Proposition 2, \S8, Ch.~III
    \dots''.) -/)
  (proof := /-- The strict transform $P_1$ of the prime $P$ is a prime ideal with
    $P_1\cap R=P$ as soon as it is proper (the point lies on it), and then $x\notin P$, so
    $Q\ne P$. Apply \cref{cor:III.prop2-1}; in characteristic zero the residue field is perfect
    of the same characteristic as $R$. \textbf{Deviation from the paper (gap filled).} The paper
    does not verify the hypotheses of Corollary~1 here. -/)
  (proofUses := ["cor:III.prop2-1"])
  (latexEnv := "lemma")]
theorem isPermissibleCenter_of_isPermissibleCenter_strictTransformIdeal [Hironaka.HironakaCitedResults.{u}]
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero (ResidueField R)]
    (J P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P ≤ Q) (hJP : J ≤ P)
    [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)]
    {m : ℕ} (f : Fin m → R) (hfJ : ∀ k, f k ∈ J)
    (hiii : ∀ k, Ideal.ordElem (maximalIdeal R) (f k) = Ideal.ordElem Q (f k))
    (hiv : Ideal.span (Set.range fun k => initialForm (maximalIdeal R) (f k)) =
      grIdeal (maximalIdeal R) J)
    (T : MonoidalTransform R Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (hne : strictTransformIdeal T P ≠ ⊤)
    (ν : Fin m → ℕ) (hν : ∀ k, (ν k : ℕ∞) = Ideal.ordElem Q (f k))
    (g : Fin m → T.ring) (hg : ∀ k, T.toRing T.x ^ ν k * g k = T.toRing (f k))
    (hvi : ∀ k, Ideal.ordElem (maximalIdeal T.ring) (g k) = (ν k : ℕ∞))
    (hperm₁ : IsPermissibleCenter T.ring (strictTransformIdeal T J) (strictTransformIdeal T P)) :
    IsPermissibleCenter R J P := by
  have hQ : Q.IsPrime := inferInstance
  have hSQ : IsRegularLocalRing (R ⧸ Q) := inferInstance
  obtain ⟨hprime₁, hcomap⟩ := MonoidalTransform.isPrime_strictTransformIdeal_and_comap_eq T hQ
    hSQ P hne
  have hxP : T.x ∉ P := MonoidalTransform.x_notMem_of_strictTransformIdeal_ne_top T hQ hSQ P hne
  have hQP : Q ≠ P := fun h => hxP (h ▸ T.x_mem)
  have hx : Q.map T.toRing = Ideal.span {T.toRing T.x} := (MonoidalTransform.span_xR_eq_map T).symm
  have hcharZ : CharZero R := by
    have : CharP R 0 := ⟨fun n => by
      constructor
      · intro h
        have h1 : ((n : ResidueField R)) = 0 := by
          rw [← map_natCast (algebraMap R (ResidueField R)), h, map_zero]
        exact (zero_dvd_iff.mpr (Nat.cast_eq_zero.mp h1))
      · intro h
        rw [zero_dvd_iff.mp h]
        simp⟩
    exact CharP.charP_to_charZero R
  have hchar : ringChar (ResidueField R) = ringChar R := by
    rw [ringChar.eq (ResidueField R) 0, ringChar.eq R 0]
  have := hprime₁
  exact isPermissibleCenter_of_perfectField_residueField R hchar J P Q hPQ hJP hQP f hfJ hiii hiv T
    (strictTransformIdeal T P) hcomap T.x T.x_mem hx ν hν g hg hvi hperm₁

end Core1

end

end Hironaka
