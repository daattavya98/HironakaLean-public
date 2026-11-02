/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Stalk
public import Architect
public import Hironaka.Ch0.AlgebraicScheme
public import Hironaka.Ch1.ResolutionData
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Compat.BlowupCompositionIdeals
public import Hironaka.Compat.BlowupExceptional
public import Hironaka.Compat.BlowupLocalIso
public import Hironaka.Compat.ExtendSuccessionWeak
public import Hironaka.Compat.PrimitiveGcd
public import Hironaka.Compat.PrimitiveIdeal
public import Hironaka.Compat.StalkGeneralization
public import Hironaka.Compat.WeakTransformProduct

/-!
# Ch. 0 §5 (pp. 142–143): the weak transform and the ideals `J'` of fact (*)

> Let `D` be a non-singular irreducible subscheme (resp. such an analytic subspace) of `X`, and `f : X' → X` the monoidal
> transformation of `X` with center `D`.  If `m = ν(J_x)` for the generic point `x` of `D`, then we have
> `m = ν(f⁻¹(J)_y)` for the generic point `y` of `f⁻¹(D)`, or equivalently, `f⁻¹(J)` is divisible by the `m`-th power
> of the sheaf of ideals of `f⁻¹(D)` on `X'`.  The sheaf of ideals on `X'` obtained by this division will be called the
> weak transform of `J` by the monoidal transformation `f`.  (p. 142)

> In order to see that the main theorem II implies the affirmative answer to the question (E) for the case in which `X`
> and `Y` are algebraic `B`-schemes with a field `B` of characteristic zero, the following corollary of main theorem II
> is sufficient.  (p. 143)

To pass from Corollary 1 (about weak transforms `J_j(i)`) to (*) (about the sheaves of ideals `J'` which are not divisible
by an invertible sheaf of ideals) the paper uses two facts it does not state:

* `f⁻¹(J) = J' · P` with `P` invertible, for the weak transform `J'` (`Subscheme.exists_totalTransform_eq_weakTransform_mul`,
  proved here from the printed definition of the weak transform);
* the weak transform of a sheaf of ideals not divisible by any invertible sheaf of ideals is again such a sheaf
  (`Subscheme.isPrimitive_weakTransform`, proved here: gap filled).

Without the second, the sheaf `J'` of (*) need not be the weak transform `J_j(i)`: e.g. `J = (x)(x, y)` on the plane,
whose weak transform at the origin is the principal ideal `(x₁)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Hironaka

namespace Subscheme

variable {X : Scheme.{u}} {B : Subscheme X}

/-- `f⁻¹(J) = J' · P` with `J'` the weak transform of `J` and `P` an invertible sheaf of ideals: `P` is the `m`-th power of
the exceptional ideal, `m = ν(J_ξ)` (p. 142: "`f⁻¹(J)` is divisible by the `m`-th power of the sheaf of ideals of `f⁻¹(D)`"),
and `P = O_{X'}` when the center is empty (`X' = X`). -/
theorem exists_totalTransform_eq_weakTransform_mul (hX : X.IsNonsingular) (hB : B.IsCenter)
    (t : MonoidalTransformation X B) (J : Subscheme X) (hJ : ∀ x, J.stalkIdeal x ≠ ⊥) :
    ∃ Q : Subscheme t.X', Q.IsInvertibleIdeal ∧ totalTransform t.f J = weakTransform t J * Q := by
  by_cases h : ∃ ξ : X, IsGenericPoint ξ B.pts
  · obtain ⟨ξ, hξ⟩ := h
    have : IsRegularLocalRing (X.presheaf.stalk ξ) := hX ξ
    obtain ⟨m, hm⟩ := Ideal.exists_nu_eq_natCast (hJ ξ)
    exact ⟨t.exceptional ^ m, t.invertible.pow m,
      totalTransform_eq_weakTransform_mul_pow hX hB.isNonsingular t J hξ hm⟩
  · refine ⟨⊤, isInvertibleIdeal_top, ?_⟩
    rw [weakTransform_eq_totalTransform_of_not_exists t J h]
    exact ext_stalkIdeal fun x => by rw [stalkIdeal_mul_eq, stalkIdeal_top_eq, Ideal.mul_top]

end Subscheme

/-- A prime of the stalk at `y` is the preimage of the maximal ideal of the stalk at a generization of `y`:
`η = fromSpecStalk y P` (the point of `Spec O_{Y,y}` given by `P`). -/
theorem exists_specializes_comap_maximalIdeal_eq {Y : Scheme.{u}} (y : Y)
    (P : Ideal (Y.presheaf.stalk y)) [hP : P.IsPrime] :
    ∃ (η : Y) (h : η ⤳ y),
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk η)).comap (Y.presheaf.stalkSpecializes h).hom = P := by
  let η : Y := Y.fromSpecStalk y (⟨P, hP⟩ : PrimeSpectrum _)
  have h : η ⤳ y := by
    have : η ∈ Set.range (Y.fromSpecStalk y) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  refine ⟨η, h, ?_⟩
  let cp : Spec (Y.presheaf.stalk η) := IsLocalRing.closedPoint (Y.presheaf.stalk η)
  have h2 : Y.fromSpecStalk y ((Spec.map (Y.presheaf.stalkSpecializes h)) cp) = η := by
    rw [← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkSpecializes_fromSpecStalk h,
      Scheme.fromSpecStalk_closedPoint]
  have h3 := (Y.fromSpecStalk y).isEmbedding.injective h2
  exact congrArg PrimeSpectrum.asIdeal h3

namespace Subscheme

variable {X : Scheme.{u}} {B : Subscheme X}

/-- **The stalk of the weak transform of a primitive ideal is not contained in a prime principal ideal.**  Let `ρ` be a
prime element of `O_{X',y}` with `J'_y ⊆ (ρ)`, `J'` the weak transform of `K`.
If `(ρ)` contains the exceptional ideal `E_y` then `(ρ) = E_y` (`E_y` is prime) and `f⁻¹(K)_y = J'_y E_yᵐ ⊆ E_yᵐ⁺¹`, so
`K_{f y} ⊆ B_{f y}ᵐ⁺¹` and `m + 1 ≤ ν(K_ξ) = m` (`le_nu_generic_iff`), absurd.  Otherwise the generization `η` of `y`
defined by `(ρ)` is off the exceptional divisor, where `f` is an isomorphism: `z = f η` is a point of `X`, generization of
`f y`, with `O_{X,z} ≅ O_{X',η}` regular of dimension one, `K_z ⊆ m_z`, so `K_{f y}` lies in a prime of height one, a
principal ideal of the unique factorization domain `O_{X,f y}`, contradicting the primitivity of `K` at `f y`. -/
theorem weakTransform_stalkIdeal_not_le_span [Hironaka.Cited.IsRegularLocalRingUniqueFactorizationMonoid.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular) (hB : B.IsCenter)
    (t : MonoidalTransformation X B) {K : Subscheme X} (hK : ∀ x, K.stalkIdeal x ≠ ⊥)
    (hprim : Subscheme.IsPrimitive K) (y : t.X') {ρ : t.X'.presheaf.stalk y} (hρ : Prime ρ) :
    ¬ (weakTransform t K).stalkIdeal y ≤ Ideal.span {ρ} := by
  intro hle
  have hnoeth := IsAlgebraicScheme.isNoetherian X
  have hBns := hB.isNonsingular
  have hX' : t.X'.IsNonsingular := (t.isNonsingular_and_isNonsingular_exceptional hX hBns).1
  have hE : t.exceptional.IsNonsingular := (t.isNonsingular_and_isNonsingular_exceptional hX hBns).2
  have hstalk := fun x π h => Subscheme.IsPrimitive.stalk hX hK hprim x π h
  obtain ⟨hdomy, hufdy⟩ := stalk_ufd hX' y
  have hregy : IsRegularLocalRing (t.X'.presheaf.stalk y) := hX' y
  have hnoethy : IsNoetherianRing (t.X'.presheaf.stalk y) := inferInstance
  have hPρ : (Ideal.span {ρ}).IsPrime := (Ideal.span_singleton_prime hρ.ne_zero).mpr hρ
  by_cases hEρ : t.exceptional.stalkIdeal y ≤ Ideal.span {ρ}
  · -- the exceptional ideal is contained in `(ρ)`
    have hy : y ∈ t.exceptional.pts := by
      rw [mem_pts_iff_stalkIdeal_ne_top]
      intro htop
      rw [htop, top_le_iff, Ideal.span_singleton_eq_top] at hEρ
      exact hρ.not_isUnit hEρ
    have hfy := t.mem_pts_of_mem_exceptional hy
    have hBirr : B.IsIrreducible := by
      rcases hB with h | ⟨-, h⟩
      · have hpts : B.pts = ∅ := by rw [h]; exact DatumTransform.pts_empty
        rw [hpts] at hfy
        exact absurd hfy (Set.notMem_empty _)
      · exact h
    obtain ⟨ξ, hξ⟩ := Subscheme.exists_isGenericPoint hBirr
    have : IsRegularLocalRing (X.presheaf.stalk ξ) := hX ξ
    obtain ⟨m, hm⟩ := Ideal.exists_nu_eq_natCast (hK ξ)
    have htt := totalTransform_eq_weakTransform_mul_pow hX hBns t K hξ hm
    have hEprime := isPrime_stalkIdeal_of_isNonsingular_of_mem_pts t.exceptional hE hy
    have hEne := MonoidalTransformation.stalkIdeal_exceptional_ne_bot hX t y
    -- `(ρ) = E_y`
    obtain ⟨e, heE, hep⟩ := hEprime.exists_mem_prime_of_ne_bot hEne
    have hρe : ρ ∣ e := Ideal.mem_span_singleton.mp (hEρ heE)
    have heρ : e ∣ ρ := hρ.irreducible.dvd_symm hep.irreducible hρe
    have hρE : ρ ∈ t.exceptional.stalkIdeal y :=
      (Ideal.span_singleton_le_iff_mem _).mp (Ideal.span_singleton_le_span_singleton.mpr heρ |>.trans
        ((Ideal.span_singleton_le_iff_mem _).mpr heE)) |> fun h => h
    have hweakE : (weakTransform t K).stalkIdeal y ≤ t.exceptional.stalkIdeal y :=
      hle.trans ((Ideal.span_singleton_le_iff_mem _).mpr hρE)
    have hmul : (totalTransform t.f K).stalkIdeal y ≤ t.exceptional.stalkIdeal y ^ (m + 1) := by
      rw [htt, stalkIdeal_mul_eq, stalkIdeal_pow_eq, pow_succ']
      exact Ideal.mul_mono_left hweakE
    have hKle : K.stalkIdeal (t.f y) ≤ B.stalkIdeal (t.f y) ^ (m + 1) := by
      intro k hk
      refine (MonoidalTransformation.stalkMap_mem_exceptional_pow_iff hX hBns t hy (m + 1) k).mp (hmul ?_)
      rw [stalkIdeal_totalTransform]
      exact Ideal.mem_map_of_mem _ hk
    have h1 := (Subscheme.le_nu_generic_iff hX hBns hξ hfy K (m + 1)).mpr hKle
    rw [hm] at h1
    have h2 : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := h1
    have h3 : m + 1 ≤ m := by exact_mod_cast h2
    omega
  · -- the generization defined by `(ρ)` is off the exceptional divisor
    obtain ⟨η, hηy, hcomap⟩ := exists_specializes_comap_maximalIdeal_eq y (Ideal.span {ρ})
    have hηE : η ∉ t.exceptional.pts := by
      rw [mem_pts_iff_stalkIdeal_ne_top, not_not, stalkIdeal_eq_map_stalkSpecializes t.exceptional hηy]
      obtain ⟨b, hbE, hb⟩ := Set.not_subset.mp hEρ
      have hbm : (t.X'.presheaf.stalkSpecializes hηy).hom b ∉ IsLocalRing.maximalIdeal
          (t.X'.presheaf.stalk η) := by
        rw [← Ideal.mem_comap, hcomap]
        exact hb
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hbE)
        (IsLocalRing.notMem_maximalIdeal.mp hbm)
    have hfη : t.f η ∉ B.pts := fun h => hηE (by rw [t.pts_exceptional]; exact h)
    have hbij := t.bijective_stalkMap_of_notMem_pts η hfη
    have hzx : t.f η ⤳ t.f y := hηy.map t.f.continuous
    -- `K_z ⊆ m_z` for `z = f η`
    have hweak_le : (weakTransform t K).stalkIdeal η ≤ IsLocalRing.maximalIdeal (t.X'.presheaf.stalk η) := by
      rw [stalkIdeal_eq_map_stalkSpecializes (weakTransform t K) hηy, Ideal.map_le_iff_le_comap, hcomap]
      exact hle
    have htt_le : (totalTransform t.f K).stalkIdeal η ≤
        IsLocalRing.maximalIdeal (t.X'.presheaf.stalk η) := by
      by_cases hgen : ∃ ξ : X, IsGenericPoint ξ B.pts
      · obtain ⟨ξ, hξ⟩ := hgen
        have : IsRegularLocalRing (X.presheaf.stalk ξ) := hX ξ
        obtain ⟨m, hm⟩ := Ideal.exists_nu_eq_natCast (hK ξ)
        have htt := totalTransform_eq_weakTransform_mul_pow hX hBns t K hξ hm
        rw [htt, stalkIdeal_mul_eq, stalkIdeal_pow_eq, stalkIdeal_eq_top_of_notMem_pts hηE, Ideal.top_pow,
          Ideal.mul_top]
        exact hweak_le
      · rw [← weakTransform_eq_totalTransform_of_not_exists t K hgen]
        exact hweak_le
    have hKz : K.stalkIdeal (t.f η) ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk (t.f η)) := by
      intro k hk
      by_contra hkm
      have hu : IsUnit ((t.f.stalkMap η).hom k) := (IsLocalRing.notMem_maximalIdeal.mp hkm).map _
      have hmem : (t.f.stalkMap η).hom k ∈ IsLocalRing.maximalIdeal (t.X'.presheaf.stalk η) := by
        apply htt_le
        rw [stalkIdeal_totalTransform]
        exact Ideal.mem_map_of_mem _ hk
      exact (IsLocalRing.notMem_maximalIdeal.mpr hu) hmem
    -- the prime `𝔭` of `O_{X, f y}` of the point `z`
    obtain ⟨hdomx, hufdx⟩ := stalk_ufd hX (t.f y)
    have hregx : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
    have hnoethx : IsNoetherianRing (X.presheaf.stalk (t.f y)) := inferInstance
    set 𝔭 : Ideal (X.presheaf.stalk (t.f y)) :=
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (t.f η))).comap (X.presheaf.stalkSpecializes hzx).hom
      with h𝔭
    have h𝔭prime : 𝔭.IsPrime := Ideal.comap_isPrime _ _
    have hK𝔭 : K.stalkIdeal (t.f y) ≤ 𝔭 := by
      rw [h𝔭, ← Ideal.map_le_iff_le_comap, ← stalkIdeal_eq_map_stalkSpecializes K hzx]
      exact hKz
    -- `𝔭` has height one
    have hρh : (Ideal.span {ρ}).height = 1 := by
      have hne : Ideal.span {ρ} ≠ ⊥ := by simpa using hρ.ne_zero
      refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _
        ⟨⟨hPρ, le_rfl⟩, fun r hr _ => hr.2⟩) ?_
      rw [Order.one_le_iff_pos, pos_iff_ne_zero]
      intro h0
      exact hne (Ideal.height_eq_zero_iff_eq_bot.mp h0)
    have h𝔭h : 𝔭.height = 1 := by
      let _ := (X.presheaf.stalkSpecializes hzx).hom.toAlgebra
      have hlocz := isLocalization_stalkSpecializes_of_specializes hzx
      let _ := (t.X'.presheaf.stalkSpecializes hηy).hom.toAlgebra
      have hlocη := isLocalization_stalkSpecializes_of_specializes hηy
      have hdz := IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 (X.presheaf.stalk (t.f η))
      have hdη := IsLocalization.AtPrime.ringKrullDim_eq_height
        ((IsLocalRing.maximalIdeal (t.X'.presheaf.stalk η)).comap
          (t.X'.presheaf.stalkSpecializes hηy).hom) (t.X'.presheaf.stalk η)
      rw [hcomap, hρh] at hdη
      have hdeq := ringKrullDim_eq_of_ringEquiv
        (RingEquiv.ofBijective (t.f.stalkMap η).hom hbij)
      rw [hdη, hdz] at hdeq
      exact_mod_cast hdeq
    obtain ⟨π, hπ⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one h𝔭h).principal
    have hπu := hstalk (t.f y) π (by rw [← Ideal.submodule_span_eq, ← hπ]; exact hK𝔭)
    exact h𝔭prime.ne_top (by rw [Ideal.submodule_span_eq] at hπ; rw [hπ, Ideal.span_singleton_eq_top]; exact hπu)

/-- **The weak transform of a sheaf of ideals not divisible by any invertible sheaf of ideals is again such a sheaf.**

Deviation from the paper (gap filled): used tacitly by the paper; proved here.  The paper passes from the weak transforms
`J_j(i)` of Corollary 1 to the sheaves `J'ᵢ` of (*) (p. 143: "the following corollary of main theorem II is sufficient") and
takes this for granted.  Off the exceptional divisor `f` is an isomorphism, so a prime divisor of `X'` other than the
exceptional one dividing the weak transform contracts to a prime divisor of `X` dividing `J` (the local rings are unique
factorization domains, footnote 3); and the exceptional divisor does not divide the weak transform, by the choice of
`m = ν(J_ξ)` (p. 142).  See `weakTransform_stalkIdeal_not_le_span`. -/
@[blueprint "lem:0.5-weak-transform-primitive"
  (statement := /-- Let $X$ be a non-singular algebraic scheme, $D$ a non-singular irreducible (or empty) subscheme,
    $f\colon X'\to X$ the monoidal transformation with center $D$ and $J$ a sheaf of non-zero ideals on $X$ which is not
    divisible by any invertible sheaf of ideals (except $\mathcal O_X$). Then the weak transform of $J$ by $f$ is a sheaf
    of non-zero ideals on $X'$ which is not divisible by any invertible sheaf of ideals (except $\mathcal O_{X'}$). This
    is taken for granted in passing from Corollary~1 to (*) (pp.~141, 143). \textbf{Deviation from the paper (gap
    filled).} Used tacitly by the paper; proved here. -/)
  (proof := /-- It suffices to show that no stalk of the weak transform $J'$ lies in a principal ideal $(\rho)$, $\rho$
    a prime element of the unique factorization domain $\mathcal O_{X',y}$ (footnote~3); and $J$ is not divisible at any
    point, because the sheaf of divisors of $J$ is an invertible sheaf of ideals containing $J$
    (\cref{lem:0.5-primitive-decomposition}). If $(\rho)$ contains the exceptional ideal $E_y$, then $(\rho)=E_y$ since
    $E_y$ is prime, and $f^{-1}(J)_y=J'_yE_y^m\subseteq E_y^{m+1}$, so $J_{f(y)}\subseteq D_{f(y)}^{m+1}$ and
    $m+1\le\nu(J_\xi)=m$, absurd. Otherwise the generization $\eta$ of $y$ defined by $(\rho)$ is off the exceptional divisor,
    where $f$ is an isomorphism: $z=f(\eta)$ is a generization of $f(y)$ with $\mathcal O_{X,z}\cong\mathcal O_{X',\eta}$ of
    dimension one and $J_z\subseteq\mathfrak m_z$, so $J_{f(y)}$ lies in a prime of height one, which is principal,
    contradicting the divisibility of $J$. -/)
  (proofUses := ["lem:0.5-primitive-decomposition"])
  (latexEnv := "lemma")]
theorem isPrimitive_weakTransform [Hironaka.Cited.IsRegularLocalRingUniqueFactorizationMonoid.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular) (hB : B.IsCenter)
    (t : MonoidalTransformation X B) {K : Subscheme X} (hK : ∀ x, K.stalkIdeal x ≠ ⊥)
    (hprim : Subscheme.IsPrimitive K) : Subscheme.IsPrimitive (weakTransform t K) := by
  intro Q hQ hle y
  obtain ⟨q, hqQ, hqnzd⟩ := hQ.exists_stalkIdeal_eq_span y
  by_contra hne
  have hqnu : ¬ IsUnit q := fun hu => hne (by rw [hqQ]; exact Ideal.span_singleton_eq_top.mpr hu)
  have hX' : t.X'.IsNonsingular := (t.isNonsingular_and_isNonsingular_exceptional hX hB.isNonsingular).1
  obtain ⟨hdomy, hufdy⟩ := stalk_ufd hX' y
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hqnzd
  obtain ⟨ρ, hρirr, hρq⟩ := WfDvdMonoid.exists_irreducible_factor hqnu hq0
  have hρ : Prime ρ := UniqueFactorizationMonoid.irreducible_iff_prime.mp hρirr
  refine weakTransform_stalkIdeal_not_le_span hX hB t hK hprim y hρ ?_
  calc (weakTransform t K).stalkIdeal y ≤ Q.stalkIdeal y := hle y
    _ = Ideal.span {q} := hqQ
    _ ≤ Ideal.span {ρ} := Ideal.span_singleton_le_span_singleton.mpr hρq

end Subscheme

end Hironaka
