/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch2.PointwiseFlatness
public import Hironaka.Compat.CodimOneInvertible
public import Hironaka.Compat.ComponentStalk
public import Hironaka.Compat.StalkFrameStep

/-!
# The converse of Ch. 0 §4 (I) for a locally principal ideal sheaf (p. 136)

> The converse is true if X is imbedded in a non-singular algebraic B-scheme, or analytic K-space, Y
> such that the sheaf of ideals of X on Y is everywhere locally principal; but not in general.  (p. 136)

Here `X` of the paper is the subscheme `V` of the non-singular algebraic scheme `Y` (called `X` in Lean) and
`D` is a non-singular subscheme `W` of `V`, not necessarily irreducible.  Ch. II, Corollary 2 of Theorem 2
(`Subscheme.isNormallyFlatAlong'_iff_isEquimultipleAlong`, p. 197) asks that the ideal of `V` be invertible
and `W` irreducible; the two missing cases are

* `W` reducible: `W` is the disjoint union of its irreducible components, each non-singular, and `V` is
  normally flat along `W` at `x` iff along the component through `x` (the stalk of `W` at `x` is the stalk of
  that component);
* the ideal of `V` zero on a connected component of `Y` ("locally principal" allows the zero ideal): there
  `V = Y` is regular, so `O_{V,x}` is normally flat along every non-singular `W`.

Deviation from the paper (gap filled): the paper cites Ch. II.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

namespace Subscheme

variable {X : Scheme.{u}}

/-- At every point the stalk of a locally principal ideal sheaf is principal. -/
theorem IsLocallyPrincipal.exists_stalkIdeal_eq_span {V : Subscheme X} (hV : V.IsLocallyPrincipal)
    (x : X) : ∃ f : X.presheaf.stalk x, V.stalkIdeal x = Ideal.span {f} := by
  obtain ⟨U, hxU, a, ha⟩ := hV x
  exact ⟨X.presheaf.germ U x hxU a, by
    rw [stalkIdeal_eq_map_germ_affine V U hxU, ha, Ideal.map_span, Set.image_singleton]⟩

/-- For a generization `η ⤳ y` with `O_{X,y}` a domain, the specialization map `O_{X,y} → O_{X,η}` is
injective (it is the localization of `O_{X,y}` at a prime, `O_{X,y}` being a domain). -/
theorem stalkSpecializes_injective_of_isDomain {η y : X} (h : η ⤳ y)
    [IsDomain (X.presheaf.stalk y)] : Function.Injective (X.presheaf.stalkSpecializes h).hom := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hηV : η ∈ V := h.mem_open V.isOpen hyV
  let _ : Algebra Γ(X, V) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hyV⟩
  let _ : Algebra Γ(X, V) (X.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨η, hηV⟩
  have hy := hV.isLocalization_stalk ⟨y, hyV⟩
  have hη := hV.isLocalization_stalk ⟨η, hηV⟩
  set py := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
  set pη := (hV.primeIdealOf ⟨η, hηV⟩).asIdeal
  have hsp : ∀ s : Γ(X, V), (X.presheaf.stalkSpecializes h).hom
      (algebraMap Γ(X, V) (X.presheaf.stalk y) s) = algebraMap Γ(X, V) (X.presheaf.stalk η) s :=
    fun s => TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hyV h s
  -- `p_η ⊆ p_y`
  have hle : py.primeCompl ≤ pη.primeCompl := by
    intro s hs
    have hu : IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk y) s) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ py s).mpr hs
    have hu' := hu.map (X.presheaf.stalkSpecializes h).hom
    rw [hsp] at hu'
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ pη s).mp hu'
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.mk'_surjective py.primeCompl a
  have has : a * algebraMap Γ(X, V) (X.presheaf.stalk y) s = algebraMap Γ(X, V) (X.presheaf.stalk y) b := by
    rw [← hbs]
    exact IsLocalization.mk'_spec _ _ _
  have hφb : algebraMap Γ(X, V) (X.presheaf.stalk η) b = 0 := by
    rw [← hsp, ← has, map_mul, ha, zero_mul]
  obtain ⟨⟨t, ht⟩, htb⟩ := (IsLocalization.map_eq_zero_iff pη.primeCompl _ b).mp hφb
  -- `t b = 0` in `Γ(X, V)`, hence in the domain `O_{X,y}`
  have htb' : algebraMap Γ(X, V) (X.presheaf.stalk y) t * algebraMap Γ(X, V) (X.presheaf.stalk y) b = 0 := by
    rw [← map_mul]
    exact (by simpa using congrArg (algebraMap Γ(X, V) (X.presheaf.stalk y)) htb)
  rcases mul_eq_zero.mp htb' with hts | hb
  · exfalso
    obtain ⟨⟨u, hu⟩, hut⟩ := (IsLocalization.map_eq_zero_iff py.primeCompl _ t).mp hts
    have hprod : u * t = 0 := by simpa using hut
    have : u * t ∈ pη := by rw [hprod]; exact pη.zero_mem
    rcases (PrimeSpectrum.isPrime (hV.primeIdealOf ⟨η, hηV⟩)).mem_or_mem this with h1 | h1
    · exact (hle hu) h1
    · exact ht h1
  · rw [hb] at has
    have hs : IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk y) s) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ py s).mpr s.2
    exact (hs.mul_left_eq_zero).mp has

/-- The multiplicity of `V` at a point depends only on the ideal of `V` at its image: if `V` and `V'` have
the same ideal at `z`, their multiplicities at points over `z` agree
(`O_{V,w} ≅ O_{X,z}/V_z`, `e(R)` is invariant under isomorphisms). -/
theorem multAt_eq_of_stalkIdeal_eq {V V' : Subscheme X} (w : V.toScheme) (w' : V'.toScheme)
    (hw' : V'.ι w' = V.ι w)
    (h : V.stalkIdeal (V.ι w) = V'.stalkIdeal (V.ι w)) :
    V.toScheme.multAt w = V'.toScheme.multAt w' := by
  obtain ⟨e₁⟩ := nonempty_stalk_quot_equiv V w
  obtain ⟨e₂⟩ := nonempty_stalk_quot_equiv V' w'
  generalize V'.ι w' = z' at e₂ hw'
  subst hw'
  exact samuelMultiplicity_eq_of_ringEquiv (e₁.symm.trans ((Ideal.quotEquivOfEq h).trans e₂))

/-- A prime ideal is its own unique minimal prime. -/
theorem eq_of_mem_minimalPrimes_of_isPrime {R : Type*} [CommRing R] {P q : Ideal R} [P.IsPrime]
    (hq : q ∈ P.minimalPrimes) : q = P :=
  le_antisymm (hq.2 ⟨inferInstance, le_rfl⟩ hq.1.2) hq.1.2

/-- The irreducible component of a non-singular subscheme `W` through `x`: an irreducible component `C` of
`W` with `x ∈ C`, which is a non-singular irreducible subscheme with the same ideal as `W` at each of its
points and `C ⊆ W` (p. 136: a non-singular subscheme is the disjoint union of its irreducible components). -/
theorem exists_component_of_isNonsingular {W : Subscheme X} (hW : W.IsNonsingular) {x : X}
    (hx : x ∈ W.pts) :
    ∃ Z : Closeds X, Subscheme.ofClosed Z ∈ W.irreducibleComponents ∧ x ∈ Z ∧ (Z : Set X) ⊆ W.pts ∧
      (∀ y ∈ Z, (Subscheme.ofClosed Z).stalkIdeal y = W.stalkIdeal y) ∧
      (Subscheme.ofClosed Z).IsNonsingular ∧ (Subscheme.ofClosed Z).IsIrreducible ∧
      (Subscheme.ofClosed Z).IsContainedIn W := by
  have hp := isPrime_stalkIdeal_of_isNonsingular_of_mem_pts W hW hx
  obtain ⟨C, hC, hxC, hCx⟩ := exists_mem_irreducibleComponents_of_mem_minimalPrimes W x
    (p := W.stalkIdeal x) ⟨⟨hp, le_rfl⟩, fun q hq _ => hq.2⟩
  obtain ⟨Z, ⟨⟨hZirr, hZW⟩, hZmax⟩, rfl⟩ := hC
  have hCpts : (Subscheme.ofClosed Z).pts = Z := pts_ofClosed Z
  have hCW : (Subscheme.ofClosed Z).pts ⊆ W.pts := hCpts ▸ hZW
  have hstalk : ∀ y ∈ (Subscheme.ofClosed Z).pts,
      (Subscheme.ofClosed Z).stalkIdeal y = W.stalkIdeal y := by
    intro y hy
    have := isPrime_stalkIdeal_of_isNonsingular_of_mem_pts W hW (hCW hy)
    exact eq_of_mem_minimalPrimes_of_isPrime
      (stalkIdeal_mem_minimalPrimes ⟨Z, ⟨⟨hZirr, hZW⟩, hZmax⟩, rfl⟩ hy)
  have hxZ : x ∈ Z := by rwa [pts_ofClosed] at hxC
  have hstalk' : ∀ y ∈ Z, (Subscheme.ofClosed Z).stalkIdeal y = W.stalkIdeal y := fun y hy =>
    hstalk y (by rwa [pts_ofClosed])
  refine ⟨Z, ⟨Z, ⟨⟨hZirr, hZW⟩, hZmax⟩, rfl⟩, hxZ, hZW, hstalk', ?_, ?_, ?_⟩
  · refine isNonsingular_of_stalk_quot _ fun y hy => ?_
    rw [hstalk y hy]
    exact isRegular_stalk_quot W hW (hCW hy)
  · exact isIrreducible_of_pts _ (hCpts ▸ hZirr)
  · exact fun U => (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
      (fun y hy => hZW hy) : W ≤ Subscheme.ofClosed Z) U

theorem stalkIdeal_sup_eq' (V N : Subscheme X) (y : X) :
    (V ⊔ N).stalkIdeal y = V.stalkIdeal y ⊔ N.stalkIdeal y := by
  rw [← sSup_pair, stalkIdeal_sSup_eq, iSup_pair]

/-- An irreducible component of `X` containing an irreducible closed subset `C.pts` (`X` non-singular, so
the stalks of `X` are domains and `X` is reduced). -/
theorem exists_isComponent_pts_subset (hX : X.IsNonsingular) {C : Subscheme X}
    (hC : _root_.IsIrreducible C.pts) :
    ∃ Z₁ : Closeds X, Subscheme.ofClosed Z₁ ∈ (⊥ : Subscheme X).irreducibleComponents ∧
      C.pts ⊆ Z₁ := by
  obtain ⟨ξ, hξ⟩ : ∃ ξ, IsGenericPoint ξ C.pts := QuasiSober.sober hC C.support.isClosed
  have : IsRegularLocalRing (X.presheaf.stalk ξ) := hX ξ
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk ξ)
  obtain ⟨C₁, hC₁, hξC₁, -⟩ := exists_mem_irreducibleComponents_of_mem_minimalPrimes
    (⊥ : Subscheme X) ξ (p := ⊥) (by
      rw [stalkIdeal_bot_eq]
      exact ⟨⟨Ideal.isPrime_bot, le_rfl⟩, fun q hq _ => hq.2⟩)
  obtain ⟨Z₁, hZ₁, rfl⟩ := hC₁
  refine ⟨Z₁, ⟨Z₁, hZ₁, rfl⟩, ?_⟩
  rw [← hξ.def]
  refine closure_minimal (Set.singleton_subset_iff.mpr ?_) Z₁.isClosed
  rwa [pts_ofClosed] at hξC₁

/-- The ideal at `y` of the reduced subscheme on an irreducible component `Z₁` of `X`: zero on `Z₁`, the unit
ideal off `Z₁` (`X` non-singular). -/
theorem stalkIdeal_ofClosed_component (hX : X.IsNonsingular) {Z₁ : Closeds X}
    (hZ₁ : Subscheme.ofClosed Z₁ ∈ (⊥ : Subscheme X).irreducibleComponents) (y : X) :
    ((Subscheme.ofClosed Z₁).stalkIdeal y = ⊥ ∧ y ∈ Z₁) ∨
      ((Subscheme.ofClosed Z₁).stalkIdeal y = ⊤ ∧ y ∉ Z₁) := by
  by_cases hy : y ∈ Z₁
  · left
    refine ⟨?_, hy⟩
    have : IsRegularLocalRing (X.presheaf.stalk y) := hX y
    have := isDomain_of_isRegularLocalRing (X.presheaf.stalk y)
    have hmin := stalkIdeal_mem_minimalPrimes hZ₁ (show y ∈ (Subscheme.ofClosed Z₁).pts by
      rwa [pts_ofClosed])
    rw [stalkIdeal_bot_eq] at hmin
    exact eq_of_mem_minimalPrimes_of_isPrime (P := ⊥) hmin
  · right
    refine ⟨stalkIdeal_eq_top_of_notMem_pts (by rwa [pts_ofClosed]), hy⟩

/-- On an irreducible component `Z₁` of the non-singular `X`, a locally principal ideal sheaf which is non-zero at
one point is non-zero at every point of `Z₁`: at the generic point `η₁` of `Z₁` its stalk is the image of
the stalk at the point, which stays non-zero by injectivity of `O_x → O_{η₁}`, and conversely. -/
theorem stalkIdeal_ne_bot_of_mem_component (hX : X.IsNonsingular) {V : Subscheme X}
    (hV : V.IsLocallyPrincipal) {Z₁ : Closeds X}
    (hZ₁ : Subscheme.ofClosed Z₁ ∈ (⊥ : Subscheme X).irreducibleComponents) {x : X} (hx : x ∈ Z₁)
    (hVx : V.stalkIdeal x ≠ ⊥) {y : X} (hy : y ∈ Z₁) : V.stalkIdeal y ≠ ⊥ := by
  obtain ⟨Z, ⟨⟨hZirr, -⟩, -⟩, hZeq⟩ := hZ₁
  have hZZ : Z = Z₁ := by
    have := congrArg Subscheme.pts hZeq
    rw [pts_ofClosed, pts_ofClosed] at this
    exact Closeds.ext this.symm
  subst hZZ
  obtain ⟨η, hη⟩ : ∃ η, IsGenericPoint η (Z : Set X) := QuasiSober.sober hZirr Z.isClosed
  have hηx : η ⤳ x := by rw [specializes_iff_mem_closure, hη.def]; exact hx
  have hηy : η ⤳ y := by rw [specializes_iff_mem_closure, hη.def]; exact hy
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk x)
  -- `V_η ≠ 0`
  obtain ⟨f, hf⟩ := hV.exists_stalkIdeal_eq_span x
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hVx (by rw [hf, Ideal.span_singleton_eq_bot.mpr rfl])
  have hVη : V.stalkIdeal η ≠ ⊥ := by
    rw [stalkIdeal_eq_map_stalkSpecializes V hηx, hf, Ideal.map_span, Set.image_singleton, Ne,
      Ideal.span_singleton_eq_bot]
    exact fun h => hf0 (stalkSpecializes_injective_of_isDomain hηx (h.trans (map_zero _).symm))
  intro hVy
  apply hVη
  rw [stalkIdeal_eq_map_stalkSpecializes V hηy, hVy, Ideal.map_bot]

/-- If a locally principal ideal sheaf `V` is non-zero at every point of an irreducible component `Z₁` of the
non-singular `X`, then `V ⊔ ofClosed Z₁` is invertible: it agrees with `V` on `Z₁` (where `ofClosed Z₁` has zero
ideal, `V_y` being generated by a non-zero element of the domain `O_{X,y}`) and is the unit ideal off `Z₁`. -/
theorem isInvertibleIdeal_sup_ofClosed_component [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    {V : Subscheme X} (hV : V.IsLocallyPrincipal) {Z₁ : Closeds X}
    (hZ₁ : Subscheme.ofClosed Z₁ ∈ (⊥ : Subscheme X).irreducibleComponents)
    (hne : ∀ y ∈ Z₁, V.stalkIdeal y ≠ ⊥) :
    (V ⊔ Subscheme.ofClosed Z₁).IsInvertibleIdeal := by
  have := IsAlgebraicScheme.isNoetherian X
  rw [isInvertibleIdeal_iff_forall_exists_stalkIdeal_eq_span]
  intro y
  have : IsRegularLocalRing (X.presheaf.stalk y) := hX y
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk y)
  rcases stalkIdeal_ofClosed_component hX hZ₁ y with ⟨hN, hy⟩ | ⟨hN, -⟩
  · obtain ⟨f, hf⟩ := hV.exists_stalkIdeal_eq_span y
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact hne y hy (by rw [hf, Ideal.span_singleton_eq_bot.mpr rfl])
    exact ⟨f, mem_nonZeroDivisors_of_ne_zero hf0, by rw [stalkIdeal_sup_eq', hN, sup_bot_eq, hf]⟩
  · exact ⟨1, one_mem _, by rw [stalkIdeal_sup_eq', hN, sup_top_eq, Ideal.span_singleton_one]⟩

/-- **Ch. 0 §4 (I), p. 136, the converse, as printed.**  "The converse is true if `X` is imbedded in a
non-singular algebraic `B`-scheme `Y` such that the sheaf of ideals of `X` on `Y` is everywhere locally
principal": `V ⊆ X` a subscheme of the non-singular algebraic scheme `X` whose ideal sheaf is locally
principal (possibly zero on a connected component of `X`), `W ⊆ V` a non-singular subscheme, not
necessarily irreducible; if `V` is equi-multiple along `W`, then `V` is normally flat along `W`.

Proof: let `x ∈ W` and `C` the irreducible component of `W` through `x`, a non-singular irreducible subscheme
with `C_y = W_y` on `C`.  If `V_x = 0`, then `O_{V,x} = O_{X,x}` is regular and `V` is normally flat along the
non-singular `W` at `x` (`isNormallyFlatAlongAt'_of_isSimpleAt`).  Otherwise `V` is non-zero on the
irreducible component `Z₁` of `X` containing `C` (the stalk at the generic point of `Z₁` is the image of that
at `x`, and `O_{X,x} → O_{X,η}` is injective), so `V' = V ∪ Z₁` has an invertible ideal sheaf and the same ideals
as `V` on `C`.  Ch. II, Corollary 2 of Theorem 2 for `(V', C)` gives the normal flatness at `x`
(`Subscheme.isNormallyFlatAlong'_iff_isEquimultipleAlong`), because `V'` is equi-multiple along `C` (the multiplicities
of `V` and `V'` at points of `C` agree) and normal flatness at `x` depends only on `V_x` and `C_x = W_x`.

Deviation from the paper (gap filled): the paper cites Ch. II, where `V`'s ideal is invertible and `W` is irreducible; both
missing cases are proved here.  Not formalized: "but not in general". -/
@[blueprint "prop:0.4-I-converse-printed"
  (statement := /-- Let $V$ be a subscheme of a non-singular algebraic scheme $X$ whose sheaf of ideals
    on $X$ is everywhere locally principal, and $W$ a non-singular subscheme of $V$ (not necessarily
    irreducible). If $V$ is equi-multiple along $W$, then $V$ is normally flat along $W$. (Ch.~0 \S4 (I),
    p.~136, ``the converse''.)
    \textbf{Gap in the paper filled.} The paper refers to Ch.~II, where the ideal of $V$ is invertible and
    $W$ irreducible (\cref{prop:0.4-I-converse}); the cases $W$ reducible and the ideal of $V$ zero on a
    connected component of $X$ are proved here. -/)
  (proof := /-- Let $x\in W$ and $C$ the irreducible component of $W$ through $x$ (non-singular, irreducible,
    $C_y=W_y$ on $C$). If $V_x=0$, $\mathcal O_{V,x}=\mathcal O_{X,x}$ is regular, hence normally flat along
    $W$. Otherwise $V$ is non-zero on the irreducible component $Z_1$ of $X$ through $C$, so
    $V\cup Z_1$ is invertible, agrees with $V$ along $C$ and Ch.~II Cor.~2 of Th.~2
    (\cref{cor:II.2-thm2-2}) applies. -/)
  (latexEnv := "proposition")]
theorem isNormallyFlatAlong_of_isEquimultipleAlong_of_isLocallyPrincipal [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) (V W : Subscheme X) (hV : V.IsLocallyPrincipal) (hW : W.IsNonsingular)
    (hWV : W.IsContainedIn V) (h : (totalTransform V.ι W).IsEquimultipleAlong) :
    V.IsNormallyFlatAlong' W := by
  intro x hx
  obtain ⟨Z, hZcomp, hxZ, hZW, hZstalk, hCns, hCirr, hCsub⟩ := exists_component_of_isNonsingular hW hx
  set C : Subscheme X := Subscheme.ofClosed Z with hCdef
  have hCpts : C.pts = Z := pts_ofClosed Z
  have hCV : C.IsContainedIn V := hCsub.trans hWV
  have hxC : x ∈ C.pts := by rwa [hCpts]
  have hxV : x ∈ V.pts := pts_subset_of_isContainedIn hWV hx
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk x)
  by_cases hVx : V.stalkIdeal x = ⊥
  · -- `O_{V,x} = O_{X,x}` is regular
    have hVs : V.IsSimpleAt x := ⟨hxV, by
      rw [hVx]
      exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot (X.presheaf.stalk x)).symm⟩
    exact isNormallyFlatAlongAt'_of_isSimpleAt hWV hVs ⟨hx, isRegular_stalk_quot W hW hx⟩
  · obtain ⟨Z₁, hZ₁, hCZ₁⟩ := exists_isComponent_pts_subset hX (isIrreducible_pts C hCirr)
    have hZZ₁ : Z ≤ Z₁ := fun y hy => hCZ₁ (by rwa [hCpts])
    have hne : ∀ y ∈ Z₁, V.stalkIdeal y ≠ ⊥ := fun y hy =>
      stalkIdeal_ne_bot_of_mem_component hX hV hZ₁ (hZZ₁ hxZ) hVx hy
    set V' : Subscheme X := V ⊔ Subscheme.ofClosed Z₁ with hV'def
    have hinv : V'.IsInvertibleIdeal := isInvertibleIdeal_sup_ofClosed_component hX hV hZ₁ hne
    -- the stalks of `V'` and `V` agree along `Z₁`
    have hstalkV' : ∀ y ∈ Z₁, V'.stalkIdeal y = V.stalkIdeal y := fun y hy => by
      rcases stalkIdeal_ofClosed_component hX hZ₁ y with ⟨hN, -⟩ | ⟨-, hy'⟩
      · rw [hV'def, stalkIdeal_sup_eq', hN, sup_bot_eq]
      · exact absurd hy hy'
    have hCV' : C.IsContainedIn V' := by
      intro U
      refine sup_le (hCV U) ?_
      exact (Scheme.IdealSheafData.vanishingIdeal_antimono hZZ₁) U
    -- `V'` is equi-multiple along `C`
    have heq : (totalTransform V'.ι C).IsEquimultipleAlong := by
      have hmult : ∀ y : V'.toScheme, y ∈ (totalTransform V'.ι C).pts →
          ∃ w : V.toScheme, w ∈ (totalTransform V.ι W).pts ∧
            V'.toScheme.multAt y = V.toScheme.multAt w := by
        intro y hy
        have hyC : V'.ι y ∈ C.pts := by
          rw [FlatPreimm.pts_totalTransform] at hy
          exact hy
        have hyW : V'.ι y ∈ W.pts := hZW (by rwa [hCpts] at hyC)
        obtain ⟨w, hw⟩ := exists_ι_eq_of_mem_pts V (pts_subset_of_isContainedIn hWV hyW)
        refine ⟨w, ?_, ?_⟩
        · rw [FlatPreimm.pts_totalTransform]
          show V.ι w ∈ W.pts
          rw [hw]; exact hyW
        · have hyZ₁ : V.ι w ∈ Z₁ := by
            rw [hw]; exact hZZ₁ (by rwa [hCpts] at hyC)
          exact (multAt_eq_of_stalkIdeal_eq w y hw.symm (hstalkV' _ hyZ₁).symm).symm
      intro y₁ hy₁ y₂ hy₂
      obtain ⟨w₁, hw₁, e₁⟩ := hmult y₁ hy₁
      obtain ⟨w₂, hw₂, e₂⟩ := hmult y₂ hy₂
      rw [e₁, e₂]
      exact h w₁ hw₁ w₂ hw₂
    have hnf := (isNormallyFlatAlong'_iff_isEquimultipleAlong hX V' C hinv hCns hCirr hCV').mpr heq x hxC
    -- transfer to `(V, W)` at `x`: only `V_x` and `C_x = W_x` matter
    rw [isNormallyFlatAlongAt'_iff V' C hCV' x] at hnf
    rw [isNormallyFlatAlongAt'_iff V W hWV x]
    refine ⟨hx, ?_⟩
    have := hnf.2
    rwa [hstalkV' x (hZZ₁ hxZ), hZstalk x hxZ] at this

end Subscheme

end Hironaka
