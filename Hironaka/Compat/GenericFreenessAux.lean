/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect

/-!
# Compatibility layer: freeness after inverting one element

Lemma 3 of Ch. II §1 (p. 188, generic freeness) is cited from Grothendieck (Lemma 6.7 of the
seminar note "Séminaire de Géométrie Algébrique de l'IHES, No. IV (1960)", p. 181).
Mathlib has local freeness of finitely presented modules
(`Module.FinitePresentation.exists_free_localizedModule_powers`) but not generic freeness.
This file collects the stability properties of "`M_f` is a free `A_f`-module" used in the
proof in `Hironaka/Compat/GenericFreeness.lean`: passing from `f` to `fg`, invariance under
isomorphism, the case of a module of finite type over a noetherian domain, extensions, and
exhaustive increasing filtrations by submodules.

The last two rest on two ring-agnostic statements, proved here as public helpers:
`Hironaka.free_of_shortExact_of_free` (an extension of free modules is free) and
`Hironaka.free_of_exhaustive_filtration_of_free_subquotients` (a module with an exhaustive
increasing filtration whose first term and successive quotients are free is free).
-/

@[expose] public section

namespace Hironaka

universe u

/-- If `M_f` is free over `A_f`, then `M_{fg}` is free over `A_{fg}`.

Proof: `A_{fg}` is the localization of the `A_f`-algebra `A_f` at the powers of `fg/1`, and the
canonical map `M_f → M_{fg}` is the corresponding localization of `A_f`-modules; localization
preserves freeness (`Module.free_of_isLocalizedModule`). -/
theorem free_localizedModule_away_mul {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M]
    [Module A M] (f g : A)
    [Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)] :
    Module.Free (Localization.Away (f * g)) (LocalizedModule (Submonoid.powers (f * g)) M) := by
  let Af := Localization.Away f
  let Afg := Localization.Away (f * g)
  let Mf := LocalizedModule (Submonoid.powers f) M
  let Mfg := LocalizedModule (Submonoid.powers (f * g)) M
  -- `A_{fg}` as an `A_f`-algebra: transport the structure of `(A_f)_{g/1}` along the canonical
  -- `A`-algebra isomorphism `(A_f)_{g/1} ≅ A_{fg}`.
  let T := Localization.Away (algebraMap A Af g)
  let e : T ≃ₐ[A] Afg := IsLocalization.algEquiv (Submonoid.powers (f * g)) T Afg
  let : Algebra Af Afg := (e.toRingEquiv.toRingHom.comp (algebraMap Af T)).toAlgebra
  have hT : IsLocalization.Away (algebraMap A Af g) Afg :=
    (IsLocalization.isLocalization_iff_of_ringEquiv _ e.toRingEquiv).mp inferInstance
  have hfu : IsUnit (algebraMap A Af f) := IsLocalization.Away.algebraMap_isUnit f
  -- Since `f/1` is a unit of `A_f`, `A_{fg}` is also `A_f` localized at `fg/1`.
  have hT' : IsLocalization.Away (algebraMap A Af (f * g)) Afg := by
    refine (IsLocalization.Away.iff_of_associated ?_).mp hT
    rw [map_mul]
    exact (associated_unit_mul_left _ _ hfu).symm
  have : IsScalarTower A Af Afg := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A Afg a = e (algebraMap Af T (algebraMap A Af a))
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
  -- `M_{fg}` as an `A_f`-module, by restriction of scalars along `A_f → A_{fg}`.
  let : Module Af Mfg := Module.compHom Mfg (algebraMap Af Afg)
  have : IsScalarTower Af Afg Mfg := ⟨fun a b m => mul_smul (algebraMap Af Afg a) b m⟩
  have : IsScalarTower A Af Mfg := ⟨fun a b m => by
    change algebraMap Af Afg (a • b) • m = a • (algebraMap Af Afg b • m)
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul,
      algebraMap_smul]⟩
  -- The canonical map `φ : M_f → M_{fg}` is the localization of `M_f` at `fg` over `A`.
  let mf := LocalizedModule.mkLinearMap (Submonoid.powers f) M
  let mh := LocalizedModule.mkLinearMap (Submonoid.powers (f * g)) M
  have hhu : IsUnit (algebraMap A (Module.End A Mfg) (f * g)) :=
    IsLocalizedModule.Away.isUnit_algebraMap mh (f * g)
  have hfu' : ∀ y : Submonoid.powers f, IsUnit (algebraMap A (Module.End A Mfg) y) := by
    rintro ⟨_, n, rfl⟩
    rw [map_mul, ((Commute.all f g).map (algebraMap A (Module.End A Mfg))).isUnit_mul_iff] at hhu
    simpa using hhu.1.pow n
  let φ := IsLocalizedModule.lift (Submonoid.powers f) mf mh hfu'
  have hφ : ∀ x, φ (mf x) = mh x := fun x => IsLocalizedModule.lift_apply _ _ _ _ x
  have hfu'' : IsUnit (algebraMap A (Module.End A Mf) f) :=
    IsLocalizedModule.Away.isUnit_algebraMap mf f
  have hloc : IsLocalizedModule.Away (f * g) φ := by
    refine IsLocalizedModule.Away.mk_of_addCommGroup hhu (fun y => ?_) (fun x hx => ?_)
    · obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj mh (f * g) y
      exact ⟨n, mf x, by rw [hφ, hx]⟩
    · obtain ⟨k, x', hx'⟩ := IsLocalizedModule.Away.surj mf f x
      have h0 : mh x' = 0 := by rw [← hφ, ← hx', map_smul, hx, smul_zero]
      obtain ⟨m, hm⟩ := IsLocalizedModule.Away.exists_of_eq (f * g) (f := mh)
        (h0.trans (map_zero mh).symm)
      rw [smul_zero] at hm
      refine ⟨m, ?_⟩
      have h1 : f ^ k • ((f * g) ^ m • x) = 0 := by
        rw [smul_comm, hx', ← map_smul, hm, map_zero]
      have hinj : Function.Injective (algebraMap A (Module.End A Mf) (f ^ k)) :=
        (Module.End.isUnit_iff _).mp (by rw [map_pow]; exact hfu''.pow k) |>.1
      apply hinj
      rw [map_zero]
      exact h1
  -- Hence `φ`, viewed as an `A_f`-linear map, is the localization at `fg/1` over `A_f`.
  let φ' : Mf →ₗ[Af] Mfg := φ.extendScalarsOfIsLocalization (Submonoid.powers f) Af
  have : IsLocalizedModule (Submonoid.powers (f * g)) (φ'.restrictScalars A) := hloc
  have hloc' : IsLocalizedModule (Submonoid.powers (algebraMap A Af (f * g))) φ' := by
    rw [← Algebra.algebraMapSubmonoid_powers]
    exact IsLocalizedModule.of_restrictScalars _ φ'
  exact Module.free_of_isLocalizedModule (Rₛ := Afg)
    (Submonoid.powers (algebraMap A Af (f * g))) φ'

/-- Freeness of `M_f` over `A_f` only depends on `M` up to isomorphism. -/
theorem free_localizedModule_of_linearEquiv {A : Type u} [CommRing A] (f : A) {M N : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N)
    [Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)] :
    Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) N) :=
  Module.Free.of_equiv (IsLocalizedModule.mapEquiv (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) N) (Localization.Away f) e)

/-- A module of finite type over a noetherian domain becomes free after inverting one non-zero
element. -/
@[blueprint "compat:generic-freeness-finite"
  (statement := /-- Let $A$ be a noetherian integral domain and $M$ an $A$-module of finite
    type. Then there is a non-zero $f\in A$ such that $M_f$ is a free $A_f$-module. -/)
  (proof := /-- $M\otimes_AK$ is a vector space over the field of fractions $K=A_{(0)}$, hence
    free, and $M$ is finitely presented since $A$ is noetherian; a basis of $M_{(0)}$ spreads
    out to a basis of $M_f$ for some $f\notin(0)$ (Mathlib's
    \texttt{Module.FinitePresentation.exists\_free\_localizedModule\_powers}). -/)
  (latexEnv := "lemma")]
theorem exists_free_localizedModule_of_finite (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ f : A, f ≠ 0 ∧
      Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) M) (FractionRing A)
  exact ⟨r, nonZeroDivisors.ne_zero hr, hfree⟩

/-- An extension of free modules is free: if `0 → N → M → Q → 0` is exact with `N` and `Q`
free, then `M ≅ N × Q` (the surjection splits since `Q` is projective) is free. -/
theorem free_of_shortExact_of_free {R : Type*} [Ring R] {N M Q : Type*} [AddCommGroup N]
    [Module R N] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    (i : N →ₗ[R] M) (p : M →ₗ[R] Q) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) [Module.Free R N] [Module.Free R Q] : Module.Free R M := by
  obtain ⟨l, hl⟩ := Module.projective_lifting_property p LinearMap.id hp
  exact Module.Free.of_equiv ((hex.splitSurjectiveEquiv hi ⟨l, hl⟩).1.symm)

/-- Auxiliary for `free_of_exhaustive_filtration_of_free_subquotients`: given sections
`σ j : Y (j+1)/Y j → Y (j+1)`, the pieces `W 0 = Y 0` and `W (j+1) = σ j (Y (j+1)/Y j)`. -/
private def filtrationSplitPieces {R X : Type*} [Ring R] [AddCommGroup X] [Module R X]
    (Y : ℕ → Submodule R X)
    (σ : ∀ j, (↥(Y (j + 1)) ⧸ Submodule.comap (Y (j + 1)).subtype (Y j)) →ₗ[R] Y (j + 1)) :
    ℕ → Submodule R X
  | 0 => Y 0
  | j + 1 => LinearMap.range ((Y (j + 1)).subtype ∘ₗ σ j)

/-- A module `X` with an increasing sequence of submodules `Y 0 ≤ Y 1 ≤ ⋯` whose union is `X`,
such that `Y 0` and all `Y (j+1)/Y j` are free, is free.

Proof: choose sections `σ j` of the projections `Y (j+1) → Y (j+1)/Y j` (the targets are
projective). Then `X` is the internal direct sum of `Y 0` and the images of the `σ j`, each of
which is free; the union of their bases is a basis of `X`. -/
theorem free_of_exhaustive_filtration_of_free_subquotients {R X : Type*} [Ring R]
    [AddCommGroup X] [Module R X] (Y : ℕ → Submodule R X) (hY : Monotone Y)
    (htop : ⨆ j, Y j = ⊤) (h0 : Module.Free R (Y 0))
    (hsucc : ∀ j, Module.Free R (↥(Y (j + 1)) ⧸ Submodule.comap (Y (j + 1)).subtype (Y j))) :
    Module.Free R X := by
  classical
  -- Sections of the projections `Y (j+1) → Y (j+1)/Y j`.
  have hσ : ∀ j, ∃ σ : (↥(Y (j + 1)) ⧸ Submodule.comap (Y (j + 1)).subtype (Y j)) →ₗ[R]
      Y (j + 1), (Submodule.comap (Y (j + 1)).subtype (Y j)).mkQ ∘ₗ σ = LinearMap.id :=
    fun j => by
      have := hsucc j
      exact Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _)
  choose σ hσ using hσ
  have hσ' : ∀ j q, (Submodule.comap (Y (j + 1)).subtype (Y j)).mkQ (σ j q) = q :=
    fun j q => LinearMap.congr_fun (hσ j) q
  let W := filtrationSplitPieces Y σ
  have hWs : ∀ j, W (j + 1) = LinearMap.range ((Y (j + 1)).subtype ∘ₗ σ j) := fun j => rfl
  have hWle : ∀ j, W j ≤ Y j := by
    rintro (_ | j)
    · exact le_rfl
    · rw [hWs]
      rintro _ ⟨q, rfl⟩
      exact (σ j q).2
  -- `W (j+1) ∩ Y j = 0`.
  have hdisj : ∀ j, ∀ x ∈ W (j + 1), x ∈ Y j → x = 0 := by
    intro j x hx hxY
    rw [hWs, LinearMap.mem_range] at hx
    obtain ⟨q, rfl⟩ := hx
    have hq : q = 0 := by
      rw [← hσ' j q, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hxY
    simp [hq]
  have hfree : ∀ j, Module.Free R (W j) := by
    rintro (_ | j)
    · exact h0
    · have := hsucc j
      have hinj : Function.Injective ((Y (j + 1)).subtype ∘ₗ σ j) :=
        (Y (j + 1)).injective_subtype.comp (Function.LeftInverse.injective (hσ' j))
      exact Module.Free.of_equiv (LinearEquiv.ofInjective _ hinj)
  -- The `W j` span: `Y n ≤ ⨆ j, W j` by induction on `n`.
  have hsup : ∀ n, Y n ≤ ⨆ j, W j := by
    intro n
    induction n with
    | zero => exact le_iSup W 0
    | succ n ih =>
      intro x hx
      let x' : Y (n + 1) := ⟨x, hx⟩
      let q := (Submodule.comap (Y (n + 1)).subtype (Y n)).mkQ x'
      have h1 : ((x' - σ n q : Y (n + 1)) : X) ∈ Y n := by
        have h : (Submodule.comap (Y (n + 1)).subtype (Y n)).mkQ (x' - σ n q) = 0 := by
          rw [map_sub, hσ', sub_self]
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h
      have h2 : ((σ n q : Y (n + 1)) : X) ∈ W (n + 1) := by
        rw [hWs]
        exact ⟨q, rfl⟩
      have hx' : x = ((x' - σ n q : Y (n + 1)) : X) + (σ n q : X) := by
        simp [x']
      rw [hx']
      exact add_mem (ih h1) (le_iSup W (n + 1) h2)
  -- The `W j` are independent: induction on the largest index of a finite sum.
  have hindep : iSupIndep W := by
    rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s
    induction s using Finset.induction_on_max with
    | empty => simp
    | insert b s hlt ih =>
      intro v hv hsum
      have hbs : b ∉ s := fun h => lt_irrefl b (hlt b h)
      rw [Finset.sum_insert hbs] at hsum
      have hvb : v b = 0 := by
        rcases b with _ | m
        · have hs : s = ∅ :=
            Finset.eq_empty_of_forall_notMem fun a ha => Nat.not_lt_zero a (hlt a ha)
          simpa [hs] using hsum
        · refine hdisj m _ (hv _ (Finset.mem_insert_self _ _)) ?_
          rw [eq_neg_of_add_eq_zero_left hsum]
          refine neg_mem (Submodule.sum_mem _ fun a ha => ?_)
          exact hY (Nat.lt_succ_iff.mp (hlt a ha)) (hWle a (hv a (Finset.mem_insert_of_mem ha)))
      rw [hvb, zero_add] at hsum
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hvb
      · exact ih v (fun a ha => hv a (Finset.mem_insert_of_mem ha)) hsum i hi
  have hint : DirectSum.IsInternal W := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep ?_
    rw [eq_top_iff, ← htop]
    exact iSup_le hsup
  exact Module.Free.of_basis
    (hint.collectedBasis fun j => @Module.Free.chooseBasis R (W j) _ _ _ (hfree j))

/-- A module with an exhaustive increasing filtration `F 0 ⊆ F 1 ⊆ ⋯` whose first term and
successive quotients become free after inverting `f` becomes free after inverting `f`. -/
@[blueprint "compat:free-localization-filtration"
  (statement := /-- Let $A$ be a ring, $f\in A$ and $M$ an $A$-module with an increasing
    sequence of submodules $F_0\subseteq F_1\subseteq\cdots$ whose union is $M$. If
    $(F_0)_f$ and all $(F_{j+1}/F_j)_f$ are free $A_f$-modules, then $M_f$ is a free
    $A_f$-module. -/)
  (proof := /-- Localization is exact, so $(F_j)_f$ is an increasing sequence of submodules of
    $M_f$ with union $M_f$ and free successive quotients $(F_{j+1}/F_j)_f$. Splitting each
    $(F_{j+1})_f\to(F_{j+1}/F_j)_f$ gives an isomorphism
    $(F_0)_f\oplus\bigoplus_j(F_{j+1}/F_j)_f\cong M_f$, and a direct sum of free modules is
    free. -/)
  (latexEnv := "lemma")]
theorem free_localizedModule_of_filtration {A : Type u} [CommRing A] (f : A) {M : Type u}
    [AddCommGroup M] [Module A M] (F : ℕ → Submodule A M) (hF : Monotone F)
    (htop : ⨆ j, F j = ⊤)
    (h0 : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) (F 0)))
    (hsucc : ∀ j, Module.Free (Localization.Away f)
      (LocalizedModule (Submonoid.powers f)
        (↥(F (j + 1)) ⧸ Submodule.comap (F (j + 1)).subtype (F j)))) :
    Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  -- The element `m/s` of `(P)_f ⊆ M_f` is `m/s` computed in `M_f`.
  have hcoe : ∀ (P : Submodule A M) (m : P) (s : Submonoid.powers f),
      ((IsLocalizedModule.mk' (P.toLocalized (Submonoid.powers f)) m s :
          P.localized (Submonoid.powers f)) : LocalizedModule (Submonoid.powers f) M) =
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap (Submonoid.powers f) M) (m : M) s := by
    intro P m s
    rw [eq_comm, IsLocalizedModule.mk'_eq_iff]
    exact (congrArg Subtype.val
      (IsLocalizedModule.mk'_cancel' (P.toLocalized (Submonoid.powers f)) m s)).symm
  -- Apply the abstract statement to the filtration `(F j)_f` of `M_f`.
  refine free_of_exhaustive_filtration_of_free_subquotients
    (fun j => (F j).localized (Submonoid.powers f)) ?_ ?_ ?_ ?_
  · intro i j hij
    exact (Submodule.localized'gi (Localization (Submonoid.powers f)) (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)).gc.monotone_l (hF hij)
  · show ⨆ j, (F j).localized' (Localization (Submonoid.powers f)) (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M) = ⊤
    rw [← Submodule.localized'_iSup, htop, Submodule.localized'_top]
  · have := h0
    exact Module.Free.of_equiv (Submodule.localizedEquiv (Submonoid.powers f) (F 0)).symm
  · intro j
    -- Inside `(F (j+1))_f`, the localization of `F j ⊆ F (j+1)` is `(F j)_f`.
    have heq : (Submodule.comap (F (j + 1)).subtype (F j)).localized'
        (Localization (Submonoid.powers f)) (Submonoid.powers f)
        ((F (j + 1)).toLocalized (Submonoid.powers f)) =
        Submodule.comap ((F (j + 1)).localized (Submonoid.powers f)).subtype
          ((F j).localized (Submonoid.powers f)) := by
      ext ⟨x, hx⟩
      constructor
      · rintro ⟨m, hm, s, hms⟩
        refine ⟨m, hm, s, ?_⟩
        rw [← hcoe (F (j + 1)) m s, hms]
        rfl
      · rintro ⟨m, hm, s, hms⟩
        refine ⟨⟨m, hF (Nat.le_succ j) hm⟩, hm, s, Subtype.ext ?_⟩
        rw [hcoe (F (j + 1)) ⟨m, hF (Nat.le_succ j) hm⟩ s]
        exact hms
    -- `(F (j+1))_f / (F j)_f ≅ (F (j+1)/F j)_f`.
    have := hsucc j
    exact Module.Free.of_equiv
      (((IsLocalizedModule.iso (Submonoid.powers f)
        ((Submodule.comap (F (j + 1)).subtype (F j)).toLocalizedQuotient'
          (Localization (Submonoid.powers f)) (Submonoid.powers f)
          ((F (j + 1)).toLocalized (Submonoid.powers f)))).extendScalarsOfIsLocalization
            (Submonoid.powers f) (Localization (Submonoid.powers f))).trans
        (Submodule.quotEquivOfEq _ _ heq))

end Hironaka
