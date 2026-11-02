/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Architect
public import Hironaka.Compat.DimInequality
public import Hironaka.Compat.LocalizeSuccession

/-!
# Compatibility layer for Ch. IV §1, Remark 2: `dim O_{X',x'} ≤ dim O_{X,f(x')}`

Remark 2 of Ch. IV §1 (p. 277) asserts `dim(X'_S) = dim(S)` for a succession of monoidal
transformations with nowhere dense centers of an arbitrary algebraic scheme `X`.  The inequality
`≤` rests on the dimension inequality for the local rings of a monoidal transformation: every
local ring of `X'` is a localization of a chart algebra `A[I/a]` (`compat:blowup-stalk-chart`),
which is generated over `A` by elements `g/a` with `a · (g/a) ∈ A`, `a` a non-zero-divisor; so
`ht 𝔓 ≤ ht(𝔓 ∩ A)` for every prime `𝔓` of `A[I/a]`.  The birational case of the dimension
inequality for domains is `DimIneq.height_le_height_comap_of_adjoin_eq_top`
(`Hironaka/Compat/DimInequality.lean`); the general case reduces to it modulo the minimal primes
of `A[I/a]`, which do not contain the non-zero-divisor `a`.

No non-singularity is needed (compare `MonoidalTransformation.dimAt_le`, which uses the
regularity of `O_{X,f(x')}`).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Hironaka

universe u

namespace LocSucc

/-- For a surjective ring homomorphism, `comap` is an order embedding of prime spectra. -/
theorem comap_le_comap_iff_of_surjective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (p q : PrimeSpectrum S) :
    PrimeSpectrum.comap φ p ≤ PrimeSpectrum.comap φ q ↔ p ≤ q := by
  refine ⟨fun h => ?_, fun h => Ideal.comap_mono h⟩
  change p.asIdeal ≤ q.asIdeal
  rw [← Ideal.map_comap_of_surjective φ hφ p.asIdeal, ← Ideal.map_comap_of_surjective φ hφ
    q.asIdeal]
  exact Ideal.map_mono h

theorem strictMono_comap_of_surjective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) : StrictMono (PrimeSpectrum.comap φ) := by
  intro p q hpq
  rw [lt_iff_le_not_ge, comap_le_comap_iff_of_surjective φ hφ,
    comap_le_comap_iff_of_surjective φ hφ]
  exact lt_iff_le_not_ge.mp hpq

/-- The dimension inequality for a finitely generated extension `C` of a noetherian ring `A`
whose generators `x_i` satisfy `a x_i ∈ A` for a non-zero-divisor `a` of `C`:
`ht 𝔓 ≤ ht(𝔓 ∩ A)` for every prime `𝔓` of `C` (Matsumura, Th. 15.5, transcendence degree `0`).

A chain of primes below `𝔓` starts above a minimal prime `Q` of `C`; since `a` is a
non-zero-divisor, `a ∉ Q`, and `C/Q` is a birational extension of the domain `A/(Q ∩ A)`, to
which `DimIneq.height_le_height_comap_of_adjoin_eq_top` applies. -/
theorem height_le_height_comap_of_generators {A C : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing C] [Algebra A C] {a : A} (ha : algebraMap A C a ∈ nonZeroDivisors C) {ι : Type*}
    [Fintype ι] (x : ι → C) (hx : ∀ i, ∃ r : A, algebraMap A C a * x i = algebraMap A C r)
    (hadj : Algebra.adjoin A (Set.range x) = ⊤) (P : Ideal C) [hP : P.IsPrime] :
    P.height ≤ (P.comap (algebraMap A C)).height := by
  classical
  let P' : PrimeSpectrum C := ⟨P, hP⟩
  have hPc : (P.comap (algebraMap A C)).IsPrime := Ideal.comap_isPrime _ _
  rw [show P = P'.asIdeal from rfl, PrimeSpectrum.height_eq_orderHeight]
  refine Order.height_le_iff.mpr fun p hp => ?_
  -- a minimal prime below the chain
  obtain ⟨Q, hQmin, hQle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal C))
    (J := p.head.asIdeal) bot_le
  have hQ : Q.IsPrime := hQmin.1.1
  have haQ : algebraMap A C a ∉ Q := fun h =>
    Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hQmin) h ha
  set φ := Ideal.Quotient.mk Q with hφ
  have hφs : Function.Surjective φ := Ideal.Quotient.mk_surjective
  have hrange : ∀ r : PrimeSpectrum C, Q ≤ r.asIdeal →
      ∃ rb : PrimeSpectrum (C ⧸ Q), PrimeSpectrum.comap φ rb = r := fun r hr => by
    have hk : RingHom.ker φ ≤ r.asIdeal := by rw [hφ, Ideal.mk_ker]; exact hr
    refine ⟨⟨r.asIdeal.map φ, Ideal.map_isPrime_of_surjective hφs hk⟩, ?_⟩
    ext1
    change (r.asIdeal.map φ).comap φ = r.asIdeal
    rw [Ideal.comap_map_of_surjective φ hφs, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hk
  have hpi : ∀ i, Q ≤ (p i).asIdeal := fun i => hQle.trans (p.monotone (Fin.zero_le i))
  -- the chain in `C/Q`
  let pbar : LTSeries (PrimeSpectrum (C ⧸ Q)) :=
    ⟨p.length, fun i => (hrange _ (hpi i)).choose, fun i => by
      have h : p.toFun i.castSucc < p.toFun i.succ := p.step i
      show (hrange _ (hpi i.castSucc)).choose < (hrange _ (hpi i.succ)).choose
      rw [lt_iff_le_not_ge] at h ⊢
      rw [← comap_le_comap_iff_of_surjective φ hφs, ← comap_le_comap_iff_of_surjective φ hφs,
        (hrange _ (hpi i.castSucc)).choose_spec, (hrange _ (hpi i.succ)).choose_spec]
      exact h⟩
  have hheadP : p.head ≤ P' := (p.monotone (Fin.zero_le (Fin.last _))).trans hp
  obtain ⟨Pbar, hPbar⟩ := hrange P' (hQle.trans hheadP)
  have hlast : pbar.last ≤ Pbar := by
    rw [← comap_le_comap_iff_of_surjective φ hφs, hPbar]
    show PrimeSpectrum.comap φ (hrange _ (hpi (Fin.last _))).choose ≤ P'
    rw [(hrange _ (hpi (Fin.last _))).choose_spec]
    exact hp
  have h1 : (p.length : ℕ∞) ≤ Pbar.asIdeal.height := by
    rw [PrimeSpectrum.height_eq_orderHeight]
    exact Order.length_le_height hlast
  -- the dimension inequality in the domain case
  set q₀ := Q.comap (algebraMap A C) with hq₀
  have hq₀p : q₀.IsPrime := Ideal.comap_isPrime _ _
  have hinj : Function.Injective (algebraMap (A ⧸ q₀) (C ⧸ Q)) :=
    Ideal.algebraMap_quotient_injective
  let s : Finset (C ⧸ Q) := Finset.univ.image fun i => Ideal.Quotient.mk Q (x i)
  have hd : Ideal.Quotient.mk q₀ a ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact haQ
  have hds : ∀ y ∈ s, ∃ r : A ⧸ q₀,
      algebraMap (A ⧸ q₀) (C ⧸ Q) (Ideal.Quotient.mk q₀ a) * y =
        algebraMap (A ⧸ q₀) (C ⧸ Q) r := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨r, hr⟩ := hx i
    refine ⟨Ideal.Quotient.mk q₀ r, ?_⟩
    change Ideal.Quotient.mk Q (algebraMap A C a) * Ideal.Quotient.mk Q (x i) =
      Ideal.Quotient.mk Q (algebraMap A C r)
    rw [← map_mul, hr]
  have hs : Algebra.adjoin (A ⧸ q₀) (s : Set (C ⧸ Q)) = ⊤ := by
    refine eq_top_iff.mpr fun y hytop => ?_
    clear hytop
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hc : c ∈ Algebra.adjoin A (Set.range x) := hadj ▸ Algebra.mem_top
    induction hc using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Algebra.subset_adjoin (Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    | algebraMap r => exact Subalgebra.algebraMap_mem _ (Ideal.Quotient.mk q₀ r)
    | add y z _ _ ihy ihz =>
      rw [map_add]
      exact Subalgebra.add_mem _ ihy ihz
    | mul y z _ _ ihy ihz =>
      rw [map_mul]
      exact Subalgebra.mul_mem _ ihy ihz
  let R' : PrimeSpectrum (A ⧸ q₀) := ⟨Pbar.asIdeal.comap (algebraMap (A ⧸ q₀) (C ⧸ Q)),
    Ideal.comap_isPrime _ _⟩
  have h2 : Pbar.asIdeal.height ≤ R'.asIdeal.height :=
    DimIneq.height_le_height_comap_of_adjoin_eq_top hinj hd s hds hs Pbar.asIdeal
  -- back to `A`
  have hR'A : PrimeSpectrum.comap (Ideal.Quotient.mk q₀) R' =
      ⟨P.comap (algebraMap A C), hPc⟩ := by
    ext c
    change algebraMap (A ⧸ q₀) (C ⧸ Q) (Ideal.Quotient.mk q₀ c) ∈ Pbar.asIdeal ↔
      algebraMap A C c ∈ P
    have : algebraMap (A ⧸ q₀) (C ⧸ Q) (Ideal.Quotient.mk q₀ c) = φ (algebraMap A C c) := rfl
    rw [this, ← Ideal.mem_comap]
    change algebraMap A C c ∈ (PrimeSpectrum.comap φ Pbar).asIdeal ↔ _
    rw [hPbar]
  have h3 : R'.asIdeal.height ≤ (P.comap (algebraMap A C)).height := by
    rw [PrimeSpectrum.height_eq_orderHeight]
    calc Order.height R'
        ≤ Order.height (PrimeSpectrum.comap (Ideal.Quotient.mk q₀) R') :=
          Order.height_le_height_apply_of_strictMono _
            (strictMono_comap_of_surjective _ Ideal.Quotient.mk_surjective) R'
      _ = (P.comap (algebraMap A C)).height := by
          rw [hR'A, ← PrimeSpectrum.height_eq_orderHeight]
  exact h1.trans (h2.trans h3)

/-- The dimension inequality for the chart algebras of a monoidal transformation:
`ht 𝔓 ≤ ht(𝔓 ∩ A)` for every prime `𝔓` of `A[I/a]` (`A` noetherian). -/
theorem height_le_height_comap_chartAlgebra {A : Type*} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {a : A} (P : Ideal (chartAlgebra I a)) [P.IsPrime] :
    P.height ≤ (P.comap (algebraMap A (chartAlgebra I a))).height := by
  obtain ⟨g, hg⟩ := (IsNoetherian.noetherian I : I.FG)
  have hgI : ∀ i ∈ g, i ∈ I := fun i hi => hg ▸ Submodule.subset_span hi
  have ha : algebraMap A (chartAlgebra I a) a ∈ nonZeroDivisors (chartAlgebra I a) :=
    algebraMap_mem_nonZeroDivisors_chartAlgebra
  let x : g → chartAlgebra I a := fun i => chartAlgebra.frac (a := a) (hgI i.1 i.2)
  have hx : ∀ i, ∃ r : A, algebraMap A (chartAlgebra I a) a * x i =
      algebraMap A (chartAlgebra I a) r := fun i => ⟨i.1, chartAlgebra.algebraMap_mul_frac _⟩
  have hadj : Algebra.adjoin A (Set.range x) = ⊤ := DimIneq.chartAlgebra.adjoin_frac_eq_top g hg hgI
  exact height_le_height_comap_of_generators (C := chartAlgebra I a) ha x hx hadj P

end LocSucc

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X}

/-- `dim_{x'} X' ≤ dim_{f(x')} X` for a monoidal transformation of a locally noetherian scheme:
the local ring of `X'` at `x'` is a localization of a chart algebra `A[I/a]` at a prime `𝔓`, and
that of `X` at `f(x')` is `A_{𝔓 ∩ A}` (`compat:blowup-stalk-chart`). -/
theorem dimAt_le_of_isLocallyNoetherian [IsLocallyNoetherian X] (t : MonoidalTransformation X B)
    (y : t.X') : t.X'.dimAt y ≤ X.dimAt (t.f y) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (t.f y)) isOpen_univ
  obtain ⟨a, ha, hya⟩ := t.exists_mem_chartOpen ⟨U, hU⟩ hyU
  obtain ⟨z, rfl⟩ : y ∈ Set.range (t.chart ⟨U, hU⟩ ha) := by
    rw [t.range_chart _ ha]
    exact hya
  have := t.isOpenImmersion_chart ⟨U, hU⟩ ha
  have hfz : t.f (t.chart ⟨U, hU⟩ ha z) = (isAffineOpen_of_mem_affineOpens ⟨U, hU⟩).fromSpec
      (Spec.map (chartAlgebraMap B ⟨U, hU⟩ a) z) := by
    rw [← Scheme.Hom.comp_apply, t.chart_f, chartToBase, Scheme.Hom.comp_apply]
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : z.asIdeal.IsPrime := z.isPrime
  rw [hfz, LocSucc.dimAt_eq_coheight, LocSucc.dimAt_eq_coheight,
    coheight_eq_of_isOpenImmersion, coheight_eq_of_isOpenImmersion,
    ← idealHeight_eq_coheight, ← idealHeight_eq_coheight]
  exact_mod_cast LocSucc.height_le_height_comap_chartAlgebra z.asIdeal

end MonoidalTransformation

namespace MonoidalSuccession

variable {X Y : Scheme.{u}}

private theorem dimAt_le_composite_of_isAlgebraicScheme_explicit [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (s : MonoidalSuccession X Y)
    (hX : IsAlgebraicScheme X) (y : Y) : Y.dimAt y ≤ X.dimAt (s.composite y) := by
  induction s with
  | nil X => exact le_rfl
  | @cons X₀ B t Y₀ rest ih =>
    have := hX
    have := IsAlgebraicScheme.isNoetherian X₀
    refine (ih t.isAlgebraicScheme y).trans ?_
    rw [composite_cons, Scheme.Hom.comp_apply]
    exact t.dimAt_le_of_isLocallyNoetherian _

/-- Along a succession of monoidal transformations of an algebraic scheme,
`dim_y X_m ≤ dim_{f(y)} X`. -/
theorem dimAt_le_composite_of_isAlgebraicScheme [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (s : MonoidalSuccession X Y)
    [IsAlgebraicScheme X] (y : Y) : Y.dimAt y ≤ X.dimAt (s.composite y) :=
  dimAt_le_composite_of_isAlgebraicScheme_explicit s inferInstance y

end MonoidalSuccession

end Hironaka
