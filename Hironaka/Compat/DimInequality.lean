/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Compat.BlowupCharts

/-!
# The dimension inequality for birational extensions (used in Ch. I §1, Remark 1, p. 169)

Let `R` be a noetherian domain and `S ⊇ R` a domain generated over `R` by finitely many elements
with a common denominator `d ≠ 0` (so `S` is a finitely generated birational extension of `R`).
Then `ht P ≤ ht (P ∩ R)` for every prime `P` of `S`, and `dim S ≤ dim R`
(Matsumura, *Commutative Ring Theory*, Thm. 15.5, with transcendence degree `0`).  The proof
adjoins one generator `t` at a time: writing `S = R[X]/K` with `d X - r ∈ K`, a chain below `P`
lifts to a chain below `P' ⊆ R[X]` starting at `K ≠ 0`, so `ht P + 1 ≤ ht P'`, while
`ht P' ≤ ht p + 1` by Krull's height theorem for `R → R[X]` (the fibre `k(p)[X]` has
dimension one).

Applied to the chart algebra `A[I/a]` of a monoidal transformation modulo a prime `Q ∌ a`
(`DimIneq.ringKrullDim_quotient_chartAlgebra_le`), this gives `dim A[I/a]/Q ≤ dim A/(Q ∩ A)`,
the dimension estimate behind `dim(W') ≤ dim(W)` in Remark 1, p. 169.

Deviation from the paper (gap filled): the paper uses this standard fact of dimension theory
implicitly (the strict transform `W'` is birational to `W`); it is proved here.
-/

@[expose] public section

open Order

namespace Hironaka

/-! ### Algebra: the dimension inequality for birational finitely generated extensions -/

namespace DimIneq

open Polynomial

/-- `a + 1 ≤ b` in `ℕ∞` as soon as `n + 1 ≤ b` for every natural number `n ≤ a`. -/
theorem enat_add_one_le_of_forall {a b : ℕ∞}
    (h : ∀ n : ℕ, (n : ℕ∞) ≤ a → (n : ℕ∞) + 1 ≤ b) : a + 1 ≤ b := by
  induction a using ENat.recTopCoe with
  | top =>
    have : b = ⊤ := by
      refine top_le_iff.mp ((ENat.forall_natCast_le_iff_le (m := ⊤) (n := b)).mp fun n _ => ?_)
      exact le_trans (by exact_mod_cast Nat.le_succ n) (h n le_top)
    simp [this]
  | coe m => exact_mod_cast h m le_rfl

/-- A prime of `T[X]` over the zero ideal of a domain `T` has height at most one (it survives
in `K[X]`, `K = Frac T`, which has dimension one). -/
theorem height_le_one_of_comap_C_eq_bot {T : Type*} [CommRing T] [IsDomain T]
    (Q : Ideal T[X]) [Q.IsPrime] (hQ : Q.comap (C : T →+* T[X]) = ⊥) : Q.height ≤ 1 := by
  classical
  let _ : Algebra T[X] (FractionRing T)[X] := Polynomial.algebra T (FractionRing T)
  have : IsLocalization ((nonZeroDivisors T).map (C : T →+* T[X])) (FractionRing T)[X] :=
    Polynomial.isLocalization _ _
  have hdisj : Disjoint (((nonZeroDivisors T).map (C : T →+* T[X]) : Submonoid T[X]) : Set T[X])
      (Q : Set T[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨b, hb, rfl⟩ hbQ
    have : b ∈ Q.comap (C : T →+* T[X]) := hbQ
    rw [hQ, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hb this
  rw [← IsLocalization.height_map_of_disjoint (S := (FractionRing T)[X]) _ Q hdisj]
  have hP : (Q.map (algebraMap T[X] (FractionRing T)[X])).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ Q ‹_› hdisj
  have h1 := Ideal.height_le_ringKrullDim_of_ne_top hP.ne_top
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
  exact_mod_cast h1

/-- The fibre of `R[X]` over a prime `p` has dimension one. -/
theorem height_map_quotient_le_one {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    (P : Ideal R[X]) [P.IsPrime] (hP : P.comap (C : R →+* R[X]) = p) :
    (P.map (Ideal.Quotient.mk (p.map (algebraMap R R[X])))).height ≤ 1 := by
  set J : Ideal R[X] := p.map (C : R →+* R[X])
  have hJ : J ≤ P := by rw [Ideal.map_le_iff_le_comap, hP]
  have hJ' : p.map (algebraMap R R[X]) = J := rfl
  rw [hJ']
  have hPbar : (P.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  let e := Ideal.polynomialQuotientEquivQuotientPolynomial p
  rw [← RingEquiv.height_comap e]
  have : ((P.map (Ideal.Quotient.mk J)).comap e).IsPrime := Ideal.comap_isPrime _ _
  apply height_le_one_of_comap_C_eq_bot
  ext r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  simp only [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  have he : e (C (Ideal.Quotient.mk p r)) = Ideal.Quotient.mk J (C r) := by
    have := Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk p (C r)
    rwa [Polynomial.map_C] at this
  rw [he, Ideal.mem_quotient_iff_mem hJ, ← hP, Ideal.mem_comap]

/-- The one-step dimension inequality (Matsumura 15.5 for a birational simple extension): if
`S = R[t]` with `d t ∈ R` for some `d ≠ 0`, then `ht P ≤ ht (P ∩ R)` for every prime `P` of
`S`. -/
theorem height_le_height_comap_of_adjoin_singleton {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsNoetherianRing R] [Algebra R S] {t : S}
    (ht : Algebra.adjoin R {t} = ⊤) {d r : R} (hd : d ≠ 0)
    (hdt : algebraMap R S d * t = algebraMap R S r) (P : Ideal S) [P.IsPrime] :
    P.height ≤ (P.comap (algebraMap R S)).height := by
  classical
  set φ : R[X] →ₐ[R] S := Polynomial.aeval t
  have hφ : Function.Surjective φ := by
    intro s
    have : s ∈ Algebra.adjoin R {t} := ht ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at this
    exact this
  set P' : Ideal R[X] := P.comap φ
  have : P'.IsPrime := Ideal.comap_isPrime φ P
  set p := P.comap (algebraMap R S)
  have hP'p : P'.comap (C : R →+* R[X]) = p := by
    ext x
    simp [P', p, Ideal.mem_comap, φ, Polynomial.aeval_C]
  -- the kernel contains `d X - r ≠ 0`
  set f0 : R[X] := C d * X - C r
  have hf0 : φ f0 = 0 := by
    simp [f0, φ, hdt]
  have hf00 : f0 ≠ 0 := by
    intro h
    have := congrArg (fun g => Polynomial.coeff g 1) h
    simp [f0, Polynomial.coeff_C] at this
    exact hd this
  -- `ht P + 1 ≤ ht P'`
  have h1 : P.height + 1 ≤ P'.height := by
    apply enat_add_one_le_of_forall
    intro n hn
    rw [PrimeSpectrum.height_eq_orderHeight ⟨P, ‹_›⟩] at hn
    obtain ⟨l, hlast, hlen⟩ := Order.exists_series_of_le_height (⟨P, ‹_›⟩ : PrimeSpectrum S) hn
    let l' := l.map (PrimeSpectrum.comap (φ : R[X] →+* S))
      (RingHom.strictMono_comap_of_surjective (f := (φ : R[X] →+* S)) hφ)
    have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R[X]) < l'.head := by
      refine lt_of_le_of_ne (fun x hx => ?_) fun h => ?_
      · rw [(Ideal.mem_bot).mp hx]; exact zero_mem _
      · have : f0 ∈ l'.head.asIdeal := by
          show φ f0 ∈ (l.head).asIdeal
          rw [hf0]; exact zero_mem _
        rw [← h] at this
        exact hf00 ((Ideal.mem_bot).mp this)
    let l'' := l'.cons _ hbot
    have h2 : (l''.length : ℕ∞) ≤ Order.height l''.last := Order.length_le_height_last
    have h3 : l''.last = ⟨P', ‹_›⟩ := by
      rw [RelSeries.last_cons, LTSeries.last_map, hlast]
      rfl
    rw [h3, ← PrimeSpectrum.height_eq_orderHeight] at h2
    simp only [l'', RelSeries.cons_length, l', LTSeries.map_length, hlen] at h2
    exact_mod_cast h2
  -- `ht P' ≤ ht p + 1`
  have : P'.LiesOver p := ⟨by rw [Ideal.under_def]; exact hP'p.symm⟩
  have h2 := Ideal.height_le_height_add_of_liesOver p P'
  have h3 := height_map_quotient_le_one p P' hP'p
  have h4 : P.height + 1 ≤ p.height + 1 := h1.trans (h2.trans (by gcongr))
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h4

/-- The dimension inequality for a birational extension generated by finitely many elements with
a common denominator (Matsumura 15.5 with transcendence degree `0`), in the subalgebras
`R[s] ⊆ S`. -/
theorem height_le_height_comap_of_adjoin_finset {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsNoetherianRing R] [IsDomain S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) {d : R} (hd : d ≠ 0) (s : Finset S)
    (hds : ∀ x ∈ s, ∃ r : R, algebraMap R S d * x = algebraMap R S r) :
    ∀ P : Ideal (Algebra.adjoin R (s : Set S)), P.IsPrime →
      P.height ≤ (P.comap (algebraMap R (Algebra.adjoin R (s : Set S)))).height := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro P hP
    have hbij : Function.Bijective (algebraMap R (Algebra.adjoin R ((∅ : Finset S) : Set S))) := by
      refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun x => ?_⟩
      obtain ⟨x, hx⟩ := x
      rw [Finset.coe_empty, Algebra.adjoin_empty] at hx
      obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hx
      exact ⟨r, Subtype.ext hr⟩
    let e := RingEquiv.ofBijective _ hbij
    have := RingEquiv.height_comap e P
    exact this.symm.le
  | insert t s hts ih =>
    intro P hP
    have hds' : ∀ x ∈ s, ∃ r : R, algebraMap R S d * x = algebraMap R S r :=
      fun x hx => hds x (Finset.mem_insert_of_mem hx)
    have := hP
    let T := Algebra.adjoin R (s : Set S)
    let T' := Algebra.adjoin R ((insert t s : Finset S) : Set S)
    have hTT' : T ≤ T' := Algebra.adjoin_mono (by
      rw [Finset.coe_insert]; exact Set.subset_insert _ _)
    let ι : T →ₐ[R] T' := Subalgebra.inclusion hTT'
    let _ : Algebra T T' := ι.toRingHom.toAlgebra
    have : IsNoetherianRing T := by
      have : Algebra.FiniteType R T :=
        (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset s)
      exact Algebra.FiniteType.isNoetherianRing R T
    have htmem : t ∈ T' := Algebra.subset_adjoin (by simp)
    let t' : T' := ⟨t, htmem⟩
    obtain ⟨r₀, hr₀⟩ := hds t (Finset.mem_insert_self t s)
    have hd' : algebraMap R T d ≠ 0 := fun h => hd (hinj (by
      have := congrArg Subtype.val h
      simpa using this))
    have hdt : algebraMap T T' (algebraMap R T d) * t' = algebraMap T T' (algebraMap R T r₀) := by
      apply Subtype.ext
      exact hr₀
    have hadj : Algebra.adjoin T {t'} = ⊤ := by
      refine eq_top_iff.mpr fun x hxtop => ?_
      clear hxtop
      obtain ⟨x, hx⟩ := x
      induction hx using Algebra.adjoin_induction with
      | mem y hy =>
        rw [Finset.coe_insert, Set.mem_insert_iff] at hy
        rcases hy with rfl | hy
        · exact Algebra.subset_adjoin rfl
        · have : (⟨y, Algebra.subset_adjoin (by simpa using Or.inr hy)⟩ : T') =
              algebraMap T T' ⟨y, Algebra.subset_adjoin hy⟩ := rfl
          rw [this]
          exact Subalgebra.algebraMap_mem _ _
      | algebraMap r =>
        have : (⟨algebraMap R S r, Subalgebra.algebraMap_mem _ r⟩ : T') =
            algebraMap T T' (algebraMap R T r) := rfl
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
      | add y z hy hz ihy ihz =>
        have : (⟨y + z, Subalgebra.add_mem _ hy hz⟩ : T') = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
        rw [this]
        exact Subalgebra.add_mem _ ihy ihz
      | mul y z hy hz ihy ihz =>
        have : (⟨y * z, Subalgebra.mul_mem _ hy hz⟩ : T') = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
        rw [this]
        exact Subalgebra.mul_mem _ ihy ihz
    have h1 := height_le_height_comap_of_adjoin_singleton hadj hd' hdt P
    have hP' : (P.comap (algebraMap T T')).IsPrime := Ideal.comap_isPrime _ _
    have h2 := ih hds' _ hP'
    have hcomp : (P.comap (algebraMap T T')).comap (algebraMap R T) =
        P.comap (algebraMap R T') := by
      rw [Ideal.comap_comap]
      rfl
    rw [hcomp] at h2
    exact h1.trans h2

/-- The dimension inequality for `S = R[s]`. -/
theorem height_le_height_comap_of_adjoin_eq_top {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsNoetherianRing R] [IsDomain S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) {d : R} (hd : d ≠ 0) (s : Finset S)
    (hds : ∀ x ∈ s, ∃ r : R, algebraMap R S d * x = algebraMap R S r)
    (hs : Algebra.adjoin R (s : Set S) = ⊤) (P : Ideal S) [P.IsPrime] :
    P.height ≤ (P.comap (algebraMap R S)).height := by
  let e : Algebra.adjoin R (s : Set S) ≃ₐ[R] S :=
    (Subalgebra.equivOfEq _ _ hs).trans Subalgebra.topEquiv
  let e' : Algebra.adjoin R (s : Set S) ≃+* S := e.toRingEquiv
  have hP : (P.comap e').IsPrime := Ideal.comap_isPrime _ _
  have h := height_le_height_comap_of_adjoin_finset hinj hd s hds _ hP
  rw [RingEquiv.height_comap e' P] at h
  have hc : (P.comap e').comap
      (algebraMap R (Algebra.adjoin R (s : Set S))) = P.comap (algebraMap R S) := by
    ext r
    simp only [Ideal.mem_comap]
    change e (algebraMap R _ r) ∈ P ↔ _
    rw [e.commutes]
  rwa [hc] at h

/-- `dim S ≤ dim R` for `S = R[s]` birational. -/
@[blueprint "compat:dimension-inequality-birational"
  (statement := /-- Let $R$ be a noetherian domain and $S\supseteq R$ a domain generated over $R$
    by finitely many elements $t_j$ with $d\,t_j\in R$ for some $0\ne d\in R$. Then
    $\operatorname{ht}P\le\operatorname{ht}(P\cap R)$ for every prime $P$ of $S$; in particular
    $\dim S\le\dim R$. (Matsumura, Thm.~15.5, with transcendence degree $0$.) -/)
  (proof := /-- Adjoin one generator $t$ at a time. Write $S=R[X]/K$; since $dX-r\in K$ is
    non-zero, a chain of primes of $S$ below $P$ lifts to a chain in $R[X]$ below the preimage
    $P'$ starting at $K\ne0$, and can be extended by $0$, so $\operatorname{ht}P+1\le
    \operatorname{ht}P'$. On the other hand $\operatorname{ht}P'\le\operatorname{ht}p+
    \operatorname{ht}(P'/pR[X])\le\operatorname{ht}p+1$, $p=P\cap R$, by Krull's height theorem
    and since the fibre over $p$ is a localization of $k(p)[X]$, of dimension one. -/)
  (latexEnv := "lemma")]
theorem ringKrullDim_le_of_adjoin_eq_top {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsNoetherianRing R] [IsDomain S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) {d : R} (hd : d ≠ 0) (s : Finset S)
    (hds : ∀ x ∈ s, ∃ r : R, algebraMap R S d * x = algebraMap R S r)
    (hs : Algebra.adjoin R (s : Set S) = ⊤) : ringKrullDim S ≤ ringKrullDim R := by
  rw [ringKrullDim_le_iff_height_le]
  intro P hP
  have hP' : (P.comap (algebraMap R S)).IsPrime := Ideal.comap_isPrime _ _
  refine le_trans ?_ (Ideal.height_le_ringKrullDim_of_ne_top hP'.ne_top)
  exact_mod_cast height_le_height_comap_of_adjoin_eq_top hinj hd s hds hs P

/-! ### The chart algebra `A[I/a]` modulo a prime not containing `a` -/

/-- The dimension inequality modulo a prime: if `C` is generated as an `A`-algebra by
finitely many elements `x` with `a x ∈ A`, and `a ∉ Q`, then `dim C/Q ≤ dim A/(Q ∩ A)`. -/
theorem ringKrullDim_quotient_le_of_generators {A C : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing C] [Algebra A C] (Q : Ideal C) [Q.IsPrime] {a : A}
    (ha : algebraMap A C a ∉ Q) {ι : Type*} [Fintype ι] (x : ι → C)
    (hx : ∀ i, ∃ r : A, algebraMap A C a * x i = algebraMap A C r)
    (hadj : Algebra.adjoin A (Set.range x) = ⊤) :
    ringKrullDim (C ⧸ Q) ≤ ringKrullDim (A ⧸ Q.comap (algebraMap A C)) := by
  classical
  set p := Q.comap (algebraMap A C)
  have hinj : Function.Injective (algebraMap (A ⧸ p) (C ⧸ Q)) :=
    Ideal.algebraMap_quotient_injective
  let s : Finset (C ⧸ Q) := Finset.univ.image fun i => Ideal.Quotient.mk Q (x i)
  have hd : Ideal.Quotient.mk p a ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact ha
  have hds : ∀ y ∈ s, ∃ r : A ⧸ p,
      algebraMap (A ⧸ p) (C ⧸ Q) (Ideal.Quotient.mk p a) * y = algebraMap (A ⧸ p) (C ⧸ Q) r := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨r, hr⟩ := hx i
    refine ⟨Ideal.Quotient.mk p r, ?_⟩
    change Ideal.Quotient.mk Q (algebraMap A C a) * Ideal.Quotient.mk Q (x i) =
      Ideal.Quotient.mk Q (algebraMap A C r)
    rw [← map_mul, hr]
  have hs : Algebra.adjoin (A ⧸ p) (s : Set (C ⧸ Q)) = ⊤ := by
    refine eq_top_iff.mpr fun y hytop => ?_
    clear hytop
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hc : c ∈ Algebra.adjoin A (Set.range x) := hadj ▸ Algebra.mem_top
    induction hc using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Algebra.subset_adjoin (Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    | algebraMap r =>
      exact Subalgebra.algebraMap_mem _ (Ideal.Quotient.mk p r)
    | add y z _ _ ihy ihz =>
      rw [map_add]
      exact Subalgebra.add_mem _ ihy ihz
    | mul y z _ _ ihy ihz =>
      rw [map_mul]
      exact Subalgebra.mul_mem _ ihy ihz
  exact ringKrullDim_le_of_adjoin_eq_top hinj hd s hds hs

section Chart

variable {A : Type*} [CommRing A] {I : Ideal A} {a : A}

theorem chartAlgebra.frac_add {i j : A} (hi : i ∈ I) (hj : j ∈ I) :
    (chartAlgebra.frac (a := a) (I.add_mem hi hj)) =
      chartAlgebra.frac (a := a) hi + chartAlgebra.frac hj := by
  apply Subtype.ext
  simp [chartAlgebra.frac, map_add, add_mul]

theorem chartAlgebra.frac_zero :
    (chartAlgebra.frac (a := a) (I.zero_mem)) = 0 := by
  apply Subtype.ext
  simp [chartAlgebra.frac]

theorem chartAlgebra.frac_mul (c : A) {i : A} (hi : i ∈ I) :
    (chartAlgebra.frac (a := a) (I.mul_mem_left c hi)) =
      algebraMap A (chartAlgebra I a) c * chartAlgebra.frac hi := by
  apply Subtype.ext
  simp [chartAlgebra.frac, map_mul, mul_assoc]

/-- The chart algebra is generated by the fractions `g/a`, `g` running over generators of `I`. -/
theorem chartAlgebra.adjoin_frac_eq_top (g : Finset A) (hg : Submodule.span A (g : Set A) = I)
    (hgI : ∀ i ∈ g, i ∈ I) :
    Algebra.adjoin A (Set.range fun i : g => chartAlgebra.frac (a := a) (hgI i.1 i.2)) = ⊤ := by
  set G := Set.range fun i : g => chartAlgebra.frac (a := a) (hgI i.1 i.2)
  have key : ∀ (i : A) (hi : i ∈ I), chartAlgebra.frac (a := a) hi ∈ Algebra.adjoin A G := by
    intro i hi
    have hi' : i ∈ Submodule.span A (g : Set A) := by rw [hg]; exact hi
    revert hi
    induction hi' using Submodule.span_induction with
    | mem j hj =>
      intro hi
      exact Algebra.subset_adjoin ⟨⟨j, hj⟩, rfl⟩
    | zero =>
      intro hi
      have e : chartAlgebra.frac (a := a) hi = 0 := chartAlgebra.frac_zero
      rw [e]
      exact Subalgebra.zero_mem _
    | add j k hj hk ihj ihk =>
      intro hi
      have hj' : j ∈ I := hg ▸ hj
      have hk' : k ∈ I := hg ▸ hk
      have e : chartAlgebra.frac (a := a) hi =
          chartAlgebra.frac hj' + chartAlgebra.frac hk' := chartAlgebra.frac_add hj' hk'
      rw [e]
      exact Subalgebra.add_mem _ (ihj hj') (ihk hk')
    | smul c j hj ihj =>
      intro hi
      have hj' : j ∈ I := hg ▸ hj
      have e : chartAlgebra.frac (a := a) hi =
          algebraMap A (chartAlgebra I a) c * chartAlgebra.frac hj' := chartAlgebra.frac_mul c hj'
      rw [e]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c) (ihj hj')
  refine eq_top_iff.mpr fun x hxtop => ?_
  clear hxtop
  obtain ⟨x, hx⟩ := x
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    exact key i hi
  | algebraMap r =>
    exact Subalgebra.algebraMap_mem _ r
  | add y z hy hz ihy ihz =>
    have : (⟨y + z, Subalgebra.add_mem _ hy hz⟩ : chartAlgebra I a) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
    rw [this]
    exact Subalgebra.add_mem _ ihy ihz
  | mul y z hy hz ihy ihz =>
    have : (⟨y * z, Subalgebra.mul_mem _ hy hz⟩ : chartAlgebra I a) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
    rw [this]
    exact Subalgebra.mul_mem _ ihy ihz

/-- For a prime `Q` of `A[I/a]` not containing `a`, `A[I/a]/Q` is a birational extension of
`A/(Q ∩ A)` generated by the images of `g/a`, `g` running over generators of `I`; hence
`dim A[I/a]/Q ≤ dim A/(Q ∩ A)`. -/
@[blueprint "compat:chart-quotient-dim"
  (statement := /-- Let $A$ be noetherian, $I\subseteq A$ an ideal, $a\in A$, and $\mathfrak q$
    a prime of the chart algebra $A[I/a]\subseteq A_a$ with $a\notin\mathfrak q$. Then
    $\dim A[I/a]/\mathfrak q\le\dim A/(\mathfrak q\cap A)$. -/)
  (proof := /-- $A[I/a]/\mathfrak q$ is generated over the domain $A/(\mathfrak q\cap A)$ by the
    images of $g_j/a$, $g_j$ generators of $I$, and $a\cdot(g_j/a)=g_j$ with $a\ne0$ modulo
    $\mathfrak q$; apply \cref{compat:dimension-inequality-birational}. -/)
  (latexEnv := "lemma")]
theorem ringKrullDim_quotient_chartAlgebra_le [IsNoetherianRing A]
    (Q : Ideal (chartAlgebra I a)) [Q.IsPrime] (ha : algebraMap A (chartAlgebra I a) a ∉ Q) :
    ringKrullDim (chartAlgebra I a ⧸ Q) ≤
      ringKrullDim (A ⧸ Q.comap (algebraMap A (chartAlgebra I a))) := by
  obtain ⟨g, hg⟩ := (IsNoetherian.noetherian I : I.FG)
  have hgI : ∀ i ∈ g, i ∈ I := fun i hi => hg ▸ Submodule.subset_span hi
  exact ringKrullDim_quotient_le_of_generators Q ha
    (fun i : g => chartAlgebra.frac (a := a) (hgI i.1 i.2))
    (fun i => ⟨i.1, chartAlgebra.algebraMap_mul_frac _⟩)
    (chartAlgebra.adjoin_frac_eq_top g hg hgI)

end Chart

end DimIneq

end Hironaka
