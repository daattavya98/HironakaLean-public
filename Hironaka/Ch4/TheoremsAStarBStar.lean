/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch4.ImplicationsAB
public import Hironaka.Ch4.CompletionTransforms
public import Hironaka.Ch4.ComponentwiseConstruction
public import Hironaka.Compat.NormalCrossingsDescent
public import Hironaka.Compat.CenterDimension
public import Hironaka.Statements

/-!
# Ch. IV §3 (pp. 293–310): Lemma (AB.6) and Remarks 3–5

This file continues `Hironaka/Ch4/ImplicationsAB.lean` (the symbols of §3, Lemma (AB.1), the
completion, the frame, the construction [f]–[i], Lemmas (AB.2)–(AB.5) and Remarks 1, 2) with the
part of §3 that uses the assembly of Lemma (AB.6) in `Hironaka/Ch4/CompletionTransforms.lean`:

* p. 306: Lemma (AB.6) (`lem:IV.AB-6`), assembled from
  `Frame.isIrreducible_and_isNormallyFlatAlongAt_of_isPermissibleCenter`
  (`lem:IV.AB-6-of-permissible`) and the permissibility of `P̂` ("by the same argument as in the
  proof of Lemma (AB.5) … hence by (a), (b) of (2), `P̂` is a permissible center for all the
  `Ĵ_j(s)`", `lem:IV.AB-6-hat-permissible`);
* pp. 308–310: Remarks 3–5 (`rem:IV.3-3` … `rem:IV.3-5`), in the printed form and in the form for
  an arbitrary open family with removals, for the emptied auxiliary datum (the repair of the
  the paper's error on the subschemes `Ẽ_j`), together with `dim_Bs_lt` (`n' < n`, p. 310).

Theorems A* and B* (pp. 293–294), Theorems A and B (p. 293) and the implications (A), (B) of Ch. I
§2 as consequences of Theorems A, B (`impl:A`, `impl:B`) were moved, with their
names, namespaces and blueprint labels, to `Hironaka/Ch4/TheoremsAB.lean` (the last file of the
chain: they need the one-block lemma of `Hironaka/Ch4/AStarBStarLifting.lean`).

The declarations keep the names, namespaces and blueprint labels they had in
`Hironaka/Ch4/ImplicationsAB.lean`; the file was split off so that
`Hironaka/Ch4/CompletionTransforms.lean` (which imports `ImplicationsAB`) can be used in the proof
of Lemma (AB.6).  The notation and the
formalization notes are those of the module header of `Hironaka/Ch4/ImplicationsAB.lean`.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Hironaka

universe u

noncomputable section

namespace AB

/-! ## Lemma (AB.6) (p. 306)

The statements are made for an arbitrary open family with removals `U_s` (`Frame.RemovalFamily`,
`lem:IV.3-construction-facts-generic`), with `U_s`, `Ū_s = U_s ∩ X̄_s` in place of `X̂'_s`,
`X̄'_s`; the printed statements are the instances `U_s = X̂'_s` (`Frame.removalFamily`), and the
main line of the proof of Theorems A*, B* uses the instances `U_s = X̂*'_s` of the corrected
construction (`Frame.removalFamilyStar`, `Hironaka.Ch4.ComponentwiseConstruction`). -/

/-! ### Helpers for the ring-level step of Lemma (AB.6) -/

namespace Frame

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS)

/-- The Corollary of Lemma (AB.3) (p. 296) for the reduced closure `B̄` in `X̂_s` of the image of a
set
`A ⊆ X̄_s` whose image under `ĝ_s` is `{x̂_0}`: the closure `B_s` of `c̄_s(A)` in `X_s` (reduced)
satisfies
`B̄ = c_s⁻¹(B_s)` and `c_s` induces an isomorphism `B̄ ≃ B_s`. -/
theorem exists_iso_totalTransform_of_pts_eq {s : ℕ} (A : Set (𝒮.xBar s).toScheme)
    (hAg : ((𝒮.xBar s).ι ≫ (𝒮.tHat.pre s).composite).base '' A = {hS.xh})
    (Bh : Subscheme (𝒮.tHat.X s)) (hBhred : Bh.IsReduced)
    (hBhpts : Bh.pts = closure ((𝒮.xBar s).ι.base '' A)) :
    ∃ e : Bh.toScheme ≅
        (Subscheme.ofClosed ⟨closure ((𝒮.cBar s).base '' A), isClosed_closure⟩).toScheme,
      e.hom ≫ (Subscheme.ofClosed ⟨closure ((𝒮.cBar s).base '' A), isClosed_closure⟩).ι =
        Bh.ι ≫ 𝒮.c s ∧
      Subscheme.totalTransform (𝒮.c s)
        (Subscheme.ofClosed ⟨closure ((𝒮.cBar s).base '' A), isClosed_closure⟩) = Bh := by
  have hBsA : (𝒮.cBar s).base '' A = (𝒮.c s).base '' ((𝒮.xBar s).ι.base '' A) := by
    rw [Set.image_image]; rfl
  have hclosed : IsClosed ({hS.xh} : Set (xHat0 X x₀)) :=
    ((isClosed_singleton_iff_eq_xhat0_and_c0_apply_xhat0 x₀ (hS.ambient.2.1 x₀)).1 hS.xh).mpr rfl
  have hBbarImg : (𝒮.tHat.pre s).composite.base '' Bh.pts = {hS.xh} := by
    rw [hBhpts]
    have hg' : (𝒮.tHat.pre s).composite.base '' ((𝒮.xBar s).ι.base '' A) = {hS.xh} := by
      rw [Set.image_image]; exact hAg
    refine Set.Subset.antisymm ?_ ?_
    · refine (image_closure_subset_closure_image (𝒮.tHat.pre s).composite.continuous).trans ?_
      rw [hg']; exact hclosed.closure_subset_iff.mpr le_rfl
    · rw [← hg']
      exact Set.image_mono subset_closure
  obtain ⟨B, ⟨hBred, himg, hBbar⟩, -, e, he⟩ :=
    (Completion.bijective_quotientMap_and_exists_unique_reduced_totalTransform hS
      𝒮.toCompletion s).2 Bh hBhred hBbarImg
  have hsurj : Function.Surjective e.hom.base := e.hom.homeomorph.surjective
  have hrR : Set.range Bh.ι.base = closure ((𝒮.xBar s).ι.base '' A) := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hBhpts
  have hBpts : B.pts = (𝒮.c s).base '' closure ((𝒮.xBar s).ι.base '' A) := by
    have h1 : B.pts = Set.range B.ι.base :=
      (Scheme.IdealSheafData.range_subschemeι (I := B)).symm
    have h2 : Set.range B.ι.base = Set.range (e.hom ≫ B.ι).base := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]
    rw [h1, h2, he, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrR]
  have hBsets : B.pts = closure ((𝒮.cBar s).base '' A) := by
    refine Set.Subset.antisymm ?_ ?_
    · rw [hBpts, hBsA]
      exact image_closure_subset_closure_image (𝒮.c s).continuous
    · refine closure_minimal ?_ B.support.isClosed
      rw [hBsA, hBpts]
      exact Set.image_mono subset_closure
  have hBeq : B = Subscheme.ofClosed ⟨closure ((𝒮.cBar s).base '' A), isClosed_closure⟩ := by
    rw [Subscheme.eq_ofClosed_support B hBred]
    congr 1
    exact TopologicalSpace.Closeds.ext hBsets
  subst hBeq
  exact ⟨e, he, hBbar.symm⟩

/-- The Corollary of Lemma (AB.3) for the reduced closure `B̄` in `X̂_s` of the image of `A ⊆
X̄_s`. -/
theorem exists_iso_redClosure_totalTransform {s : ℕ} (A : Set (𝒮.xBar s).toScheme)
    (hAg : ((𝒮.xBar s).ι ≫ (𝒮.tHat.pre s).composite).base '' A = {hS.xh}) :
    ∃ e : (Subscheme.redClosure ((𝒮.xBar s).ι.base '' A)).toScheme ≅
        (Subscheme.ofClosed ⟨closure ((𝒮.cBar s).base '' A), isClosed_closure⟩).toScheme,
      e.hom ≫ (Subscheme.ofClosed ⟨closure ((𝒮.cBar s).base '' A), isClosed_closure⟩).ι =
        (Subscheme.redClosure ((𝒮.xBar s).ι.base '' A)).ι ≫ 𝒮.c s ∧
      Subscheme.totalTransform (𝒮.c s)
        (Subscheme.ofClosed ⟨closure ((𝒮.cBar s).base '' A), isClosed_closure⟩) =
        Subscheme.redClosure ((𝒮.xBar s).ι.base '' A) :=
  𝒮.exists_iso_totalTransform_of_pts_eq A hAg _ (Subscheme.ofClosed_isReduced _)
    (Subscheme.pts_ofClosed _)

end Frame

section FrameOrder

theorem ordElem_pow_of_isRegularLocalRing {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (P : Ideal R) [P.IsPrime] (hP : IsRegularLocalRing (R ⧸ P)) (f : R) (a : ℕ) :
    Ideal.ordElem P (f ^ a) = a * Ideal.ordElem P f := by
  induction a with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    refine le_antisymm (Ideal.ordElem_le_of_notMem (m := 0) ?_) zero_le
    rw [zero_add, pow_one]
    exact fun h => Ideal.IsPrime.ne_top inferInstance ((Ideal.eq_top_iff_one P).mpr h)
  | succ a ih =>
    rw [pow_succ, ordElem_mul_of_isRegularLocalRing P hP, ih, Nat.cast_succ, add_mul, one_mul]

/-- `P^k`-membership of `c` from `c^m ∈ P^{km}`: for `P` prime with `R/P` regular, `m c^…`. -/
theorem mem_pow_of_pow_mem_pow {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (P : Ideal R) [P.IsPrime] (hP : IsRegularLocalRing (R ⧸ P)) (c : R) {m k : ℕ} (hm : 0 < m)
    (h : c ^ m ∈ P ^ (m * k)) : c ∈ P ^ k := by
  have h1 := Ideal.le_ordElem h
  rw [ordElem_pow_of_isRegularLocalRing P hP] at h1
  apply Ideal.mem_pow_of_le_ordElem
  by_cases hc : Ideal.ordElem P c = ⊤
  · rw [hc]; exact le_top
  obtain ⟨c0, hc0⟩ := ENat.ne_top_iff_exists.mp hc
  rw [← hc0] at h1 ⊢
  have : m * k ≤ m * c0 := by exact_mod_cast h1
  exact_mod_cast Nat.le_of_mul_le_mul_left this hm

/-- **The order of `g_{jk}(s)` along `P̂`** (p. 307: "By assumption `Ŝ_s/P̂` is regular, `z_s ∈ P̂`
and,
if `P̄ = P̂/(z_s)Ŝ_s`, `P̄^b ⊇ J̄(s)_x̂'`.  Therefore, by (1), (3) and (4), we have `ν_P̂(g_jk(s)) ≥
ν_jk`"):
ring-level form.  `R` has a regular frame `(S; z)` (so `S ≃ R/(z)`), `π : R → T̄ = R/(z)`, `q` a
prime of
`T̄` with `T̄/q` regular, `P̂ = π⁻¹(q)`, and `g = z^ν + ∑ c_i z^{ν-i}` with `(π c_i)^{b/i} ∈ q^b`,
`i ∣ b`; then `g ∈ P̂^ν`. -/
theorem weierstrass_mem_pow_comap {R T' : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing T']
    [IsRegularLocalRing T'] (F : RegularFrame R) (z : R) (hr : F.r = 1) (hz : ∀ i, F.z i = z)
    (π : R →+* T') (hπ : Function.Surjective π) (hker : RingHom.ker π = Ideal.span {z})
    (q : Ideal T') [q.IsPrime] (hq : IsRegularLocalRing (T' ⧸ q)) {ν : ℕ} (co : Fin ν → F.S)
    {b : ℕ} (hb : 0 < b) (hdvd : ∀ i : Fin ν, ((i : ℕ) + 1) ∣ b)
    (hcoq : ∀ i : Fin ν, π (algebraMap F.S R (co i)) ^ (b / ((i : ℕ) + 1)) ∈ q ^ b) :
    z ^ ν + ∑ i : Fin ν, algebraMap F.S R (co i) * z ^ (ν - ((i : ℕ) + 1)) ∈ (q.comap π) ^ ν := by
  classical
  set Ph := q.comap π with hPh
  have hzP : z ∈ Ph := by
    rw [hPh, Ideal.mem_comap]
    have : π z = 0 := RingHom.mem_ker.mp (hker ▸ Ideal.mem_span_singleton_self z)
    rw [this]; exact q.zero_mem
  have hI : Ideal.span (Set.range F.z) = Ideal.span {z} := by
    have h0 : 0 < F.r := by rw [hr]; exact one_pos
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨i, rfl⟩; rw [hz i]; exact Ideal.mem_span_singleton_self z
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Ideal.subset_span ⟨⟨0, h0⟩, hz _⟩
  have hker' : RingHom.ker π = Ideal.span (Set.range F.z) := hker.trans hI.symm
  let e : (R ⧸ Ideal.span (Set.range F.z)) ≃+* T' :=
    (Ideal.quotEquivOfEq hker'.symm).trans (RingHom.quotientKerEquivOfSurjective hπ)
  have he : ∀ a, e (Ideal.Quotient.mk _ a) = π a := fun a => rfl
  have hθ : Function.Bijective (π.comp (algebraMap F.S R)) := by
    have : π.comp (algebraMap F.S R) =
        e.toRingHom.comp ((Ideal.Quotient.mk _).comp (algebraMap F.S R)) := by
      ext s; exact (he (algebraMap F.S R s)).symm
    rw [this]
    exact e.bijective.comp F.quot_bijective
  let eθ : F.S ≃+* T' := RingEquiv.ofBijective _ hθ
  have hpow : ∀ (k : ℕ) (c : F.S),
      π (algebraMap F.S R c) ∈ q ^ k → algebraMap F.S R c ∈ Ph ^ k := by
    intro k c hc
    have h1 : c ∈ (q ^ k).comap eθ := hc
    have h2 : (q ^ k).comap eθ = (q.comap eθ) ^ k := by
      rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]
    rw [h2] at h1
    have h3 : (q.comap eθ).map (algebraMap F.S R) ≤ Ph := by
      rw [Ideal.map_le_iff_le_comap]
      intro s hs
      exact hs
    have h4 := Ideal.mem_map_of_mem (algebraMap F.S R) h1
    rw [Ideal.map_pow] at h4
    exact Ideal.pow_right_mono h3 k |> fun h => h h4
  have hterm : ∀ i : Fin ν, algebraMap F.S R (co i) * z ^ (ν - ((i : ℕ) + 1)) ∈ Ph ^ ν := by
    intro i
    have hm : 0 < b / ((i : ℕ) + 1) := Nat.div_pos (Nat.le_of_dvd hb (hdvd i)) (Nat.succ_pos _)
    have hmk : b / ((i : ℕ) + 1) * ((i : ℕ) + 1) = b := Nat.div_mul_cancel (hdvd i)
    have hk : π (algebraMap F.S R (co i)) ∈ q ^ ((i : ℕ) + 1) := by
      refine mem_pow_of_pow_mem_pow q hq _ hm ?_
      rw [hmk]
      exact hcoq i
    have h1 := hpow _ _ hk
    have h2 : z ^ (ν - ((i : ℕ) + 1)) ∈ Ph ^ (ν - ((i : ℕ) + 1)) := Ideal.pow_mem_pow hzP _
    have h3 := Ideal.mul_mem_mul h1 h2
    have hi := i.2
    rwa [← pow_add, show (i : ℕ) + 1 + (ν - ((i : ℕ) + 1)) = ν by omega] at h3
  exact Ideal.add_mem _ (Ideal.pow_mem_pow hzP ν) (Ideal.sum_mem _ fun i _ => hterm i)

end FrameOrder

theorem stalkIdeal_ker_comp_eq_comap {W Y : Scheme.{u}} (i : W ⟶ Y) [IsClosedImmersion i]
    (Bb : Subscheme W) (b : Bb.toScheme) :
    Subscheme.stalkIdeal (Bb.ι ≫ i).ker ((Bb.ι ≫ i).base b) =
      (Bb.stalkIdeal (Bb.ι.base b)).comap (i.stalkMap (Bb.ι.base b)).hom := by
  obtain ⟨e₀, he₀⟩ := Subscheme.exists_iso_ker (Bb.ι ≫ i)
  have hf : Bb.ι ≫ i = e₀.symm.hom ≫ Subscheme.ι ((Bb.ι ≫ i).ker) := by
    show Bb.ι ≫ i = e₀.symm.hom ≫ (Bb.ι ≫ i).ker.subschemeι
    rw [Iso.symm_hom, ← he₀]
    simp
  have h := (Subscheme.ker_stalkMap_eq_and_surjective_of_eq_iso_comp (Bb.ι ≫ i) _ e₀.symm hf b).1
  rw [← h, Scheme.Hom.stalkMap_comp]
  change RingHom.ker (CommRingCat.Hom.hom (i.stalkMap (Bb.ι.base b) ≫ Bb.ι.stalkMap b)) = _
  rw [CommRingCat.hom_comp, stalkIdeal_eq_ker_stalkMap Bb b]
  ext a
  simp [RingHom.mem_ker, Ideal.mem_comap]

theorem Standing.sys_last_isContainedIn [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    (hS : Standing N n ℜ P r T x₀) (s : ℕ) (j : Fin (ℜ.β + 1)) :
    (T.sys ℜ s (Fin.last ℜ.β)).IsContainedIn (T.sys ℜ s j) := by
  have := hS.ambient.1
  have hdatum : ((T.pre s).transformI ℜ).IsDatum := MonoidalSuccession.transformI_isDatum
    (T.pre s) hS.ambient.2.1 ℜ hS.isDatum (hS.permissible s).isPermissibleI
  obtain ⟨-, -, -, -, hWV⟩ := hdatum
  obtain ⟨h1, h2⟩ := succSystem_eq_transformI (T.pre s) ℜ
  induction j using Fin.lastCases with
  | last => exact fun U => le_rfl
  | cast i =>
    show (succSystem (T.pre s) ℜ (Fin.last ℜ.β)).IsContainedIn (succSystem (T.pre s) ℜ i.castSucc)
    rw [h1, h2 i]
    exact hWV _

/-- p. 306, the ring-level step of the proof of Lemma (AB.6), for an arbitrary open family with
removals (see `Frame.isPermissibleCenter_totalTransform_closure_of_jBar_le_pow`, the printed
instance, for the paper's words).  Proved: the paper's argument ("by the same argument as in the
proof of Lemma (AB.5)") applies verbatim, as for `lem:IV.AB-5-generic`.

\textbf{Deviation from the paper (gap filled).} The paper writes "Let `P` (resp. `P̂`) be the prime
ideal of `B_s` in `S_s` (resp. `B̄'` in `Ŝ_s`); then `P̂ = PŜ_s`".  In Lean `P̂` is the stalk of
`c_s⁻¹(B_s)` at `x̂'`; it is identified with the preimage of the ideal of `B̄` under `Ŝ_s → T̄_s` by
the Corollary of Lemma (AB.3) (`exists_iso_redClosure_totalTransform`,
`stalkIdeal_totalTransform_eq_ker_and_isSimpleAt_of_isOpen`, `stalkIdeal_ker_comp_eq_comap`).
"Therefore, by (1), (3), (4), `ν_P̂(g_jk(s)) ≥ ν_jk`" is the ring-level
`weierstrass_mem_pow_comap`: the coefficients `g_jki(s) ∈ T_s ≃ Ŝ_s/(z_s)` satisfy
`g_jki(s)^{b/i} ∈ P̄^b`, `i ∣ b = ∏ ν_jk!`, hence `g_jki(s) ∈ P̄^i` (the order along the prime `P̄`
with
`T̄_s/P̄` regular is additive on products), and `g_jk(s) ∈ P̂^{ν_jk}` since `z_s ∈ P̂`.  `J ≤ P̂`:
`B_s ⊆ W(s) ⊆ V_j(s)` (Lemma (AB.5) (i) and the datum `ℜ(s)`). -/
@[blueprint "lem:IV.AB-6-hat-permissible-generic"
  (statement := /-- Notation as in \cref{lem:IV.AB-6-hat-permissible}, for an arbitrary open
    family with removals $U_s\subseteq\hat X_s$ (\cref{lem:IV.3-construction-facts-generic}),
    with $\bar B'\subseteq\bar U_s=U_s\cap\bar X_s$: at every point $\hat x'$ of $\bar B'$ the
    ideal $\hat P=P\hat S_s$ is a permissible center for all the $\hat J_j(s)$.
    (Formalization note: the printed version is the instance $U_s=\hat X_s'$; the corrected
    construction of \cref{def:IV.3-construction-componentwise} is the instance
    $U_s=\hat X_s^{*\prime}$.) -/)
  (proof := /-- As \cref{lem:IV.AB-6-hat-permissible}: the frames of the proof of Lemma (AB.5)
    for the family (\cref{lem:IV.AB-5-generic}) give (1)--(4) at $\hat x'$, and
    \cref{lem:IV.AB-6-permissible} concludes.

    In Lean: $\hat P=\hat J_0$ of $c_s^{-1}(B_s)$ at $\hat x'$ is the preimage of the ideal of $\bar
    B$ in
    $\bar T_s$ under $\hat S_s\to\bar T_s$ (Corollary of Lemma (AB.3)); $z_s\in\hat P$ and
    $\hat S_s/\hat P\simeq\bar T_s/\bar P$ is regular; by (4) and $\bar J(s)\subseteq\bar P^b$ the
    coefficients $g_{jki}(s)$ lie in $\bar P^i$ (as $g_{jki}(s)^{b/i}\in\bar P^b$, $i\mid b$, orders
    along $\bar P$
    being additive), so by (3) $g_{jk}(s)\in\hat P^{\nu_{jk}}$, i.e.\ $\nu_{\hat
    P}(g_{jk}(s))\ge\nu_{jk}=
    \nu_{\hat M}(g_{jk}(s))$; $\hat J_j(s)\subseteq\hat P$ because $B_s\subseteq W(s)\subseteq
    V_j(s)$.

    \textbf{Deviation from the paper (gap filled).} The paper identifies $\hat P=P\hat S_s$ without
    proof
    (here via the Corollary of Lemma (AB.3), \cref{cor:IV.AB-3}) and writes ``$\nu_{\hat
    P}(g_{jk}(s))\ge
    \nu_{jk}$'' for ``by (1), (3), (4)'': the divisibility $i\mid b$ (from $b=\prod\nu_{jk}!$) and
    the
    additivity of $\nu_{\bar P}$ on powers are used to get $g_{jki}(s)\in\bar P^i$ from
    $g_{jki}(s)^{b/i}\in\bar P^b$. -/)
  (proofUses := ["lem:IV.AB-5-generic", "lem:IV.AB-6-permissible", "lem:IV.AB-4-frames"])
  (latexEnv := "lemma")]
theorem Frame.RemovalFamily.isPermissibleCenter_totalTransform_closure_of_jBar_le_pow [Hironaka.HironakaCitedResults.{u}] {N n : ℕ}
    {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
    {𝒮 : Frame hS} (R : 𝒮.RemovalFamily) (s : ℕ) (Bb : Subscheme (𝒮.xBar s).toScheme)
    (hns : ∀ xb ∈ Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme), Bb.IsSimpleAt xb)
    (_hirr : IsIrreducible (Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme)))
    (hg : ((𝒮.xBar s).ι ≫ (𝒮.tHat.pre s).composite).base ''
      (Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme)) = {hS.xh})
    (hJ : ∀ xb ∈ Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme),
      (𝒮.jBar s).stalkIdeal xb ≤ (Bb.stalkIdeal xb) ^ 𝒮.b) :
    ∀ xb ∈ Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme), ∀ j,
      IsPermissibleCenter ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb))
        ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal ((𝒮.xBar s).ι.base xb))
        ((Subscheme.totalTransform (𝒮.c s) (Subscheme.ofClosed
          ⟨closure ((𝒮.cBar s).base ''
            (Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme))), isClosed_closure⟩)).stalkIdeal
          ((𝒮.xBar s).ι.base xb)) := by
  classical
  intro xb hxb j
  set A : Set (𝒮.xBar s).toScheme := Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme) with hA
  set Bs : Subscheme (T.X s) :=
    Subscheme.ofClosed ⟨closure ((𝒮.cBar s).base '' A), isClosed_closure⟩ with hBs
  -- the orders `ν(J̄(s)_{x̂'}) ≥ b`
  have hν : ∀ xb' ∈ A, (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal xb') := by
    intro xb' hxb'
    have h2 : Bb.stalkIdeal xb' ≤ maximalIdeal _ :=
      Subscheme.stalkIdeal_le_maximalIdeal Bb hxb'.1
    exact_mod_cast Ideal.le_ord ((hJ xb' hxb').trans (Ideal.pow_right_mono h2 _))
  -- `B_s ⊆ V_j(s)`
  have hsysW : T.sys ℜ s (Fin.last ℜ.β) = (T.pre s).strictTransform ℜ.W := by
    show (T.pre s).strictTransform (datumSystem ℜ (Fin.last ℜ.β)) = _
    simp only [datumSystem, Fin.snoc_last]
  have hBsW : Bs.pts ⊆ (T.sys ℜ s (Fin.last ℜ.β)).pts := by
    rw [hsysW]
    refine closure_minimal (Set.image_subset_iff.mpr fun xb' h => ?_)
      (show IsClosed ((T.pre s).strictTransform ℜ.W).pts from
        ((T.pre s).strictTransform ℜ.W).support.isClosed)
    exact (R.cbar_mem_strictTransform_and_not_isSimpleAt_of_b_le_nu s xb' h.2 (hν xb' h)).1
  have hBsV : Bs.IsContainedIn (T.sys ℜ s j) :=
    Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced _)
      (hBsW.trans (pts_subset_of_isContainedIn (hS.sys_last_isContainedIn s j)))
  -- the Corollary of Lemma (AB.3): `c_s⁻¹(B_s) = B̄`
  obtain ⟨e, he, htt⟩ := 𝒮.exists_iso_redClosure_totalTransform A hg
  have hOW : ∀ b : (𝒮.xBar s).toScheme, b ∈ (R.uBar s : Set (𝒮.xBar s).toScheme) ↔
      (𝒮.xBar s).ι.base b ∈ (R.U s : Set (𝒮.tHat.X s)) := fun b => Iff.rfl
  obtain ⟨hker, -⟩ := Subscheme.stalkIdeal_totalTransform_eq_ker_and_isSimpleAt_of_isOpen
    (𝒮.c s) (𝒮.xBar s).ι Bb (OY := (R.U s : Set (𝒮.tHat.X s))) (R.U s).isOpen hOW hns Bs htt e he
  -- a point `b` of `B̄` over `xb`
  obtain ⟨b, rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts Bb hxb.1
  have hP : (Subscheme.totalTransform (𝒮.c s) Bs).stalkIdeal
        ((𝒮.xBar s).ι.base (Bb.ι.base b)) =
      (Bb.stalkIdeal (Bb.ι.base b)).comap ((𝒮.xBar s).ι.stalkMap (Bb.ι.base b)).hom := by
    rw [hker _ hxb.2]
    exact stalkIdeal_ker_comp_eq_comap (𝒮.xBar s).ι Bb b
  rw [hP]
  have hxb' : Bb.ι.base b ∈ A := hxb
  have hgen := R.exists_hasGenericStalkFrame_of_b_le_nu s (Bb.ι.base b) hxb.2 (hν _ hxb')
  obtain ⟨F, z, m, ν, g, co, hr, hz, hXz, hgJ, hgr, hordg, -, hbprod, hform, hJbar⟩ := hgen
  have hTreg : IsRegularLocalRing ((𝒮.xBar s).toScheme.presheaf.stalk (Bb.ι.base b)) :=
    (R.isSimpleAt_and_isIrreducible_and_isNonsingCodimOneOn s).1 _ hxb.2
  have hRreg : IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base (Bb.ι.base b))) :=
    𝒮.isNonsingular_tHat_X s _
  set π := ((𝒮.xBar s).ι.stalkMap (Bb.ι.base b)).hom with hπ
  have hπsurj : Function.Surjective π := (𝒮.xBar s).ι.stalkMap_surjective _
  have hπker : RingHom.ker π = Ideal.span {z} := by
    rw [← hXz]; exact (stalkIdeal_eq_ker_stalkMap (𝒮.xBar s) (Bb.ι.base b)).symm
  set q := Bb.stalkIdeal (Bb.ι.base b) with hq
  have hqreg : IsRegularLocalRing ((𝒮.xBar s).toScheme.presheaf.stalk (Bb.ι.base b) ⧸ q) :=
    (hns _ hxb').2
  have hqprime : q.IsPrime := by
    have : IsDomain ((𝒮.xBar s).toScheme.presheaf.stalk (Bb.ι.base b) ⧸ q) :=
      Transforms.isDomain_of_isRegularLocalRing _
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  have hPprime : (q.comap π).IsPrime := Ideal.IsPrime.comap _
  have hPreg : IsRegularLocalRing (_ ⧸ q.comap π) := by
    let e := RingEquiv.ofBijective (Ideal.quotientMap q π le_rfl)
      ⟨Ideal.quotientMap_injective, Ideal.quotientMap_surjective hπsurj⟩
    exact IsRegularLocalRing.of_ringEquiv e.symm
  have hJP : (Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal
      ((𝒮.xBar s).ι.base (Bb.ι.base b)) ≤ q.comap π := by
    rw [← hP, stalkIdeal_totalTransform, stalkIdeal_totalTransform]
    exact Ideal.map_mono (Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hBsV _)
  have hbpos : 0 < 𝒮.b := by
    rw [hbprod]
    exact Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => Nat.factorial_pos _
  have hdvd : ∀ j k (i : Fin (ν j k)), ((i : ℕ) + 1) ∣ 𝒮.b := by
    intro j k i
    rw [hbprod]
    exact (Nat.dvd_factorial (Nat.succ_pos _) i.2).trans
      ((Finset.dvd_prod_of_mem (fun k' => (ν j k').factorial) (Finset.mem_univ k)).trans
        (Finset.dvd_prod_of_mem (fun j' => ∏ k', (ν j' k').factorial) (Finset.mem_univ j)))
  have hcoq : ∀ j k (i : Fin (ν j k)),
      π (algebraMap F.S ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base (Bb.ι.base b)))
        (co j k i)) ^ (𝒮.b / ((i : ℕ) + 1)) ∈ q ^ 𝒮.b := by
    intro j k i
    have hy : algebraMap F.S ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base (Bb.ι.base b)))
        (co j k i) ^ (𝒮.b / ((i : ℕ) + 1)) ∈
        Ideal.span {y | ∃ j k i, y = algebraMap F.S
          ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base (Bb.ι.base b)))
            (co j k i) ^ (𝒮.b / ((i : ℕ) + 1))} :=
      Ideal.subset_span ⟨j, k, i, rfl⟩
    set φ := (((𝒮.tHat.X s).presheaf.stalkCongr (Inseparable.of_eq
      (rfl : (𝒮.xBar s).ι.base (Bb.ι.base b) = (𝒮.xBar s).ι.base (Bb.ι.base b)))).hom ≫
        (𝒮.xBar s).ι.stalkMap (Bb.ι.base b)).hom with hφ
    have hφπ : ∀ a, φ a = π a := by
      intro a
      simp [hφ, hπ, TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
    have h1 := Ideal.mem_map_of_mem φ hy
    rw [← hJbar (Bb.ι.base b) rfl] at h1
    have h2 := hJ _ hxb' h1
    rw [map_pow, hφπ] at h2
    exact h2
  have hfin : ∀ k : Fin (m j), g j k ∈ (q.comap π) ^ (ν j k) := by
    intro k
    rw [hform j k]
    exact weierstrass_mem_pow_comap F z hr hz π hπsurj hπker q hqreg (co j k) hbpos (hdvd j k)
      (hcoq j k)
  exact isPermissibleCenter_of_ordElem_le _ (q.comap π) hJP (g j) (hgJ j)
    (fun k => by rw [hordg j k]; exact Ideal.le_ordElem (hfin k)) (hgr j).symm

/-- **Lemma (AB.6)** (p. 306) for an arbitrary open family with removals, assembled from
`Frame.RemovalFamily.isIrreducible_and_isNormallyFlatAlongAt_of_isPermissibleCenter`
(`lem:IV.AB-6-of-permissible-generic`) and
`Frame.RemovalFamily.isPermissibleCenter_totalTransform_closure_of_jBar_le_pow`
(`lem:IV.AB-6-hat-permissible-generic`); the printed Lemma (AB.6) is the instance `U_s = X̂'_s`
(`Frame.isIrreducible_and_isNormallyFlatAlongAt_of_jbar_le_pow`, see there for the paper's
words). -/
@[blueprint "lem:IV.AB-6-generic"
  (statement := /-- Notation as in \cref{lem:IV.AB-6}, for an arbitrary open family with
    removals $U_s\subseteq\hat X_s$ (\cref{lem:IV.3-construction-facts-generic}), with $U_s$ and
    $\bar U_s=U_s\cap\bar X_s$ in place of $\hat X_s'$ and $\bar X_s'$: the conclusion of
    \cref{lem:IV.AB-6} holds, with $\bar B'=c_s^{-1}(B_s)\cap U_s$. (Formalization note: the
    printed Lemma (AB.6) is the instance $U_s=\hat X_s'$; the corrected construction of
    \cref{def:IV.3-construction-componentwise} is the instance $U_s=\hat X_s^{*\prime}$.) -/)
  (proof := /-- The proof of \cref{lem:IV.AB-6}, split as there into
    \cref{lem:IV.AB-6-hat-permissible-generic} and \cref{lem:IV.AB-6-of-permissible-generic}. -/)
  (proofUses := ["lem:IV.AB-6-of-permissible-generic", "lem:IV.AB-6-hat-permissible-generic"])
  (latexEnv := "lemma")]
theorem Frame.RemovalFamily.isIrreducible_and_isNormallyFlatAlongAt_of_jbar_le_pow [Hironaka.HironakaCitedResults.{u}] {N n : ℕ}
    {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
    {𝒮 : Frame hS} (R : 𝒮.RemovalFamily) (s : ℕ) (Bb : Subscheme (𝒮.xBar s).toScheme)
    (hns : ∀ xb ∈ Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme), Bb.IsSimpleAt xb)
    (hirr : IsIrreducible (Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme)))
    (hg : ((𝒮.xBar s).ι ≫ (𝒮.tHat.pre s).composite).base ''
      (Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme)) = {hS.xh})
    (hJ : ∀ xb ∈ Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme),
      (𝒮.jBar s).stalkIdeal xb ≤ (Bb.stalkIdeal xb) ^ 𝒮.b) :
    let Bs : Subscheme (T.X s) := Subscheme.ofClosed
      ⟨closure ((𝒮.cBar s).base '' (Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme))),
        isClosed_closure⟩
    Bs.IsIrreducible ∧
    (∀ xh ∈ R.U s, (Subscheme.totalTransform (𝒮.c s) Bs).stalkIdeal xh =
      Subscheme.stalkIdeal (Bb.ι ≫ (𝒮.xBar s).ι).ker xh) ∧
    ∃ Us : Set (T.X s), (∃ U₀ : Set (T.X s), IsOpen U₀ ∧ Us = U₀ ∩ Bs.pts) ∧ Us.Nonempty ∧
      (∀ x ∈ Us, Bs.IsSimpleAt x) ∧
      (𝒮.cBar s).base '' (Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme)) ⊆ Us ∧
      ∀ x ∈ Us, ∀ j, Subscheme.IsNormallyFlatAlongAt' (T.sys ℜ s j) Bs x :=
  R.isIrreducible_and_isNormallyFlatAlongAt_of_isPermissibleCenter s Bb hns hirr hg
    (R.isPermissibleCenter_totalTransform_closure_of_jBar_le_pow s Bb hns hirr hg hJ)

/-- p. 306, the ring-level step of the proof of Lemma (AB.6): at every point `x̂'` of
`B̄' = Bb ∩ X̄'_s`, the ideal `P̂ = P Ŝ_s` of `c_s⁻¹(B_s)` (`B_s` the closure of `c_s(B̄')`) is a
permissible center for every `Ĵ_j(s) = J_j(s) Ŝ_s`.  The paper: "By the same argument as in the
proof of Lemma (AB.5), we can find a regular frame `(T_s; z_s)` of `Ŝ_s` and elements `g_{jk}(s)`
of `Ĵ_j(s)` such that (1) `z_s` generates the kernel of `Ŝ_s → T̄_s`, (2) (a) the initial forms
of the `g_{jk}(s)` generate `gr_{M̂_s}(Ĵ_j(s), Ŝ_s)` and (b) `ν_{M̂_s}(g_{jk}(s)) = ν_{jk}`,
(3) `g_{jk}(s) = z_s^{ν_{jk}} + ∑ g_{jki}(s) z_s^{ν_{jk}-i}` with `g_{jki}(s) ∈ T_s`, and (4)
`J̄(s)_{x̂'} = (g_{jki}(s)^{b/i}) T̄_s`. Let `P` (resp. `P̂`) be the prime ideal of `B_s` in `S_s`
(resp. `B̄'` in `Ŝ_s`); then `P̂ = P Ŝ_s`. By assumption `Ŝ_s/P̂` is regular, `z_s ∈ P̂` and, if
`P̄ = P̂/(z_s)Ŝ_s`, `P̄^b ⊇ J̄(s)_{x̂'}`. Therefore, by (1), (3), (4), `ν_{P̂}(g_{jk}(s)) ≥ ν_{jk}`
for all `j, k`; hence by (a), (b) of (2), `P̂` is a permissible center for all the `Ĵ_j(s)`."

Proved as the instance `U_s = X̂'_s` of
`Frame.RemovalFamily.isPermissibleCenter_totalTransform_closure_of_jBar_le_pow` (the frames of the
proof of
Lemma (AB.5) at `x̂'`, the identification of the ideal of `B̄'` with `P̂` on `X̂'_s`, and
`isPermissibleCenter_of_ordElem_le`, `lem:IV.AB-6-permissible`). -/
@[blueprint "lem:IV.AB-6-hat-permissible"
  (statement := /-- Notation as in \cref{lem:IV.AB-6}. At every point $\hat x'$ of $\bar B'$,
    with $P$ the ideal of $B_s$ at $x'=c_s(\hat x')$ and $\hat S_s$ the local ring of $\hat X_s$
    at $\hat x'$, the ideal $\hat P=P\hat S_s$ is a permissible center for
    $\hat J_j(s)=J_j(s)\hat S_s$ for all $0\le j\le\beta$ (\cref{def:III.8}). (The ring-level
    step of the proof of \cref{lem:IV.AB-6}, p.~306.) -/)
  (proof := /-- ``By the same argument as in the proof of Lemma (AB.5), we can find a regular
    frame $(T_s;z_s)$ of $\hat S_s$ and elements $g_{jk}(s)$ of $\hat J_j(s)$'' with (1)--(4)
    as in \cref{lem:IV.AB-6}; $\hat P=P\hat S_s$ contains $z_s$, $\hat S_s/\hat P$ is regular
    and $\bar P^b\supseteq\bar J(s)_{\hat x'}$, so $\nu_{\hat P}(g_{jk}(s))\ge\nu_{jk}$, and
    by (a), (b) of (2) $\hat P$ is a permissible center for all the $\hat J_j(s)$
    (\cref{lem:IV.AB-6-permissible}). Proved in Lean through the generic form.
    (Formalization note: in Lean this is the instance $U_s=\hat X_s'$ of
    \cref{lem:IV.AB-6-hat-permissible-generic}.) -/)
  (proofUses := ["lem:IV.AB-5", "lem:IV.AB-6-permissible", "lem:IV.AB-4-frames",
    "lem:IV.AB-6-hat-permissible-generic"])
  (latexEnv := "lemma")]
theorem Frame.isPermissibleCenter_totalTransform_closure_of_jBar_le_pow [Hironaka.HironakaCitedResults.{u}] {N n : ℕ}
    {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
    (𝒮 : Frame hS) (s : ℕ) (Bb : Subscheme (𝒮.xBar s).toScheme)
    (hns : ∀ xb ∈ Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme), Bb.IsSimpleAt xb)
    (hirr : IsIrreducible (Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme)))
    (hg : ((𝒮.xBar s).ι ≫ (𝒮.tHat.pre s).composite).base ''
      (Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme)) = {hS.xh})
    (hJ : ∀ xb ∈ Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme),
      (𝒮.jBar s).stalkIdeal xb ≤ (Bb.stalkIdeal xb) ^ 𝒮.b) :
    ∀ xb ∈ Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme), ∀ j,
      IsPermissibleCenter ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb))
        ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal ((𝒮.xBar s).ι.base xb))
        ((Subscheme.totalTransform (𝒮.c s) (Subscheme.ofClosed
          ⟨closure ((𝒮.cBar s).base ''
            (Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme))), isClosed_closure⟩)).stalkIdeal
          ((𝒮.xBar s).ι.base xb)) :=
  𝒮.removalFamily.isPermissibleCenter_totalTransform_closure_of_jBar_le_pow s Bb hns hirr hg hJ

/-- **Lemma (AB.6)** (p. 306).  The non-singular irreducible subscheme `B̄'` of the open
subscheme `X̄'_s` is given as the restriction to `X̄'_s` of a subscheme `Bb` of `X̄_s` (every
closed subscheme of `X̄'_s` is such a restriction, e.g. of its closure, which is how the proof
proceeds); its points are `Bb.pts ∩ X̄'_s`.  "`B̄' = c_s⁻¹(B_s) ∩ X̂'_s`" is compared stalkwise at
the points of `X̂'_s`, `B̄'` being viewed in `X̂_s` through `X̄_s ⊆ X̂_s`; "containing no
multiple points of `B_s`" means that every point of `U_s` is a simple point of `B_s`.

In Lean the proof is the paper's, split in two: the scheme-level part is
`Frame.isIrreducible_and_isNormallyFlatAlongAt_of_isPermissibleCenter`
(`Hironaka/Ch4/CompletionTransforms.lean`, `lem:IV.AB-6-of-permissible`), from the ring-level step
that `P̂` is a permissible center for the `Ĵ_j(s)`
(`Frame.isPermissibleCenter_totalTransform_closure_of_jBar_le_pow`,
`lem:IV.AB-6-hat-permissible`). -/
@[blueprint "lem:IV.AB-6"
  (statement := /-- \textbf{Lemma (AB.6).} Notation as in \cref{def:IV.3-setup},
    \cref{def:IV.3-frame}, \cref{def:IV.3-construction}. Let $\bar B'$ be any non-singular
    irreducible subscheme of $\bar X_s'$ such that $\hat g_s(\bar B')$ consists of only the
    point $\hat x_0$, and that the stalk $\bar J(s)_{\hat x}$ is contained in the $b$th power
    of the prime ideal of $\bar B'$ at every point $\hat x$ of $\bar B'$. Let $B_s$ be the
    closure of $c_s(\bar B')$ in $X_s$, which may be viewed as a reduced subscheme of $X_s$.
    Then $B_s$ is an irreducible subscheme of $X_s$ such that
    $\bar B'=c_s^{-1}(B_s)\cap\hat X_s'$, and there exists a non-empty open subset $U_s$ of
    $B_s$, containing no multiple points of $B_s$, such that (i) $U_s\supseteq c_s(\bar B')$
    and (ii) $V_1(s),\dots,V_\beta(s)$ and $W(s)$ are all normally flat along $B_s$ at every
    point of $U_s$ (\cref{def:0.1-normally-flat-at}). (p.~306.) (Formalization notes (encoding):
    $\bar B'$ is given as the restriction to $\bar X_s'$ of a subscheme of $\bar X_s$;
    $\bar B'=c_s^{-1}(B_s)\cap\hat X_s'$ is compared at the points of $\hat X_s'$; ``no
    multiple points'' means that every point of $U_s$ is a simple point of $B_s$.) -/)
  (proof := /-- Let $\bar B$ be the closure of $\bar B'$ in $\bar X_s$ (i.e., the subscheme of
    $\hat X_s$ in which $\bar B'$ is dense). Since $\hat X_s'$ (resp.\ $\bar X_s'$) is an open
    subscheme of $\hat X_s$ (resp.\ $\bar X_s$) and $\bar X_s'=\bar X_s\cap\hat X_s'$, we have
    $\bar B'=\bar B\cap\bar X_s'=\bar B\cap\hat X_s'$. Then $\bar B$ is a reduced irreducible
    subscheme of $\hat X_s$ and $\hat g_s(\bar B)=\hat x_0$. Hence by the Corollary of Lemma
    (AB.3) (\cref{cor:IV.AB-3}) we have a unique reduced irreducible subscheme $B_s$ of $X_s$
    such that $\bar B=c_s^{-1}(B_s)$ and $B_s=c_s(\bar B)$; moreover $c_s$ induces an
    isomorphism $\bar B\to B_s$. Clearly, $B_s$ is the closure of $c_s(\bar B')$ in $X_s$, and
    $\bar B'=c_s^{-1}(B_s)\cap\hat X_s'$. Let $U_s$ be the open subset of $B_s$ consisting of
    those simple points of $B_s$ at which all the $V_j(s)$ $(1\le j\le\beta)$ and $W(s)$ are
    normally flat along $B_s$. We want to prove that $U_s\supseteq c_s(\bar B')$. Let
    $\hat x'$ be any point of $\bar B'$, $x'=c_s(\hat x')$, $S_s$ (resp.\ $\hat S_s$) the local
    ring of $X_s'$ at $x'$ (resp.\ $\hat X_s'$ at $\hat x'$), $J_j(s)$ the ideal of $V_j(s)$,
    $J_0(s)$ that of $W(s)$ in $S_s$, $\hat J_j(s)=J_j(s)\hat S_s$ $(0\le j\le\beta)$, and
    $\bar T_s$ the local ring of $\bar X_s'$ at $\hat x'$. By the same argument as in the proof
    of Lemma (AB.5) (\cref{lem:IV.AB-5}), we can find a regular frame $(T_s;z_s)$ of $\hat S_s$
    and elements $g_{jk}(s)$ of $\hat J_j(s)$ with (1) $z_s$ generates the kernel of
    $\hat S_s\to\bar T_s$, (2) (a) the initial forms of the $g_{jk}(s)$ generate
    $\operatorname{gr}_{\hat M_s}(\hat J_j(s),\hat S_s)$ and (b)
    $\nu_{\hat M_s}(g_{jk}(s))=\nu_{jk}$, (3)
    $g_{jk}(s)=z_s^{\nu_{jk}}+\sum_ig_{jki}(s)z_s^{\nu_{jk}-i}$ with $g_{jki}(s)\in T_s$, and (4)
    $\bar J(s)_{\hat x'}=(g_{jki}(s)^{b/i})\bar T_s$. Let $P$ (resp.\ $\hat P$) be the prime
    ideal of $B_s$ in $S_s$ (resp.\ $\bar B'$ in $\hat S_s$); then $\hat P=P\hat S_s$. By
    assumption $\hat S_s/\hat P$ is regular, $z_s\in\hat P$ and, if $\bar P=\hat P/(z_s)\hat S_s$,
    $\bar P^b\supseteq\bar J(s)_{\hat x'}$. Therefore, by (1), (3), (4),
    $\nu_{\hat P}(g_{jk}(s))\ge\nu_{jk}$ for all $j,k$; hence by (a), (b) of (2), $\hat P$ is a
    permissible center for all the $\hat J_j(s)$. Since $S_s\to\hat S_s$ is faithfully flat and
    $\hat P=P\hat S_s$, $P$ is a permissible center for all $J_j(s)$ (Lemma~9, \S3, Ch.~II,
    \cref{lem:II.3-9}). In other words, all the $V_j(s)$ and $W(s)$ are normally flat along
    $B_s$ at $x'$, i.e.\ $x'=c_s(\hat x')\in U_s$. We conclude that $c_s(\bar B')\subseteq U_s$.
    \textsc{q.e.d.}

    (Formalization note: in Lean this is the instance $U_s=\hat X_s'$ of
    \cref{lem:IV.AB-6-generic}, the lemma for an arbitrary open family with removals.) -/)
  (proofUses := ["cor:IV.AB-3", "lem:IV.AB-5", "lem:II.3-9", "lem:IV.AB-6-of-permissible",
    "lem:IV.AB-6-hat-permissible", "lem:IV.AB-6-generic"])
  (latexEnv := "lemma")]
theorem Frame.isIrreducible_and_isNormallyFlatAlongAt_of_jbar_le_pow [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}}
    {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
    (𝒮 : Frame hS) (s : ℕ) (Bb : Subscheme (𝒮.xBar s).toScheme)
    (hns : ∀ xb ∈ Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme), Bb.IsSimpleAt xb)
    (hirr : IsIrreducible (Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme)))
    (hg : ((𝒮.xBar s).ι ≫ (𝒮.tHat.pre s).composite).base ''
      (Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme)) = {hS.xh})
    (hJ : ∀ xb ∈ Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme),
      (𝒮.jBar s).stalkIdeal xb ≤ (Bb.stalkIdeal xb) ^ 𝒮.b) :
    let Bs : Subscheme (T.X s) := Subscheme.ofClosed
      ⟨closure ((𝒮.cBar s).base '' (Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme))),
        isClosed_closure⟩
    Bs.IsIrreducible ∧
    (∀ xh ∈ 𝒮.xHatPrime s, (Subscheme.totalTransform (𝒮.c s) Bs).stalkIdeal xh =
      Subscheme.stalkIdeal (Bb.ι ≫ (𝒮.xBar s).ι).ker xh) ∧
    ∃ Us : Set (T.X s), (∃ U₀ : Set (T.X s), IsOpen U₀ ∧ Us = U₀ ∩ Bs.pts) ∧ Us.Nonempty ∧
      (∀ x ∈ Us, Bs.IsSimpleAt x) ∧
      (𝒮.cBar s).base '' (Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme)) ⊆ Us ∧
      ∀ x ∈ Us, ∀ j, Subscheme.IsNormallyFlatAlongAt' (T.sys ℜ s j) Bs x :=
  𝒮.removalFamily.isIrreducible_and_isNormallyFlatAlongAt_of_jbar_le_pow s Bb hns hirr hg hJ

/-! ## Remarks 3–5 (pp. 308–310)

As for Lemma (AB.6): each remark is stated for an arbitrary open family with removals
(`Frame.RemovalFamily`), with `X̃ = Ū_s = U_s ∩ X̄_s` (`RemovalFamily.xTilde`) in place of
`X̄'_s`; the printed remarks are the instances `U_s = X̂'_s`. -/

/-! ### Helpers for Remarks 3–5 (generic) -/

theorem stalkIdeal_prod_eq' {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (f : ι → Subscheme X)
    (x : X) : (∏ i ∈ s, f i).stalkIdeal x = ∏ i ∈ s, (f i).stalkIdeal x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (1 : Subscheme X) = ⊤ := rfl
    rw [Finset.prod_empty, Finset.prod_empty, this, Subscheme.stalkIdeal_top_eq]
    exact Ideal.one_eq_top.symm
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Subscheme.stalkIdeal_mul_eq, ih]

theorem ord_mul_prod_ge' {R : Type*} [CommRing R] (M : Ideal R) {ι : Type*} (s : Finset ι)
    (P : ι → Ideal R) (I : Ideal R) :
    Ideal.ord M I + ∑ i ∈ s, Ideal.ord M (P i) ≤ Ideal.ord M (I * ∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have h1 := (Ideal.ord_basic M ⊥ (I * ∏ j ∈ s, P j) (P i)).2.2.2
    have h2 : I * (P i * ∏ j ∈ s, P j) = (I * ∏ j ∈ s, P j) * P i := by ring
    rw [h2]
    calc Ideal.ord M I + (Ideal.ord M (P i) + ∑ j ∈ s, Ideal.ord M (P j))
        = (Ideal.ord M I + ∑ j ∈ s, Ideal.ord M (P j)) + Ideal.ord M (P i) := by ring
      _ ≤ Ideal.ord M (I * ∏ j ∈ s, P j) + Ideal.ord M (P i) := by gcongr
      _ ≤ _ := h1

theorem le_ord_pow_of_le' {R : Type*} [CommRing R] {M Q : Ideal R} (hQ : Q ≤ M) (a : ℕ) :
    (a : ℕ∞) ≤ Ideal.ord M (Q ^ a) :=
  Ideal.le_ord (Ideal.pow_right_mono hQ a)

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

/-- p. 308, "(or, equivalently, `ν_x̃(J̄(s)) ≥ b`)", the easy direction: a point of `S(ℜ^{N-1}_II)`
has `ν(J̄(s)) ≥ b`, by superadditivity of `ν` on products (the `E~_j` are non-singular and the
weight counts the `E~_j` through the point).
Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the paper (p. 308)
"In both cases, we see that `Ẽ_1, ⋯, Ẽ_α̃` are non-singular irreducible subschemes of `X̄'_s` of
codimension 1, and that `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on `X̄'_s`" is false as printed:
the `Ẽ_j` need not be irreducible, and `Ẽ_i = X̃` if `F = E_i`.
The statement is made for the datum with the traces equal to `X̃` emptied
(`(R.datumII s a Jt).emptyIfBot`), which is a weak datum (`isWeakDatum_emptyIfBot_datumII`):
`hII` is `IsWeakDatum`, and `hJt`, `hperm` and the conclusions refer to the emptied datum.  The
irreducibility of the `Ẽ_j` is not used, and there is no hypothesis `hFE`.  For a resolution
datum nothing is emptied (`DatumII.Raw.IsDatum.emptyIfBot_eq`), which gives the printed
statements. -/
theorem le_nu_jBarT_of_mem_S {s : ℕ} (a : Fin (𝒮.eTilde s).1 → ℕ) (Jt : Subscheme (R.xTilde s))
    (hJt : Jt * ∏ j, (((R.datumII s a Jt).emptyIfBot).E j) ^ (a j) = R.jBarT s)
    {xt : R.xTilde s} (hx : xt ∈ ((R.datumII s a Jt).emptyIfBot).S) :
    (𝒮.b : ℕ∞) ≤ Ideal.nu ((R.jBarT s).stalkIdeal xt) := by
  classical
  rw [← hJt, Subscheme.stalkIdeal_mul_eq, stalkIdeal_prod_eq']
  simp only [Subscheme.stalkIdeal_pow_eq]
  refine hx.trans ?_
  have h1 := ord_mul_prod_ge' (maximalIdeal ((R.xTilde s).presheaf.stalk xt)) Finset.univ
    (fun j => ((((R.datumII s a Jt).emptyIfBot).E j).stalkIdeal xt) ^ (a j)) (Jt.stalkIdeal xt)
  refine le_trans ?_ h1
  have hw : ((((R.datumII s a Jt).emptyIfBot).weight xt : ℕ) : ℕ∞) =
      ∑ i ∈ Finset.univ.filter (fun i => xt ∈ (((R.datumII s a Jt).emptyIfBot).E i).pts),
        (a i : ℕ∞) := by
    unfold DatumII.Raw.weight
    rw [Nat.cast_sum]
    rfl
  show ((((R.datumII s a Jt).emptyIfBot).weight xt : ℕ) : ℕ∞) + Ideal.nu (Jt.stalkIdeal xt) ≤ _
  rw [add_comm, hw]
  refine add_le_add le_rfl ?_
  calc (∑ i ∈ Finset.univ.filter fun i => xt ∈ (((R.datumII s a Jt).emptyIfBot).E i).pts,
        (a i : ℕ∞))
      ≤ ∑ i ∈ Finset.univ.filter fun i => xt ∈ ((((R.datumII s a Jt).emptyIfBot).E i)).pts,
          Ideal.ord (maximalIdeal ((R.xTilde s).presheaf.stalk xt))
            (((((R.datumII s a Jt).emptyIfBot).E i).stalkIdeal xt) ^ (a i)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact le_ord_pow_of_le'
          (Subscheme.stalkIdeal_le_maximalIdeal _ (Finset.mem_filter.mp hi).2) _
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end Frame.RemovalFamily

/-- A proper specialization strictly increases the dimension of the local ring at a point of
finite dimension: if `p ⤳ q` and `dim_p = dim_q < ∞` then `p = q`. -/
theorem eq_of_specializes_of_dimAt_eq' {Y : Scheme.{u}} {p q : Y} (h : p ⤳ q) {n : ℕ}
    (hp : Y.dimAt p = (n : WithBot ℕ∞)) (hq : Y.dimAt q = (n : WithBot ℕ∞)) : p = q := by
  by_contra hne
  have hqp : q < p := by
    rw [lt_iff_le_not_ge]
    refine ⟨Scheme.le_iff_specializes.mpr h, fun h' => hne ?_⟩
    exact ((Scheme.le_iff_specializes.mp h').antisymm h).eq.symm
  have hc : ∀ {y : Y} {m : ℕ}, Y.dimAt y = (m : WithBot ℕ∞) → Order.coheight y = (m : ℕ∞) := by
    intro y m hy
    have h1 : ((Order.coheight y : ℕ∞) : WithBot ℕ∞) = (m : WithBot ℕ∞) := by
      rw [← ringKrullDim_stalk_eq_coheight]; exact hy
    exact_mod_cast WithBot.coe_injective h1
  have hp' := hc hp
  have hq' := hc hq
  have := Order.coheight_strictAnti hqp (by rw [hp']; exact ENat.natCast_lt_top n)
  rw [hp', hq'] at this
  exact lt_irrefl _ this

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

/-- `ν` of the stalk of `J̄(s)` on `X̃ = Ū_s` is that of `J̄(s)` on `X̄_s` (an open immersion is an
isomorphism on stalks). -/
theorem nu_jBarT_eq (s : ℕ) (xt : R.xTilde s) :
    Ideal.nu ((R.jBarT s).stalkIdeal xt) =
      Ideal.nu ((𝒮.jBar s).stalkIdeal ((R.uBar s).ι.base xt)) := by
  let xt' : (R.uBar s : Scheme.{u}) := xt
  have h := stalkIdeal_totalTransform (R.uBar s).ι (𝒮.jBar s) xt'
  have : IsIso ((R.uBar s).ι.stalkMap xt') := inferInstance
  have e := LocSucc.nu_map_ringEquiv_of_equivLike
    (asIso ((R.uBar s).ι.stalkMap xt')).commRingCatIsoToRingEquiv
    ((𝒮.jBar s).stalkIdeal ((R.uBar s).ι.base xt'))
  exact (congrArg Ideal.nu h).trans e

end Frame.RemovalFamily

namespace Frame

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS)

/-- `c_0 ∘ ĝ_s = g_s ∘ c_s` on points (the square `X̂_s = X_s ×_X X̂_0`). -/
theorem c0_comp_pre_apply (s : ℕ) (y : 𝒮.tHat.X s) :
    (c0 X x₀).base ((𝒮.tHat.pre s).composite.base y) =
      (T.pre s).composite.base ((𝒮.c s).base y) := by
  have hw := (𝒮.isPullback s).w
  rw [𝒮.c_zero] at hw
  rw [← Scheme.Hom.comp_apply, ← hw, Scheme.Hom.comp_apply]

/-- Every point of `X̄_s` goes under `g_s ∘ c̄_s` to a generization of `x_0` (every point of
`Spec Ŝ` specializes to the closed point `x̂_0`). -/
theorem specializes_composite_cBar (s : ℕ) (xb : (𝒮.xBar s).toScheme) :
    (T.pre s).composite.base ((𝒮.cBar s).base xb) ⤳ x₀ := by
  have := 𝒮.regShat
  have h1 : ((𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base xb)) ⤳ hS.xh :=
    (PrimeSpectrum.le_iff_specializes (R := Shat X x₀) _ _).mp
      (IsLocalRing.le_maximalIdeal
        ((𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base xb) :
          PrimeSpectrum (Shat X x₀)).isPrime.ne_top)
  have h2 := h1.map (c0 X x₀).continuous
  rw [Standing.xh, c0_apply_xhat0] at h2
  have hGeq : (T.pre s).composite.base ((𝒮.cBar s).base xb) =
      (c0 X x₀).base ((𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base xb)) := by
    rw [𝒮.c0_comp_pre_apply]
    rfl
  rw [hGeq]
  exact h2

end Frame

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

/-- Remark 3, the inclusion `c_s(S(ℜ^{N-1}_II)) ⊆ S(ℜ(s)) ∩ g_s⁻¹(x_0)` pointwise (p. 308: "By
virtue of Lemma (AB.5), Remark 1 and the assumption [(1)]"): a point `x̃` of `X̃ = Ū_s` with
`ν(J̄(s)_{x̃}) ≥ b` goes to a point of `S(ℜ(s))` lying over `x_0`.

Gap filled: the paper says only "by virtue of Lemma (AB.5), Remark 1 and the assumption [(1)]".
In the open case `x' = c̄_s(x̃)` is not resolved by Remark 1 with (ii), (iii) of Lemma (AB.5); that
`g_s(x') = x_0` uses that `g_s(x')` is a generization of `x_0` (every point of `Spec Ŝ` specializes
to
the closed point) lying in the finite set `g_s(S(ℜ(s)))` of points at which `X` has dimension `N`,
as
is `x_0` ([(1)]); a proper generization has strictly smaller dimension. -/
theorem cTilde_mem_S_and_composite_eq [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ P r T x₀ s) {xt : R.xTilde s}
    (hν : (𝒮.b : ℕ∞) ≤ Ideal.nu ((R.jBarT s).stalkIdeal xt)) :
    (R.cTilde s).base xt ∈ S ((T.pre s).transformI ℜ) (r.transformSucc (T.pre s)) ∧
      (T.pre s).composite.base ((R.cTilde s).base xt) = x₀ := by
  classical
  have hxb : (R.uBar s).ι.base xt ∈ R.uBar s := xt.2
  have hν' : (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal ((R.uBar s).ι.base xt)) :=
    (R.nu_jBarT_eq s xt) ▸ hν
  obtain ⟨hW, hF, hsing, hNF⟩ := R.cbar_mem_strictTransform_and_not_isSimpleAt_of_b_le_nu s
    ((R.uBar s).ι.base xt) hxb hν'
  have hc : (R.cTilde s).base xt = (𝒮.cBar s).base ((R.uBar s).ι.base xt) := rfl
  have hS' : (R.cTilde s).base xt ∈ S ((T.pre s).transformI ℜ) (r.transformSucc (T.pre s)) := by
    rw [hc]
    cases r with
    | closed F =>
      exact ⟨by rw [MonoidalSuccession.transformI_W]; exact hW, hF F rfl⟩
    | opn U =>
      refine ⟨by rw [MonoidalSuccession.transformI_W]; exact hW, fun hres => ?_⟩
      obtain ⟨hsimple, hNFs, -⟩ := hres
      rw [MonoidalSuccession.transformI_W] at hsimple hNFs
      rcases hS.not_isSimpleAt_or_exists_not_isNormallyFlatAlongAt_of_prepHyp s U rfl hprep with
        hs | ⟨j, hj⟩
      · exact hsing hs hsimple
      · by_cases hW0 : ℜ.W.IsSimpleAt x₀
        · apply hNF hW0 j hj
          have := hNFs (Fin.cast (MonoidalSuccession.β_transformI (T.pre s) ℜ).symm j)
          rwa [MonoidalSuccession.V_transformI] at this
        · exact hsing hW0 hsimple
  refine ⟨hS', ?_⟩
  have hdim := hprep.2.1 _ ⟨_, hS', rfl⟩
  have hdx : X.dimAt x₀ = (N : WithBot ℕ∞) := hprep.2.1 _ hprep.2.2.2
  exact eq_of_specializes_of_dimAt_eq' (by rw [hc]; exact 𝒮.specializes_composite_cBar s _) hdim hdx

end Frame.RemovalFamily

section OrderAdditive

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- `ν(f ^ a) = a ν(f)` in a regular local ring (`gr_M(R)` is a domain). -/
theorem ordElem_pow_maximalIdeal (f : R) (a : ℕ) :
    Ideal.ordElem (maximalIdeal R) (f ^ a) = a * Ideal.ordElem (maximalIdeal R) f := by
  induction a with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    exact Ideal.ordElem_eq_zero_of_isUnit isUnit_one
  | succ a ih =>
    rw [pow_succ, ordElem_mul_maximalIdeal, ih, Nat.cast_succ, add_mul, one_mul]

theorem ordElem_prod_maximalIdeal {ι : Type*} (s : Finset ι) (f : ι → R) :
    Ideal.ordElem (maximalIdeal R) (∏ i ∈ s, f i) =
      ∑ i ∈ s, Ideal.ordElem (maximalIdeal R) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact Ideal.ordElem_eq_zero_of_isUnit isUnit_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ordElem_mul_maximalIdeal, ih]

/-- `ν(I · (π)) ≤ ν(I) + ν(π)` in a regular local ring (`gr_M(R)` is a domain). -/
theorem nu_mul_span_singleton_le (I : Ideal R) (π : R) :
    Ideal.nu (I * Ideal.span {π}) ≤ Ideal.nu I + Ideal.ordElem (maximalIdeal R) π := by
  by_cases he : Ideal.ordElem (maximalIdeal R) π = ⊤
  · rw [he, add_top]; exact le_top
  obtain ⟨e0, he0⟩ := ENat.ne_top_iff_exists.mp he
  refine Ideal.ord_le fun ν hν => ?_
  by_cases hle : ν ≤ e0
  · calc (ν : ℕ∞) ≤ e0 := by exact_mod_cast hle
      _ = Ideal.ordElem (maximalIdeal R) π := he0
      _ ≤ _ := le_add_self
  · push Not at hle
    have hI : I ≤ maximalIdeal R ^ (ν - e0) := by
      intro f hf
      have hfπ : f * π ∈ maximalIdeal R ^ ν :=
        hν (Ideal.mul_mem_mul hf (Ideal.mem_span_singleton_self π))
      have h1 : (ν : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) f + e0 := by
        have := Ideal.le_ordElem hfπ
        rwa [ordElem_mul_maximalIdeal, ← he0] at this
      apply Ideal.mem_pow_of_le_ordElem
      by_cases hf' : Ideal.ordElem (maximalIdeal R) f = ⊤
      · rw [hf']; exact le_top
      obtain ⟨f0, hf0⟩ := ENat.ne_top_iff_exists.mp hf'
      rw [← hf0] at h1 ⊢
      have : ν ≤ f0 + e0 := by exact_mod_cast h1
      exact_mod_cast (by omega : ν - e0 ≤ f0)
    have h2 := Ideal.le_ord hI
    calc (ν : ℕ∞) = ((ν - e0 : ℕ) : ℕ∞) + e0 := by
          rw [← Nat.cast_add]; congr 1; omega
      _ ≤ Ideal.nu I + e0 := by gcongr
      _ = _ := by rw [he0]

end OrderAdditive

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

/-- `X̃ = Ū_s` is non-singular (an open subscheme of `X̄_s`, which is non-singular on `Ū_s`). -/
theorem isNonsingular_xTilde [Hironaka.HironakaCitedResults.{u}] (s : ℕ) : (R.xTilde s).IsNonsingular := fun xt => by
  let xt' : (R.uBar s : Scheme.{u}) := xt
  have h := (R.isSimpleAt_and_isIrreducible_and_isNonsingCodimOneOn s).1
    ((R.uBar s).ι.base xt') xt.2
  have h' : IsRegularLocalRing ((𝒮.xBar s).toScheme.presheaf.stalk ((R.uBar s).ι.base xt')) := h
  have : IsIso ((R.uBar s).ι.stalkMap xt') := inferInstance
  exact IsRegularLocalRing.of_ringEquiv
    (asIso ((R.uBar s).ι.stalkMap xt')).commRingCatIsoToRingEquiv

/-- Remark 3 (a), the converse direction: a point of `X̃` with `ν(J̄(s)_x̃) ≥ b` lies in
`S(ℜ^{N-1}_II)`, i.e. `∑_{x̃∈Ẽ_i} a_i + ν(J̃_x̃) ≥ b` (p. 308: "or, equivalently,
`ν_x̃(J̄(s)) ≥ b`").  Orders of ideals are additive on products because `gr_M` is a domain, and the
stalk of `Ẽ_i` at a point of `Ẽ_i` is generated by a regular parameter (order one).

Gap filled: the paper says only "(or, equivalently, ...)".
Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the paper (p. 308)
"In both cases, we see that `Ẽ_1, ⋯, Ẽ_α̃` are non-singular irreducible subschemes of `X̄'_s` of
codimension 1, and that `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on `X̄'_s`" is false as printed:
the `Ẽ_j` need not be irreducible, and `Ẽ_i = X̃` if `F = E_i`.
The statement is made for the datum with the traces equal to `X̃` emptied
(`(R.datumII s a Jt).emptyIfBot`), which is a weak datum (`isWeakDatum_emptyIfBot_datumII`):
`hII` is `IsWeakDatum`, and `hJt`, `hperm` and the conclusions refer to the emptied datum.  The
irreducibility of the `Ẽ_j` is not used, and there is no hypothesis `hFE`.  For a resolution
datum nothing is emptied (`DatumII.Raw.IsDatum.emptyIfBot_eq`), which gives the printed
statements. -/
theorem mem_S_of_le_nu_jBarT [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (a : Fin (𝒮.eTilde s).1 → ℕ) (Jt : Subscheme (R.xTilde s))
    (hJt : Jt * ∏ j, (((R.datumII s a Jt).emptyIfBot).E j) ^ (a j) = R.jBarT s)
    (hII : ((R.datumII s a Jt).emptyIfBot).IsWeakDatum) {xt : R.xTilde s}
    (hν : (𝒮.b : ℕ∞) ≤ Ideal.nu ((R.jBarT s).stalkIdeal xt)) :
    xt ∈ ((R.datumII s a Jt).emptyIfBot).S := by
  classical
  have : IsRegularLocalRing ((R.xTilde s).presheaf.stalk xt) := R.isNonsingular_xTilde s xt
  obtain ⟨Z, hZ, -, hE⟩ := DatumTransform.exists_rsop_adapted_of_isNonsingularDivisor (B := ⊥)
    ((R.datumII s a Jt).emptyIfBot).E (R.isNonsingular_xTilde s) hII.2.1 hII.2.2.1
    (fun x _ => hII.2.2.1 x) xt
  have hq : ∀ j, ∃ q : (R.xTilde s).presheaf.stalk xt,
      ((((R.datumII s a Jt).emptyIfBot).E j).stalkIdeal xt) ^ (a j) = Ideal.span {q} ∧
        Ideal.ordElem (maximalIdeal _) q =
          if xt ∈ (((R.datumII s a Jt).emptyIfBot).E j).pts then (a j : ℕ∞) else 0 := by
    intro j
    rcases hE j with h | ⟨c, hc, h⟩
    · refine ⟨1, ?_, ?_⟩
      · rw [h, Ideal.top_pow, Ideal.span_singleton_one]
      · have : xt ∉ (((R.datumII s a Jt).emptyIfBot).E j).pts := by
          rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, not_not]; exact h
        rw [ite_eq_right_iff.mpr (fun h => absurd h this)]
        exact Ideal.ordElem_eq_zero_of_isUnit isUnit_one
    · have hext : ExtendsToRSOP _ Z := ExtendsToRSOP.of_isRegularSystemOfParameters hZ
      have hcm : c ∈ maximalIdeal _ := hext.mem_maximalIdeal hc
      have hc2 : c ∉ maximalIdeal _ ^ 2 := hext.notMem_maximalIdeal_sq hc
      refine ⟨c ^ (a j), ?_, ?_⟩
      · rw [h, Ideal.span_singleton_pow]
      · have : xt ∈ (((R.datumII s a Jt).emptyIfBot).E j).pts := by
          rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, h, Ne, Ideal.span_singleton_eq_top]
          exact (IsLocalRing.mem_maximalIdeal _).mp hcm
        rw [ite_eq_left_iff.mpr (fun h => absurd this h), ordElem_pow_maximalIdeal,
          Ideal.ordElem_eq_one_of_mem_of_notMem_sq (maximalIdeal.isMaximal _).ne_top hcm hc2,
          mul_one]
  choose q hq1 hq2 using hq
  have hprod : (R.jBarT s).stalkIdeal xt =
      (Jt.stalkIdeal xt) * Ideal.span {∏ j, q j} := by
    rw [← hJt, Subscheme.stalkIdeal_mul_eq, stalkIdeal_prod_eq']
    simp only [Subscheme.stalkIdeal_pow_eq, hq1]
    rw [Ideal.prod_span_singleton]
  have hw : ((((R.datumII s a Jt).emptyIfBot).weight xt : ℕ) : ℕ∞) =
      ∑ j, Ideal.ordElem (maximalIdeal _) (q j) := by
    simp only [hq2]
    unfold DatumII.Raw.weight
    rw [Nat.cast_sum, Finset.sum_filter]
    rfl
  have hle : Ideal.nu ((R.jBarT s).stalkIdeal xt) ≤
      ((((R.datumII s a Jt).emptyIfBot).weight xt : ℕ) : ℕ∞) + Ideal.nu (Jt.stalkIdeal xt) := by
    rw [hprod, add_comm]
    refine (nu_mul_span_singleton_le _ _).trans ?_
    rw [ordElem_prod_maximalIdeal, ← hw]
  exact hν.trans (hle.trans le_rfl)

end Frame.RemovalFamily

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

/-- Remark 4 (p. 309), the hypothesis `J̄(s)_x̂ ⊆ P(B̃)^b` of Lemma (AB.6): for a non-singular
irreducible `B̃ ⊆ S(ℜ^{N-1}_II)` the ideal `J̄(s)` is contained in the `b`th power of the ideal of
`B̃` at every point of `B̃`.

Gap filled: the paper says only "By Lemma (AB.6)" and does not derive the hypothesis of (AB.6) from
the
permissibility of `f_B̃` (`B̃ ⊆ S*(ℜ^{N-1}_II)`).  In Lean: at the generic point `ξ` of `B̃` one has
`ν(J̄(s)_ξ) ≥ b` since `ξ ∈ S(ℜ^{N-1}_II)`, and the `P`-adic order of `J̄(s)_x̃` is the order at the
generic point (`Subscheme.le_nu_generic_iff`: the powers of `P_x̃` are `P_x̃`-primary).
Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the paper (p. 308)
"In both cases, we see that `Ẽ_1, ⋯, Ẽ_α̃` are non-singular irreducible subschemes of `X̄'_s` of
codimension 1, and that `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on `X̄'_s`" is false as printed:
the `Ẽ_j` need not be irreducible, and `Ẽ_i = X̃` if `F = E_i`.
The statement is made for the datum with the traces equal to `X̃` emptied
(`(R.datumII s a Jt).emptyIfBot`), which is a weak datum (`isWeakDatum_emptyIfBot_datumII`):
`hII` is `IsWeakDatum`, and `hJt`, `hperm` and the conclusions refer to the emptied datum.  The
irreducibility of the `Ẽ_j` is not used, and there is no hypothesis `hFE`.  For a resolution
datum nothing is emptied (`DatumII.Raw.IsDatum.emptyIfBot_eq`), which gives the printed
statements. -/
theorem stalkIdeal_jBarT_le_pow [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (a : Fin (𝒮.eTilde s).1 → ℕ) (Jt : Subscheme (R.xTilde s))
    (hJt : Jt * ∏ j, (((R.datumII s a Jt).emptyIfBot).E j) ^ (a j) = R.jBarT s)
    (Bt : Subscheme (R.xTilde s))
    (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hsub : ∀ xt ∈ Bt.pts, xt ∈ ((R.datumII s a Jt).emptyIfBot).S) {xt : R.xTilde s}
    (hx : xt ∈ Bt.pts) :
    (R.jBarT s).stalkIdeal xt ≤ (Bt.stalkIdeal xt) ^ 𝒮.b := by
  have hirr := Subscheme.isIrreducible_pts Bt hBti
  have hξ : IsGenericPoint hirr.genericPoint Bt.pts := by
    rw [IsGenericPoint, hirr.isGenericPoint_genericPoint_closure.def]
    exact (show IsClosed Bt.pts from Bt.support.isClosed).closure_eq
  have hξB : hirr.genericPoint ∈ Bt.pts := hξ.mem
  exact (Subscheme.le_nu_generic_iff (R.isNonsingular_xTilde s) hBt hξ hx (R.jBarT s) 𝒮.b).mp
    (R.le_nu_jBarT_of_mem_S a Jt hJt (hsub _ hξB))

end Frame.RemovalFamily

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

/-- The closure in `X̄_s` of (the image of) a subscheme `B̃` of the open subscheme `X̃ = Ū_s`, with
its
reduced structure: the subscheme `B̄` of `X̄_s` whose restriction to `X̃` is `B̃` when `B̃` is
reduced
(the form in which Lemma (AB.6) is stated, with `B̄' = B̄ ∩ X̄'_s`). -/
def bb (s : ℕ) (Bt : Subscheme (R.xTilde s)) : Subscheme (𝒮.xBar s).toScheme :=
  Subscheme.ofClosed ⟨closure ((R.uBar s).ι.base '' Bt.pts), isClosed_closure⟩

theorem pts_bb (s : ℕ) (Bt : Subscheme (R.xTilde s)) :
    (R.bb s Bt).pts = closure ((R.uBar s).ι.base '' Bt.pts) :=
  Subscheme.pts_ofClosed _

theorem preimage_pts_bb (s : ℕ) (Bt : Subscheme (R.xTilde s)) :
    (R.uBar s).ι.base ⁻¹' (R.bb s Bt).pts = Bt.pts := by
  rw [pts_bb]
  have h := (R.uBar s).ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image
    (show Set (R.uBar s : Scheme.{u}) from Bt.pts)
  exact h.symm.trans (show IsClosed Bt.pts from Bt.support.isClosed).closure_eq

theorem pts_bb_inter_uBar (s : ℕ) (Bt : Subscheme (R.xTilde s)) :
    (R.bb s Bt).pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme) = (R.uBar s).ι.base '' Bt.pts := by
  ext xb
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨xt, rfl⟩ : xb ∈ Set.range (R.uBar s).ι.base := by
      rw [Scheme.Opens.range_ι]; exact h2
    exact ⟨xt, by rw [← R.preimage_pts_bb s Bt]; exact h1, rfl⟩
  · rintro ⟨xt, hxt, rfl⟩
    refine ⟨?_, xt.2⟩
    rw [pts_bb]
    exact subset_closure ⟨xt, hxt, rfl⟩

theorem totalTransform_bb (s : ℕ) (Bt : Subscheme (R.xTilde s)) (hBtred : Bt.IsReduced) :
    Subscheme.totalTransform (R.uBar s).ι (R.bb s Bt) = Bt := by
  have hred : (Subscheme.totalTransform (R.uBar s).ι (R.bb s Bt)).IsReduced :=
    FlatPreimm.isReduced_totalTransform (R.uBar s).ι _ (Subscheme.ofClosed_isReduced _)
  have hpts : (Subscheme.totalTransform (R.uBar s).ι (R.bb s Bt)).pts = Bt.pts := by
    rw [FlatPreimm.pts_totalTransform]
    exact R.preimage_pts_bb s Bt
  rw [Subscheme.eq_ofClosed_support _ hred, Subscheme.eq_ofClosed_support Bt hBtred]
  congr 1
  exact TopologicalSpace.Closeds.ext hpts

theorem stalkIdeal_eq_map_bb (s : ℕ) (Bt : Subscheme (R.xTilde s)) (hBtred : Bt.IsReduced)
    (xt : R.xTilde s) :
    Bt.stalkIdeal xt = ((R.bb s Bt).stalkIdeal ((R.uBar s).ι.base xt)).map
      (FlatPreimm.stalkEquiv (R.uBar s).ι xt) := by
  conv_lhs => rw [← R.totalTransform_bb s Bt hBtred]
  exact FlatPreimm.stalkIdeal_totalTransform (R.uBar s).ι _ xt

end Frame.RemovalFamily

/-- `ℜ(s).extendBy B` is resolved at `x` iff `B` is simple at `x`, all members `V_1(s), …, V_β(s),
W(s)`
of the transformed datum are normally flat along `B` at `x`, and `E(s)` has only normal crossings
with
`B` at `x` (the system `succSystem` is that of `ℜ(s)`). -/
theorem resolvedAt_extendBy_transformI_iff {X Y : Scheme.{u}} (g : MonoidalSuccession X Y)
    (ℜ : DatumI.Raw X) (B : Subscheme Y) (x : Y) :
    ((g.transformI ℜ).extendBy B).ResolvedAt x ↔
      B.IsSimpleAt x ∧ (∀ j, Subscheme.IsNormallyFlatAlongAt' (succSystem g ℜ j) B x) ∧
        (g.transformI ℜ).E.HasOnlyNormalCrossingsWithAt B x := by
  obtain ⟨hW, hV⟩ := succSystem_eq_transformI g ℜ
  have hβ := MonoidalSuccession.β_transformI g ℜ
  show B.IsSimpleAt x ∧ (∀ j, Subscheme.IsNormallyFlatAlongAt'
    ((Fin.snoc (α := fun _ => Subscheme Y) (g.transformI ℜ).V (g.transformI ℜ).W :
      Fin ((g.transformI ℜ).β + 1) → Subscheme Y) j) B x) ∧ _ ↔ _
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  constructor
  · intro H j
    induction j using Fin.lastCases with
    | last =>
      rw [hW]
      have := H (Fin.last _)
      rwa [Fin.snoc_last] at this
    | cast i =>
      rw [hV i]
      have := H (Fin.castSucc (Fin.cast hβ.symm i))
      rwa [Fin.snoc_castSucc] at this
  · intro H j
    induction j using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last, ← hW]
      exact H _
    | cast i =>
      rw [Fin.snoc_castSucc]
      have := H (Fin.castSucc (Fin.cast hβ i))
      have e : Fin.cast hβ.symm (Fin.cast hβ i) = i := Fin.ext rfl
      rwa [hV, e] at this

theorem exists_pts_subset_closure_inter {Z : Type*} [TopologicalSpace Z] [QuasiSober Z] {A : Set Z}
    (hA : IsClosed A) (hirr : IsIrreducible A) {O : Set Z} (hO : IsOpen O)
    (hne : (O ∩ A).Nonempty) :
    A ⊆ closure (O ∩ A) := by
  have hξ : closure {hirr.genericPoint} = A := hirr.closure_genericPoint hA
  obtain ⟨z, hzO, hzA⟩ := hne
  have hξA : hirr.genericPoint ∈ A := hξ.le (subset_closure (Set.mem_singleton _))
  have hξz : hirr.genericPoint ⤳ z := specializes_iff_mem_closure.mpr (by rw [hξ]; exact hzA)
  have hξO : hirr.genericPoint ∈ O := hξz.mem_open hO hzO
  have hmem : hirr.genericPoint ∈ O ∩ A := ⟨hξO, hξA⟩
  calc A = closure {hirr.genericPoint} := hξ.symm
    _ ⊆ closure (O ∩ A) :=
      closure_minimal (Set.singleton_subset_iff.mpr (subset_closure hmem)) isClosed_closure

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

theorem isSimpleAt_bb {s : ℕ} {Bt : Subscheme (R.xTilde s)} (hBt : Bt.IsNonsingular)
    (hBtred : Bt.IsReduced) {xt : R.xTilde s} (hx : xt ∈ Bt.pts) :
    (R.bb s Bt).IsSimpleAt ((R.uBar s).ι.base xt) := by
  refine ⟨?_, ?_⟩
  · show _ ∈ (R.bb s Bt).pts
    rw [R.pts_bb]
    exact subset_closure ⟨xt, hx, rfl⟩
  · have hreg : IsRegularLocalRing ((R.xTilde s).presheaf.stalk xt ⧸
        (Subscheme.totalTransform (R.uBar s).ι (R.bb s Bt)).stalkIdeal xt) := by
      rw [R.totalTransform_bb s Bt hBtred]
      exact Subscheme.isRegularLocalRing_quotient_of_isNonsingular hBt hx
    obtain ⟨e⟩ := FlatPreimm.quotEquiv (R.uBar s).ι (R.bb s Bt) xt
    exact IsRegularLocalRing.of_ringEquiv e.symm

end Frame.RemovalFamily

theorem le_of_map_le_map_equiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    {I K : Ideal A} (h : I.map e ≤ K.map e) : I ≤ K := by
  have := Ideal.map_le_iff_le_comap.mp h
  rwa [Ideal.comap_map_of_bijective e e.bijective] at this

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

/-- The hypotheses of Lemma (AB.6) for `B̄ = R.bb s Bt` with `B̄' = B̄ ∩ Ū_s = B̃`, for a
non-singular irreducible `B̃ ⊆ S(ℜ^{N-1}_II)`.
Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the paper (p. 308)
"In both cases, we see that `Ẽ_1, ⋯, Ẽ_α̃` are non-singular irreducible subschemes of `X̄'_s` of
codimension 1, and that `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on `X̄'_s`" is false as printed:
the `Ẽ_j` need not be irreducible, and `Ẽ_i = X̃` if `F = E_i`.
The statement is made for the datum with the traces equal to `X̃` emptied
(`(R.datumII s a Jt).emptyIfBot`), which is a weak datum (`isWeakDatum_emptyIfBot_datumII`):
`hII` is `IsWeakDatum`, and `hJt`, `hperm` and the conclusions refer to the emptied datum.  The
irreducibility of the `Ẽ_j` is not used, and there is no hypothesis `hFE`.  For a resolution
datum nothing is emptied (`DatumII.Raw.IsDatum.emptyIfBot_eq`), which gives the printed
statements. -/
theorem ab6_inputs [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (a : Fin (𝒮.eTilde s).1 → ℕ) (Jt : Subscheme (R.xTilde s))
    (hJt : Jt * ∏ j, (((R.datumII s a Jt).emptyIfBot).E j) ^ (a j) = R.jBarT s)
    (Bt : Subscheme (R.xTilde s)) (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hsub : ∀ xt ∈ Bt.pts, xt ∈ ((R.datumII s a Jt).emptyIfBot).S)
    (hg : ∀ xt ∈ Bt.pts, (R.gTilde s).base xt = hS.xh) :
    (∀ xb ∈ (R.bb s Bt).pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme), (R.bb s Bt).IsSimpleAt xb) ∧
    IsIrreducible ((R.bb s Bt).pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme)) ∧
    ((𝒮.xBar s).ι ≫ (𝒮.tHat.pre s).composite).base ''
      ((R.bb s Bt).pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme)) = {hS.xh} ∧
    (∀ xb ∈ (R.bb s Bt).pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme),
      (𝒮.jBar s).stalkIdeal xb ≤ ((R.bb s Bt).stalkIdeal xb) ^ 𝒮.b) := by
  have hBtred : Bt.IsReduced := Subscheme.isReduced_of_isNonsingular hBt
  have hirrBt : IsIrreducible Bt.pts := Subscheme.isIrreducible_pts Bt hBti
  have hint := R.pts_bb_inter_uBar s Bt
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro xb hxb
    rw [hint] at hxb
    obtain ⟨xt, hxt, rfl⟩ := hxb
    exact R.isSimpleAt_bb hBt hBtred hxt
  · rw [hint]
    exact hirrBt.image _ (R.uBar s).ι.continuous.continuousOn
  · refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · obtain ⟨xt, hxt⟩ := hirrBt.nonempty
      refine ⟨(R.uBar s).ι.base xt, ?_, hg xt hxt⟩
      rw [hint]
      exact ⟨xt, hxt, rfl⟩
    · rintro _ ⟨xb, hxb, rfl⟩
      rw [hint] at hxb
      obtain ⟨xt, hxt, rfl⟩ := hxb
      exact hg xt hxt
  · intro xb hxb
    rw [hint] at hxb
    obtain ⟨xt, hxt, rfl⟩ := hxb
    have h1 := R.stalkIdeal_jBarT_le_pow a Jt hJt Bt hBt hBti hsub hxt
    have h2 : (R.jBarT s).stalkIdeal xt = ((𝒮.jBar s).stalkIdeal ((R.uBar s).ι.base xt)).map
        (FlatPreimm.stalkEquiv (R.uBar s).ι xt) :=
      FlatPreimm.stalkIdeal_totalTransform (R.uBar s).ι (𝒮.jBar s) xt
    refine le_of_map_le_map_equiv (FlatPreimm.stalkEquiv (R.uBar s).ι xt) ?_
    rw [Ideal.map_pow]
    refine h2.symm.le.trans (h1.trans ?_)
    exact (congrArg (· ^ 𝒮.b) (R.stalkIdeal_eq_map_bb s Bt hBtred xt)).le

end Frame.RemovalFamily

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

/-- The points of `X̃` over `S(ℜ^{N-1}_II)` go to `x̂_0` under `g̃` (p. 309: "we have `g̃(B̃) =
x̂_0`"). -/
theorem gTilde_eq_xh [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ P r T x₀ s) {xt : R.xTilde s}
    (hν : (𝒮.b : ℕ∞) ≤ Ideal.nu ((R.jBarT s).stalkIdeal xt)) :
    (R.gTilde s).base xt = hS.xh :=
  𝒮.composite_tHat_eq_xhat0 (hS.ambient.2.1 x₀) s
    ((𝒮.xBar s).ι.base ((R.uBar s).ι.base xt)) (R.cTilde_mem_S_and_composite_eq hprep hν).2

end Frame.RemovalFamily

/-- Adding divisors that contain the center: if `⨅_{i ∈ S} E_i` has an adapted regular system of
parameters with `D`, and the other `E_i` are `⊤` or contained in `D` at `x`, while all the `E_i` are
generated by members of one regular system of parameters at `x` (they form a datum), then
`⨅ E_i` has only normal crossings with `D` at `x`.  (p. 309, open case: "either `E_i(s)` does not
contain `x` or it contains `B_s`.  In view of this fact, we can again conclude that
`⋃ E_i(s)` has only normal crossings with `B_s` at the point `x`".) -/
theorem Subscheme.hasOnlyNormalCrossingsWithAt_iInf_of_seen_of_old {Y : Scheme.{u}} {x : Y}
    [IsRegularLocalRing (Y.presheaf.stalk x)] {ι : Type*} [Fintype ι] (E : ι → Subscheme Y)
    (S : Set ι) (D : Subscheme Y)
    (hDreg : IsRegularLocalRing (Y.presheaf.stalk x ⧸ D.stalkIdeal x))
    (hE0 : ∃ Z₀ : Finset (Y.presheaf.stalk x), IsRegularSystemOfParameters _ Z₀ ∧
      ∀ i, (E i).stalkIdeal x = ⊤ ∨ ∃ k ∈ Z₀, (E i).stalkIdeal x = Ideal.span {k})
    (hseen : ∃ Z₁ : Finset (Y.presheaf.stalk x), IsRegularSystemOfParameters _ Z₁ ∧
      (∃ T ⊆ Z₁, D.stalkIdeal x = Ideal.span (T : Set (Y.presheaf.stalk x))) ∧
      ∀ i ∈ S, (E i).stalkIdeal x = ⊤ ∨ ∃ a ∈ Z₁, (E i).stalkIdeal x = Ideal.span {a})
    (hold : ∀ i ∉ S, (E i).stalkIdeal x = ⊤ ∨ (E i).stalkIdeal x ≤ D.stalkIdeal x) :
    (⨅ i, E i).HasOnlyNormalCrossingsWithAt D x := by
  classical
  obtain ⟨Z₀, hZ₀, hE0'⟩ := hE0
  have hZ₀ext : ExtendsToRSOP _ Z₀ := ExtendsToRSOP.of_isRegularSystemOfParameters hZ₀
  obtain ⟨K₁, hK₁Z, hK₁gen, hK₁⟩ := exists_iInf_eq_span_prod_of_forall_eq_top_or_eq_span
    (fun j => (E j).stalkIdeal x) hZ₀ext hE0'
  have hK₁ext : ExtendsToRSOP _ K₁ := hZ₀ext.mono hK₁Z
  have hmaxk : ∀ k ∈ K₁, k ∈ maximalIdeal _ := fun k hk => hZ₀ext.mem_maximalIdeal (hK₁Z hk)
  have hP : (D.stalkIdeal x).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (Transforms.isDomain_of_isRegularLocalRing _)
  obtain ⟨Z₁, hZ₁, ⟨T, hTZ, hT⟩, hS1⟩ := hseen
  have hβex : ∀ k, k ∈ K₁ → k ∉ D.stalkIdeal x → ∃ b ∈ Z₁, Ideal.span {k} = Ideal.span {b} := by
    intro k hk hkP
    obtain ⟨i, hi⟩ := hK₁gen k hk
    by_cases hiS : i ∈ S
    · have hne : (E i).stalkIdeal x ≠ ⊤ := by
        rw [hi, Ne, Ideal.span_singleton_eq_top]
        intro hu
        exact (IsLocalRing.mem_maximalIdeal _).mp (hmaxk k hk) hu
      obtain ⟨a, haZ, ha⟩ := (hS1 i hiS).resolve_left hne
      exact ⟨a, haZ, hi.symm.trans ha⟩
    · exfalso
      rcases hold i hiS with h | h
      · rw [hi, Ideal.span_singleton_eq_top] at h
        exact (IsLocalRing.mem_maximalIdeal _).mp (hmaxk k hk) h
      · rw [hi, Ideal.span_singleton_le_iff_mem] at h
        exact hkP h
  choose! β hβZ hβspan using hβex
  have hcomap : (Ideal.span (T : Set (Y.presheaf.stalk x))).comap (RingHom.id _) =
      D.stalkIdeal x := by
    rw [Ideal.comap_id, hT]
  obtain ⟨Z, T', hZ, hKZ, hT'Z, hT'⟩ :=
    exists_isRegularSystemOfParameters_adapted_of_associated_rsop
    (RingHom.id (Y.presheaf.stalk x)) (D.stalkIdeal x) hDreg hZ₁ hTZ hcomap hK₁ext β
    (fun k hk hkP => hβZ k hk hkP) (fun k hk hkP => hβspan k hk hkP) (by
      intro k hk _ k' hk' _ hkk
      exact hZ₀ext.span_singleton_injOn (Finset.mem_coe.mpr (hK₁Z hk))
        (Finset.mem_coe.mpr (hK₁Z hk')) hkk)
  have hEst : (⨅ i, E i).stalkIdeal x = Ideal.span {∏ k ∈ K₁, k} := by
    rw [DatumTransform.stalkIdeal_iInf_fintype]
    exact hK₁
  exact _root_.Hironaka.Subscheme.hasOnlyNormalCrossingsWithAt_of_stalkIdeal_eq hZ hKZ hT'Z hEst
    hT'.symm

theorem Tower.esys_castAdd {X : Scheme.{u}} (T : Tower X) {α : ℕ} (E : Fin α → Subscheme X) (s : ℕ)
    (i : Fin α) : T.Esys E s (Fin.castAdd s i) = (T.pre s).strictTransform (E i) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have h : Fin.castAdd (s + 1) i = Fin.castSucc (Fin.castAdd s i) := Fin.ext rfl
    rw [h, esys_succ_castSucc, ih]
    show _ = (MonoidalSuccession.snoc (T.pre s) (T.B s)
      (T.monoidalTransformation s)).strictTransform (E i)
    rw [MonoidalSuccession.strictTransform_snoc]

theorem Standing.transformI_E_eq_iInf_esys [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    (hS : Standing N n ℜ P r T x₀) (s : ℕ) :
    ((T.pre s).transformI ℜ).E = ⨅ j, T.Esys P.E s j := by
  have := hS.ambient.1
  have hdatum : ((T.pre s).transformI ℜ).IsDatum := MonoidalSuccession.transformI_isDatum
    (T.pre s) hS.ambient.2.1 ℜ hS.isDatum (hS.permissible s).isPermissibleI
  have hred : (⨅ j, T.Esys P.E s j).IsReduced :=
    Subscheme.isReduced_iInf_of_isNonsingular _ fun j => hS.isNonsingular_esys s j
  have hpts : ((T.pre s).transformI ℜ).E.pts = (⨅ j, T.Esys P.E s j).pts := by
    rw [Tower.pts_transformI_E_eq_iUnion_esys ℜ P T s, Subscheme.pts_iInf]
  rw [Subscheme.eq_ofClosed_support _ hdatum.1, Subscheme.eq_ofClosed_support _ hred]
  congr 1
  exact TopologicalSpace.Closeds.ext hpts

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

/-- p. 309, open case: by [(2)] and Remark 1/Lemma (AB.5), "for `1 ≤ i ≤ α`, either `E_i(s)` does
not
contain `x` or it contains all the irreducible components of `W(s)` which contain `x`.  Since `W(s)`
contains `B_s`, either `E_i(s)` does not contain `x` or it contains `B_s`".  Ideal-level form at the
points `x = c̃(x̃)` of `B_s`. -/
theorem stalkIdeal_esys_castAdd_le_or_eq_top {s : ℕ} (hprep : PrepHyp N ℜ P r T x₀ s) {U : Set X}
    (hU : r = .opn U) {Bt : Subscheme (R.xTilde s)} (hBti : Bt.IsIrreducible)
    (hS3 : ∀ xt ∈ Bt.pts, (R.cTilde s).base xt ∈
      S ((T.pre s).transformI ℜ) (r.transformSucc (T.pre s)))
    (i : Fin P.α) {xt : R.xTilde s} (hxt : xt ∈ Bt.pts) :
    (T.Esys P.E s (Fin.castAdd s i)).stalkIdeal ((R.cTilde s).base xt) = ⊤ ∨
      (T.Esys P.E s (Fin.castAdd s i)).stalkIdeal ((R.cTilde s).base xt) ≤
        (Subscheme.ofClosed
          ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩).stalkIdeal
            ((R.cTilde s).base xt) := by
  classical
  by_cases hmem : (R.cTilde s).base xt ∈ (T.Esys P.E s (Fin.castAdd s i)).pts
  swap
  · exact Or.inl (Subscheme.stalkIdeal_eq_top_of_notMem_pts hmem)
  right
  set Bs : Subscheme (T.X s) :=
    Subscheme.ofClosed ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩ with hBs
  have hirrBt : IsIrreducible Bt.pts := Subscheme.isIrreducible_pts Bt hBti
  have hirrBs : IsIrreducible Bs.pts := by
    show IsIrreducible (closure _)
    exact (hirrBt.image _ (R.cTilde s).continuous.continuousOn).closure
  have hBsW : Bs.pts ⊆ ((T.pre s).transformI ℜ).W.pts := by
    show closure _ ⊆ _
    exact closure_minimal (Set.image_subset_iff.mpr fun xt' hx' => S_subset_pts_W (hS3 xt' hx'))
      (show IsClosed ((T.pre s).transformI ℜ).W.pts from
        ((T.pre s).transformI ℜ).W.support.isClosed)
  -- a component `W₁` of `W(s)` containing `B_s`
  set ξ := hirrBs.genericPoint with hξ
  have hξcl : closure {ξ} = Bs.pts := hirrBs.closure_genericPoint (show IsClosed Bs.pts from
    Bs.support.isClosed)
  have hξB : ξ ∈ Bs.pts := hξcl.le (subset_closure (Set.mem_singleton _))
  obtain ⟨W₁, hW₁, hξW₁⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_pts
    ((T.pre s).transformI ℜ).W (hBsW hξB)
  have hBsW₁ : Bs.pts ⊆ W₁.pts := by
    rw [← hξcl]
    exact closure_minimal (Set.singleton_subset_iff.mpr hξW₁)
      (show IsClosed W₁.pts from W₁.support.isClosed)
  have hxBs : (R.cTilde s).base xt ∈ Bs.pts := subset_closure ⟨xt, hxt, rfl⟩
  have hEi : T.Esys P.E s (Fin.castAdd s i) = (T.pre s).strictTransform (P.E i) :=
    Tower.esys_castAdd T P.E s i
  rw [hEi] at hmem ⊢
  rcases hprep.2.2.1 U hU W₁ hW₁ i with hc | hempty
  · have hpts : Bs.pts ⊆ ((T.pre s).strictTransform (P.E i)).pts :=
      hBsW₁.trans (pts_subset_of_isContainedIn hc)
    exact Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn
      (Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced _) hpts) _
  · exfalso
    have hmem3 : (R.cTilde s).base xt ∈ ((T.pre s).strictTransform (P.E i)).pts ∩ W₁.pts ∩
        S ((T.pre s).transformI ℜ) (r.transformSucc (T.pre s)) :=
      ⟨⟨hmem, hBsW₁ hxBs⟩, hS3 xt hxt⟩
    rw [hempty] at hmem3
    exact hmem3

end Frame.RemovalFamily

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

/-- Normal crossings of the seen exceptional divisors with `B_s` at `x = c̃(x̃)`, from those of
their
traces on `X̃` with `B̃` (p. 309, "the permissibility of `f_B̃` for `ℜ^{N-1}_II` implies …
Therefore, by the
above property of the homomorphism `S_s → Ŝ_s`, we can conclude").  Uses the descent of normal
crossings (`Subscheme.hasOnlyNormalCrossingsWithAt_iInf_of_totalTransform`), with `hinj` from the
transversality of the `Ê_j` to `X̄_s` (Remark 2) and the faithful flatness of `S_s → Ŝ_s`.

Generalized for the repair of the paper's error on the subschemes `Ẽ_j`: the index set is any finite type, and the
traces `Ed i` are only required to be non-singular divisors (not necessarily irreducible); the
case of traces equal to `X̃` is `hasOnlyNormalCrossingsWithAt_iInf_esys_of_traces_emptyIfBot`. -/
theorem hasOnlyNormalCrossingsWithAt_iInf_esys_of_traces [Hironaka.HironakaCitedResults.{u}] {s : ℕ} {ι : Type*} [Fintype ι]
    (σ : ι → Fin (P.α + s)) (Ed : ι → Subscheme (R.xTilde s))
    (hEd : ∀ i, Ed i = Subscheme.totalTransform (R.uBar s).ι
      (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.eHat s (σ i))))
    (hEdcod : ∀ i, (Ed i).IsNonsingularDivisor) (Bt : Subscheme (R.xTilde s))
    (hNCt : (⨅ i, Ed i).HasOnlyNormalCrossingsWith Bt)
    (hNCx : ∀ xt ∈ Bt.pts, (⨅ i, 𝒮.eHat s (σ i)).HasOnlyNormalCrossingsWithAt (𝒮.xBar s)
      ((𝒮.xBar s).ι.base ((R.uBar s).ι.base xt)))
    (Bs : Subscheme (T.X s))
    (hsimple : ∀ xt ∈ Bt.pts, Bs.IsSimpleAt ((R.cTilde s).base xt))
    (hcomap : ∀ xt ∈ Bt.pts, (Bt.stalkIdeal xt).comap ((R.cTilde s).stalkMap xt).hom =
      Bs.stalkIdeal ((R.cTilde s).base xt))
    (hover : ∀ xt ∈ Bt.pts,
      (𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base ((R.uBar s).ι.base xt)) = hS.xh) :
    ∀ xt ∈ Bt.pts, (⨅ i, T.Esys P.E s (σ i)).HasOnlyNormalCrossingsWithAt Bs
      ((R.cTilde s).base xt) := by
  classical
  intro xt hxt
  have hX : IsRegularLocalRing ((T.X s).presheaf.stalk ((R.cTilde s).base xt)) :=
    hS.isNonsingular_X s _
  have hX' : IsRegularLocalRing ((R.xTilde s).presheaf.stalk xt) := R.isNonsingular_xTilde s xt
  have hEdc : ∀ i, Subscheme.totalTransform (R.cTilde s) (T.Esys P.E s (σ i)) = Ed i := by
    intro i
    rw [hEd i]
    show Subscheme.totalTransform (R.cTilde s) (T.Esys P.E s (σ i)) =
      Subscheme.totalTransform (R.uBar s).ι (Subscheme.totalTransform (𝒮.xBar s).ι
        (Subscheme.totalTransform (𝒮.c s) (T.Esys P.E s (σ i))))
    rw [← Subscheme.totalTransform_comp, ← Subscheme.totalTransform_comp]
    rfl
  have hEsys := hS.esys_isNonsingularIrreducibleCodimOne_and_hasOnlyNormalCrossings s
  obtain ⟨Z₀, hZ₀, -, hE0⟩ := DatumTransform.exists_rsop_adapted_of_isDatum (B := ⊥)
    (T.Esys P.E s) (hS.isNonsingular_X s) hEsys.1 hEsys.2 (fun x _ => hEsys.2 x)
    ((R.cTilde s).base xt)
  obtain ⟨Zt, hZt, hTb, hEj⟩ :=
    DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt_of_isNonsingularDivisor Ed hEdcod
    (fun i => iInf_le _ i) (D := Bt) (hNCt xt hxt)
  refine Subscheme.hasOnlyNormalCrossingsWithAt_iInf_of_totalTransform (R.cTilde s) xt
    (fun i => T.Esys P.E s (σ i)) Bs Bt (hsimple xt hxt).2 (hcomap xt hxt)
    ⟨Z₀, hZ₀, fun i => hE0 (σ i)⟩
    ⟨Zt, hZt, hTb, fun i => by rw [hEdc i]; exact hEj i⟩ ?_
  intro i j hi hij
  rw [hEdc, hEdc] at hij
  set xb : (𝒮.xBar s).toScheme := (R.uBar s).ι.base xt with hxb
  set yh : 𝒮.tHat.X s := (𝒮.xBar s).ι.base xb with hyh
  have hxU : xb ∈ R.uBar s := xt.2
  have hreg : IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk yh) := 𝒮.isNonsingular_tHat_X s yh
  have hsimp : ∀ k, yh ∈ (𝒮.eHat s (σ k)).pts →
      (𝒮.eHat s (σ k)).IsSimpleAt yh ∧ (𝒮.eHat s (σ k)).codimAt yh = 1 := fun k hk =>
    𝒮.isSimpleAt_and_codimAt_eq_one_totalTransform_c s (hS.isNonsingular_esys s _)
      (hS.exists_stalkIdeal_esys s _) _ hk
  -- stalks of `Ed k` through the traces
  have hEdstalk : ∀ k, (Ed k).stalkIdeal xt =
      ((Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.eHat s (σ k))).stalkIdeal xb).map
        (FlatPreimm.stalkEquiv (R.uBar s).ι xt) := fun k => by
    rw [hEd k]
    exact FlatPreimm.stalkIdeal_totalTransform (R.uBar s).ι _ xt
  have hTrstalk : ∀ k, (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.eHat s (σ k))).stalkIdeal xb =
      ((𝒮.eHat s (σ k)).stalkIdeal yh).map ((𝒮.xBar s).ι.stalkMap xb).hom := fun k =>
    stalkIdeal_totalTransform _ _ _
  have hTbar : IsRegularLocalRing ((𝒮.xBar s).toScheme.presheaf.stalk xb) :=
    (R.isSimpleAt_and_isIrreducible_and_isNonsingCodimOneOn s).1 xb hxU
  have hZtext : ExtendsToRSOP _ Zt := ExtendsToRSOP.of_isRegularSystemOfParameters hZt
  have hTF : ∀ k, yh ∈ (𝒮.eHat s (σ k)).pts →
      ¬ (𝒮.eHat s (σ k)).stalkIdeal yh ≤ (𝒮.xBar s).stalkIdeal yh := by
    intro k hk hle
    have hmem : xt ∈ (Ed k).pts := by
      rw [hEd k]
      have hpt := FlatPreimm.pts_totalTransform (R.uBar s).ι
        (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.eHat s (σ k)))
      have h1 : (𝒮.xBar s).ι.base xb ∈ (𝒮.eHat s (σ k)).pts := hk
      have h2 := (Subscheme.mem_pts_totalTransform_subschemeι_iff (E := 𝒮.eHat s (σ k)) xb).mpr h1
      exact (Set.ext_iff.mp hpt xt).mpr h2
    have hne : (Ed k).stalkIdeal xt ≠ ⊤ := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hmem
    obtain ⟨β, hβZ, hβ⟩ := (hEj k).resolve_left hne
    have h0 : (Ed k).stalkIdeal xt = ⊥ := by
      rw [hEdstalk k, hTrstalk k]
      have h1 : ((𝒮.eHat s (σ k)).stalkIdeal yh).map ((𝒮.xBar s).ι.stalkMap xb).hom = ⊥ := by
        refine (Ideal.map_eq_bot_iff_le_ker _).mpr ?_
        refine hle.trans ?_
        rw [stalkIdeal_eq_ker_stalkMap (𝒮.xBar s) xb]
      rw [h1, Ideal.map_bot]
      rfl
    rw [h0] at hβ
    have : β = 0 := by
      have := hβ.symm
      rwa [Ideal.span_singleton_eq_bot] at this
    exact hZtext.ne_zero hβZ this
  obtain ⟨-, zb, K, hzb, hKzb, hKmem, hK0, hKst, -, hKinj⟩ :=
    Subscheme.exists_stalk_presentation_iInf_totalTransform_ι (E := fun k => 𝒮.eHat s (σ k))
      (D := 𝒮.xBar s)
      (Subscheme.isReduced_iInf_of_forall_isNonsingular _ fun k => 𝒮.isNonsingular_eHat s (σ k))
      xb
      (hNCx xt hxt) hsimp hTF
  have hzbext : ExtendsToRSOP _ zb := ExtendsToRSOP.of_isRegularSystemOfParameters hzb
  -- `i` passes through `ŷ`
  have hcy : (𝒮.c s).base yh = (R.cTilde s).base xt := rfl
  have hmem_i : yh ∈ (𝒮.eHat s (σ i)).pts := by
    have hx : (R.cTilde s).base xt ∈ (T.Esys P.E s (σ i)).pts :=
      Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr hi
    show yh ∈ (Subscheme.totalTransform (𝒮.c s) (T.Esys P.E s (σ i))).pts
    rw [Subscheme.pts_totalTransform_eq_preimage, Set.mem_preimage]
    exact hx
  obtain ⟨bi, hbiz, hKi⟩ := hKmem i hmem_i
  -- equal traces on `X̃`
  have hTr : (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.eHat s (σ i))).stalkIdeal xb =
      (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.eHat s (σ j))).stalkIdeal xb := by
    have h1 := hij
    rw [hEdstalk i, hEdstalk j] at h1
    have h2 := congrArg (Ideal.comap (FlatPreimm.stalkEquiv (R.uBar s).ι xt)) h1
    rwa [Ideal.comap_map_of_bijective _ (FlatPreimm.stalkEquiv (R.uBar s).ι xt).bijective,
      Ideal.comap_map_of_bijective _ (FlatPreimm.stalkEquiv (R.uBar s).ι xt).bijective] at h2
  have hKij : Ideal.span {∏ a ∈ K i, a} = Ideal.span {∏ a ∈ K j, a} := by
    rw [← hKst i, ← hKst j]; exact hTr
  rw [hKi, Finset.prod_singleton] at hKij
  have hmem_j : yh ∈ (𝒮.eHat s (σ j)).pts := by
    by_contra hnj
    rw [hK0 j hnj, Finset.prod_empty, Ideal.span_singleton_one] at hKij
    rw [Ideal.span_singleton_eq_top] at hKij
    exact (IsLocalRing.mem_maximalIdeal _).mp (hzbext.mem_maximalIdeal hbiz) hKij
  obtain ⟨bj, hbjz, hKj⟩ := hKmem j hmem_j
  rw [hKj, Finset.prod_singleton] at hKij
  have hbb : bi = bj := hzbext.span_singleton_injOn (Finset.mem_coe.mpr hbiz)
    (Finset.mem_coe.mpr hbjz) hKij
  have hKeq : K i = K j := by rw [hKi, hKj, hbb]
  have hÊ := hKinj i j hKeq
  -- faithful flatness of `S_s → Ŝ_s`
  have hflat := 𝒮.toCompletion.comap_map_stalkMap (hS.ambient.2.1 x₀) hS.isNonsingular_X
    hS.isNonsingular_B s yh (hover xt hxt)
  have hÊstalk : ∀ k, (𝒮.eHat s (σ k)).stalkIdeal yh =
      ((T.Esys P.E s (σ k)).stalkIdeal ((𝒮.c s).base yh)).map ((𝒮.c s).stalkMap yh).hom :=
    fun k => stalkIdeal_totalTransform _ _ _
  have e1 := hflat ((T.Esys P.E s (σ i)).stalkIdeal ((𝒮.c s).base yh))
  have e2 := hflat ((T.Esys P.E s (σ j)).stalkIdeal ((𝒮.c s).base yh))
  rw [← hÊstalk i] at e1
  rw [← hÊstalk j] at e2
  rw [hÊ] at e1
  exact e1.symm.trans e2

open Classical in
/-- **Normal crossings of the seen exceptional divisors with `B_s`, for the emptied traces**
(p. 309, as `hasOnlyNormalCrossingsWithAt_iInf_esys_of_traces`).  The traces `Ẽ_i` may be the whole
space `X̃` (this is the case `F = E_j` of the closed restriction: then `Ê_j(s) ⊇ X̄_s`);
`Ed i` is the trace, and the hypotheses are those of the emptied datum: `(Ed i).emptyIfBot` is a
non-singular
divisor and `⋃ (Ed i).emptyIfBot` has only normal crossings with `B̃`.

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the printed argument
("the permissibility of `f_B̃` for `ℜ^{N-1}_II` implies …") presupposes that all the traces
`Ẽ_j` are non-singular irreducible of codimension one.  Here the members with `Ed i ≠ ⊥` are treated
by `hasOnlyNormalCrossingsWithAt_iInf_esys_of_traces` (the kept traces form a sub-family, whose
normal crossings with `X̄_s` are inherited: `Subscheme.hasOnlyNormalCrossingsWithAt_iInf_comp`),
and the members with `Ed i = ⊥` satisfy `(E_j(s))_x ⊆ (B_s)_x`: their total transform to `X̃` is
zero, so their stalk lies in the kernel of the stalk map, which lies in `(B̃_x̃) ∩ O_{X_s,x} =
(B_s)_x`.  They are added by `Subscheme.hasOnlyNormalCrossingsWithAt_iInf_of_seen_of_old`. -/
theorem hasOnlyNormalCrossingsWithAt_iInf_esys_of_traces_emptyIfBot [Hironaka.HironakaCitedResults.{u}] {s : ℕ} {ι : Type*}
    [Fintype ι] (σ : ι → Fin (P.α + s)) (Ed : ι → Subscheme (R.xTilde s))
    (hEd : ∀ i, Ed i = Subscheme.totalTransform (R.uBar s).ι
      (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.eHat s (σ i))))
    (hEdcod : ∀ i, (Ed i).emptyIfBot.IsNonsingularDivisor) (Bt : Subscheme (R.xTilde s))
    (hNCt : (⨅ i, (Ed i).emptyIfBot).HasOnlyNormalCrossingsWith Bt)
    (hNCx : ∀ xt ∈ Bt.pts, (⨅ i, 𝒮.eHat s (σ i)).HasOnlyNormalCrossingsWithAt (𝒮.xBar s)
      ((𝒮.xBar s).ι.base ((R.uBar s).ι.base xt)))
    (Bs : Subscheme (T.X s))
    (hsimple : ∀ xt ∈ Bt.pts, Bs.IsSimpleAt ((R.cTilde s).base xt))
    (hcomap : ∀ xt ∈ Bt.pts, (Bt.stalkIdeal xt).comap ((R.cTilde s).stalkMap xt).hom =
      Bs.stalkIdeal ((R.cTilde s).base xt))
    (hover : ∀ xt ∈ Bt.pts,
      (𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base ((R.uBar s).ι.base xt)) = hS.xh) :
    ∀ xt ∈ Bt.pts, (⨅ i, T.Esys P.E s (σ i)).HasOnlyNormalCrossingsWithAt Bs
      ((R.cTilde s).base xt) := by
  intro xt hxt
  have hX : IsRegularLocalRing ((T.X s).presheaf.stalk ((R.cTilde s).base xt)) :=
    hS.isNonsingular_X s _
  have hEdc : ∀ i, Subscheme.totalTransform (R.cTilde s) (T.Esys P.E s (σ i)) = Ed i := by
    intro i
    rw [hEd i]
    show Subscheme.totalTransform (R.cTilde s) (T.Esys P.E s (σ i)) =
      Subscheme.totalTransform (R.uBar s).ι (Subscheme.totalTransform (𝒮.xBar s).ι
        (Subscheme.totalTransform (𝒮.c s) (T.Esys P.E s (σ i))))
    rw [← Subscheme.totalTransform_comp, ← Subscheme.totalTransform_comp]
    rfl
  -- the members with a trace other than the whole space
  have hNCx' : ∀ xt ∈ Bt.pts, (⨅ i : {i // Ed i ≠ ⊥}, 𝒮.eHat s (σ i.1)).HasOnlyNormalCrossingsWithAt
      (𝒮.xBar s) ((𝒮.xBar s).ι.base ((R.uBar s).ι.base xt)) := by
    intro xt' hxt'
    have : IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk
        ((𝒮.xBar s).ι.base ((R.uBar s).ι.base xt'))) := 𝒮.isNonsingular_tHat_X s _
    exact Subscheme.hasOnlyNormalCrossingsWithAt_iInf_comp (E := fun i => 𝒮.eHat s (σ i))
      (fun i : {i // Ed i ≠ ⊥} => i.1)
      (Subscheme.isReduced_iInf_of_forall_isNonsingular _ fun i => 𝒮.isNonsingular_eHat s (σ i))
      (hNCx xt' hxt') fun j hj => 𝒮.isSimpleAt_and_codimAt_eq_one_totalTransform_c s
        (hS.isNonsingular_esys s _) (hS.exists_stalkIdeal_esys s _) _ hj
  have hkept := R.hasOnlyNormalCrossingsWithAt_iInf_esys_of_traces
    (ι := {i // Ed i ≠ ⊥}) (fun i => σ i.1) (fun i => Ed i.1) (fun i => hEd i.1)
    (fun i => (Subscheme.eq_bot_or_isNonsingularDivisor_of_emptyIfBot (hEdcod i.1)).resolve_left
      i.2) Bt (by rw [← Subscheme.iInf_emptyIfBot_eq]; exact hNCt) hNCx' Bs hsimple hcomap hover
    xt hxt
  have hEsys := hS.esys_isNonsingularIrreducibleCodimOne_and_hasOnlyNormalCrossings s
  obtain ⟨Z₀, hZ₀, -, hE0⟩ := DatumTransform.exists_rsop_adapted_of_isDatum (B := ⊥)
    (T.Esys P.E s) (hS.isNonsingular_X s) hEsys.1 hEsys.2 (fun x _ => hEsys.2 x)
    ((R.cTilde s).base xt)
  obtain ⟨Z₁, hZ₁, hT₁, hE1⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    (fun i : {i // Ed i ≠ ⊥} => T.Esys P.E s (σ i.1)) (fun i => hEsys.1 _)
    (fun i => iInf_le _ i) (D := Bs) hkept
  refine Subscheme.hasOnlyNormalCrossingsWithAt_iInf_of_seen_of_old (fun i => T.Esys P.E s (σ i))
    {i | Ed i ≠ ⊥} Bs (hsimple xt hxt).2 ⟨Z₀, hZ₀, fun i => hE0 (σ i)⟩
    ⟨Z₁, hZ₁, hT₁, fun i hi => hE1 ⟨i, hi⟩⟩ (fun i hi => Or.inr ?_)
  -- the members with `Ed i = ⊥` contain `B_s`
  have hi' : Ed i = ⊥ := not_not.mp hi
  have h0 : ((T.Esys P.E s (σ i)).stalkIdeal ((R.cTilde s).base xt)).map
      ((R.cTilde s).stalkMap xt).hom = ⊥ := by
    rw [← stalkIdeal_totalTransform, hEdc i, hi', Subscheme.stalkIdeal_bot_eq]
  have hker := (Ideal.map_eq_bot_iff_le_ker _).mp h0
  rw [← hcomap xt hxt]
  intro a ha
  have := hker ha
  rw [RingHom.mem_ker] at this
  rw [Ideal.mem_comap, this]
  exact zero_mem _

end Frame.RemovalFamily

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

/-- **The normal crossings of `E(s)` with `B_s`** (p. 309, proof of Remark 4: "To show that
`⋃ E_i(s)` has only normal crossings with `B_s` at `x` we note that … the canonical homomorphism
`S_s → Ŝ_s` transforms a regular system of parameters of `S_s` into such a system … the
permissibility of `f_B̃` for `ℜ^{N-1}_II` implies that `⋃ c_s⁻¹(E_i(s))` has only normal crossings
with `B̃` at `x̂` … Therefore … `⋃ E_i(s)` has only normal crossings with `B_s` at `x`", and, in the
open
case, "the assumption [(2)] … for `1 ≤ i ≤ α`, either `E_i(s)` does not contain `x` or it contains
`B_s`").  Proved from the descent of normal
crossings `Hironaka/Compat/NormalCrossingsDescent.lean`; see
`hasOnlyNormalCrossingsWithAt_iInf_esys_of_traces`
and `Subscheme.hasOnlyNormalCrossingsWithAt_iInf_of_seen_of_old`.
Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the paper (p. 308)
"In both cases, we see that `Ẽ_1, ⋯, Ẽ_α̃` are non-singular irreducible subschemes of `X̄'_s` of
codimension 1, and that `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on `X̄'_s`" is false as printed:
the `Ẽ_j` need not be irreducible, and `Ẽ_i = X̃` if `F = E_i`.
The statement is made for the datum with the traces equal to `X̃` emptied
(`(R.datumII s a Jt).emptyIfBot`), which is a weak datum (`isWeakDatum_emptyIfBot_datumII`):
`hII` is `IsWeakDatum`, and `hJt`, `hperm` and the conclusions refer to the emptied datum.  The
irreducibility of the `Ẽ_j` is not used, and there is no hypothesis `hFE`.  For a resolution
datum nothing is emptied (`DatumII.Raw.IsDatum.emptyIfBot_eq`), which gives the printed
statements. -/
theorem hasOnlyNormalCrossingsWithAt_transformI_E_cTilde [Hironaka.HironakaCitedResults.{u}] {s : ℕ}
    (hprep : PrepHyp N ℜ P r T x₀ s) (a : Fin (𝒮.eTilde s).1 → ℕ) (Jt : Subscheme (R.xTilde s))
    (hJt : Jt * ∏ j, (((R.datumII s a Jt).emptyIfBot).E j) ^ (a j) = R.jBarT s)
    (hII : ((R.datumII s a Jt).emptyIfBot).IsWeakDatum) (Bt : Subscheme (R.xTilde s))
    (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : ((R.datumII s a Jt).emptyIfBot).IsPermissible Bt)
    (hsimple : ∀ xt ∈ Bt.pts, (Subscheme.ofClosed
      ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩).IsSimpleAt
        ((R.cTilde s).base xt))
    (hcomap : ∀ xt ∈ Bt.pts, (Bt.stalkIdeal xt).comap ((R.cTilde s).stalkMap xt).hom =
      (Subscheme.ofClosed ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩).stalkIdeal
        ((R.cTilde s).base xt)) :
    ∀ xt ∈ Bt.pts, ((T.pre s).transformI ℜ).E.HasOnlyNormalCrossingsWithAt
      (Subscheme.ofClosed ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩)
      ((R.cTilde s).base xt) := by
  classical
  have hsub : ∀ xt ∈ Bt.pts, xt ∈ ((R.datumII s a Jt).emptyIfBot).S := fun xt hx => (hperm.2.1 hx).1
  have hnu : ∀ xt ∈ Bt.pts, (𝒮.b : ℕ∞) ≤ Ideal.nu ((R.jBarT s).stalkIdeal xt) :=
    fun xt hx => R.le_nu_jBarT_of_mem_S a Jt hJt (hsub xt hx)
  have hS3 := fun xt (hx : xt ∈ Bt.pts) => R.cTilde_mem_S_and_composite_eq hprep (hnu xt hx)
  have hover : ∀ xt ∈ Bt.pts,
      (𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base ((R.uBar s).ι.base xt)) = hS.xh :=
    fun xt hx => R.gTilde_eq_xh hprep (hnu xt hx)
  have hNCx : ∀ xt ∈ Bt.pts,
      (⨅ i : Fin (bdryCard r P.α s), 𝒮.eHat s (bdryIdx r P.α s i)).HasOnlyNormalCrossingsWithAt
      (𝒮.xBar s) ((𝒮.xBar s).ι.base ((R.uBar s).ι.base xt)) := fun xt hx =>
    R.hasOnlyNormalCrossingsWithAt_iInf_eHat_bdry s (show (R.uBar s).ι.base xt ∈ R.uBar s from xt.2)
      (Subscheme.mem_pts_ι _ _)
  rw [hS.transformI_E_eq_iInf_esys s]
  have hEsys := hS.esys_isNonsingularIrreducibleCodimOne_and_hasOnlyNormalCrossings s
  cases r with
  | closed F =>
    exact R.hasOnlyNormalCrossingsWithAt_iInf_esys_of_traces_emptyIfBot (ι := Fin (P.α + s))
      (fun i => i) (R.datumII s a Jt).E (fun i => rfl) hII.2.1 Bt hperm.2.2 hNCx _ hsimple hcomap
      hover
  | opn U =>
    intro xt hxt
    have h1 := R.hasOnlyNormalCrossingsWithAt_iInf_esys_of_traces_emptyIfBot (ι := Fin s)
      (fun i => Fin.natAdd P.α i) (R.datumII s a Jt).E (fun i => rfl) hII.2.1 Bt hperm.2.2 hNCx _
      hsimple hcomap hover xt hxt
    have hX : IsRegularLocalRing ((T.X s).presheaf.stalk ((R.cTilde s).base xt)) :=
      hS.isNonsingular_X s _
    obtain ⟨Z₀, hZ₀, -, hE0⟩ := DatumTransform.exists_rsop_adapted_of_isDatum (B := ⊥)
      (T.Esys P.E s) (hS.isNonsingular_X s) hEsys.1 hEsys.2 (fun x _ => hEsys.2 x)
      ((R.cTilde s).base xt)
    obtain ⟨Z₁, hZ₁, hT₁, hE1⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
      (fun i : Fin s => T.Esys P.E s (Fin.natAdd P.α i)) (fun i => hEsys.1 _)
      (fun i => iInf_le _ i) (D := _) h1
    refine Subscheme.hasOnlyNormalCrossingsWithAt_iInf_of_seen_of_old (fun j => T.Esys P.E s j)
      {j | P.α ≤ j.val} _ (hsimple xt hxt).2 ⟨Z₀, hZ₀, hE0⟩ ⟨Z₁, hZ₁, hT₁, fun j hj => ?_⟩
      (fun j hj => ?_)
    · have hj' : P.α ≤ j.val := hj
      have hjs := j.2
      have : j = Fin.natAdd P.α (⟨j.val - P.α, by omega⟩ : Fin s) := Fin.ext (by simp; omega)
      rw [this]
      exact hE1 _
    · have hjα : j.val < P.α := by simpa using hj
      have : j = Fin.castAdd s (⟨j.val, hjα⟩ : Fin P.α) := Fin.ext rfl
      rw [this]
      exact R.stalkIdeal_esys_castAdd_le_or_eq_top hprep rfl hBti
        (fun xt' hx' => (hS3 xt' hx').1) _ hxt

end Frame.RemovalFamily

theorem stalkIdeal_ker_comp_eq_comap' {W Y : Scheme.{u}} (i : W ⟶ Y) [IsClosedImmersion i]
    (Bb : Subscheme W) {xb : W} (hxb : xb ∈ Bb.pts) :
    Subscheme.stalkIdeal (Bb.ι ≫ i).ker (i.base xb) =
      (Bb.stalkIdeal xb).comap (i.stalkMap xb).hom := by
  obtain ⟨b, rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts Bb hxb
  exact stalkIdeal_ker_comp_eq_comap i Bb b

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

/-- `B̃_{x̃} ∩ O_{X_s, x} = (B_s)_x` at the points of `B̃` (p. 309: the local rings of `B̃` and
`B_s`
agree, "`c_s` induces an open immersion `B̃ → B_s`"), from the identification of the stalk of
`c_s⁻¹(B_s)` (Corollary of Lemma (AB.3)) and the faithful flatness of `S_s → Ŝ_s`. -/
theorem comap_stalkIdeal_cTilde_eq {s : ℕ} (Bt : Subscheme (R.xTilde s)) (hBtred : Bt.IsReduced)
    (hg : ∀ xt ∈ Bt.pts, (R.gTilde s).base xt = hS.xh)
    (hker : ∀ xh ∈ R.U s, (Subscheme.totalTransform (𝒮.c s) (Subscheme.ofClosed
        ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩)).stalkIdeal xh =
      Subscheme.stalkIdeal ((R.bb s Bt).ι ≫ (𝒮.xBar s).ι).ker xh)
    {xt : R.xTilde s} (hxt : xt ∈ Bt.pts) :
    (Bt.stalkIdeal xt).comap ((R.cTilde s).stalkMap xt).hom =
      (Subscheme.ofClosed ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩).stalkIdeal
        ((R.cTilde s).base xt) := by
  classical
  set Bs : Subscheme (T.X s) :=
    Subscheme.ofClosed ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩ with hBs
  set xb : (𝒮.xBar s).toScheme := (R.uBar s).ι.base xt with hxb
  set yh : 𝒮.tHat.X s := (𝒮.xBar s).ι.base xb with hyh
  have hxbB : xb ∈ (R.bb s Bt).pts := by
    rw [R.pts_bb]; exact subset_closure ⟨xt, hxt, rfl⟩
  have hyU : yh ∈ (R.U s : Set (𝒮.tHat.X s)) := xt.2
  -- the three comaps
  let xt' : (R.uBar s : Scheme.{u}) := xt
  have h1 : (Bt.stalkIdeal xt).comap ((R.uBar s).ι.stalkMap xt').hom =
      (R.bb s Bt).stalkIdeal xb := by
    rw [R.stalkIdeal_eq_map_bb s Bt hBtred xt]
    exact Ideal.comap_map_of_bijective _ (FlatPreimm.stalkEquiv (R.uBar s).ι xt).bijective
  have h2 : ((R.bb s Bt).stalkIdeal xb).comap ((𝒮.xBar s).ι.stalkMap xb).hom =
      (Subscheme.totalTransform (𝒮.c s) Bs).stalkIdeal yh := by
    rw [hker yh hyU]
    exact (stalkIdeal_ker_comp_eq_comap' (𝒮.xBar s).ι (R.bb s Bt) hxbB).symm
  have hflat := 𝒮.toCompletion.comap_map_stalkMap (hS.ambient.2.1 x₀) hS.isNonsingular_X
    hS.isNonsingular_B s yh (hg xt hxt)
  have h3 : ((Subscheme.totalTransform (𝒮.c s) Bs).stalkIdeal yh).comap
      ((𝒮.c s).stalkMap yh).hom = Bs.stalkIdeal ((𝒮.c s).base yh) := by
    rw [stalkIdeal_totalTransform]
    exact hflat _
  have hc : (R.cTilde s).stalkMap xt =
      ((𝒮.c s).stalkMap yh ≫ (𝒮.xBar s).ι.stalkMap xb) ≫ (R.uBar s).ι.stalkMap xt' := by
    have h1' := Scheme.Hom.stalkMap_comp (R.uBar s).ι (𝒮.cBar s) xt'
    have h2' := Scheme.Hom.stalkMap_comp (𝒮.xBar s).ι (𝒮.c s) xb
    exact h1'.trans (congrArg (· ≫ (R.uBar s).ι.stalkMap xt') h2')
  have hfin : (Bt.stalkIdeal xt).comap ((R.cTilde s).stalkMap xt).hom =
      (((Bt.stalkIdeal xt).comap ((R.uBar s).ι.stalkMap xt').hom).comap
        ((𝒮.xBar s).ι.stalkMap xb).hom).comap ((𝒮.c s).stalkMap yh).hom := by
    rw [hc]
    simp only [Ideal.comap_comap]
    rfl
  rw [hfin, h1, h2, h3]
  rfl

end Frame.RemovalFamily

theorem isDatum_extendBy_of_isContainedIn {Y : Scheme.{u}} {ℜ' : DatumI.Raw Y} (hℜ : ℜ'.IsDatum)
    {B : Subscheme Y} (hB : B.IsReduced) (hBW : B.IsContainedIn ℜ'.W) :
    (ℜ'.extendBy B).IsDatum := by
  obtain ⟨hE1, hE2, hE3, hW1, hWV⟩ := hℜ
  refine ⟨hE1, hE2, hE3, hB, fun j => ?_⟩
  induction j using Fin.lastCases with
  | last =>
    simpa only [DatumI.Raw.extendBy, Fin.snoc_last] using hBW
  | cast i =>
    simp only [DatumI.Raw.extendBy, Fin.snoc_castSucc]
    exact fun U => (hWV i U).trans (hBW U)

theorem isPermissible_of_isPermissible_extendBy {Y : Scheme.{u}} {ℜ' : DatumI.Raw Y}
    {B C : Subscheme Y} (h : (ℜ'.extendBy B).IsPermissible C) : ℜ'.IsPermissible C := by
  obtain ⟨hC, ⟨hE1, hE2, hE3, hW1, hWV⟩, hres⟩ := h
  refine ⟨hC, ⟨hE1, hE2, hE3, hW1, fun j => ?_⟩, fun x hx => ?_⟩
  · have := hWV j.castSucc
    have e : (Fin.snoc (α := fun _ => Subscheme Y) (Fin.snoc (α := fun _ => Subscheme Y) ℜ'.V ℜ'.W)
        B j.castSucc : Subscheme Y) = Fin.snoc (α := fun _ => Subscheme Y) ℜ'.V ℜ'.W j :=
      Fin.snoc_castSucc _ _ _
    show C.IsContainedIn (Fin.snoc (α := fun _ => Subscheme Y) ℜ'.V ℜ'.W j)
    rw [← e]
    exact this
  · obtain ⟨hs, hnf, hnc⟩ := hres x hx
    refine ⟨hs, fun j => ?_, hnc⟩
    have := hnf j.castSucc
    have e : (Fin.snoc (α := fun _ => Subscheme Y) (Fin.snoc (α := fun _ => Subscheme Y) ℜ'.V ℜ'.W)
        B j.castSucc : Subscheme Y) = Fin.snoc (α := fun _ => Subscheme Y) ℜ'.V ℜ'.W j :=
      Fin.snoc_castSucc _ _ _
    show Subscheme.IsNormallyFlatAlongAt' (Fin.snoc (α := fun _ => Subscheme Y) ℜ'.V ℜ'.W j) C x
    rw [← e]
    exact this

section ClopenFibre

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X}

/-- Remark 3 (p. 309): "`S(ℜ(s)) ∩ g_s⁻¹(x_0)` … is by the assumption [(1)] a closed and open subset
of
`S(ℜ(s))`".  The image `g_s(S(ℜ(s)))` is a finite set of points at which `X` has dimension `N`
([(1)]); two points of it are never comparable under specialization (a proper generization has
smaller dimension), so it is a finite discrete space, and `{p | g_s(p) = x_0}` is the preimage of a
point.

Gap filled: the paper says only "by the assumption [(1)]". -/
theorem isClopen_composite_eq_x₀ {s : ℕ} (hprep : PrepHyp N ℜ P r T x₀ s) :
    IsClopen {p : S ((T.pre s).transformI ℜ) (r.transformSucc (T.pre s)) |
      (T.pre s).composite.base p = x₀} := by
  classical
  set Y : Set X := (T.pre s).composite.base ''
    S ((T.pre s).transformI ℜ) (r.transformSucc (T.pre s)) with hY
  have : Finite Y := hprep.1.to_subtype
  have hT1 : T1Space Y := by
    rw [t1Space_iff_specializes_imp_eq]
    intro p q hpq
    apply Subtype.ext
    have hsp : (p : X) ⤳ (q : X) := Topology.IsInducing.subtypeVal.specializes_iff.mpr hpq
    exact eq_of_specializes_of_dimAt_eq' hsp (hprep.2.1 _ p.2) (hprep.2.1 _ q.2)
  have : DiscreteTopology Y := inferInstance
  let g : S ((T.pre s).transformI ℜ) (r.transformSucc (T.pre s)) → Y := fun p =>
    ⟨(T.pre s).composite.base p, ⟨p, p.2, rfl⟩⟩
  have hg : Continuous g :=
    Continuous.subtype_mk ((T.pre s).composite.continuous.comp continuous_subtype_val) _
  have : {p : S ((T.pre s).transformI ℜ) (r.transformSucc (T.pre s)) |
      (T.pre s).composite.base p = x₀} = g ⁻¹' {⟨x₀, hprep.2.2.2⟩} := by
    ext p
    simp [g, Subtype.ext_iff]
  rw [this]
  exact (isClopen_discrete _).preimage hg

end ClopenFibre

/-- The restriction of a closed subscheme `D` of `Y` to the open subscheme `Y'` (its total transform
`j⁻¹(D)`) is an open subscheme of `D`: the base change of the open immersion `j`. -/
theorem exists_isOpenImmersion_totalTransform {Y' Y : Scheme.{u}} (j : Y' ⟶ Y) [IsOpenImmersion j]
    (D : Subscheme Y) :
    ∃ φ : (Subscheme.totalTransform j D).toScheme ⟶ D.toScheme, IsOpenImmersion φ ∧
      φ ≫ D.ι = (Subscheme.totalTransform j D).ι ≫ j := by
  let e' : (Subscheme.totalTransform j D).toScheme ≅ pullback j D.ι :=
    Scheme.IdealSheafData.comapIso D j
  have h1 : e'.hom ≫ pullback.fst j D.ι = (Subscheme.totalTransform j D).ι :=
    Scheme.IdealSheafData.comapIso_hom_fst D j
  refine ⟨e'.hom ≫ pullback.snd j D.ι, inferInstance, ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, h1]

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

/-- Remark 3 (p. 309): "by Corollary of Lemma (AB. 3), `c_s` induces an open immersion of `B̃` into
a
reduced irreducible subscheme `B_s` of `X_s`, where `B_s` is obtained as the closure of `c_s(B̃)`".

Proved.  \textbf{Deviation from the paper (gap filled).} The paper says only "by Corollary of Lemma
(AB.3)": the closure `B̄` of `B̃` in `X̂_s` has `ĝ_s(B̄) = x̂_0`, so `B̄ ≃ B_s` through `c_s`
(`Frame.exists_iso_totalTransform_of_pts_eq`); `B̃` is the open subscheme of the closure `B̄` of its
image in
`X̄_s` over `Ū_s` (the base change of the open immersion `Ū_s → X̄_s`,
`exists_isOpenImmersion_totalTransform`; here `B̃` reduced is used, `totalTransform_bb`), and `B̄ ⊆
X̄_s` is
identified with the reduced closure in `X̂_s` through the closed immersion `X̄_s → X̂_s`. -/
theorem exists_isOpenImmersion_cTilde {s : ℕ} (Bt : Subscheme (R.xTilde s))
    (hBtred : Bt.IsReduced) (hBti : Bt.IsIrreducible)
    (hg : ∀ xt ∈ Bt.pts, (R.gTilde s).base xt = hS.xh) :
    let Bs : Subscheme (T.X s) :=
      Subscheme.ofClosed ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩
    ∃ φ : Bt.toScheme ⟶ Bs.toScheme, IsOpenImmersion φ ∧ φ ≫ Bs.ι = Bt.ι ≫ R.cTilde s := by
  intro Bs
  classical
  have hirrBt : IsIrreducible Bt.pts := Subscheme.isIrreducible_pts Bt hBti
  set A : Set (𝒮.xBar s).toScheme := (R.uBar s).ι.base '' Bt.pts with hA
  have hAg : ((𝒮.xBar s).ι ≫ (𝒮.tHat.pre s).composite).base '' A = {hS.xh} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · obtain ⟨xt, hxt⟩ := hirrBt.nonempty
      exact ⟨(R.uBar s).ι.base xt, ⟨xt, hxt, rfl⟩, hg xt hxt⟩
    · rintro _ ⟨_, ⟨xt, hxt, rfl⟩, rfl⟩
      exact hg xt hxt
  have hBbpts : (R.bb s Bt).pts = closure A := R.pts_bb s Bt
  have hBbred : (R.bb s Bt).IsReduced := Subscheme.ofClosed_isReduced _
  let K : Subscheme (𝒮.tHat.X s) := ((R.bb s Bt).ι ≫ (𝒮.xBar s).ι).ker
  obtain ⟨e₀, he₀⟩ := Subscheme.exists_iso_ker ((R.bb s Bt).ι ≫ (𝒮.xBar s).ι)
  have hKred : Subscheme.IsReduced K := by
    have : IsReduced (R.bb s Bt).toScheme := hBbred
    exact isReduced_of_isOpenImmersion e₀.hom
  have hKpts : Subscheme.pts K = closure ((𝒮.xBar s).ι.base '' A) := by
    have h1 : Subscheme.pts K = Set.range (Subscheme.ι K).base :=
      (Scheme.IdealSheafData.range_subschemeι (I := K)).symm
    have h2 : Set.range (Subscheme.ι K).base =
        Set.range (e₀.hom ≫ (R.bb s Bt).ι ≫ (𝒮.xBar s).ι).base := by
      rw [he₀]
    have hsurj : Function.Surjective e₀.hom.base := e₀.hom.homeomorph.surjective
    rw [h1, h2, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq,
      Set.image_univ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      show Set.range (R.bb s Bt).ι.base = (R.bb s Bt).pts from
        Scheme.IdealSheafData.range_subschemeι (I := R.bb s Bt), hBbpts]
    exact ((𝒮.xBar s).ι.isClosedEmbedding.closure_image_eq A).symm
  have h2 := 𝒮.exists_iso_totalTransform_of_pts_eq A hAg K hKred hKpts
  have hcc : (𝒮.cBar s).base '' A = (R.cTilde s).base '' Bt.pts := by
    ext y
    constructor
    · rintro ⟨_, ⟨xt, hxt, rfl⟩, rfl⟩
      exact ⟨xt, hxt, rfl⟩
    · rintro ⟨xt, hxt, rfl⟩
      exact ⟨_, ⟨xt, hxt, rfl⟩, rfl⟩
  rw [hcc] at h2
  obtain ⟨e, he, -⟩ := h2
  have h1 := exists_isOpenImmersion_totalTransform (R.uBar s).ι (R.bb s Bt)
  rw [R.totalTransform_bb s Bt hBtred] at h1
  obtain ⟨φ₁, hφ₁, hφ₁c⟩ := h1
  let e₁ : (R.bb s Bt).toScheme ≅ Bs.toScheme := e₀.symm ≪≫ e
  have h3 : IsOpenImmersion e₁.hom := inferInstance
  refine ⟨φ₁ ≫ e₁.hom, @IsOpenImmersion.comp _ _ _ _ _ hφ₁ h3, ?_⟩
  have hinv : e₀.inv ≫ Subscheme.ι K = (R.bb s Bt).ι ≫ (𝒮.xBar s).ι := by
    show e₀.inv ≫ Scheme.IdealSheafData.subschemeι (((R.bb s Bt).ι ≫ (𝒮.xBar s).ι).ker) = _
    rw [← he₀]
    simp
  show (φ₁ ≫ e₀.symm.hom ≫ e.hom) ≫ Bs.ι = Bt.ι ≫ (R.uBar s).ι ≫ (𝒮.xBar s).ι ≫ 𝒮.c s
  rw [Category.assoc, Category.assoc, he, Iso.symm_hom, ← Category.assoc e₀.inv, hinv,
    ← Category.assoc, ← Category.assoc, hφ₁c]
  rfl

end Frame.RemovalFamily

/-- **Remark 3** (pp. 308–309) for an arbitrary open family with removals; the printed Remark 3
is the instance `U_s = X̂'_s` (`Frame.mem_S_iff_le_nu_and_exists_isOpenImmersion_of_prepHyp`,
see there for the paper's words and the deviations).  The paper's argument applies with
`lem:IV.AB-5-generic` in place of Lemma (AB.5).

Proved.  \textbf{Deviation from the paper (gap
filled).} (a) "or, equivalently, `ν_x̃(J̄(s)) ≥ b`": `mem_S_of_le_nu_jBarT`, `le_nu_jBarT_of_mem_S`
(additivity of `ν` on products in the regular local ring `O_{X̃,x̃}`; the `Ẽ_j` have order one at
their
points).  (b) the inclusion `c_s(S(ℜ^{N-1}_II)) ⊆ S(ℜ(s)) ∩ g_s⁻¹(x_0)`:
`cTilde_mem_S_and_composite_eq`
(Lemma (AB.5), Remark 1, [(1)]; `g_s(x')` is a generization of `x_0` of the same dimension `N`,
hence `x_0`).
(c) the closed and open subset: `isClopen_composite_eq_x₀` (the finite image consists of pairwise
incomparable points, hence is discrete).  (d) `g̃(B̃) = x̂_0`: `gTilde_eq_xh`.

\textbf{Statement modified (transcription).} The last assertion has the extra hypothesis
`Bt.IsReduced`: the paper's "irreducible subscheme" B̃ (p. 309) is reduced, as the open immersion
into the reduced `B_s` requires (an open immersion into a reduced scheme has reduced source).
Without it the statement is false: `Bt = Spec(O_{X̃,x̂_0}/m²)` (irreducible, one point of
`S(ℜ_II)`, not reduced) admits no open immersion into the reduced `Bs`.
Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the paper (p. 308)
"In both cases, we see that `Ẽ_1, ⋯, Ẽ_α̃` are non-singular irreducible subschemes of `X̄'_s` of
codimension 1, and that `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on `X̄'_s`" is false as printed:
the `Ẽ_j` need not be irreducible, and `Ẽ_i = X̃` if `F = E_i`.
The statement is made for the datum with the traces equal to `X̃` emptied
(`(R.datumII s a Jt).emptyIfBot`), which is a weak datum (`isWeakDatum_emptyIfBot_datumII`):
`hII` is `IsWeakDatum`, and `hJt`, `hperm` and the conclusions refer to the emptied datum.  The
irreducibility of the `Ẽ_j` is not used, and there is no hypothesis `hFE`.  For a resolution
datum nothing is emptied (`DatumII.Raw.IsDatum.emptyIfBot_eq`), which gives the printed
statements.

The dimension hypothesis `dim X̃ = N - 1` of the printed statement is not used by the proof and
is dropped in this generic statement (it is not derivable from the data alone,
`lem:IV.3-xtilde-ambient`). -/
@[blueprint "rem:IV.3-3-generic"
  (statement := /-- Notation as in \cref{rem:IV.3-3}, for an arbitrary open family with
    removals $U_s\subseteq\hat X_s$ (\cref{lem:IV.3-construction-facts-generic}), with
    $\tilde X=\bar U_s=U_s\cap\bar X_s$ in place of $\bar X_s'$: the assertions of
    \cref{rem:IV.3-3} hold. (Formalization note: the printed Remark~3 is the instance
    $U_s=\hat X_s'$; the corrected construction of \cref{def:IV.3-construction-componentwise}
    is the instance $U_s=\hat X_s^{*\prime}$.)

    \textbf{Statement modified (transcription).} The subscheme $\tilde B$ is assumed reduced (the
    paper's ``irreducible subscheme'' $\tilde B$ is reduced, as the open immersion into the reduced
    $B_s$ requires). Without this the statement is false: $\tilde B=\operatorname{Spec}
    (\mathcal O_{\tilde X,\hat x_0}/\mathfrak m^2)$ is irreducible, lies in
    $S(\mathfrak R^{N-1}_{\mathrm{II}})$ and is not reduced.

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$).} The
    datum $\mathfrak R^{N-1}_{\mathrm{II}}$ is not a resolution datum: the printed sentence
    (p.~308) ``In both cases, we see that $\tilde E_1,\dots,\tilde E_{\tilde\alpha}$ are
    non-singular irreducible subschemes of $\bar X_s'$ of codimension 1, and that $\tilde
    E_1\cup\dots\cup\tilde E_{\tilde\alpha}$ has only normal crossings on $\bar X_s'$'' is false
    (the $\tilde E_j$ can be reducible, and $\tilde E_i=\tilde X$ if $F=E_i$). The statement is made for the datum $\mathfrak R^{N-1,e}_{\mathrm{II}}$ whose
    entries equal to $\tilde X$ are emptied, which is a weak datum (\cref{rem:IV.3-2-repaired}):
    the hypotheses ``is a resolution datum'', $\tilde J\prod\tilde P_j^{a_j}=\bar J(s)$,
    ``$f_{\tilde B}$ permissible'' and the conclusions refer to it. For a resolution datum nothing
    is emptied, which gives the printed statement. -/)
  (proof := /-- The proof of \cref{rem:IV.3-3}, with \cref{lem:IV.AB-5-generic} in place of
    Lemma (AB.5).

    In Lean: $\bar J(s)=\tilde J\prod_j\tilde P_j^{a_j}$ and orders of ideals are additive on
    products in
    the regular local ring $\mathcal O_{\tilde X,\tilde x}$ ($\mathrm{gr}$ is a domain), the
    $\tilde P_j$ having order one at their points; so $\sum_{\tilde x\in\tilde E_i}a_i+\nu(\tilde
    J)=
    \nu(\bar J(s))$. If $\nu_{\tilde x}(\bar J(s))\ge b$ then $c_s(\tilde x)\in S(\mathfrak R(s))$
    by
    \cref{lem:IV.AB-5-generic} and Remark~1, and $g_s(c_s(\tilde x))$ is a generization of $x_0$ at
    which $X$
    has dimension $N$, like $x_0$ itself, hence equals $x_0$. The finite set $g_s(S(\mathfrak
    R(s)))$ of points of
    dimension $N$ has no two comparable points, so it is discrete and $S(\mathfrak R(s))\cap
    g_s^{-1}(x_0)$ is
    clopen. The points of a reduced irreducible $\tilde B\subseteq S(\mathfrak
    R^{N-1}_{\mathrm{II}})$ lie
    over $x_0$, hence over $\hat x_0$ (the fibre of $c_0$ over $x_0$), and the closure $\bar B$ of
    $\tilde B$ in
    $\hat X_s$ satisfies $\hat g_s(\bar B)=\hat x_0$; the Corollary of Lemma (AB.3) gives the
    reduced
    $B_s$ with $c_s\colon\bar B\simeq B_s$, whence the open immersion $\tilde B=\bar B\cap\hat
    X_s'\to B_s$.

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$).} The
    orders of ideals are additive on $\tilde J\prod_j(\tilde P^e_j)^{a_j}$ because the kept
    $\tilde E_j$ are non-singular divisors (order one at their points) and the emptied ones are
    units; irreducibility of the $\tilde E_j$ is not used. In the descent of normal crossings the
    members $k$ of a regular system of parameters of $\mathcal O_{X_s,x}$ outside $B_{s,x}$ have
    non-zero image, so their traces are kept; the others (the emptied traces, $E_j(s)=F(s)\supseteq
    B_s$) are old and are added by the case ``seen or old''. See
    \cref{rem:IV.3-2-repaired}. -/)
  (proofUses := ["lem:IV.AB-5-generic", "rem:IV.3-1", "cor:IV.AB-3"])
  (latexEnv := "remark")]
theorem Frame.RemovalFamily.mem_S_iff_le_nu_and_exists_isOpenImmersion_of_prepHyp [Hironaka.HironakaCitedResults.{u}] {N n : ℕ}
    {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
    {𝒮 : Frame hS} (R : 𝒮.RemovalFamily) (s : ℕ) (hprep : PrepHyp N ℜ P r T x₀ s)
    (a : Fin (𝒮.eTilde s).1 → ℕ) (Jt : Subscheme (R.xTilde s))
    (hJt : Jt * ∏ j, (((R.datumII s a Jt).emptyIfBot).E j) ^ (a j) = R.jBarT s)
    (hII : ((R.datumII s a Jt).emptyIfBot).IsWeakDatum) :
    (∀ xt : R.xTilde s, xt ∈ ((R.datumII s a Jt).emptyIfBot).S ↔
      (𝒮.b : ℕ∞) ≤ Ideal.nu ((R.jBarT s).stalkIdeal xt)) ∧
    (R.cTilde s).base '' ((R.datumII s a Jt).emptyIfBot).S ⊆
      S ((T.pre s).transformI ℜ) (r.transformSucc (T.pre s)) ∩
        (T.pre s).composite.base ⁻¹' {x₀} ∧
    IsClopen {p : S ((T.pre s).transformI ℜ) (r.transformSucc (T.pre s)) |
      (T.pre s).composite.base p = x₀} ∧
    ∀ Bt : Subscheme (R.xTilde s), Bt.IsIrreducible → Bt.IsReduced →
      Bt.pts ⊆ ((R.datumII s a Jt).emptyIfBot).S →
      (R.gTilde s).base '' Bt.pts = {hS.xh} ∧
      let Bs : Subscheme (T.X s) :=
        Subscheme.ofClosed ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩
      Bs.IsReduced ∧ Bs.IsIrreducible ∧
        ∃ φ : Bt.toScheme ⟶ Bs.toScheme, IsOpenImmersion φ ∧ φ ≫ Bs.ι = Bt.ι ≫ R.cTilde s := by
  have hiff : ∀ xt : R.xTilde s, xt ∈ ((R.datumII s a Jt).emptyIfBot).S ↔
      (𝒮.b : ℕ∞) ≤ Ideal.nu ((R.jBarT s).stalkIdeal xt) := fun xt =>
    ⟨fun h => R.le_nu_jBarT_of_mem_S a Jt hJt h, fun h => R.mem_S_of_le_nu_jBarT a Jt hJt hII h⟩
  refine ⟨hiff, ?_, isClopen_composite_eq_x₀ hprep, ?_⟩
  · rintro _ ⟨xt, hxt, rfl⟩
    exact R.cTilde_mem_S_and_composite_eq hprep ((hiff xt).mp hxt)
  · intro Bt hBti hBtred hsub
    have hirrBt : IsIrreducible Bt.pts := Subscheme.isIrreducible_pts Bt hBti
    have hg : ∀ xt ∈ Bt.pts, (R.gTilde s).base xt = hS.xh :=
      fun xt hx => R.gTilde_eq_xh hprep ((hiff xt).mp (hsub hx))
    refine ⟨?_, Subscheme.ofClosed_isReduced _, ?_,
      R.exists_isOpenImmersion_cTilde Bt hBtred hBti hg⟩
    · refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
      · obtain ⟨xt, hxt⟩ := hirrBt.nonempty
        exact ⟨xt, hxt, hg xt hxt⟩
      · rintro _ ⟨xt, hxt, rfl⟩
        exact hg xt hxt
    · refine Subscheme.isIrreducible_of_pts _ ?_
      show IsIrreducible (closure _)
      exact (hirrBt.image _ (R.cTilde s).continuous.continuousOn).closure

/-- **Remark 4** (p. 309) for an arbitrary open family with removals; the printed Remark 4 is
the instance `U_s = X̂'_s` (`Frame.isContainedIn_W_and_resolvedAt_extendBy_of_isPermissible`,
see there).  The paper's argument applies with `lem:IV.AB-5-generic`, `lem:IV.AB-6-generic` in
place of Lemmas (AB.5), (AB.6).

\textbf{Deviation from the paper (gap filled), normal crossings.} "the canonical homomorphism
`S_s → Ŝ_s` transforms a regular system of parameters into such a system … Therefore, by the above
property
of the homomorphism, we can conclude": in Lean this is the descent of normal crossings from `X̃` to
`X_s` (`hasOnlyNormalCrossingsWithAt_transformI_E_cTilde`): the stalk map `O_{X_s,x} → O_{X̃,x̃}` is
a
local homomorphism of regular local rings with `(B̃_{x̃}) ∩ O_{X_s,x} = (B_s)_x`
(`comap_stalkIdeal_cTilde_eq`), the generators of the `E_j(s)` through `x` have images generating
the
stalks of the `Ẽ_j` (adapted to `B̃` by the permissibility of `f_B̃`), and two different generators
do not
become associated because the `Ê_j(s)` are transversal to `X̄_s` (Remark 2) and `S_s → Ŝ_s` is
faithfully
flat (`Compat/NormalCrossingsDescent.lean`,
`Subscheme.hasOnlyNormalCrossingsWithAt_iInf_of_totalTransform`).
In the open case the `E_i(s)`, `i ≤ α`, are `(1)` or contain `B_s` at `x` by [(2)]
(`stalkIdeal_esys_castAdd_le_or_eq_top`) and are added by
`Subscheme.hasOnlyNormalCrossingsWithAt_iInf_of_seen_of_old`.

\textbf{Deviation from the paper (gap filled).} (1) "By Lemma (AB.6)": the paper does not derive the
hypothesis `J̄(s)_x̂ ⊆ P(B̃)^b` of (AB.6) from the permissibility of `f_B̃`; here it follows from
`B̃ ⊆ S(ℜ^{N-1}_II)` at the generic point of `B̃` (`stalkIdeal_jBarT_le_pow`: orders of ideals are
additive on products, the powers of `P` are `P`-primary).  (2) `B̃ ⊆ S(ℜ^{N-1}_II)`, `g̃(B̃) = x̂_0`
and
`c_s(B̃) ⊆ S(ℜ(s)) ∩ g_s⁻¹(x_0)` are those of Remark 3 (`cTilde_mem_S_and_composite_eq`,
`gTilde_eq_xh`).  (3) "the set of points of `B_s` at which `ℜ^{N,n'}_I(s)` is resolved is open and
contains `c_s(B̃)`": openness is Lemma 1 of § 1 (`DatumI.Raw.exists_isOpen_resolvedSet`); it is
dense
because `B_s` is irreducible and the set is a non-empty open subset of it.  The codimension
hypothesis
The codimension
hypothesis `hFE` of Remark 2 is not needed: the traces equal to `X̃` (`F = E_i`) are emptied and
treated as the old components `E_i(s) ⊇ B_s`
(`hasOnlyNormalCrossingsWithAt_iInf_esys_of_traces_emptyIfBot`).
Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the paper (p. 308)
"In both cases, we see that `Ẽ_1, ⋯, Ẽ_α̃` are non-singular irreducible subschemes of `X̄'_s` of
codimension 1, and that `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on `X̄'_s`" is false as printed:
the `Ẽ_j` need not be irreducible, and `Ẽ_i = X̃` if `F = E_i`.
The statement is made for the datum with the traces equal to `X̃` emptied
(`(R.datumII s a Jt).emptyIfBot`), which is a weak datum (`isWeakDatum_emptyIfBot_datumII`):
`hII` is `IsWeakDatum`, and `hJt`, `hperm` and the conclusions refer to the emptied datum.  The
irreducibility of the `Ẽ_j` is not used, and there is no hypothesis `hFE`.  For a resolution
datum nothing is emptied (`DatumII.Raw.IsDatum.emptyIfBot_eq`), which gives the printed
statements.

The dimension hypothesis `dim X̃ = N - 1` of the printed statement is not used by the proof and
is dropped in this generic statement (it is not derivable from the data alone,
`lem:IV.3-xtilde-ambient`). -/
@[blueprint "rem:IV.3-4-generic"
  (statement := /-- Notation as in \cref{rem:IV.3-4}, for an arbitrary open family with
    removals $U_s\subseteq\hat X_s$, with $\tilde X=\bar U_s$ in place of $\bar X_s'$: the
    assertions of \cref{rem:IV.3-4} hold. (Formalization note: the printed Remark~4 is the
    instance $U_s=\hat X_s'$; the corrected construction of
    \cref{def:IV.3-construction-componentwise} is the instance $U_s=\hat X_s^{*\prime}$.)

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$).} The
    datum $\mathfrak R^{N-1}_{\mathrm{II}}$ is not a resolution datum: the printed sentence
    (p.~308) ``In both cases, we see that $\tilde E_1,\dots,\tilde E_{\tilde\alpha}$ are
    non-singular irreducible subschemes of $\bar X_s'$ of codimension 1, and that $\tilde
    E_1\cup\dots\cup\tilde E_{\tilde\alpha}$ has only normal crossings on $\bar X_s'$'' is false
    (the $\tilde E_j$ can be reducible, and $\tilde E_i=\tilde X$ if $F=E_i$). The statement is made for the datum $\mathfrak R^{N-1,e}_{\mathrm{II}}$ whose
    entries equal to $\tilde X$ are emptied, which is a weak datum (\cref{rem:IV.3-2-repaired}):
    the hypotheses ``is a resolution datum'', $\tilde J\prod\tilde P_j^{a_j}=\bar J(s)$,
    ``$f_{\tilde B}$ permissible'' and the conclusions refer to it. For a resolution datum nothing
    is emptied, which gives the printed statement. -/)
  (proof := /-- The proof of \cref{rem:IV.3-4}, with \cref{lem:IV.AB-5-generic} and
    \cref{lem:IV.AB-6-generic} in place of Lemmas (AB.5) and (AB.6).

    In Lean: $\tilde B\subseteq S^*(\mathfrak R^{N-1}_{\mathrm{II}})$ gives
    $\nu_{\tilde x}(\bar J(s))\ge b$ at every point of $\tilde B$ (superadditivity of $\nu$ on
    $\tilde J\prod\tilde P_j^{a_j}=\bar J(s)$), so $c_s(\tilde B)\subseteq S(\mathfrak R(s))$ lies
    over $x_0$ (\cref{lem:IV.AB-5-generic}, Remark~1 and [(1)]), $B_s\subseteq W(s)$, and
    $\hat g_s(\tilde B)=\hat x_0$; the hypotheses of Lemma (AB.6) hold for the closure of $\tilde B$
    in
    $\bar X_s$ (\cref{lem:IV.AB-6-generic}), so $B_s$ is simple and the $V_j(s)$, $W(s)$ are
    normally
    flat along $B_s$ at the points of $c_s(\tilde B)$; $\bigcup E_i(s)$ has only normal crossings
    with
    $B_s$ there by the descent of normal crossings along $S_s\to\hat S_s$ (and, for
    $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},U)$, by [(2)], Remark~1 and
    \cref{lem:IV.AB-5-generic}); the set $U_s$ of points of $B_s$ at which $\mathfrak
    R^{N,n'}_{\mathrm I}(s)$ is
    resolved is open (\cref{lem:IV.1-1}), contains $c_s(\tilde B)$ and is dense as $B_s$ is
    irreducible.

    \textbf{Deviation from the paper (gap filled).} The paper writes only ``By Lemma (AB.6)'': the
    hypothesis $\bar J(s)_{\hat x}\subseteq P^b$ of Lemma (AB.6) is derived from
    $\tilde B\subseteq S(\mathfrak R^{N-1}_{\mathrm{II}})$ at the generic point of $\tilde B$ and
    the fact
    that the powers of $P$ are $P$-primary ($R/P$ regular). The descent of normal crossings
    ``by the above property of the homomorphism $S_s\to\hat S_s$'' is proved as follows: the stalk
    map
    $\mathcal O_{X_s,x}\to\mathcal O_{\tilde X,\tilde x}$ is a local homomorphism of regular local
    rings
    with $\tilde B_{\tilde x}\cap\mathcal O_{X_s,x}=(B_s)_x$ (Corollary of Lemma (AB.3) and the
    faithful
    flatness of $S_s\to\hat S_s$), the generators of the $E_j(s)$ at $x$ map to generators of the
    $\tilde E_j$, which are adapted to $\tilde B$ by the permissibility of $f_{\tilde B}$, and they
    stay
    distinct since the $\hat E_j(s)$ are transversal to $\bar X_s$ (Remark~2) and $S_s\to\hat S_s$
    is
    faithfully flat.

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$).} The
    orders of ideals are additive on $\tilde J\prod_j(\tilde P^e_j)^{a_j}$ because the kept
    $\tilde E_j$ are non-singular divisors (order one at their points) and the emptied ones are
    units; irreducibility of the $\tilde E_j$ is not used. In the descent of normal crossings the
    members $k$ of a regular system of parameters of $\mathcal O_{X_s,x}$ outside $B_{s,x}$ have
    non-zero image, so their traces are kept; the others (the emptied traces, $E_j(s)=F(s)\supseteq
    B_s$) are old and are added by the case ``seen or old''. See
    \cref{rem:IV.3-2-repaired}. -/)
  (proofUses := ["lem:IV.AB-5-generic", "lem:IV.AB-6-generic", "lem:IV.AB-2", "rem:IV.3-1",
    "lem:IV.1-1"])
  (latexEnv := "remark")]
theorem Frame.RemovalFamily.isContainedIn_W_and_resolvedAt_extendBy_of_isPermissible [Hironaka.HironakaCitedResults.{u}] {N n : ℕ}
    {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
    {𝒮 : Frame hS} (R : 𝒮.RemovalFamily) (s : ℕ) (hprep : PrepHyp N ℜ P r T x₀ s)
    (a : Fin (𝒮.eTilde s).1 → ℕ) (Jt : Subscheme (R.xTilde s))
    (hJt : Jt * ∏ j, (((R.datumII s a Jt).emptyIfBot).E j) ^ (a j) = R.jBarT s)
    (hII : ((R.datumII s a Jt).emptyIfBot).IsWeakDatum) (Bt : Subscheme (R.xTilde s))
    (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : ((R.datumII s a Jt).emptyIfBot).IsPermissible Bt) :
    let Bs : Subscheme (T.X s) :=
      Subscheme.ofClosed ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩
    Bs.IsContainedIn ((T.pre s).strictTransform ℜ.W) ∧
    ∃ Us : Set (T.X s), (∃ U₀ : Set (T.X s), IsOpen U₀ ∧ Us = U₀ ∩ Bs.pts) ∧
      Bs.pts ⊆ closure Us ∧ (R.cTilde s).base '' Bt.pts ⊆ Us ∧
      ∀ x ∈ Us, (((T.pre s).transformI ℜ).extendBy Bs).ResolvedAt x := by
  intro Bs
  classical
  have hBtred : Bt.IsReduced := Subscheme.isReduced_of_isNonsingular hBt
  have hirrBt : IsIrreducible Bt.pts := Subscheme.isIrreducible_pts Bt hBti
  have hsub : ∀ xt ∈ Bt.pts, xt ∈ ((R.datumII s a Jt).emptyIfBot).S := fun xt hx => (hperm.2.1 hx).1
  have hnu : ∀ xt ∈ Bt.pts, (𝒮.b : ℕ∞) ≤ Ideal.nu ((R.jBarT s).stalkIdeal xt) :=
    fun xt hx => R.le_nu_jBarT_of_mem_S a Jt hJt (hsub xt hx)
  have hS3 := fun xt (hx : xt ∈ Bt.pts) => R.cTilde_mem_S_and_composite_eq hprep (hnu xt hx)
  have hW : ∀ xt ∈ Bt.pts, (R.cTilde s).base xt ∈ ((T.pre s).transformI ℜ).W.pts :=
    fun xt hx => S_subset_pts_W (hS3 xt hx).1
  have hBsW : Bs.pts ⊆ ((T.pre s).transformI ℜ).W.pts := by
    show closure _ ⊆ _
    exact closure_minimal (Set.image_subset_iff.mpr fun xt hx => hW xt hx)
      (show IsClosed ((T.pre s).transformI ℜ).W.pts from
        ((T.pre s).transformI ℜ).W.support.isClosed)
  have hBsC : Bs.IsContainedIn ((T.pre s).strictTransform ℜ.W) := by
    rw [← MonoidalSuccession.transformI_W]
    exact Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced _) hBsW
  refine ⟨hBsC, ?_⟩
  -- Lemma (AB.6)
  obtain ⟨hns, hirr, hg, hJ⟩ := R.ab6_inputs a Jt hJt Bt hBt hBti hsub
    (fun xt hx => R.gTilde_eq_xh hprep (hnu xt hx))
  have h6 := R.isIrreducible_and_isNormallyFlatAlongAt_of_jbar_le_pow s (R.bb s Bt) hns hirr hg hJ
  have hcc : (𝒮.cBar s).base '' ((R.bb s Bt).pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme)) =
      (R.cTilde s).base '' Bt.pts := by
    rw [R.pts_bb_inter_uBar]
    ext y
    constructor
    · rintro ⟨_, ⟨xt, hxt, rfl⟩, rfl⟩
      exact ⟨xt, hxt, rfl⟩
    · rintro ⟨xt, hxt, rfl⟩
      exact ⟨_, ⟨xt, hxt, rfl⟩, rfl⟩
  rw [hcc] at h6
  obtain ⟨hBsirr, hBsker, Us, ⟨U₀, hU₀, hUs⟩, hUne, hUsimp, hUsub, hUNF⟩ := h6
  have hXa : IsAlgebraicScheme (T.X s) := hS.isAlgebraicScheme_X s
  have hXns : (T.X s).IsNonsingular := hS.isNonsingular_X s
  have := hS.ambient.1
  have hdatum : ((T.pre s).transformI ℜ).IsDatum := MonoidalSuccession.transformI_isDatum
    (T.pre s) hS.ambient.2.1 ℜ hS.isDatum (hS.permissible s).isPermissibleI
  have hBsC' : Bs.IsContainedIn ((T.pre s).transformI ℜ).W := by
    rw [MonoidalSuccession.transformI_W]; exact hBsC
  have hdatum' : (((T.pre s).transformI ℜ).extendBy Bs).IsDatum := by
    obtain ⟨hE1, hE2, hE3, hW1, hWV⟩ := hdatum
    refine ⟨hE1, hE2, hE3, Subscheme.ofClosed_isReduced _, fun j => ?_⟩
    induction j using Fin.lastCases with
    | last =>
      simpa only [DatumI.Raw.extendBy, Fin.snoc_last] using hBsC'
    | cast i =>
      simp only [DatumI.Raw.extendBy, Fin.snoc_castSucc]
      exact fun U => (hWV i U).trans (hBsC' U)
  obtain ⟨U₁, hU₁, hU₁eq⟩ := DatumI.Raw.exists_isOpen_resolvedSet hXns _ hdatum'
  have hU₁eq : {y | y ∈ Bs.pts ∧ (((T.pre s).transformI ℜ).extendBy Bs).ResolvedAt y} =
      U₁ ∩ Bs.pts := hU₁eq
  have hres : ∀ xt ∈ Bt.pts,
      (((T.pre s).transformI ℜ).extendBy Bs).ResolvedAt ((R.cTilde s).base xt) := by
    intro xt hxt
    have hxU : (R.cTilde s).base xt ∈ Us := hUsub ⟨xt, hxt, rfl⟩
    rw [resolvedAt_extendBy_transformI_iff]
    exact ⟨hUsimp _ hxU, fun j => hUNF _ hxU j,
      R.hasOnlyNormalCrossingsWithAt_transformI_E_cTilde hprep a Jt hJt hII Bt hBt hBti hperm
        (fun xt' hxt' => hUsimp _ (hUsub ⟨xt', hxt', rfl⟩))
        (fun xt' hxt' => R.comap_stalkIdeal_cTilde_eq Bt hBtred
          (fun x hx => R.gTilde_eq_xh hprep (hnu x hx)) hBsker hxt') xt hxt⟩
  have hmemBs : ∀ xt ∈ Bt.pts, (R.cTilde s).base xt ∈ Bs.pts := fun xt hxt =>
    subset_closure ⟨xt, hxt, rfl⟩
  refine ⟨{y | y ∈ Bs.pts ∧ (((T.pre s).transformI ℜ).extendBy Bs).ResolvedAt y},
    ⟨U₁, hU₁, hU₁eq⟩, ?_, ?_, fun x hx => hx.2⟩
  · obtain ⟨xt₀, hxt₀⟩ := hirrBt.nonempty
    rw [hU₁eq]
    refine exists_pts_subset_closure_inter (show IsClosed Bs.pts from Bs.support.isClosed)
      (Subscheme.isIrreducible_pts Bs hBsirr) hU₁ ⟨(R.cTilde s).base xt₀, ?_, hmemBs xt₀ hxt₀⟩
    have : (R.cTilde s).base xt₀ ∈
        {y | y ∈ Bs.pts ∧ (((T.pre s).transformI ℜ).extendBy Bs).ResolvedAt y} :=
      ⟨hmemBs xt₀ hxt₀, hres xt₀ hxt₀⟩
    rw [hU₁eq] at this
    exact this.1
  · rintro _ ⟨xt, hxt, rfl⟩
    exact ⟨hmemBs xt hxt, hres xt hxt⟩

/-- **Remark 5** (pp. 309–310) for an arbitrary open family with removals; the printed Remark 5
is the instance `U_s = X̂'_s` (`Frame.isPermissibleCenter_of_isPermissibleOpen_extendBy`, see
there).  The paper's argument applies with `lem:IV.AB-5-generic`, `rem:IV.3-4-generic` in place of
Lemma (AB.5), Remark 4.

Proved (no leaf of its own; it uses `lem:IV.AB-5-generic` through
`Frame.RemovalFamily.cTilde_mem_S_and_composite_eq`, and the open restriction `U(s)` through
`IsGoodDatumI.succession_open`).

\textbf{Deviation from the paper (gap filled).} The paper says only "it is clear that `B_s` is
contained
in `W(s) ∩ F(s)` (resp. `W(s) − U(s)`) … It follows that any permissible monoidal transformation …".
In Lean: `S(ℜ(s))` is `W(s) ∩ F(s)` (closed) resp. the unresolved points of `W(s)` (which lie off
`U(s)` since `ℜ(s)` is resolved on the open restriction `U(s)`, and `W(s) − U(s) = W(s) ∩ U₀ᶜ` is
closed), `c_s(B̃) ⊆ S(ℜ(s))` by Remark 3, and `B_s` is the closure of `c_s(B̃)`; a center `C`
permissible for
`(ℜ^{N,n'}_I(s), U_s)` is permissible for `ℜ(s)` because the data `(ℜ(s).extendBy B_s).extendBy C`
and
`ℜ(s).extendBy C` have the same boundary, `C` is reduced and contained in all the `V_j(s)`, `W(s)`,
and the
`V_j(s)`, `W(s)` are normally flat along `C` at its points
(`isPermissible_of_isPermissible_extendBy`).
Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the paper (p. 308)
"In both cases, we see that `Ẽ_1, ⋯, Ẽ_α̃` are non-singular irreducible subschemes of `X̄'_s` of
codimension 1, and that `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on `X̄'_s`" is false as printed:
the `Ẽ_j` need not be irreducible, and `Ẽ_i = X̃` if `F = E_i`.
The statement is made for the datum with the traces equal to `X̃` emptied
(`(R.datumII s a Jt).emptyIfBot`), which is a weak datum (`isWeakDatum_emptyIfBot_datumII`):
`hII` is `IsWeakDatum`, and `hJt`, `hperm` and the conclusions refer to the emptied datum.  The
irreducibility of the `Ẽ_j` is not used, and there is no hypothesis `hFE`.  For a resolution
datum nothing is emptied (`DatumII.Raw.IsDatum.emptyIfBot_eq`), which gives the printed
statements.

The dimension hypothesis `dim X̃ = N - 1` of the printed statement is not used by the proof and
is dropped in this generic statement (it is not derivable from the data alone,
`lem:IV.3-xtilde-ambient`). -/
@[blueprint "rem:IV.3-5-generic"
  (statement := /-- Notation as in \cref{rem:IV.3-5}, for an arbitrary open family with
    removals $U_s\subseteq\hat X_s$, with $\tilde X=\bar U_s$ in place of $\bar X_s'$: the
    assertions of \cref{rem:IV.3-5} hold. (Formalization note: the printed Remark~5 is the
    instance $U_s=\hat X_s'$; the corrected construction of
    \cref{def:IV.3-construction-componentwise} is the instance $U_s=\hat X_s^{*\prime}$.)

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$).} The
    datum $\mathfrak R^{N-1}_{\mathrm{II}}$ is not a resolution datum: the printed sentence
    (p.~308) ``In both cases, we see that $\tilde E_1,\dots,\tilde E_{\tilde\alpha}$ are
    non-singular irreducible subschemes of $\bar X_s'$ of codimension 1, and that $\tilde
    E_1\cup\dots\cup\tilde E_{\tilde\alpha}$ has only normal crossings on $\bar X_s'$'' is false
    (the $\tilde E_j$ can be reducible, and $\tilde E_i=\tilde X$ if $F=E_i$). The statement is made for the datum $\mathfrak R^{N-1,e}_{\mathrm{II}}$ whose
    entries equal to $\tilde X$ are emptied, which is a weak datum (\cref{rem:IV.3-2-repaired}):
    the hypotheses ``is a resolution datum'', $\tilde J\prod\tilde P_j^{a_j}=\bar J(s)$,
    ``$f_{\tilde B}$ permissible'' and the conclusions refer to it. For a resolution datum nothing
    is emptied, which gives the printed statement. -/)
  (proof := /-- The proof of \cref{rem:IV.3-5}, with \cref{lem:IV.AB-5-generic} and
    \cref{rem:IV.3-4-generic} in place of Lemma (AB.5) and Remark~4.

    In Lean: $c_s(\tilde B)\subseteq S(\mathfrak R(s))$ (Remark~3), $S(\mathfrak R(s))=W(s)\cap
    F(s)$ is
    closed in the closed case; in the open case the points of $c_s(\tilde B)$ are unresolved points
    of
    $W(s)$, hence outside $U(s)$, and $W(s)-U(s)$ is closed ($U(s)$ is an open restriction of
    $\mathfrak R(s)$). So $B_s=\overline{c_s(\tilde B)}\subseteq W(s)\cap F(s)$ (resp.\
    $W(s)-U(s)$).
    A center $C$ permissible for $(\mathfrak R^{N,n'}_{\mathrm I}(s),U_s)$ lies in $B_s$, is
    non-singular
    irreducible, and $\mathfrak R(s).\mathrm{extendBy}\,C$ is a resolution datum resolved at every
    point of $C$
    (the conditions on $V_j(s)$, $W(s)$ and on $\bigcup E_i(s)$ are among those for $C$), so $C$ is
    permissible
    for $\mathfrak R(s)$; the last assertion is the case $C=B_s$.

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$).} The
    orders of ideals are additive on $\tilde J\prod_j(\tilde P^e_j)^{a_j}$ because the kept
    $\tilde E_j$ are non-singular divisors (order one at their points) and the emptied ones are
    units; irreducibility of the $\tilde E_j$ is not used. In the descent of normal crossings the
    members $k$ of a regular system of parameters of $\mathcal O_{X_s,x}$ outside $B_{s,x}$ have
    non-zero image, so their traces are kept; the others (the emptied traces, $E_j(s)=F(s)\supseteq
    B_s$) are old and are added by the case ``seen or old''. See
    \cref{rem:IV.3-2-repaired}. -/)
  (proofUses := ["rem:IV.3-1", "lem:IV.AB-5-generic", "rem:IV.3-4-generic"])
  (latexEnv := "remark")]
theorem Frame.RemovalFamily.isPermissibleCenter_of_isPermissibleOpen_extendBy [Hironaka.HironakaCitedResults.{u}] {N n : ℕ}
    {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
    {𝒮 : Frame hS} (R : 𝒮.RemovalFamily) (s : ℕ) (hprep : PrepHyp N ℜ P r T x₀ s)
    (a : Fin (𝒮.eTilde s).1 → ℕ) (Jt : Subscheme (R.xTilde s))
    (hJt : Jt * ∏ j, (((R.datumII s a Jt).emptyIfBot).E j) ^ (a j) = R.jBarT s)
    (hII : ((R.datumII s a Jt).emptyIfBot).IsWeakDatum) (Bt : Subscheme (R.xTilde s))
    (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : ((R.datumII s a Jt).emptyIfBot).IsPermissible Bt) :
    let Bs : Subscheme (T.X s) :=
      Subscheme.ofClosed ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩
    let ℜs := (T.pre s).transformI ℜ
    (∀ F, r = .closed F → Bs.pts ⊆ ℜs.W.pts ∩ ((T.pre s).strictTransform F).pts) ∧
    (∀ U, r = .opn U → Bs.pts ⊆ ℜs.W.pts \ (T.pre s).transformOpen U) ∧
    (∀ Us : Set (T.X s), (ℜs.extendBy Bs).IsOpenRestriction Us → ∀ C : Subscheme (T.X s),
      (ℜs.extendBy Bs).IsPermissibleOpen Us C →
        (r.transformSucc (T.pre s)).IsPermissibleCenter ℜs C) ∧
    ((∀ x ∈ Bs.pts, (ℜs.extendBy Bs).ResolvedAt x) →
      (r.transformSucc (T.pre s)).IsPermissibleCenter ℜs Bs) := by
  intro Bs ℜs
  classical
  have hirrBt : IsIrreducible Bt.pts := Subscheme.isIrreducible_pts Bt hBti
  have hsub : ∀ xt ∈ Bt.pts, xt ∈ ((R.datumII s a Jt).emptyIfBot).S := fun xt hx => (hperm.2.1 hx).1
  have hnu : ∀ xt ∈ Bt.pts, (𝒮.b : ℕ∞) ≤ Ideal.nu ((R.jBarT s).stalkIdeal xt) :=
    fun xt hx => R.le_nu_jBarT_of_mem_S a Jt hJt (hsub xt hx)
  have hS3 := fun xt (hx : xt ∈ Bt.pts) => R.cTilde_mem_S_and_composite_eq hprep (hnu xt hx)
  have hW : ∀ xt ∈ Bt.pts, (R.cTilde s).base xt ∈ ℜs.W.pts :=
    fun xt hx => S_subset_pts_W (hS3 xt hx).1
  have hBsW : Bs.pts ⊆ ℜs.W.pts := by
    show closure _ ⊆ _
    exact closure_minimal (Set.image_subset_iff.mpr fun xt hx => hW xt hx)
      (show IsClosed ℜs.W.pts from ℜs.W.support.isClosed)
  have hBsC' : Bs.IsContainedIn ℜs.W :=
    Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced _) hBsW
  have := hS.ambient.1
  have hdatum : ℜs.IsDatum := MonoidalSuccession.transformI_isDatum
    (T.pre s) hS.ambient.2.1 ℜ hS.isDatum (hS.permissible s).isPermissibleI
  have hdatumBs : (ℜs.extendBy Bs).IsDatum :=
    isDatum_extendBy_of_isContainedIn hdatum (Subscheme.ofClosed_isReduced _) hBsC'
  have hBsirr : Bs.IsIrreducible := by
    refine Subscheme.isIrreducible_of_pts Bs ?_
    show IsIrreducible (closure _)
    exact (hirrBt.image _ (R.cTilde s).continuous.continuousOn).closure
  -- the central assertion: `B_s ⊆ T`, with `T = W(s) ∩ F(s)` resp. `W(s) − U(s)`
  have key : ∀ T' : Set (T.X s), IsClosed T' → (∀ xt ∈ Bt.pts, (R.cTilde s).base xt ∈ T') →
      Bs.pts ⊆ T' := fun T' hT' h =>
    closure_minimal (Set.image_subset_iff.mpr fun xt hx => h xt hx) hT'
  have hcenter : (∀ x ∈ Bs.pts, (ℜs.extendBy Bs).ResolvedAt x) → ℜs.IsPermissible Bs := by
    intro hres
    refine ⟨Or.inr ⟨?_, hBsirr⟩, hdatumBs, fun x hx => hres x hx⟩
    refine Subscheme.isNonsingular_of_stalk_quot Bs fun z hz => ?_
    exact (hres z hz).1.2
  cases r with
  | closed F =>
    have hT : Bs.pts ⊆ ℜs.W.pts ∩ ((T.pre s).strictTransform F).pts :=
      key _ (ℜs.W.support.isClosed.inter ((T.pre s).strictTransform F).support.isClosed)
        fun xt hx => (hS3 xt hx).1
    refine ⟨fun F' hF' => ?_, fun U hU => (by cases hU), fun Us _ C hC => ?_, fun hres => ?_⟩
    · cases hF'; exact hT
    · exact ⟨isPermissible_of_isPermissible_extendBy hC.1, fun x hx => hT (hC.2 hx).1⟩
    · exact ⟨hcenter hres, hT⟩
  | opn U =>
    have hgood : IsGoodDatumI N n X ℜ := ⟨hS.ambient, hS.isDatum, hS.dim_W.le⟩
    obtain ⟨-, ⟨U₀, hU₀, hUeq⟩, -, hUres⟩ :=
      IsGoodDatumI.succession_open (T.pre s) hgood hS.isFor (hS.permissible s)
    have hcl : IsClosed (ℜs.W.pts \ (T.pre s).transformOpen U) := by
      have : ℜs.W.pts \ (T.pre s).transformOpen U = ℜs.W.pts ∩ U₀ᶜ := by
        rw [hUeq]
        ext y
        simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff]
        tauto
      rw [this]
      exact ℜs.W.support.isClosed.inter hU₀.isClosed_compl
    have hT : Bs.pts ⊆ ℜs.W.pts \ (T.pre s).transformOpen U :=
      key _ hcl fun xt hx => ⟨hW xt hx, fun hU' => (hS3 xt hx).1.2 (hUres _ hU')⟩
    refine ⟨fun F hF => (by cases hF), fun U' hU' => ?_, fun Us _ C hC => ?_, fun hres => ?_⟩
    · cases hU'; exact hT
    · exact ⟨isPermissible_of_isPermissible_extendBy hC.1, fun x hx => hT (hC.2 hx).1⟩
    · exact ⟨hcenter hres, hT⟩

/-- For a resolution datum no entry is the whole space, so the factorization
`J̃ ∏ Ẽ_j^{a_j} = J̄(s)` holds for the emptied entries (the printed Remarks 3–5 are the instances of
the generic ones for the
datum `ℜ^{N-1}_II`, which is assumed to be a resolution datum). -/
theorem Frame.RemovalFamily.mul_prod_emptyIfBot_eq_jBarT {N n : ℕ} {X : Scheme.{u}}
    {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS} (R : 𝒮.RemovalFamily) (s : ℕ)
    (a : Fin (𝒮.eTilde s).1 → ℕ) (Jt : Subscheme (R.xTilde s))
    (hII : (R.datumII s a Jt).IsDatum)
    (hJt : Jt * ∏ j, ((R.datumII s a Jt).E j) ^ (a j) = R.jBarT s) :
    Jt * ∏ j, (((R.datumII s a Jt).emptyIfBot).E j) ^ (a j) = R.jBarT s := by
  have hE : ∀ j, ((R.datumII s a Jt).E j).emptyIfBot = (R.datumII s a Jt).E j := fun j =>
    Subscheme.emptyIfBot_eq_self_of_isNonsingularIrreducibleCodimOne (hII.2.1 j)
  have : (∏ j, (((R.datumII s a Jt).emptyIfBot).E j) ^ (a j)) =
      ∏ j, ((R.datumII s a Jt).E j) ^ (a j) :=
    Finset.prod_congr rfl fun j _ => by
      change (((R.datumII s a Jt).E j).emptyIfBot) ^ (a j) = _
      rw [hE j]
  rw [this]
  exact hJt

/-- **Remark 3** (pp. 308–309).  The datum `ℜ^{N-1}_II` is `Frame.datumII` for the given
`a_j`, `J̃` with `J̃ ∏ P̃_j^{a_j} = J̄(s)` on `X̃`, and is assumed to be a resolution datum (the
paper calls it one); "`X̃` has dimension `N - 1`" is the case of interest (p. 308).  The
garbled sentence "We shall write `S_0(ℜ(s)) ∩ g_s⁻¹(x_0)`, which is by the assumption [(1)] a
closed and open subset of `S(ℜ(s))`" (a paper misprint) is read as introducing
`S(ℜ(s)) ∩ g_s⁻¹(x_0)`, which is clopen in `S(ℜ(s))`.

Deviation from the paper (statement modified): that `ℜ^{N-1}_II` is a resolution datum and that
`X̃` has dimension `N - 1` are hypotheses (`hII`, `hdim`).

\textbf{Statement modified (transcription).} The last assertion has the extra hypothesis
`Bt.IsReduced`: the paper's "irreducible subscheme" B̃ is reduced, as the open immersion into the
reduced `B_s` requires.  Without it the statement is false: `Bt = Spec(O_{X̃,x̂_0}/m²)`
(irreducible,
one point of `S(ℜ_II)`, not reduced) admits no open immersion into the reduced `Bs`.

Proof (repair of the paper's error on the subschemes `Ẽ_j`): the generic version holds for the datum with the traces
equal to `X̃` emptied; for a resolution datum `hII` nothing is emptied
(`DatumII.Raw.IsDatum.emptyIfBot_eq`), so the printed statement is the instance. -/
@[blueprint "rem:IV.3-3"
  (statement := /-- \textbf{Remark 3.} Notation as in \cref{rem:IV.3-2}. We shall be only
    interested in the case in which $\bar X_s'$ has dimension $N-1$. Let us write $\tilde X$
    for $\bar X_s'$ and consider a resolution datum $\mathfrak R^{N-1}_{\mathrm{II}}$ on
    $\tilde X$ (without restriction) of the form
    $\mathfrak R^{N-1}_{\mathrm{II}}=\big(\tilde E_1,\dots,\tilde E_{\tilde\alpha}\,\big|\,
    \tilde J,b\,\big|\,a_1,\dots,a_{\tilde\alpha}\big)$ (\cref{def:I.3-II}), where $b$ is the
    positive integer defined above, and the integers $a_j\ge0$ and the coherent sheaf of ideals
    $\tilde J$ on $\tilde X$ are such that $\tilde J(\prod_{j=1}^{\tilde\alpha}\tilde
    P_j^{a_j})=\bar J(s)$, where $\tilde P_j$ is the sheaf of prime ideals of $\tilde E_j$ on
    $\tilde X$. (For example, we may choose $a_j=0$ for all $j$.) Let us recall that
    $S(\mathfrak R^{N-1}_{\mathrm{II}})$ denotes the closed subset of $\tilde X$ of those points
    $\tilde x$ for which $\sum_{\tilde x\in\tilde E_i}a_i+\nu_{\tilde x}(\tilde J)\ge b$
    (\cref{def:I.S}) (or, equivalently, $\nu_{\tilde x}(\bar J(s))\ge b$). By virtue of Lemma
    (AB.5), Remark~1 and the assumption [(1)],
    $c_s(S(\mathfrak R^{N-1}_{\mathrm{II}}))\subseteq S(\mathfrak R(s))\cap g_s^{-1}(x_0)$, and
    $S(\mathfrak R(s))\cap g_s^{-1}(x_0)$ is, by the assumption [(1)], a closed and open subset
    of $S(\mathfrak R(s))$. We shall write $\tilde g$ for
    $\bar g_s'\colon\tilde X\to\operatorname{Spec}(\hat S)=\hat X_0$. The above inclusion shows
    that if $\tilde B$ is any irreducible subscheme of $\tilde X$ contained in
    $S(\mathfrak R^{N-1}_{\mathrm{II}})$, we have $\tilde g(\tilde B)=\hat x_0$ (the unique
    chosen point of $\hat X_0$) so that, by the Corollary of Lemma (AB.3), $c_s$ induces an open
    immersion of $\tilde B$ into a reduced irreducible subscheme $B_s$ of $X_s$, where $B_s$ is
    obtained as the closure of $c_s(\tilde B)$ in $X_s$. (pp.~308--309.)

    \textbf{Paper misprint.} The paper reads ``We shall write $S_0(\mathfrak R(s))\cap
    g_s^{-1}(x_0)$, which is by the assumption [(1)] a closed and open subset of
    $S(\mathfrak R(s))$''; the sentence is garbled (meant: we write $S_0(\mathfrak R(s))$ for
    $S(\mathfrak R(s))\cap g_s^{-1}(x_0)$), and the clopen assertion is stated for
    $S(\mathfrak R(s))\cap g_s^{-1}(x_0)$.

    \textbf{Deviation from the paper (statement modified).} That $\mathfrak R^{N-1}_{\mathrm{II}}$
    is a resolution datum (which the paper presupposes; cf.\ \cref{rem:IV.3-2}) and that
    $\tilde X$ has dimension $N-1$ (the only case of interest, p.~308) are hypotheses of the
    Lean statement.

    \textbf{Statement modified (transcription).} The subscheme $\tilde B$ of the last assertion
    is assumed reduced: the paper's ``irreducible subscheme'' $\tilde B$ is reduced, as the open
    immersion into the reduced $B_s$ requires. Without this the statement is false:
    $\tilde B=\operatorname{Spec}(\mathcal O_{\tilde X,\hat x_0}/\mathfrak m^2)$ is irreducible,
    lies in $S(\mathfrak R^{N-1}_{\mathrm{II}})$ and is not reduced. -/)
  (proof := /-- The equivalence: $\bar J(s)=\tilde J\prod_j\tilde P_j^{a_j}$ with $\tilde P_j$
    principal prime, generated by a regular parameter at the points of $\tilde E_j$, so
    $\nu_{\tilde x}(\bar J(s))=\nu_{\tilde x}(\tilde J)+\sum_{\tilde x\in\tilde E_i}a_i$. The
    inclusion: if $\nu_{\tilde x}(\bar J(s))\ge b$ then by Lemma (AB.5) (\cref{lem:IV.AB-5})
    $x'=c_s(\tilde x)$ lies on $W(s)$ (and on $F(s)$ in the closed case); in the open case, by
    Remark~1 (\cref{rem:IV.3-1}) $W$ is singular at $x_0$ or some $V_j$ is not normally flat
    along $W$ at $x_0$, and then by (ii), (iii) of Lemma (AB.5) the datum $\mathfrak R(s)$ is
    not resolved at $x'$; so $x'\in S(\mathfrak R(s))$. Moreover $g_s(x')$ is a generization of
    $x_0$ (the image of $\hat X_0\to X$ consists of the generizations of $x_0$) lying in the
    finite set $g_s(S(\mathfrak R(s)))$ of points at which $X$ has dimension $N$ ([(1)]), hence
    $g_s(x')=x_0$. By [(1)], $g_s$ maps $S(\mathfrak R(s))$ onto finitely many closed points,
    so $S(\mathfrak R(s))\cap g_s^{-1}(x_0)$ is closed and open in $S(\mathfrak R(s))$. Finally,
    for $\tilde B$ as stated, $\tilde g(\tilde B)$ lies over $x_0$ and in the image of
    $S(\mathfrak R^{N-1}_{\mathrm{II}})$, so $\tilde g(\tilde B)=\hat x_0$; the closure
    $\bar B$ of $\tilde B$ in $\hat X_s$ then satisfies $\hat g_s(\bar B)=\hat x_0$ and the
    Corollary of Lemma (AB.3) (\cref{cor:IV.AB-3}) gives the reduced irreducible $B_s$ with
    $c_s$ inducing $\bar B\simeq B_s$, whence an open immersion $\tilde B\to B_s$.

    (Formalization note: in Lean this is the instance $U_s=\hat X_s'$ of
    \cref{rem:IV.3-3-generic}, the remark for an arbitrary open family with removals.) -/)
  (proofUses := ["lem:IV.AB-5", "rem:IV.3-1", "cor:IV.AB-3", "rem:IV.3-3-generic"])
  (latexEnv := "remark")]
theorem Frame.mem_S_iff_le_nu_and_exists_isOpenImmersion_of_prepHyp [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}}
    {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
    (𝒮 : Frame hS) (s : ℕ) (hprep : PrepHyp N ℜ P r T x₀ s)
    (_hdim : (𝒮.xTilde s).dim = ((N - 1 : ℕ) : WithBot ℕ∞))
    (a : Fin (𝒮.eTilde s).1 → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, ((𝒮.datumII s a Jt).E j) ^ (a j) = 𝒮.jBarT s)
    (hII : (𝒮.datumII s a Jt).IsDatum) :
    (∀ xt : 𝒮.xTilde s, xt ∈ (𝒮.datumII s a Jt).S ↔
      (𝒮.b : ℕ∞) ≤ Ideal.nu ((𝒮.jBarT s).stalkIdeal xt)) ∧
    (𝒮.cTilde s).base '' (𝒮.datumII s a Jt).S ⊆
      S ((T.pre s).transformI ℜ) (r.transformSucc (T.pre s)) ∩
        (T.pre s).composite.base ⁻¹' {x₀} ∧
    IsClopen {p : S ((T.pre s).transformI ℜ) (r.transformSucc (T.pre s)) |
      (T.pre s).composite.base p = x₀} ∧
    ∀ Bt : Subscheme (𝒮.xTilde s), Bt.IsIrreducible → Bt.IsReduced →
      Bt.pts ⊆ (𝒮.datumII s a Jt).S →
      (𝒮.gTilde s).base '' Bt.pts = {hS.xh} ∧
      let Bs : Subscheme (T.X s) :=
        Subscheme.ofClosed ⟨closure ((𝒮.cTilde s).base '' Bt.pts), isClosed_closure⟩
      Bs.IsReduced ∧ Bs.IsIrreducible ∧
        ∃ φ : Bt.toScheme ⟶ Bs.toScheme, IsOpenImmersion φ ∧ φ ≫ Bs.ι = Bt.ι ≫ 𝒮.cTilde s :=
  by
  have hemp : (𝒮.removalFamily.datumII s a Jt).emptyIfBot = 𝒮.datumII s a Jt := hII.emptyIfBot_eq
  have h := 𝒮.removalFamily.mem_S_iff_le_nu_and_exists_isOpenImmersion_of_prepHyp s hprep a Jt
    (𝒮.removalFamily.mul_prod_emptyIfBot_eq_jBarT s a Jt hII hJt)
    (by rw [hemp]; exact hII.isWeakDatum)
  rw [hemp] at h
  exact h

/-- **Remark 4** (p. 309).  `B_s` is the closure of `c_s(B̃)` in `X_s` (Remark 3); the datum
`ℜ^{N,n'}_I(s) = (⋃ E_i(s); V_1(s), …, V_β(s), W(s); B_s)` is `ℜ(s).extendBy B_s`.

Deviation from the paper (statement modified): as in Remark 3, `hII` and `hdim` are hypotheses.

Proof (repair of the paper's error on the subschemes `Ẽ_j`): the generic version holds for the datum with the traces
equal to `X̃` emptied; for a resolution datum `hII` nothing is emptied
(`DatumII.Raw.IsDatum.emptyIfBot_eq`), so the printed statement is the instance. -/
@[blueprint "rem:IV.3-4"
  (statement := /-- \textbf{Remark 4.} Notation as in \cref{rem:IV.3-3}. Let $\tilde B$ be any
    non-singular irreducible subscheme of $\tilde X$ such that the monoidal transformation
    $f_{\tilde B}$ of $\tilde X$ with center $\tilde B$ is permissible for the resolution datum
    $\mathfrak R^{N-1}_{\mathrm{II}}$ on $\tilde X$ (\cref{def:I.6-II}). Let $B_s$ be the
    reduced irreducible subscheme of $X_s$ such that $c_s$ induces an open immersion
    $\tilde B\to B_s$. Then $B_s$ is contained in $W(s)$ and there exists an open dense subset
    $U_s$ of $B_s$ such that $c_s(\tilde B)\subseteq U_s$ and that the resolution datum
    $\mathfrak R^{N,n'}_{\mathrm I}(s)=(\bigcup_{i=1}^{\alpha+s}E_i(s);V_1(s),\dots,V_\beta(s),
    W(s);B_s)$, where $n'=\dim B_s$, is resolved at every point of $U_s$ (\cref{def:I.4-I}).
    (p.~309.)

    \textbf{Deviation from the paper (statement modified).} As in \cref{rem:IV.3-3}, that
    $\mathfrak R^{N-1}_{\mathrm{II}}$ is a resolution datum and that $\tilde X$ has dimension
    $N-1$ are hypotheses of the Lean statement. -/)
  (proof := /-- First of all it is clear that $B_s\subseteq W(s)$ by Lemma (AB.5)
    (\cref{lem:IV.AB-5}). Let $U_s$ be the open subset of $B_s$ which consists of those points
    at which the above $\mathfrak R^{N,n'}_{\mathrm I}(s)$ is resolved (\cref{lem:IV.1-1}); we
    show that $U_s\supseteq c_s(\tilde B)$. By Lemma (AB.6) (\cref{lem:IV.AB-6}), if $\hat x$
    is any point of $\tilde B$ and $x=c_s(\hat x)$, then $x$ is a simple point of $B_s$ and all
    the $V_j(s)$ and $W(s)$ are normally flat along $B_s$ at $x$. To show that
    $\bigcup_{i=1}^{\alpha+s}E_i(s)$ has only normal crossings with $B_s$ at $x$, note that the
    canonical homomorphism $S_s\to\hat S_s$ of the local rings of $X_s$ at $x$ and $\hat X_s$
    at $\hat x$ transforms a regular system of parameters into such a system
    (\cref{lem:IV.AB-2}). For $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$, the
    permissibility of $f_{\tilde B}$ for $\mathfrak R^{N-1}_{\mathrm{II}}$ implies that
    $\bigcup_{i=1}^{\alpha+s}c_s^{-1}(E_i(s))$ has only normal crossings with $\tilde B$ at
    $\hat x$; hence $\bigcup_{i=1}^{\alpha+s}E_i(s)$ has only normal crossings with $B_s$ at
    $x$. For $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},U)$, the same argument shows that
    $\bigcup_{i=\alpha+1}^{\alpha+s}E_i(s)$ has only normal crossings with $B_s$ at $x$. By
    Remark~1 and Lemma (AB.5), every point of $B_s$ is contained in $S(\mathfrak R(s))$, and
    therefore the assumption [(2)] implies that, for $1\le i\le\alpha$, either $E_i(s)$ does not
    contain $x$ or it contains all the irreducible components of $W(s)$ which contain $x$;
    since $W(s)$ contains $B_s$, either $E_i(s)$ does not contain $x$ or it contains $B_s$. In
    view of this fact, we can again conclude that $\bigcup_{i=1}^{\alpha+s}E_i(s)$ has only
    normal crossings with $B_s$ at the point $x$.

    (Formalization note: in Lean this is the instance $U_s=\hat X_s'$ of
    \cref{rem:IV.3-4-generic}, the remark for an arbitrary open family with removals.) -/)
  (proofUses := ["lem:IV.AB-5", "lem:IV.AB-6", "lem:IV.AB-2", "rem:IV.3-1", "lem:IV.1-1",
    "rem:IV.3-4-generic"])
  (latexEnv := "remark")]
theorem Frame.isContainedIn_W_and_resolvedAt_extendBy_of_isPermissible [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}}
    {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
    (𝒮 : Frame hS) (s : ℕ) (hprep : PrepHyp N ℜ P r T x₀ s)
    (_hdim : (𝒮.xTilde s).dim = ((N - 1 : ℕ) : WithBot ℕ∞))
    (a : Fin (𝒮.eTilde s).1 → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, ((𝒮.datumII s a Jt).E j) ^ (a j) = 𝒮.jBarT s)
    (hII : (𝒮.datumII s a Jt).IsDatum) (Bt : Subscheme (𝒮.xTilde s))
    (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : (𝒮.datumII s a Jt).IsPermissible Bt) :
    let Bs : Subscheme (T.X s) :=
      Subscheme.ofClosed ⟨closure ((𝒮.cTilde s).base '' Bt.pts), isClosed_closure⟩
    Bs.IsContainedIn ((T.pre s).strictTransform ℜ.W) ∧
    ∃ Us : Set (T.X s), (∃ U₀ : Set (T.X s), IsOpen U₀ ∧ Us = U₀ ∩ Bs.pts) ∧
      Bs.pts ⊆ closure Us ∧ (𝒮.cTilde s).base '' Bt.pts ⊆ Us ∧
      ∀ x ∈ Us, (((T.pre s).transformI ℜ).extendBy Bs).ResolvedAt x :=
  by
  have hemp : (𝒮.removalFamily.datumII s a Jt).emptyIfBot = 𝒮.datumII s a Jt := hII.emptyIfBot_eq
  exact 𝒮.removalFamily.isContainedIn_W_and_resolvedAt_extendBy_of_isPermissible s hprep a Jt
    (𝒮.removalFamily.mul_prod_emptyIfBot_eq_jBarT s a Jt hII hJt)
    (by rw [hemp]; exact hII.isWeakDatum) Bt hBt hBti
    (by rw [hemp]; exact hperm)

/-- **Remark 5** (pp. 309–310).  Permissibility for `ℜ(s)` is for the transformed restriction
`F(s)`, resp. `U(s)`.

Deviation from the paper (statement modified): the open restriction `U_s` (the specific one of
Remark 4 in the paper) ranges over all open restrictions for `ℜ^{N,n'}_I(s)` (Definition 5
(I.2)), a stronger statement; and `hII`, `hdim` are hypotheses as in Remark 3.

Proof (repair of the paper's error on the subschemes `Ẽ_j`): the generic version holds for the datum with the traces
equal to `X̃` emptied; for a resolution datum `hII` nothing is emptied
(`DatumII.Raw.IsDatum.emptyIfBot_eq`), so the printed statement is the instance. -/
@[blueprint "rem:IV.3-5"
  (statement := /-- \textbf{Remark 5.} $\tilde B$ being as in Remark~4 (\cref{rem:IV.3-4}), it
    is clear that $B_s$ is contained in $W(s)\cap F(s)$ for the case in which
    $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$, and that $B_s$ is contained in
    $W(s)-U(s)$ for the case in which $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},U)$. It
    follows that any permissible monoidal transformation of $X_s$ for the resolution datum
    $(\mathfrak R^{N,n'}_{\mathrm I}(s),U_s)$ with open restriction $U_s$ is a permissible
    monoidal transformation of $X_s$ for the resolution datum $\mathfrak R(s)$, which is either
    $(\mathfrak R^{N,n}_{\mathrm I}(s),F(s))$ or $(\mathfrak R^{N,n}_{\mathrm I}(s),U(s))$
    (\cref{def:I.6-I-closed}, \cref{def:I.6-I-open}), and moreover that, if
    $\mathfrak R^{N,n'}_{\mathrm I}(s)$ is resolved at every point of $B_s$, then the monoidal
    transformation of $X_s$ with center $B_s$ is permissible for $\mathfrak R(s)$.
    (pp.~309--310.)

    \textbf{Deviation from the paper (statement modified).} The Lean statement is made for every
    open restriction $U_s$ of $\mathfrak R^{N,n'}_{\mathrm I}(s)$, not only for the $U_s$ of
    Remark~4 (a stronger statement, true by the same argument: a permissible center lies in
    $B_s$); and, as in \cref{rem:IV.3-3}, that $\mathfrak R^{N-1}_{\mathrm{II}}$ is a
    resolution datum and that $\tilde X$ has dimension $N-1$ are hypotheses. -/)
  (proof := /-- For the second case, we refer to Remark~1 (\cref{rem:IV.3-1}) and Lemma (AB.5)
    (\cref{lem:IV.AB-5}): every point of $B_s$ lies in $S(\mathfrak R(s))$, i.e.\ in
    $W(s)-U(s)$; in the first case $\bar X_s'=c_s^{-1}(F(s))\cap\hat X_s'$ gives
    $B_s\subseteq F(s)$, and $B_s\subseteq W(s)$ by Remark~4. A center $C$ permissible for
    $(\mathfrak R^{N,n'}_{\mathrm I}(s),U_s)$ lies in $B_s-U_s$, is non-singular, the
    $V_j(s)$, $W(s)$ and $B_s$ are normally flat along it and $\bigcup E_i(s)$ has only normal
    crossings with it; as $C\subseteq B_s\subseteq W(s)\cap F(s)$ (resp.\ $W(s)-U(s)$), $C$ is
    permissible for $\mathfrak R(s)$ (\cref{def:I.6-I}). The last assertion is the case
    $C=B_s$.

    (Formalization note: in Lean this is the instance $U_s=\hat X_s'$ of
    \cref{rem:IV.3-5-generic}, the remark for an arbitrary open family with removals.) -/)
  (proofUses := ["rem:IV.3-1", "lem:IV.AB-5", "rem:IV.3-4", "rem:IV.3-5-generic"])
  (latexEnv := "remark")]
theorem Frame.isPermissibleCenter_of_isPermissibleOpen_extendBy [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}}
    {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
    (𝒮 : Frame hS) (s : ℕ) (hprep : PrepHyp N ℜ P r T x₀ s)
    (_hdim : (𝒮.xTilde s).dim = ((N - 1 : ℕ) : WithBot ℕ∞))
    (a : Fin (𝒮.eTilde s).1 → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, ((𝒮.datumII s a Jt).E j) ^ (a j) = 𝒮.jBarT s)
    (hII : (𝒮.datumII s a Jt).IsDatum) (Bt : Subscheme (𝒮.xTilde s))
    (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : (𝒮.datumII s a Jt).IsPermissible Bt) :
    let Bs : Subscheme (T.X s) :=
      Subscheme.ofClosed ⟨closure ((𝒮.cTilde s).base '' Bt.pts), isClosed_closure⟩
    let ℜs := (T.pre s).transformI ℜ
    (∀ F, r = .closed F → Bs.pts ⊆ ℜs.W.pts ∩ ((T.pre s).strictTransform F).pts) ∧
    (∀ U, r = .opn U → Bs.pts ⊆ ℜs.W.pts \ (T.pre s).transformOpen U) ∧
    (∀ Us : Set (T.X s), (ℜs.extendBy Bs).IsOpenRestriction Us → ∀ C : Subscheme (T.X s),
      (ℜs.extendBy Bs).IsPermissibleOpen Us C →
        (r.transformSucc (T.pre s)).IsPermissibleCenter ℜs C) ∧
    ((∀ x ∈ Bs.pts, (ℜs.extendBy Bs).ResolvedAt x) →
      (r.transformSucc (T.pre s)).IsPermissibleCenter ℜs Bs) :=
  by
  have hemp : (𝒮.removalFamily.datumII s a Jt).emptyIfBot = 𝒮.datumII s a Jt := hII.emptyIfBot_eq
  exact 𝒮.removalFamily.isPermissibleCenter_of_isPermissibleOpen_extendBy s hprep a Jt
    (𝒮.removalFamily.mul_prod_emptyIfBot_eq_jBarT s a Jt hII hJt)
    (by rw [hemp]; exact hII.isWeakDatum) Bt hBt hBti
    (by rw [hemp]; exact hperm)

/-! ## `dim B_s < n` (p. 310)

The abstract part is `Hironaka/Compat/CenterDimension.lean`; the glue uses Remarks 3, 4 and 5. -/

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

/-- **`dim B_s < n`** (p. 310): for a non-singular irreducible `B̃ ⊆ X̃` such that `f_B̃` is
permissible for `ℜ^{N-1}_II`, the reduced irreducible subscheme `B_s` of `X_s` (the closure of
`c_s(B̃)`) has dimension `n' = dim B_s < n = dim W`.

\textbf{Deviation from the paper (gap filled).} The paper applies "Theorem `I₂^{N,n'}` (with `n' <
n`)
to the resolution datum `(ℜ^{N,n'}_I(s), U_s)`" (p. 310) and does not prove `n' < n`.  Lean:
`B_s ⊆ W(s)` and `dim W(s) ≤ dim W = n` (Remark 1 of Ch. I, p. 169).  Closed case: `B_s ⊆ W(s) ∩
F(s)`
(Remark 5), `W(s) − F(s)` is dense in `W(s)` (`F(s)` is a closed restriction of `ℜ(s)`), so `B_s`
lies
in an irreducible component of `W(s)` which is not contained in `F(s)`, and the inclusion is strict:
dimension drops (`Subscheme.dim_lt_of_pts_subset_inter_of_subset_closure_diff`).  Open case:
`c_s(B̃)`
consists of unresolved points of `W(s)` (Remark 3, Lemma (AB.5) and Remark 1), but `ℜ^{N,n'}_I(s)`
is
resolved at the points of `U_s ⊇ c_s(B̃)` (Remark 4).  If `B_s` were an irreducible component of
`W(s)`,
`W(s)` would be normally flat along it at such a point (the datum `ℜ^{N,n'}_I(s)` has `W(s)` among
its
`V`'s), so `W(s) = B_s` near the point, and `ℜ(s)` would be resolved there, a contradiction
(`Subscheme.dim_lt_of_resolvedAt_extendBy_of_not_resolvedAt`); so `B_s` lies strictly in a component
of
`W(s)` and the dimension drops.

The dimension hypothesis `dim X̃ = N - 1` of the printed statement is not used by the proof and
is dropped in this generic statement (it is not derivable from the data alone,
`lem:IV.3-xtilde-ambient`). -/
@[blueprint "lem:IV.3-dim-Bs-lt"
  (statement := /-- Notation as in \cref{rem:IV.3-4}. If $f_{\tilde B}$ is permissible for
    $\mathfrak R^{N-1}_{\mathrm{II}}$ and $B_s$ is the reduced irreducible subscheme of $X_s$ with
    $c_s$ inducing an open immersion $\tilde B\to B_s$, then $n'=\dim B_s<n=\dim W$.
    (Used on p.~310: ``applying Theorem $\mathrm I_2^{N,n'}$ (with $n'<n$)''.) -/)
  (proof := /-- $B_s\subseteq W(s)$ and $\dim W(s)\le n$. In the closed case $B_s\subseteq W(s)\cap
    F(s)$ (Remark~5), and $W(s)-F(s)$ is dense in $W(s)$, so $B_s$ lies in a component of $W(s)$ not
    contained in $F(s)$: its dimension is smaller. In the open case, if $B_s$ were a component of
    $W(s)$, then at a point of $c_s(\tilde B)\subseteq U_s$ the datum $\mathfrak R^{N,n'}_{\mathrm
    I}(s)$
    is resolved (Remark~4), so $W(s)$ is normally flat along $B_s$ there and equals $B_s$ near the
    point, whence $\mathfrak R(s)$ is resolved there; but the points of $c_s(\tilde B)$ are in
    $S(\mathfrak R(s))$ (Remark~3).

    \textbf{Deviation from the paper (gap filled).} The paper does not prove $n'<n$. -/)
  (latexEnv := "lemma")]
theorem dim_Bs_lt [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hprep : PrepHyp N ℜ P r T x₀ s)
    (a : Fin (𝒮.eTilde s).1 → ℕ) (Jt : Subscheme (R.xTilde s))
    (hJt : Jt * ∏ j, (((R.datumII s a Jt).emptyIfBot).E j) ^ (a j) = R.jBarT s)
    (hII : ((R.datumII s a Jt).emptyIfBot).IsWeakDatum) (Bt : Subscheme (R.xTilde s))
    (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : ((R.datumII s a Jt).emptyIfBot).IsPermissible Bt) :
    (Subscheme.ofClosed ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩ :
      Subscheme (T.X s)).dim < ℜ.n := by
  classical
  have hgood : IsGoodDatumI N n X ℜ := ⟨hS.ambient, hS.isDatum, hS.dim_W.le⟩
  obtain ⟨hgoods, hfor⟩ := isGoodDatumI_transformI_and_isFor_transformSucc (T.pre s) hgood
    hS.isFor (hS.permissible s)
  obtain ⟨hamb, hℜs, hWs⟩ := hgoods
  have hAlg : IsAlgebraicScheme (T.X s) := hamb.1
  have := IsAlgebraicScheme.noetherianSpace (T.X s)
  have hirrBt : IsIrreducible Bt.pts := Subscheme.isIrreducible_pts Bt hBti
  set Bs : Subscheme (T.X s) :=
    Subscheme.ofClosed ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩ with hBs
  have hBspts : Bs.pts = closure ((R.cTilde s).base '' Bt.pts) := Subscheme.pts_ofClosed _
  have hBsirr : IsIrreducible Bs.pts := by
    rw [hBspts]
    exact (hirrBt.image _ (R.cTilde s).base.hom.continuous.continuousOn).closure
  have hn : ((T.pre s).transformI ℜ).W.dim ≤ ((n : ℕ) : WithBot ℕ∞) := hWs
  have hnn : ℜ.n = ((n : ℕ) : WithBot ℕ∞) := hS.dim_W
  rw [hnn]
  have hsub := hperm.2.1
  have hsubS : ∀ xt ∈ Bt.pts, xt ∈ ((R.datumII s a Jt).emptyIfBot).S := fun xt hx => (hsub hx).1
  have h3 := (R.mem_S_iff_le_nu_and_exists_isOpenImmersion_of_prepHyp s hprep a Jt hJt hII).2.1
  cases hr : r with
  | closed F =>
    have h5 := (R.isPermissibleCenter_of_isPermissibleOpen_extendBy s hprep a Jt hJt hII Bt hBt
      hBti hperm).1 F hr
    have hdense : ((T.pre s).transformI ℜ).W.pts ⊆
        closure (((T.pre s).transformI ℜ).W.pts \ ((T.pre s).strictTransform F).pts) := by
      have := hfor
      rw [hr] at this
      exact this.2.2
    exact Subscheme.dim_lt_of_pts_subset_inter_of_subset_closure_diff hBsirr
      (fun x hx => (h5 hx).1) (fun x hx => (h5 hx).2) hdense hn
  | opn U =>
    obtain ⟨hBsC, Us, -, -, hcUs, hresUs⟩ :=
      R.isContainedIn_W_and_resolvedAt_extendBy_of_isPermissible s hprep a Jt hJt hII Bt hBt
        hBti hperm
    obtain ⟨xt, hxt⟩ := hirrBt.nonempty
    have hx := hresUs _ (hcUs ⟨xt, hxt, rfl⟩)
    have hxBs : (R.cTilde s).base xt ∈ Bs.pts := by
      rw [hBspts]; exact subset_closure ⟨xt, hxt, rfl⟩
    have hnres : ¬ ((T.pre s).transformI ℜ).ResolvedAt ((R.cTilde s).base xt) := by
      have h' : (R.cTilde s).base xt ∈ S ((T.pre s).transformI ℜ) (r.transformSucc (T.pre s)) :=
        (h3 ⟨xt, hsubS xt hxt, rfl⟩).1
      have heq : r.transformSucc (T.pre s) = .opn ((T.pre s).transformOpen U) := by
        rw [hr]; rfl
      rw [heq] at h'
      exact h'.2
    have hBsC' : Bs.IsContainedIn ((T.pre s).transformI ℜ).W := by
      rw [MonoidalSuccession.transformI_W]; exact hBsC
    exact Subscheme.dim_lt_of_resolvedAt_extendBy_of_not_resolvedAt hamb.2.1 hℜs
      (Subscheme.ofClosed_isReduced _) (Subscheme.isIrreducible_of_pts _ hBsirr) hBsC' hxBs hx
      hnres hn

end Frame.RemovalFamily

end AB

end

end Hironaka
