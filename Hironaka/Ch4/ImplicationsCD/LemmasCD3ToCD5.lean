/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch4.ImplicationsCD.LemmasD1AndD2
public import Hironaka.Statements

/-!
# Ch. IV §4 (pp. 315–320): Lemmas (CD.3), (CD.4) and (CD.5)

Lemma (CD.3) (p. 315), Lemma (CD.4) with the frame-transform induction of its proof (pp. 316–318), and
Lemma (CD.5) (pp. 318–320).

This is part 2 of 3 of `Hironaka.Ch4.ImplicationsCD`, which imports all parts; its description holds the
notation and the formalization notes for the whole section.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits

namespace Hironaka

universe u

noncomputable section

namespace CD

variable {X : Scheme.{u}}

variable {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ} {T : AB.Tower X} {x₀ : X}

/-! ## Lemmas (CD.3), (CD.4), the Corollary of (CD.4) and (CD.5) (pp. 315–320) -/

/-- A scheme isomorphic to an irreducible scheme is irreducible. -/
theorem irreducibleSpace_of_iso {A B : Scheme.{u}} (e : A ≅ B) [IrreducibleSpace B] :
    IrreducibleSpace A := by
  have hsurj : Function.Surjective e.inv := fun a => ⟨e.hom a, by
    rw [← Scheme.Hom.comp_apply, CategoryTheory.Iso.hom_inv_id]
    rfl⟩
  rw [irreducibleSpace_def]
  have := (IrreducibleSpace.isIrreducible_univ B).image e.inv e.inv.continuous.continuousOn
  rwa [Set.image_univ, hsurj.range_eq] at this

theorem Restriction.IsPermissibleSucc.isPermissibleII {Y : Scheme.{u}} {r : Restriction X}
    {g : MonoidalSuccession X Y} {ℜ : DatumII.Raw X} (h : r.IsPermissibleSucc g ℜ) :
    g.IsPermissibleII ℜ := by
  cases r with
  | unrestricted => exact h
  | closed F => exact MonoidalSuccession.IsPermissibleIIClosed.isPermissibleII h

theorem Restriction.isPermissibleCenter_of_isPermissibleSucc_snoc {Y : Scheme.{u}}
    (r : Restriction X) (g : MonoidalSuccession X Y) {B : Subscheme Y}
    (t : MonoidalTransformation Y B) (ℜ : DatumII.Raw X)
    (h : r.IsPermissibleSucc (g.snoc B t) ℜ) :
    (r.transformSucc g).IsPermissibleCenter (g.transformII ℜ) B := by
  cases r with
  | unrestricted =>
    exact ((MonoidalSuccession.isPermissibleII_snoc_iff g B t ℜ).mp h).2
  | closed F =>
    have h' : (g.append (MonoidalSuccession.cons B t (MonoidalSuccession.nil
      t.X'))).IsPermissibleIIClosed
        ℜ F := by
      rw [← MonoidalSuccession.snoc_eq_append]; exact h
    have := ((MonoidalSuccession.isPermissibleIIClosed_append _ _ ℜ F).mp h').2
    exact this.1

/-- **Lemma (CD.3)** (pp. 315–316).  "`ĥ_s(B̂) = x̂_0`" is `ĥ_s(B̂) = {x̂_0}`; "`c_s` induces an
isomorphism `B̂ → B`" is an isomorphism of the subschemes compatible with `c_s`. -/
theorem Standing.isPermissibleCenter_B (hS : Standing N ℜ r ν T x₀) (t : ℕ) :
    (restriction T r t).IsPermissibleCenter (datum T ℜ t) (T.B t) :=
  Restriction.isPermissibleCenter_of_isPermissibleSucc_snoc r (T.pre t) (T.monoidalTransformation t)
    ℜ (hS.permissible (t + 1))

/-- The centers `B_s` of the standing succession are non-singular (Def. 6, p. 167). -/
theorem Standing.isNonsingular_B (hS : Standing N ℜ r ν T x₀) (t : ℕ) :
    (T.B t).IsNonsingular := by
  have h := hS.isPermissibleCenter_B t
  generalize restriction T r t = R at h
  cases R with
  | unrestricted => exact h.1.isNonsingular
  | closed F => exact h.1.1.isNonsingular

/-- The schemes `X_s` of the standing succession are non-singular (p. 142). -/
theorem Standing.isNonsingular_X (hS : Standing N ℜ r ν T x₀) : ∀ s, (T.X s).IsNonsingular
  | 0 => hS.ambient.2.1
  | s + 1 => ((T.monoidalTransformation s).isNonsingular_and_isNonsingular_exceptional
      (hS.isNonsingular_X s) (hS.isNonsingular_B s)).1

/-- `x_0` is a closed point of `X` (`dim_{x_0} X = N = dim X`). -/
theorem Standing.isClosed_singleton (hS : Standing N ℜ r ν T x₀) : IsClosed ({x₀} : Set X) := by
  refine closure_subset_iff_isClosed.mp fun y hy => ?_
  have hsp : x₀ ⤳ y := specializes_iff_mem_closure.mpr hy
  by_contra hne
  have h1 := LocSucc.dimAt_add_one_le_of_specializes hsp (Ne.symm hne)
  have h2 := LocSucc.dimAt_le_dim y
  rw [hS.dimAt_x₀] at h1
  rw [hS.ambient.2.2.2] at h2
  have h3 : ((N + 1 : ℕ) : WithBot ℕ∞) ≤ (N : WithBot ℕ∞) := by
    have := h1.trans h2
    exact_mod_cast this
  have h4 : N + 1 ≤ N := by exact_mod_cast h3
  omega

@[blueprint "lem:IV.CD-3"
  (statement := /-- \textbf{Lemma (CD.3).} Notation as in \cref{def:IV.4-standing},
    \cref{def:IV.4-frame}. Let $h_s$ (resp.\ $\hat h_s$) denote the succession of the monoidal
    transformations $f_t$ (resp.\ $\hat f_t$) for $0\le t\le s-1$. Then the canonical morphism
    $c_s$ induces a bijection of the point sets: $\hat h_s^{-1}(\hat x_0)\to h_s^{-1}(x_0)$ (the
    paper prints $\bar h_s^{-1}(\hat x_0)$ [sic]), and, if $\hat x\in\hat h_s^{-1}(\hat x_0)$ and
    $x=c_s(\hat x)\in h_s^{-1}(x_0)$, then the local homomorphism of the local ring of $X_s$ at
    $x$ into that of $\hat X_s$ at $\hat x$, induced by $c_s$, transforms a regular system of
    parameters into such a system of parameters (\cref{def:III.rsop-map}). Moreover, if
    $\hat B$ is any irreducible subscheme of $\hat X_s$ such that [sic: ``that that'']
    $\hat h_s(\hat B)=\hat x_0$, there exists a unique irreducible subscheme $B$ of $X_s$ such
    that $\hat B=c_s^{-1}(B)$, that $B=c_s(\hat B)$ and that $c_s$ induces an isomorphism
    $\hat B\to B$. (pp.~315--316.)

    \textbf{Deviation from the paper (gap filled).} ``As in the previous section'' covers only reduced
    $\hat B$ (the Corollary of (AB.3)); the non-reduced case, as printed, is proved in
    \cref{lem:IV.CD-3-as-printed-irreducible} through the powers of $\hat M\hat S_s$ and the faithful
    flatness of $S_s\to\hat S_s$.

    \textbf{Deviation from the paper (gap filled).} The paper gives no proof beyond ``as in the
    previous section''; Lean derives the lemma from \cref{lem:IV.AB-2} and \cref{cor:IV.AB-3} for the
    completion datum.

    \textbf{Paper misprint.} The paper prints $\bar h_s^{-1}(\hat x_0)$ for
    $\hat h_s^{-1}(\hat x_0)$ (p.~315). -/)
  (proof := /-- ``Here we remark, as in the previous section, the following fact'' (p.~315):
    the proof is that of Lemma (AB.2) and of the Corollary of Lemma (AB.3) in \S3
    (\cref{lem:IV.AB-2}, \cref{cor:IV.AB-3}), which only use the succession $\{f_s\}$, the point
    $x_0$ and the completion: by induction on $s$, via Lemma~4, \S2, Ch.~III and its
    corollaries, the monoidal transforms of $\hat S_s$ lying over a point of the fibre
    correspond to those of $S_s$ with the same residue fields, the canonical homomorphisms
    transforming regular systems of parameters into such systems; and
    $S_s/M_0S_s\simeq\hat S_s/\hat M_0\hat S_s$ identifies the reduced subschemes lying over
    $\hat x_0$ and over $x_0$. -/)
  (proofUses := ["lem:IV.AB-2", "cor:IV.AB-3"])
  (latexEnv := "lemma")]
theorem Standing.bijOn_and_mapsRSOP_and_exists_unique_totalTransform (hS : Standing N ℜ r ν T x₀) (𝒞 : AB.Completion T x₀) (s : ℕ) :
    Set.BijOn (𝒞.c s).base ((𝒞.tHat.pre s).composite.base ⁻¹' {hS.xh})
      ((T.pre s).composite.base ⁻¹' {x₀}) ∧
    (∀ xh ∈ (𝒞.tHat.pre s).composite.base ⁻¹' {hS.xh},
      RingHom.MapsRSOP ((𝒞.c s).stalkMap xh).hom) ∧
    ∀ Bh : Subscheme (𝒞.tHat.X s), Bh.IsIrreducible →
      (𝒞.tHat.pre s).composite.base '' Bh.pts = {hS.xh} →
      ∃ B : Subscheme (T.X s),
        (B.IsIrreducible ∧ Bh = Subscheme.totalTransform (𝒞.c s) B ∧
          B.pts = (𝒞.c s).base '' Bh.pts ∧
          ∃ e : Bh.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bh.ι ≫ 𝒞.c s) ∧
        ∀ B' : Subscheme (T.X s), B'.IsIrreducible →
          Bh = Subscheme.totalTransform (𝒞.c s) B' → B'.pts = (𝒞.c s).base '' Bh.pts →
          (∃ e : Bh.toScheme ≅ B'.toScheme, e.hom ≫ B'.ι = Bh.ι ≫ 𝒞.c s) → B' = B := by
  have hx := hS.ambient.2.1 x₀
  refine ⟨𝒞.bijOn_c_of_isNonsingular hx hS.isNonsingular_X hS.isNonsingular_B s, fun xh hxh =>
    (𝒞.isRegularLocalRing_and_mapsRSOP_stalkMap hx hS.isNonsingular_X hS.isNonsingular_B s xh
      hxh).2.1, ?_⟩
  intro Bh hirr himg
  exact 𝒞.exists_unique_irreducible_totalTransform hx hS.isNonsingular_X hS.isNonsingular_B
    hS.isClosed_singleton s Bh hirr himg

/-- The empty strict transform: if `V ⊆ B` then the strict transform of `V` is empty
(p. 167: the strict transform is the closure of `f⁻¹(V ∖ B)`). -/
theorem pts_strictTransform_eq_empty_of_subset {Y : Scheme.{u}} {B : Subscheme Y}
    (t : MonoidalTransformation Y B) (V : Subscheme Y) (h : V.pts ⊆ B.pts) :
    (Subscheme.strictTransform t V).pts = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  obtain ⟨q, hq, hqE, -⟩ := t.exists_generization_notMem_exceptional V hp
  apply hqE
  rw [t.pts_exceptional]
  exact h (t.pts_strictTransform_subset V hq)

/-- The strict transform of a reduced subscheme `V` of a non-singular scheme is reduced: the ideal
sheaf of the strict transform is the largest one agreeing with `f⁻¹(V)` off the exceptional
divisor, where `f` is a local isomorphism and `f⁻¹(V)` is reduced; hence it equals its radical.

Deviation from the paper (gap filled): the paper (p. 316) states it without proof. -/
theorem _root_.Hironaka.MonoidalTransformation.isReduced_strictTransform {X : Scheme.{u}} {B : Subscheme X}
    (hX : X.IsNonsingular) (t : MonoidalTransformation X B) (V : Subscheme X)
    (hV : V.IsReduced) : (Subscheme.strictTransform t V).IsReduced := by
  set D := Subscheme.strictTransform t V with hD
  have hle : D ≤ Scheme.IdealSheafData.radical D := by
    intro U
    exact Ideal.le_radical
  have hmem : Scheme.IdealSheafData.radical D ∈
      {V' : Subscheme t.X' | ∀ x' : t.X', x' ∉ t.exceptional.pts →
        V'.stalkIdeal x' = (Subscheme.totalTransform t.f V).stalkIdeal x'} := by
    intro x' hx'
    have hfx : t.f.base x' ∉ B.pts := fun h => hx' (by rw [t.pts_exceptional]; exact h)
    have : IsRegularLocalRing (X.presheaf.stalk (t.f.base x')) := hX _
    have hbij := _root_.Hironaka.MonoidalTransformation.bijective_stalkMap_of_notMem t x' hfx
    have hDx : D.stalkIdeal x' = (Subscheme.totalTransform t.f V).stalkIdeal x' :=
      _root_.Hironaka.MonoidalTransformation.strictTransform_stalkIdeal_of_notMem t V hx'
    have hrad : ((Subscheme.totalTransform t.f V).stalkIdeal x').IsRadical := by
      rw [stalkIdeal_totalTransform]
      have h1 := Subscheme.isRadical_stalkIdeal_of_isReduced hV (t.f.base x')
      have hsurj : Function.Surjective (t.f.stalkMap x').hom := hbij.2
      have hker : RingHom.ker (t.f.stalkMap x').hom ≤ V.stalkIdeal (t.f.base x') := by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp hbij.1]; exact bot_le
      have h2 := Ideal.map_radical_of_surjective hsurj hker
      rw [h1.radical] at h2
      exact Ideal.radical_eq_iff.mp h2.symm
    apply le_antisymm
    · calc Subscheme.stalkIdeal (Scheme.IdealSheafData.radical D) x' ≤ (D.stalkIdeal x').radical :=
            AB.stalkIdeal_radical_le D x'
        _ = D.stalkIdeal x' := by rw [hDx]; exact hrad.radical
        _ = _ := hDx
    · rw [← hDx]
      exact Subscheme.stalkIdeal_mono hle x'
  have h2 : Scheme.IdealSheafData.radical D ≤ D := le_sSup hmem
  exact Subscheme.isReduced_of_radical_eq D (le_antisymm h2 hle)

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- `X̄_0 = Spec(Ŝ_0/(z_0))` has dimension `N - 1` and `(z_0)` is prime (`z_0` is a member of a
regular system of parameters of the regular local ring `Ŝ_0` of dimension `N`). -/
theorem isPrime_span_z_and_ringKrullDim_quotient :
    (Ideal.span {𝒮.z}).IsPrime ∧
      ringKrullDim (AB.Shat X x₀ ⧸ Ideal.span {𝒮.z}) = ((N - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  have := 𝒮.regShat
  obtain ⟨Fr, h1, hz, hF, ⟨kk, hkk, y, e, hc, hy, hrsop⟩, -⟩ := 𝒮.frame
  have hzmem : 𝒮.z ∈ insert 𝒮.z (Finset.image (fun i => algebraMap Fr.S (AB.Shat X x₀) (y i))
      Finset.univ) := Finset.mem_insert_self _ _
  have hzM : 𝒮.z ∈ maximalIdeal (AB.Shat X x₀) := hrsop.1 ▸ Ideal.subset_span hzmem
  have : IsLocalRing (AB.Shat X x₀ ⧸ Ideal.span {𝒮.z}) :=
    isLocalRing_quotient_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hzM)
  obtain ⟨hQ, hQrsop, hinj⟩ :=
    hrsop.isRegularLocalRing_and_isRegularSystemOfParameters_quotient_span_singleton hzmem
  refine ⟨?_, ?_⟩
  · have := isDomain_of_isRegularLocalRing (AB.Shat X x₀ ⧸ Ideal.span {𝒮.z})
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  · rw [← hQrsop.2, Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hzmem]
    have := hrsop.2
    rw [hS.ringKrullDim_shat] at this
    have hc : (insert 𝒮.z (Finset.image (fun i => algebraMap Fr.S (AB.Shat X x₀) (y i))
        Finset.univ)).card = N := by exact_mod_cast this
    rw [hc]

/-- p. 316: "`X̄_0 = Spec(T̄_0)` is a non-singular irreducible subscheme of `X̂_0` of codimension 1" (stated without proof): `X̄_0 = V(z_0)`, `z_0` a member of a regular system of parameters of the regular local ring `Ŝ_0`, so `Ŝ_0/(z_0)` is regular (hence a domain); the local rings of `V(z_0)` are the localizations of `Ŝ_0/(z_0)` (Serre, cited leaf).

Deviation from the paper (gap filled): the paper states it without proof. -/
theorem xBar_zero_facts [Hironaka.HironakaCitedResults.{u}] :
    (𝒮.xBar 0).IsNonsingular ∧ (𝒮.xBar 0).IsIrreducible ∧ (𝒮.xBar 0).codim = 1 := by
  classical
  have hreg0 := 𝒮.regShat
  obtain ⟨Fr, h1, hz, hF, ⟨kk, hkk, y, e, hc, hy, hrsop⟩, -⟩ := 𝒮.frame
  have hzmem : 𝒮.z ∈ insert 𝒮.z (Finset.image (fun i => algebraMap Fr.S (AB.Shat X x₀) (y i))
      Finset.univ) := Finset.mem_insert_self _ _
  have hzM : 𝒮.z ∈ maximalIdeal (AB.Shat X x₀) := hrsop.1 ▸ Ideal.subset_span hzmem
  have hext : ExtendsToRSOP (AB.Shat X x₀) {𝒮.z} :=
    ⟨_, Finset.singleton_subset_iff.mpr hzmem, hrsop⟩
  have hreg : IsRegularLocalRing (AB.Shat X x₀ ⧸ Ideal.span {𝒮.z}) :=
    hext.isRegularLocalRing_quotient_span_singleton (Finset.mem_singleton_self _)
  have hz0 : 𝒮.z ≠ 0 := hext.ne_zero (Finset.mem_singleton_self _)
  have hprime := (𝒮.isPrime_span_z_and_ringKrullDim_quotient).1
  have : (Ideal.span {𝒮.z}).IsPrime := hprime
  have : IsRegularLocalRing (CommRingCat.of (AB.Shat X x₀)) := hreg0
  have : IsRegularLocalRing (CommRingCat.of (AB.Shat X x₀) ⧸ Ideal.span {𝒮.z}) := hreg
  have : IsDomain (AB.Shat X x₀) := isDomain_of_isRegularLocalRing _
  have hh : (Ideal.span {𝒮.z}).height = 1 := by
    refine Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hz0) ?_
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).mp hzM hu
  have hns := isNonsingular_ofIdealTop_spec (CommRingCat.of (AB.Shat X x₀)) (Ideal.span {𝒮.z})
  have hic := isIrreducible_and_codim_ofIdealTop_spec (CommRingCat.of (AB.Shat X x₀))
    (Ideal.span {𝒮.z}) hh
  exact ⟨hns, hic.1, hic.2⟩

/-- p. 316: "`X̄_s` is an irreducible subscheme" (stated without proof): the strict transform of the irreducible `X̄_0` along a monoidal transformation is irreducible, or empty when `X̄_s ⊆ B̂_s` (agreement of p. 163).

Deviation from the paper (gap filled): proved by induction on `s` (`strictTransform_isIrreducible`). -/
theorem xBar_pts_eq_empty_or_isIrreducible [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    (𝒮.xBar s).pts = ∅ ∨ (𝒮.xBar s).IsIrreducible := by
  induction s with
  | zero => exact Or.inr 𝒮.xBar_zero_facts.2.1
  | succ s ih =>
    by_cases hsub : (𝒮.xBar s).pts ⊆ (𝒮.tHat.B s).pts
    · left
      exact pts_strictTransform_eq_empty_of_subset (𝒮.tHat.monoidalTransformation s) (𝒮.xBar s) hsub
    · right
      have hirr : (𝒮.xBar s).IsIrreducible :=
        ih.resolve_left (fun h => hsub (h ▸ Set.empty_subset _))
      exact MonoidalTransformation.strictTransform_isIrreducible
        (𝒮.tHat.monoidalTransformation s) (𝒮.xBar s) hirr hsub

/-- `f̄_s` is the map induced by `f̂_s` on strict transforms (`ι ∘ f̄_s = f̂_s ∘ ι` and `ι` is a monomorphism). -/
theorem fBar_eq_strictTransformMap (s : ℕ) :
    𝒮.fBar s = (𝒮.tHat.monoidalTransformation s).strictTransformMap (𝒮.xBar s) := by
  exact (cancel_mono (𝒮.xBar s).ι).mp
    ((𝒮.fBar_comm s).trans (MonoidalTransformation.strictTransformMap_ι _ _).symm)

/-- p. 316: "if `B̂_s` is contained in `X̄_s`, `f̄_s` is obtained by the monoidal transformation of `X̄_s` with the center `B̂_s`" (stated without proof; (a), (b) of p. 167).  Needs no irreducibility of the center.

Deviation from the paper (gap filled): `nonempty_monoidalTransformation_strictTransform`. -/
theorem isMonoidalTransformationOf_fBar [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    AB.IsMonoidalTransformationOf (𝒮.fBar s) (𝒮.bBarOn s) := by
  rw [fBar_eq_strictTransformMap]
  exact (𝒮.tHat.monoidalTransformation s).isMonoidalTransformationOf_strictTransformMap (𝒮.xBar s)

/-- p. 316: "if moreover `X̄_s` is non-singular and irreducible, then `X̄_{s+1}` is non-singular and `P̄_{s+1}` is a sheaf of invertible ideals" (stated without proof): a monoidal transform of a non-singular scheme with a non-singular center (`B̂_s ⊆ X̄_s`, so the center is isomorphic to `B̂_s`) is non-singular with invertible exceptional ideal; `P̄_{s+1}` is that ideal (`pBar_eq`).

Deviation from the paper (gap filled): the paper states it without proof. -/
theorem isNonsingular_xBar_succ_and_isInvertibleIdeal_pBar [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hc : 𝒮.IsCenterContained s)
    (h : 𝒮.IsNonsingIrred s) : (𝒮.xBar (s + 1)).IsNonsingular ∧ (𝒮.pBar s).IsInvertibleIdeal := by
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨s'⟩, hs⟩ := Subscheme.nonempty_monoidalTransformation_strictTransform
      (𝒮.tHat.monoidalTransformation s) (𝒮.xBar s)
    obtain ⟨e, -⟩ := hs s'
    have hBns : (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s)).IsNonsingular := by
      obtain ⟨e2⟩ := nonempty_totalTransform_iso_of_isContainedIn hc
      exact isNonsingular_of_iso e2 (𝒮.toCompletion.isNonsingular_B (hS.ambient.2.1 x₀)
        hS.isNonsingular_X hS.isNonsingular_B s)
    have hX' := (s'.isNonsingular_and_isNonsingular_exceptional h.1 hBns).1
    exact isNonsingular_of_iso e.symm hX'
  · rw [𝒮.pBar_eq s]
    exact (𝒮.isMonoidalTransformationOf_fBar s).1

/-- p. 316: "`X̄_s` is a reduced subscheme" (stated without proof): `X̄_0` is non-singular, hence reduced, and the
strict transform of a reduced subscheme of a non-singular scheme is reduced
(`MonoidalTransformation.isReduced_strictTransform`).

Deviation from the paper (gap filled): the paper states it without proof. -/
theorem isReduced_xBar [Hironaka.HironakaCitedResults.{u}] (s : ℕ) : (𝒮.xBar s).IsReduced := by
  induction s with
  | zero => exact DatumTransform.isReduced_of_isNonsingular 𝒮.xBar_zero_facts.1
  | succ s ih =>
    exact MonoidalTransformation.isReduced_strictTransform
      (𝒮.toCompletion.isNonsingular_tHat (hS.ambient.2.1 x₀) hS.isNonsingular_X
        hS.isNonsingular_B s)
      (𝒮.tHat.monoidalTransformation s) (𝒮.xBar s) ih

/-- The facts asserted on p. 316 in the course of the construction.  Formalization note: "an
irreducible reduced subscheme" is read with the agreement of p. 163 that the empty subscheme
counts as irreducible (the strict transform `X̄_{s+1}` is empty when `B̂_s ⊇ X̄_s`). -/
@[blueprint "lem:IV.4-construction-facts"
  (statement := /-- In the construction of \cref{def:IV.4-frame} and \cref{def:IV.4-construction}:
    $\bar X_0=\operatorname{Spec}(\bar T_0)$ is a non-singular irreducible subscheme of
    $\hat X_0$ of codimension $1$; $\bar X_s$ is an irreducible reduced subscheme of $\hat X_s$
    for every $s\ge0$; if $\hat B_s$ is contained in $\bar X_s$, then the morphism
    $\bar f_s\colon\bar X_{s+1}\to\bar X_s$ is obtained by the monoidal transformation of
    $\bar X_s$ with the center $\hat B_s$ (\cref{def:monoidal-transformation}); and if moreover
    $\bar X_s$ is non-singular and irreducible, then $\bar X_{s+1}$ is non-singular and
    $\bar P_{s+1}$ is a sheaf of invertible ideals. (p.~316.) (Formalization note (encoding):
    ``irreducible'' for $\bar X_s$, $s>0$, allows the empty subscheme, by the agreement of
    p.~163.) -/)
  (proof := /-- $\bar X_0=V(z_0)$ with $z_0$ a member of a regular system of parameters of the
    regular local ring $\hat S_0$, so $\bar T_0$ is regular of dimension $N-1$; $\bar X_s$ is the
    strict transform of the reduced irreducible $\bar X_0$ (\cref{def:strict-transform}). If
    $\hat B_s\subseteq\bar X_s$, the strict transform of $\bar X_s$ by the monoidal
    transformation $\hat f_s$ with center $\hat B_s$ is the monoidal transform of $\bar X_s$ with
    center $\hat B_s$ ((a), (b) of p.~167, \cref{lem:strict-transform-is-blowup}); a monoidal
    transform of a non-singular scheme with non-singular center is non-singular, with invertible
    exceptional ideal (\cref{lem:monoidal-transformation-nonsingular}), and $\bar P_{s+1}$ is
    that ideal (\cref{lem:IV.4-Pbar}).

    \textbf{Deviation from the paper (gap filled).} The four claims of p.~316, each stated
    without proof, are proved: (1) $\bar X_0=V(z_0)$ is non-singular (its local rings are the
    localizations of the regular local ring $\hat S_0/(z_0)$, Serre), irreducible ($(z_0)$ is prime)
    and of codimension $1$ (Krull's principal ideal theorem); (2) every $\bar X_s$ is reduced (the
    strict transform is the largest ideal sheaf agreeing with $\hat f_s^{-1}(\bar X_s)$ off the
    exceptional divisor, where $\hat f_s$ is a local isomorphism) and irreducible or empty (induction
    on $s$); (3) $\bar f_s$ is the monoidal transformation of $\bar X_s$ with center $\hat B_s$
    (\cref{lem:strict-transform-is-blowup}); (4) $\bar X_{s+1}$ is non-singular and $\bar P_{s+1}$
    invertible when $\bar X_s$ is non-singular and irreducible and $\hat B_s\subseteq\bar X_s$ (the
    center is isomorphic to the non-singular $\hat B_s$). No irreducibility of $\hat B_s$ is needed:
    the universal property of a monoidal transformation does not ask for an irreducible center. -/)
  (proofUses := ["lem:strict-transform-is-blowup", "lem:monoidal-transformation-nonsingular",
    "lem:IV.4-Pbar"])
  (latexEnv := "lemma")]
theorem isNonsingular_xBar_zero_and_isMonoidalTransformationOf_fBar [Hironaka.HironakaCitedResults.{u}] :
    ((𝒮.xBar 0).IsNonsingular ∧ (𝒮.xBar 0).IsIrreducible ∧ (𝒮.xBar 0).codim = 1) ∧
    (∀ s, (𝒮.xBar s).IsReduced ∧ ((𝒮.xBar s).pts = ∅ ∨ (𝒮.xBar s).IsIrreducible)) ∧
    ∀ s, 𝒮.IsCenterContained s →
      AB.IsMonoidalTransformationOf (𝒮.fBar s) (𝒮.bBarOn s) ∧
      (𝒮.IsNonsingIrred s → (𝒮.xBar (s + 1)).IsNonsingular ∧ (𝒮.pBar s).IsInvertibleIdeal) :=
  ⟨𝒮.xBar_zero_facts, fun s => ⟨𝒮.isReduced_xBar s, 𝒮.xBar_pts_eq_empty_or_isIrreducible s⟩,
    fun s hc => ⟨𝒮.isMonoidalTransformationOf_fBar s,
      fun h => 𝒮.isNonsingular_xBar_succ_and_isInvertibleIdeal_pBar s hc h⟩⟩

end Frame

/-! ### Lemma (CD.4): the frame-transform induction (pp. 316–318) -/

/-- `ν(ℜ(t)) ≤ ν` (non-increase of `ν` under permissible transformations). -/
theorem Standing.nu_datum_le [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) (t : ℕ) : (datum T ℜ t).nu ≤ ν := by
  have := hS.ambient.1
  have := MonoidalSuccession.nu_transformII_le (T.pre t) hS.ambient.2.1 ℜ hS.isDatum
    (hS.permissible t).isPermissibleII
  exact hS.nu_eq_II ▸ this

/-- `B_t ⊆ S*(ℜ(t))` (permissibility of the center `B_t`, p. 318). -/
theorem Standing.pts_B_subset_sStar (hS : Standing N ℜ r ν T x₀) (t : ℕ) :
    (T.B t).pts ⊆ (datum T ℜ t).sStar := by
  have h := hS.isPermissibleCenter_B t
  generalize restriction T r t = R at h
  intro x hx
  cases R with
  | unrestricted => exact h.2.1 hx
  | closed F => exact h.1.2.1 hx

/-- `ν(ℜ(t)) = ν` as soon as `S_ν(ℜ(t))` is non-empty (`ν(ℜ(t)) ≤ ν(ℜ) = ν` by stability of `ν`
under permissible transformations, and `S_ν(ℜ(t)) ≠ ∅` gives `≥`). -/
theorem Standing.nu_datum_eq [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) (t : ℕ)
    (hne : (sNu (datum T ℜ t) (restriction T r t) ν).Nonempty) : (datum T ℜ t).nu = ν := by
  have := hS.ambient.1
  have hle : (datum T ℜ t).nu ≤ ν := by
    have := MonoidalSuccession.nu_transformII_le (T.pre t) hS.ambient.2.1 ℜ hS.isDatum
      (hS.permissible t).isPermissibleII
    exact hS.nu_eq_II ▸ this
  refine le_antisymm hle ?_
  obtain ⟨y, hy⟩ := hne
  obtain ⟨hyS, hyν⟩ := (mem_Snu_iff _ _ _ _).mp hy
  have hyS' : y ∈ (datum T ℜ t).S := by
    cases hR : restriction T r t with
    | unrestricted => rw [hR] at hyS; exact hyS
    | closed F => rw [hR] at hyS; exact hyS.1
  exact hyν.trans (le_iSup₂ (f := fun x (_ : x ∈ (datum T ℜ t).S) => (datum T ℜ t).nuAt x) y hyS')

/-- `B_t ⊆ S_ν(ℜ(t))` (p. 318: "since `B_t` is contained in `S_ν(h_t^*(ℜ))`"). -/
theorem Standing.pts_B_subset_sNu [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) (t : ℕ)
    (hne : (sNu (datum T ℜ t) (restriction T r t) ν).Nonempty) :
    (T.B t).pts ⊆ sNu (datum T ℜ t) (restriction T r t) ν := by
  have h := hS.isPermissibleCenter_B t
  have hν := hS.nu_datum_eq t hne
  generalize restriction T r t = R at h hne ⊢
  intro x hx
  cases R with
  | unrestricted =>
    have := h.2.1 hx
    rw [DatumII.Raw.sStar, hν] at this
    exact this
  | closed F =>
    have := h.1.2.1 hx
    rw [DatumII.Raw.sStar, hν] at this
    exact ⟨this, h.2 hx⟩

/-- `f_t(S_ν(ℜ(t+1))) ⊆ S_ν(ℜ(t))` (p. 317: "`x'_t ∈ S_ν(h_t^*(ℜ))` for all `t`"). -/
theorem Standing.f_mem_sNu [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) (t : ℕ) {y : T.X (t + 1)}
    (hy : y ∈ sNu (datum T ℜ (t + 1)) (restriction T r (t + 1)) ν) :
    (T.f t).base y ∈ sNu (datum T ℜ t) (restriction T r t) ν := by
  have hXa := hS.ambient.1
  obtain ⟨hY, hd⟩ := (T.pre t).isAmbient_transformII hS.ambient ℜ hS.isDatum
    (hS.permissible t).isPermissibleII
  have := hY.1
  have hP := hS.isPermissibleCenter_B t
  have hdat : datum T ℜ (t + 1) = (datum T ℜ t).transform (T.monoidalTransformation t) :=
    MonoidalSuccession.transformII_snoc (T.pre t) (T.B t) (T.monoidalTransformation t) ℜ
  have key : ∀ {c : ℕ∞} {y : T.X (t + 1)}, y ∈ (datum T ℜ (t + 1)).sNu c →
      (T.f t).base y ∈ (datum T ℜ t).sNu c := by
    intro c y hy
    have hPII : (datum T ℜ t).IsPermissible (T.B t) := by
      cases hR : restriction T r t with
      | unrestricted => rw [hR] at hP; exact hP
      | closed F => rw [hR] at hP; exact hP.1
    let e : MonoidalSuccession (T.X t) (T.X (t + 1)) :=
      MonoidalSuccession.cons (T.B t) (T.monoidalTransformation t) (MonoidalSuccession.nil _)
    have he : e.IsPermissibleII (datum T ℜ t) := ⟨hPII, trivial⟩
    have h1 : y ∈ (e.transformII (datum T ℜ t)).sNu c := by
      have : datum T ℜ (t + 1) = e.transformII (datum T ℜ t) := hdat
      rw [this] at hy
      exact hy
    have h2 := MonoidalSuccession.mem_sNu_of_mem_sNu_transformII e hY.2.1 _ hd he h1
    exact h2
  have hR : restriction T r (t + 1) = Restriction.transformSucc
      (restriction T r t) (MonoidalSuccession.cons (T.B t) (T.monoidalTransformation t)
        (MonoidalSuccession.nil _)) := by
    cases r with
    | unrestricted => rfl
    | closed F =>
      simp only [restriction, Restriction.transformSucc]
      exact congrArg Restriction.closed (MonoidalSuccession.strictTransform_snoc (T.pre t) (T.B t)
        (T.monoidalTransformation t) F)
  generalize restriction T r t = R at hR hy ⊢
  rw [hR] at hy
  cases R with
  | unrestricted => exact key hy
  | closed F =>
    refine ⟨key hy.1, ?_⟩
    have := T.monoidalTransformation t |>.pts_strictTransform_subset F hy.2
    exact this

/-- `S_ν(ℜ(s)) ≠ ∅` implies `S_ν(ℜ(t)) ≠ ∅` for `t ≤ s` (`f_t(S_ν(ℜ(t+1))) ⊆ S_ν(ℜ(t))`). -/
theorem Standing.sNu_nonempty_of_le [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) {t s : ℕ} (hts : t ≤ s)
    (hne : (sNu (datum T ℜ s) (restriction T r s) ν).Nonempty) :
    (sNu (datum T ℜ t) (restriction T r t) ν).Nonempty := by
  induction s, hts using Nat.le_induction with
  | base => exact hne
  | succ s _ ih =>
    obtain ⟨y, hy⟩ := hne
    exact ih ⟨_, hS.f_mem_sNu s hy⟩

/-- Ring level, p. 317–318: if `f = z^ν + g₁ z^{ν-1} + g₂ z^{ν-2} + ⋯ + g_ν` (`g_i ∈ S`, `g₁ = 0`)
has order `≥ ν` in `R_Q` for a prime `Q` of `R`, then `z ∈ Q` (Lemma 22, §10, Ch. III). -/
theorem frame_z_mem_of_ordElem_ge [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) (hr : F.r = 1) [CharZero (ResidueField F.S)] (ν : ℕ) (hν : 0 < ν)
    (co : Fin ν → F.S) (hco : co ⟨0, hν⟩ = 0) (Q : Ideal R) [Q.IsPrime]
    (hord : (ν : ℕ∞) ≤ Ideal.ordElem (Q.map (algebraMap R (Localization.AtPrime Q)))
      (algebraMap R (Localization.AtPrime Q) (F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ^ ν +
        ∑ i : Fin ν, algebraMap F.S R (co i) *
          F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ^ (ν - ((i : ℕ) + 1))))) :
    F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ∈ Q := by
  classical
  set z := F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ with hz
  let g : ℕ → F.S := fun j => if h : 2 ≤ j ∧ j ≤ ν then co ⟨j - 1, by omega⟩ else 0
  have hxz : ∀ j, F.z j = z := by
    intro j
    have : j = ⟨0, by rw [hr]; exact Nat.one_pos⟩ := by
      apply Fin.ext
      have h1 := j.2
      show (j : ℕ) = 0
      omega
    rw [this]
  have hsum : ∑ i : Fin ν, algebraMap F.S R (co i) * z ^ (ν - ((i : ℕ) + 1)) =
      ∑ j ∈ Finset.Icc 2 ν, algebraMap F.S R (g j) * z ^ (ν - j) := by
    obtain ⟨n, rfl⟩ : ∃ n, ν = n + 1 := ⟨ν - 1, by omega⟩
    rw [Fin.sum_univ_succ]
    have h0 : co 0 = 0 := hco
    simp only [h0, map_zero, zero_mul, zero_add]
    have hIcc : Finset.Icc 2 (n + 1) = Finset.Ico 2 (n + 2) := rfl
    rw [hIcc, Finset.sum_Ico_eq_sum_range, show n + 2 - 2 = n by omega,
      ← Fin.sum_univ_eq_sum_range (fun k => (algebraMap F.S R) (g (2 + k)) * z ^ (n + 1 - (2 +
        k))) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hg : g (2 + (i : ℕ)) = co i.succ := by
      have hc : 2 ≤ 2 + (i : ℕ) ∧ 2 + (i : ℕ) ≤ n + 1 := by omega
      simp only [g, hc, and_self, ↓reduceDIte]
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [hg]
    congr 2
    simp only [Fin.val_succ]
    omega
  refine mem_prime_of_ordElem_localization_ge F hr z hxz
    (z ^ ν + ∑ i : Fin ν, algebraMap F.S R (co i) * z ^ (ν - ((i : ℕ) + 1))) ν hν g
    (by rw [hsum]) Q hord

/-- Ring level, p. 317–318: if `f = z^ν + g₁ z^{ν-1} + g₂ z^{ν-2} + ⋯ + g_ν` (`g_i ∈ S`, `g₁ = 0`)
lies in `Q^ν` for a prime `Q` of `R`, then `z ∈ Q` (Lemma 22, §10, Ch. III). -/
theorem frame_z_mem_of_mem_pow [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) (hr : F.r = 1) [CharZero (ResidueField F.S)] (ν : ℕ) (hν : 0 < ν)
    (co : Fin ν → F.S) (hco : co ⟨0, hν⟩ = 0) (Q : Ideal R) [Q.IsPrime]
    (hf : (F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ^ ν + ∑ i : Fin ν,
      algebraMap F.S R (co i) * F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ^ (ν - ((i : ℕ) + 1))) ∈
        Q ^ ν) :
    F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ∈ Q :=
  frame_z_mem_of_ordElem_ge F hr ν hν co hco Q (by
    refine Ideal.le_ordElem (ν := ν) ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hf)

/-- The quotient map of the localized frame is bijective (p. 317: "`(T'_0; z_0)` is a regular
frame of
`S'_0`"): `R_P/(z)R_P ≅ S_{P ∩ S}`. -/
theorem localized_frame_quot_bijective {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (P : Ideal R) [P.IsPrime]
    (hz : z ∈ P) :
    Function.Bijective ((Ideal.Quotient.mk
      (Ideal.span {algebraMap R (Localization.AtPrime P) z})).comp
      (Localization.localRingHom (P.comap (algebraMap F.S R)) P (algebraMap F.S R) rfl)) := by
  have hq := F.quot_bijective
  have hzrange : Set.range F.z = {z} := by
    ext a
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩; exact hzF j
    · rintro rfl
      exact ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, hzF _⟩
  rw [hzrange] at hq
  have hdom := isDomain_of_isRegularLocalRing R
  classical
  set P' := P.comap (algebraMap F.S R) with hP'
  have : P'.IsPrime := Ideal.comap_isPrime _ _
  set φ := Localization.localRingHom P' P (algebraMap F.S R) rfl with hφ
  have hφmk : ∀ (a : F.S) (s : P'.primeCompl),
      φ (IsLocalization.mk' (Localization.AtPrime P') a s) =
        IsLocalization.mk' (Localization.AtPrime P) (algebraMap F.S R a)
          (⟨algebraMap F.S R s, s.2⟩ : P.primeCompl) :=
    fun a s => Localization.localRingHom_mk' _ _ _ _ a s
  -- every element of `R` is congruent mod `z` to the image of an element of `S`
  have hsurjS : ∀ a : R, ∃ α : F.S, algebraMap F.S R α - a ∈ Ideal.span {z} := fun a => by
    obtain ⟨α, hα⟩ := hq.2 (Ideal.Quotient.mk _ a)
    exact ⟨α, Ideal.Quotient.eq.mp hα⟩
  have hinjS : ∀ α : F.S, algebraMap F.S R α ∈ Ideal.span {z} → α = 0 := fun α h => by
    apply hq.1
    simp only [RingHom.comp_apply, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h
  have hnotP : ∀ (t : R) (τ : F.S), t ∉ P → algebraMap F.S R τ - t ∈ Ideal.span {z} →
      τ ∈ P'.primeCompl := by
    intro t τ ht h hτ
    apply ht
    have h1 : t = algebraMap F.S R τ - (algebraMap F.S R τ - t) := by ring
    rw [h1]
    exact P.sub_mem hτ (Ideal.span_singleton_le_iff_mem _ |>.mpr hz h)
  set Rl := Localization.AtPrime P
  have hmk' : ∀ (a : R) (s : P.primeCompl),
      IsLocalization.mk' Rl a s * algebraMap R Rl s = algebraMap R Rl a :=
    fun a s => IsLocalization.mk'_spec Rl a s
  have hinjR : Function.Injective (algebraMap R Rl) :=
    IsLocalization.injective Rl (Ideal.primeCompl_le_nonZeroDivisors P)
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, ?_⟩
  · obtain ⟨⟨a₀, s₀⟩, rfl⟩ := IsLocalization.mk'_surjective P'.primeCompl x
    have hx' : φ (IsLocalization.mk' (Localization.AtPrime P') a₀ s₀) ∈
        Ideal.span {algebraMap R Rl z} := Ideal.Quotient.eq_zero_iff_mem.mp hx
    rw [hφmk, Ideal.mem_span_singleton'] at hx'
    obtain ⟨y, hy⟩ := hx'
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    set σ : R := algebraMap F.S R s₀
    have hσP : σ ∈ P.primeCompl := s₀.2
    have e1 : algebraMap R Rl (algebraMap F.S R a₀ * t) = algebraMap R Rl (b * z * σ) := by
      have h1 := hmk' (algebraMap F.S R a₀) ⟨σ, hσP⟩
      have h2 := hmk' b t
      simp only [map_mul]
      rw [← h1, ← h2, ← hy]
      ring
    have e2 : algebraMap F.S R a₀ * t = b * z * σ := hinjR e1
    obtain ⟨τ, hτ⟩ := hsurjS t
    have hτP : τ ∈ P'.primeCompl := hnotP t τ t.2 hτ
    have h3 : algebraMap F.S R (a₀ * τ) ∈ Ideal.span {z} := by
      have : algebraMap F.S R (a₀ * τ) = algebraMap F.S R a₀ * (algebraMap F.S R τ - t) +
          b * z * σ := by
        rw [map_mul, mul_sub, e2]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hτ)
        (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
    have h4 := hinjS _ h3
    refine (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨τ, hτP⟩, ?_⟩
    show τ * a₀ = 0
    rw [mul_comm]
    exact h4
  · intro y'
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    obtain ⟨α, hα⟩ := hsurjS a
    obtain ⟨σ, hσ⟩ := hsurjS s
    have hσP : σ ∈ P'.primeCompl := hnotP s σ s.2 hσ
    refine ⟨IsLocalization.mk' (Localization.AtPrime P') α ⟨σ, hσP⟩, ?_⟩
    show Ideal.Quotient.mk _ (φ _) = Ideal.Quotient.mk _ _
    rw [hφmk, Ideal.Quotient.eq, Ideal.mem_span_singleton']
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hα
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hσ
    have hσ'P : algebraMap F.S R σ ∈ P.primeCompl := by
      intro h
      exact hσP h
    refine ⟨IsLocalization.mk' Rl (u * s - a * v) ⟨algebraMap F.S R σ * s, P.primeCompl.mul_mem
        hσ'P s.2⟩, ?_⟩
    have hunit : IsUnit (algebraMap R Rl (algebraMap F.S R σ * s)) :=
      IsLocalization.map_units Rl (⟨algebraMap F.S R σ * s, P.primeCompl.mul_mem hσ'P s.2⟩ :
          P.primeCompl)
    apply hunit.mul_left_cancel
    have h1 := hmk' (algebraMap F.S R α) ⟨algebraMap F.S R σ, hσ'P⟩
    have h2 := hmk' a s
    have h3 := hmk' (u * s - a * v) ⟨algebraMap F.S R σ * s, P.primeCompl.mul_mem hσ'P s.2⟩
    have hnz : (u * s - a * v) * z = algebraMap F.S R α * s - a * algebraMap F.S R σ := by
      have : (u * s - a * v) * z = (u * z) * s - a * (v * z) := by ring
      rw [this, hu, hv]; ring
    simp only [map_mul, map_sub] at h3 hnz ⊢
    have hnz' := congrArg (algebraMap R Rl) (show (u * s - a * v) * z = _ from hnz)
    simp only [map_mul, map_sub] at hnz'
    have h1' : IsLocalization.mk' Rl (algebraMap F.S R α) ⟨algebraMap F.S R σ, hσ'P⟩ *
        algebraMap R Rl (algebraMap F.S R σ) = algebraMap R Rl (algebraMap F.S R α) := h1
    linear_combination (algebraMap R Rl z) * h3 + hnz' -
      (algebraMap R Rl (s : R)) * h1' + (algebraMap R Rl (algebraMap F.S R σ)) * h2

/-- p. 317 (base case), ring level: "if `T'_0` is the localization of `T_0` with respect to
`P ∩ T_0`, `(T'_0; z_0)` is a regular frame of `S'_0 = (Ŝ_0)_P`": the regular frame `(S; z)`
(`r = 1`) of `R` localizes, at a prime `P ∋ z`, to a regular frame of `R_P` with coefficient ring
the localization of `S` at `P ∩ S`, with the same `z` and the same coefficients.

Gap in the paper filled: the paper asserts this ("is a regular frame") without proof; here
`R_P/(z)R_P ≅ S_{P ∩ S}` is proved from `R/(z)R ≅ S` and `z` is shown to extend to a regular
system of parameters of `R_P`. -/
theorem exists_frame_localization [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) (hr : F.r = 1) (P : Ideal R) [P.IsPrime]
    (hz : F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ∈ P) :
    haveI := isRegularLocalRing_localization_of_isRegularLocalRing R P
    ∃ (F' : RegularFrame (Localization.AtPrime P)) (hr' : F'.r = 1)
      (φ : F.S →+* F'.S),
      F'.z ⟨0, by rw [hr']; exact Nat.one_pos⟩ =
        algebraMap R (Localization.AtPrime P) (F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩) ∧
      ∀ s : F.S, algebraMap F'.S (Localization.AtPrime P) (φ s) =
        algebraMap R (Localization.AtPrime P) (algebraMap F.S R s) := by
  classical
  have hRP := isRegularLocalRing_localization_of_isRegularLocalRing R P
  have hdom := isDomain_of_isRegularLocalRing R
  set z := F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ with hzdef
  have hzF : ∀ j, F.z j = z := by
    intro j
    have : j = ⟨0, by rw [hr]; exact Nat.one_pos⟩ := by
      apply Fin.ext
      have h1 := j.2
      show (j : ℕ) = 0
      omega
    rw [this]
  set P' := P.comap (algebraMap F.S R) with hP'
  have : P'.IsPrime := Ideal.comap_isPrime _ _
  have hS' := isRegularLocalRing_localization_of_isRegularLocalRing F.S P'
  set φ := Localization.localRingHom P' P (algebraMap F.S R) rfl with hφ
  have hbij := localized_frame_quot_bijective F z hzF hr P hz
  set z' := algebraMap R (Localization.AtPrime P) z with hz'
  have hspan : Set.range (fun _ : Fin 1 => z') = {z'} := Set.range_const
  let e := RingEquiv.ofBijective _ hbij
  have hqreg : IsRegularLocalRing (Localization.AtPrime P ⧸ Ideal.span {z'}) :=
    IsRegularLocalRing.of_ringEquiv e
  have hz'M : z' ∈ maximalIdeal (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P z).mpr hz
  have hext : ExtendsToRSOP (Localization.AtPrime P) {z'} := by
    have hcoe : (({z'} : Finset (Localization.AtPrime P)) : Set (Localization.AtPrime P)) =
        ({z'} : Set (Localization.AtPrime P)) := by simp
    have : IsRegularLocalRing (Localization.AtPrime P ⧸
        Ideal.span (({z'} : Finset (Localization.AtPrime P)) : Set (Localization.AtPrime P))) := by
      rw [hcoe]; exact hqreg
    refine rsop_extends_of_quotient_regular (K := {z'}) (fun k hk => ?_) ?_
    · rw [Finset.mem_singleton.mp hk]; exact hz'M
    · have hmem : z ∈ Finset.image F.z Finset.univ :=
        Finset.mem_image.mpr ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, Finset.mem_univ _, rfl⟩
      have hzne : z ≠ 0 := F.extends_rsop.ne_zero hmem
      have hnz : z' ∈ nonZeroDivisors (Localization.AtPrime P) := by
        refine mem_nonZeroDivisors_of_ne_zero ?_
        intro h
        apply hzne
        exact (IsLocalization.injective (Localization.AtPrime P)
          (Ideal.primeCompl_le_nonZeroDivisors P)) (by rw [map_zero]; exact h)
      have := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz
      rw [hcoe]
      simpa using this
  refine ⟨{ S := Localization.AtPrime P'
            algebra := φ.toAlgebra
            isLocalHom := ?_
            r := 1
            z := fun _ => z'
            z_injective := Function.injective_of_subsingleton _
            extends_rsop := ?_
            quot_bijective := ?_ }, rfl, algebraMap F.S _, rfl, ?_⟩
  · show IsLocalHom φ
    infer_instance
  · simpa using hext
  · rw [hspan]
    exact hbij
  · intro s
    show φ (algebraMap F.S _ s) = _
    rw [Localization.localRingHom_to_map]

/-- `S ∩ Q^k = (Q ∩ S)^k` modulo `z`: if `R/(z) ≅ S` and `z ∈ Q`, then `y ∈ S` with
`y ∈ Q^k + (z)` (in `R`) lies in `(Q ∩ S)^k`. -/
theorem frame_mem_comap_pow_of_mem_pow_add {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (Q : Ideal R)
    (hzQ : z ∈ Q) (k : ℕ) (y : F.S)
    (hy : algebraMap F.S R y ∈ Q ^ k ⊔ Ideal.span {z}) :
    y ∈ (Q.comap (algebraMap F.S R)) ^ k := by
  have hq := F.quot_bijective
  have hzrange : Set.range F.z = {z} := by
    ext a
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩; exact hzF j
    · rintro rfl
      exact ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, hzF _⟩
  rw [hzrange] at hq
  let ψ : F.S ≃+* R ⧸ Ideal.span {z} := RingEquiv.ofBijective _ hq
  have hψ : ∀ s, ψ s = Ideal.Quotient.mk _ (algebraMap F.S R s) := fun s => rfl
  have hspan : Ideal.span {z} ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr hzQ
  -- `ψ⁻¹(Q/(z)) = Q ∩ S`
  have hk : Ideal.comap (Ideal.Quotient.mk (Ideal.span {z})) ⊥ = Ideal.span {z} := by
    rw [← RingHom.ker_eq_comap_bot]; exact Ideal.mk_ker
  have hcomap : (Q.map (Ideal.Quotient.mk (Ideal.span {z}))).comap (ψ : F.S →+* _) =
      Q.comap (algebraMap F.S R) := by
    ext s
    rw [Ideal.mem_comap, Ideal.mem_comap, RingEquiv.coe_toRingHom, hψ,
      ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, hk,
      sup_eq_left.mpr hspan]
  have e1 : ∀ I : Ideal (R ⧸ Ideal.span {z}),
      I.comap (ψ : F.S →+* _) = I.map (ψ.symm : (R ⧸ Ideal.span {z}) →+* F.S) := fun I => by
    exact Ideal.comap_symm (I := I) ψ.symm
  have hpow : ((Q.map (Ideal.Quotient.mk (Ideal.span {z}))) ^ k).comap (ψ : F.S →+* _) =
      (Q.comap (algebraMap F.S R)) ^ k := by
    rw [e1, Ideal.map_pow, ← e1, hcomap]
  rw [← hpow, Ideal.mem_comap, RingEquiv.coe_toRingHom, hψ]
  rw [← Ideal.map_pow]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy
  have hb' : Ideal.Quotient.mk (Ideal.span {z}) b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
  have : Ideal.Quotient.mk (Ideal.span {z}) (algebraMap F.S R y) =
      Ideal.Quotient.mk (Ideal.span {z}) a := by
    rw [← hab, map_add, hb', add_zero]
  rw [this]
  exact Ideal.mem_map_of_mem _ ha

/-- p. 318 ("it then follows that `g_{ji}(t) ∈ (Q̂'_t ∩ T'_t)^i`"), ring level: if
`z^n + c_1 z^{n-1} + ⋯ + c_n ∈ Q^n` for a regular frame `(S; z)` (`r = 1`) and a prime `Q ∋ z`
with `R/Q` regular, then `c_i ∈ (Q ∩ S)^i`.

Gap in the paper filled: the paper says "it then follows" without proof.  Proof: modulo `z` the
element is `c_n`, so `c_n ∈ (Q ∩ S)^n` (`R/(z) ≅ S`); then `z · g'' ∈ Q^n` where `g''` has the same
shape with `n - 1`, and `ν_Q(z) = 1` (`z ∉ M²`) with `gr_Q(R)` a domain gives `g'' ∈ Q^{n-1}`. -/
theorem frame_coeff_mem_pow {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (Q : Ideal R) [Q.IsPrime]
    (hQ : IsRegularLocalRing (R ⧸ Q)) (hzQ : z ∈ Q) :
    ∀ (n : ℕ) (c : Fin n → F.S),
      z ^ n + ∑ i : Fin n, algebraMap F.S R (c i) * z ^ (n - ((i : ℕ) + 1)) ∈ Q ^ n →
        ∀ i : Fin n, c i ∈ (Q.comap (algebraMap F.S R)) ^ ((i : ℕ) + 1) := by
  classical
  have hdom := isDomain_of_isRegularLocalRing R
  have hgr := isDomain_assocGraded Q hQ
  have hzmem : z ∈ Finset.image F.z Finset.univ :=
    Finset.mem_image.mpr ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, Finset.mem_univ _, hzF _⟩
  have hzM2 : z ∉ maximalIdeal R ^ 2 := F.extends_rsop.notMem_maximalIdeal_sq hzmem
  have hzQ2 : z ∉ Q ^ 2 := fun h =>
    hzM2 (Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) 2 h)
  have hordz : Ideal.ordElem Q z = 1 := by
    refine le_antisymm ?_ ?_
    · exact Ideal.ordElem_le_of_notMem (m := 1) hzQ2
    · exact_mod_cast Ideal.le_ordElem (ν := 1) (by rwa [pow_one])
  intro n
  induction n with
  | zero => intro c _ i; exact i.elim0
  | succ n ih =>
    intro c hg i
    set g'' : R := z ^ n + ∑ i : Fin n, algebraMap F.S R (c i.castSucc) * z ^ (n - ((i : ℕ) + 1))
      with hg''
    have hsplit : z ^ (n + 1) + ∑ i : Fin (n + 1),
        algebraMap F.S R (c i) * z ^ (n + 1 - ((i : ℕ) + 1)) =
        z * g'' + algebraMap F.S R (c (Fin.last n)) := by
      rw [Fin.sum_univ_castSucc, hg'', mul_add, Finset.mul_sum]
      simp only [Fin.val_last, Fin.val_castSucc, Nat.sub_self, pow_zero, mul_one]
      have : ∀ j : Fin n, z * (algebraMap F.S R (c j.castSucc) * z ^ (n - ((j : ℕ) + 1))) =
          algebraMap F.S R (c j.castSucc) * z ^ (n + 1 - ((j : ℕ) + 1)) := fun j => by
        have hj := j.2
        rw [show n + 1 - ((j : ℕ) + 1) = (n - ((j : ℕ) + 1)) + 1 by omega, pow_succ]
        ring
      simp only [this]
      ring
    rw [hsplit] at hg
    have hlast : c (Fin.last n) ∈ (Q.comap (algebraMap F.S R)) ^ (n + 1) := by
      refine frame_mem_comap_pow_of_mem_pow_add F z hzF hr Q hzQ (n + 1) _ ?_
      have h1 : algebraMap F.S R (c (Fin.last n)) =
          (z * g'' + algebraMap F.S R (c (Fin.last n))) - z * g'' := by ring
      rw [h1]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left hg)
        (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
    have hlastQ : algebraMap F.S R (c (Fin.last n)) ∈ Q ^ (n + 1) := by
      have h := Ideal.mem_map_of_mem (algebraMap F.S R) hlast
      rw [Ideal.map_pow] at h
      exact Ideal.pow_right_mono Ideal.map_comap_le _ h
    have hzg : z * g'' ∈ Q ^ (n + 1) := by
      have : z * g'' = (z * g'' + algebraMap F.S R (c (Fin.last n))) -
          algebraMap F.S R (c (Fin.last n)) := by ring
      rw [this]
      exact Ideal.sub_mem _ hg hlastQ
    have hg''Q : g'' ∈ Q ^ n := by
      refine Ideal.mem_pow_of_le_ordElem (I := Q) ?_
      have h1 : ((n + 1 : ℕ) : ℕ∞) ≤ Ideal.ordElem Q (z * g'') := Ideal.le_ordElem hzg
      rw [ordElem_mul_of_isDomain, hordz] at h1
      have h2 : ((n : ℕ) : ℕ∞) + 1 ≤ 1 + Ideal.ordElem Q g'' := by
        simpa [add_comm] using h1
      rw [add_comm (1 : ℕ∞)] at h2
      exact (ENat.add_le_add_iff_right (by norm_num)).mp h2
    have ih' := ih (fun i => c i.castSucc) (by simpa [hg''] using hg''Q)
    induction i using Fin.lastCases with
    | last => simpa using hlast
    | cast i => simpa using ih' i

/-- `Q = zR + (Q ∩ S)R` for a regular frame `(S; z)` (`r = 1`) and a prime `Q ∋ z`
(`R/(z) ≅ S`). -/
theorem frame_ideal_eq_sup {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (Q : Ideal R)
    (hzQ : z ∈ Q) :
    Q = Ideal.span {z} ⊔ (Q.comap (algebraMap F.S R)).map (algebraMap F.S R) := by
  have hq := F.quot_bijective
  have hzrange : Set.range F.z = {z} := by
    ext a
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩; exact hzF j
    · rintro rfl
      exact ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, hzF _⟩
  rw [hzrange] at hq
  refine le_antisymm (fun q hq' => ?_) (sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hzQ)
    Ideal.map_comap_le)
  obtain ⟨s, hs⟩ := hq.2 (Ideal.Quotient.mk _ q)
  have hs' : algebraMap F.S R s - q ∈ Ideal.span {z} := Ideal.Quotient.eq.mp hs
  have hsQ : algebraMap F.S R s ∈ Q := by
    have : algebraMap F.S R s = (algebraMap F.S R s - q) + q := by ring
    rw [this]
    exact Q.add_mem ((Ideal.span_singleton_le_iff_mem _).mpr hzQ hs') hq'
  have hq2 : q = algebraMap F.S R s - (algebraMap F.S R s - q) := by ring
  rw [hq2]
  exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hsQ))
    (Ideal.mem_sup_left hs')

/-- Ring level, p. 318 (the paper's indirect argument): with `Q R₁ = (w)`, `z = wζ`, `g_j = z^ν +
∑ g_{ji} z^{ν-i}` with `g_{ji} ∈ (Q ∩ S)^i`, and `h_j = g_j/w^ν ∈ M₁^ν` for some `j` (`ν ≥ 1`),
some element of `Q ∩ S` is `w` times a unit of `R₁` ("`w_t^{-1}(Q_t ∩ T'_t) S'_{t+1}` is the unit
ideal").  "In fact, if otherwise, `z_t/w_t` should be a unit and therefore `g_j(t)/w_t^ν` should be
a unit.  This contradicts the above fact" (p. 318): if no element of `Q ∩ S` is `w` times a unit,
then `(Q ∩ S)R₁ ⊆ w M₁`, so `(w) = (z) + (Q ∩ S)R₁` gives `ζ` a unit (Nakayama), and then
`h_j = ζ^ν + ∑ (g_{ji}/w^i) ζ^{ν-i} ≡ ζ^ν` modulo `M₁` is a unit, contradicting `h_j ∈ M₁^ν`. -/
theorem exists_mem_comap_assoc_w {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (ν : ℕ) (hν : 0 < ν)
    (m : ℕ) (g : Fin m → R) (co : Fin m → Fin ν → F.S)
    (hshape : ∀ j, g j = z ^ ν + ∑ i : Fin ν,
      algebraMap F.S R (co j i) * z ^ (ν - ((i : ℕ) + 1)))
    (Q : Ideal R) [Q.IsPrime] (hcoef : ∀ (j : Fin m) (i : Fin ν),
      co j i ∈ (Q.comap (algebraMap F.S R)) ^ ((i : ℕ) + 1))
    (hzQ : z ∈ Q) (T : MonoidalTransform R Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (w : T.ring) (hw : Ideal.span {w} = Q.map T.toRing) (ζ : T.ring)
    (hζ : T.toRing z = w * ζ) (hm : 0 < m) (h : Fin m → T.ring)
    (hh : ∀ j, h j ∈ maximalIdeal T.ring ^ ν) (hwh : ∀ j, w ^ ν * h j = T.toRing (g j)) :
    ∃ x : F.S, algebraMap F.S R x ∈ Q ∧ ∃ ε : T.ringˣ, T.toRing (algebraMap F.S R x) = w * ε := by
  classical
  by_contra hcon
  push Not at hcon
  have hdom := isDomain_of_isRegularLocalRing R
  have hdomT := isDomain_of_isRegularLocalRing T.ring
  have hzne : z ≠ 0 := by
    have hmem : z ∈ Finset.image F.z Finset.univ :=
      Finset.mem_image.mpr ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, Finset.mem_univ _, hzF _⟩
    exact F.extends_rsop.ne_zero hmem
  have hw0 : w ≠ 0 := by
    intro h0
    have hz0 : T.toRing z = 0 := by rw [hζ, h0, zero_mul]
    exact hzne (T.toRing_injective (by rw [hz0, map_zero]))
  have hx : ∀ x : F.S, algebraMap F.S R x ∈ Q → ∃ e ∈ maximalIdeal T.ring,
      T.toRing (algebraMap F.S R x) = w * e := by
    intro x hx
    have hmem : T.toRing (algebraMap F.S R x) ∈ Ideal.span {w} := by
      rw [hw]; exact Ideal.mem_map_of_mem _ hx
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨e, ?_, by rw [← he, mul_comm]⟩
    by_contra hem
    have hu := IsLocalRing.notMem_maximalIdeal.mp hem
    exact hcon x hx hu.unit (by rw [IsUnit.unit_spec, ← he, mul_comm])
  set P' := Q.comap (algebraMap F.S R) with hP'
  have hle : P'.map (T.toRing.comp (algebraMap F.S R)) ≤ Ideal.span {w} * maximalIdeal T.ring := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    obtain ⟨e, he, hpe⟩ := hx p (Ideal.mem_comap.mp hp)
    rw [Ideal.mem_comap]
    show T.toRing (algebraMap F.S R p) ∈ _
    rw [hpe]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self w) he
  -- `ζ` is not in `M₁`: otherwise `w = a (wζ) + w e` gives `1 ∈ M₁`
  have hζu : ζ ∉ maximalIdeal T.ring := by
    intro hζm
    have hwQ : w ∈ Q.map T.toRing := hw ▸ Ideal.mem_span_singleton_self w
    have hwQ' : w ∈ Ideal.span {T.toRing z} ⊔ P'.map (T.toRing.comp (algebraMap F.S R)) := by
      have h1 := Ideal.map_mono (f := T.toRing) (frame_ideal_eq_sup F z hzF hr Q hzQ).le
      have h2 : Ideal.map T.toRing (Ideal.span {z} ⊔ P'.map (algebraMap F.S R)) =
          Ideal.span {T.toRing z} ⊔ P'.map (T.toRing.comp (algebraMap F.S R)) := by
        rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_map]
      exact h2 ▸ h1 hwQ
    obtain ⟨a', ha', p, hp, hap⟩ := Submodule.mem_sup.mp hwQ'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha'
    have hp' := hle hp
    rw [mul_comm, Ideal.mem_mul_span_singleton] at hp'
    obtain ⟨e, he, hep⟩ := hp'
    have h1 : (c * ζ + e - 1) * w = 0 := by
      have : w = c * (w * ζ) + e * w := by rw [← hζ, hc, hep, hap]
      calc (c * ζ + e - 1) * w = c * (w * ζ) + e * w - w := by ring
        _ = 0 := by rw [← this, sub_self]
    rcases mul_eq_zero.mp h1 with h0 | h0
    · have h2 : (1 : T.ring) = c * ζ + e := by
        rw [sub_eq_zero] at h0; exact h0.symm
      have : (1 : T.ring) ∈ maximalIdeal T.ring := by
        rw [h2]; exact add_mem (Ideal.mul_mem_left _ _ hζm) he
      exact (IsLocalRing.maximalIdeal.isMaximal T.ring).ne_top ((Ideal.eq_top_iff_one _).mpr this)
    · exact hw0 h0
  -- the coefficients: `T(g_{ji}) = w^{i+1} e_i` with `e_i ∈ M₁`
  have hpow : ∀ (k : ℕ), 1 ≤ k → ∀ y ∈ (Ideal.span {w} * maximalIdeal T.ring) ^ k,
      ∃ e ∈ maximalIdeal T.ring, y = w ^ k * e := by
    intro k hk y hy
    rw [mul_pow, Ideal.span_singleton_pow, mul_comm, Ideal.mem_mul_span_singleton] at hy
    obtain ⟨e, he, hey⟩ := hy
    exact ⟨e, Ideal.pow_le_self (by omega) he, by rw [← hey, mul_comm]⟩
  let j0 : Fin m := ⟨0, hm⟩
  have hex : ∀ i : Fin ν, ∃ e ∈ maximalIdeal T.ring,
      T.toRing (algebraMap F.S R (co j0 i)) = w ^ ((i : ℕ) + 1) * e := by
    intro i
    have h1 := Ideal.mem_map_of_mem (T.toRing.comp (algebraMap F.S R)) (hcoef j0 i)
    rw [Ideal.map_pow] at h1
    exact hpow _ (by omega) _ (Ideal.pow_right_mono hle _ h1)
  choose e he heq using hex
  have hsum : w ^ ν * h j0 = w ^ ν * (ζ ^ ν + ∑ i : Fin ν, e i * ζ ^ (ν - ((i : ℕ) + 1))) := by
    rw [hwh, hshape, map_add, map_pow, map_sum, hζ, mul_pow, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hζ, heq, mul_pow]
    have hi : (i : ℕ) + 1 ≤ ν := i.2
    have : w ^ ν = w ^ ((i : ℕ) + 1) * w ^ (ν - ((i : ℕ) + 1)) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    ring
  have hh' := mul_left_cancel₀ (pow_ne_zero ν hw0) hsum
  have hhm : h j0 ∈ maximalIdeal T.ring := Ideal.pow_le_self (by omega) (hh j0)
  have hsm : ∑ i : Fin ν, e i * ζ ^ (ν - ((i : ℕ) + 1)) ∈ maximalIdeal T.ring :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (he i)
  have hζν : ζ ^ ν ∈ maximalIdeal T.ring := by
    have : ζ ^ ν = h j0 - ∑ i : Fin ν, e i * ζ ^ (ν - ((i : ℕ) + 1)) := by
      rw [hh']; ring
    rw [this]
    exact sub_mem hhm hsm
  exact hζu ((Ideal.IsPrime.mem_of_pow_mem inferInstance ν hζν))

theorem ordElem_pow_of_isDomain_assocGraded {A : Type u} [CommRing A] (I : Ideal A) (hI : I ≠ ⊤)
    [IsDomain (AssocGraded I)] (a : A) (k : ℕ) :
    Ideal.ordElem I (a ^ k) = k * Ideal.ordElem I a := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact le_antisymm (Ideal.ordElem_le_of_notMem (m := 0) (by
      rw [zero_add, pow_one]; exact fun h => hI ((Ideal.eq_top_iff_one _).mpr h))) bot_le
  | succ k ih =>
    rw [pow_succ, ordElem_mul_of_isDomain, ih]
    push_cast
    ring

/-- Deviation from the paper (gap filled), p. 318 ("`g_{ji}(t) ∈ (Q̂'_t ∩ T'_t)^i`"): the coefficient step.
If `a^k ∈ Q^{kn} + (z)` (`k > 0`), then `a ∈ Q^n + (z)`: in the regular local ring `R/(z)`,
`gr_{Q̄}` is a domain, so `ν_{Q̄}(ā^k) = k ν_{Q̄}(ā)`. -/
theorem mem_pow_sup_span_of_pow_mem {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (Q : Ideal R) [Q.IsPrime]
    (hQ : IsRegularLocalRing (R ⧸ Q)) (hzQ : z ∈ Q) (a : R) (k n : ℕ) (hk : 0 < k)
    (h : a ^ k ∈ Q ^ (k * n) ⊔ Ideal.span {z}) : a ∈ Q ^ n ⊔ Ideal.span {z} := by
  classical
  have hzmem : z ∈ Finset.image F.z Finset.univ :=
    Finset.mem_image.mpr ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, Finset.mem_univ _, hzF _⟩
  have hext : ExtendsToRSOP R {z} :=
    F.extends_rsop.mono (Finset.singleton_subset_iff.mpr hzmem)
  have hTreg : IsRegularLocalRing (R ⧸ Ideal.span {z}) :=
    hext.isRegularLocalRing_quotient_span_singleton (Finset.mem_singleton_self _)
  have hzspan : Ideal.span {z} ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr hzQ
  set mk := Ideal.Quotient.mk (Ideal.span {z}) with hmk
  have hQbp : (Q.map mk).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]; exact hzspan)
  have hQbreg : IsRegularLocalRing ((R ⧸ Ideal.span {z}) ⧸ Q.map mk) :=
    IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hzspan).symm
  have hgr := isDomain_assocGraded (Q.map mk) hQbreg
  have hne : Q.map mk ≠ ⊤ := hQbp.ne_top
  have hk1 : mk a ^ k ∈ (Q.map mk) ^ (k * n) := by
    have h2 : ((Q ^ (k * n) ⊔ Ideal.span {z}).map mk) = (Q ^ (k * n)).map mk := by
      rw [Ideal.map_sup, hmk, Ideal.map_quotient_self, sup_bot_eq]
    have : mk (a ^ k) ∈ (Q ^ (k * n) ⊔ Ideal.span {z}).map mk := Ideal.mem_map_of_mem _ h
    rw [h2, Ideal.map_pow] at this
    rwa [map_pow] at this
  have hord : ((k * n : ℕ) : ℕ∞) ≤ k * Ideal.ordElem (Q.map mk) (mk a) := by
    rw [← ordElem_pow_of_isDomain_assocGraded (Q.map mk) hne]
    exact Ideal.le_ordElem hk1
  have hord' : (n : ℕ∞) ≤ Ideal.ordElem (Q.map mk) (mk a) := by
    by_cases ht : Ideal.ordElem (Q.map mk) (mk a) = ⊤
    · rw [ht]; exact le_top
    · obtain ⟨o, ho⟩ := ENat.ne_top_iff_exists.mp ht
      rw [← ho] at hord ⊢
      have h3 : ((k * n : ℕ) : ℕ∞) ≤ ((k * o : ℕ) : ℕ∞) := by
        push_cast; exact hord
      have h4 : k * n ≤ k * o := Nat.cast_le.mp h3
      exact Nat.cast_le.mpr (Nat.le_of_mul_le_mul_left h4 hk)
  have hmem := Ideal.mem_pow_of_le_ordElem hord'
  rw [← Ideal.map_pow] at hmem
  obtain ⟨q, hq, hqa⟩ := (Ideal.mem_map_iff_of_surjective mk Ideal.Quotient.mk_surjective).mp hmem
  have : a - q ∈ Ideal.span {z} := by
    rw [← Ideal.Quotient.eq]; exact hqa.symm
  have : a = q + (a - q) := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mem_sup_left hq) (Ideal.mem_sup_right ‹_›)

/-- Deviation from the paper (gap filled), p. 318/320 ("`w_t^{-1}(Q̂'_t ∩ T'_t)Ŝ'_{t+1}` is the unit ideal"): the Nakayama step.
Ring level, p. 319-320 (Lemma (CD.5), the frame transform without a bound on `ν(Ĵ_{t+1})`):
with `Q R₁ = (w)`, `z = wζ` and `ζ` a non-unit of `R₁`, some element of `Q ∩ S` is `w` times a unit
of `R₁`.  Here `Q = (z) + (Q ∩ S)R` (`z ∈ Q`, `R/(z) ≅ S`), so `(w) = (z)R₁ + (Q ∩ S)R₁
⊆ M₁ (w) + (Q ∩ S)R₁`; Nakayama gives `(w) = (Q ∩ S)R₁`, whence a generator `x` of `Q ∩ S` with
`x = w · unit`. -/
theorem exists_mem_comap_assoc_w_of_mem_maximalIdeal {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R]
    (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (Q : Ideal R) [Q.IsPrime]
    (hzQ : z ∈ Q) (T : MonoidalTransform R Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (w : T.ring) (hw : Ideal.span {w} = Q.map T.toRing) (ζ : T.ring)
    (hζ : T.toRing z = w * ζ) (hζm : ζ ∈ maximalIdeal T.ring) :
    ∃ x : F.S, algebraMap F.S R x ∈ Q ∧ ∃ ε : T.ringˣ, T.toRing (algebraMap F.S R x) = w * ε := by
  classical
  have := isDomain_of_isRegularLocalRing T.ring
  have hz0 : z ≠ 0 := by
    have hzmem : z ∈ Finset.image F.z Finset.univ :=
      Finset.mem_image.mpr ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, Finset.mem_univ _, hzF _⟩
    exact F.extends_rsop.ne_zero hzmem
  have hw0 : w ≠ 0 := by
    intro h0
    have : T.toRing z ∈ Q.map T.toRing := Ideal.mem_map_of_mem _ hzQ
    rw [← hw, h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at this
    exact hz0 (T.toRing_injective (this.trans (map_zero _).symm))
  set C := Q.comap (algebraMap F.S R) with hC
  set N : Ideal T.ring := C.map (T.toRing.comp (algebraMap F.S R)) with hN
  have hQ := frame_ideal_eq_sup F z hzF hr Q hzQ
  have h1 : Ideal.span {w} ≤ Ideal.span {w * ζ} ⊔ N := by
    rw [hw, Ideal.map_le_iff_le_comap]
    intro q hq
    have hq' : q ∈ Ideal.span {z} ⊔ C.map (algebraMap F.S R) := hQ ▸ hq
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hq'
    rw [Ideal.mem_comap, map_add]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
    · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, hζ]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · have : T.toRing b ∈ (C.map (algebraMap F.S R)).map T.toRing := Ideal.mem_map_of_mem _ hb
      rwa [Ideal.map_map] at this
  have h2 : Ideal.span {w * ζ} ≤ maximalIdeal T.ring * Ideal.span {w} := by
    rw [Ideal.span_singleton_le_iff_mem, mul_comm]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self w) hζm |> fun h => by
      simpa [mul_comm] using Ideal.mul_mem_mul hζm (Ideal.mem_span_singleton_self w)
  have h3 : Ideal.span {w} ≤ N ⊔ maximalIdeal T.ring • Ideal.span {w} := by
    refine h1.trans (sup_le ?_ le_sup_left)
    refine h2.trans ?_
    rw [smul_eq_mul]
    exact le_sup_right
  have hFG : (Ideal.span {w} : Submodule T.ring T.ring).FG := ⟨{w}, by simp⟩
  have hjac : maximalIdeal T.ring ≤ Ideal.jacobson ⊥ :=
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have h4 : Ideal.span {w} ≤ N :=
    Submodule.le_of_le_smul_of_le_jacobson_bot hFG hjac h3
  have hwN : w ∈ N := h4 (Ideal.mem_span_singleton_self w)
  have hwN' : w ∈ Submodule.span T.ring ((T.toRing.comp (algebraMap F.S R)) '' (C : Set F.S)) := hwN
  obtain ⟨f, t, hts, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hwN'
  have hmemw : ∀ y ∈ t, ∃ (x : F.S) (b : T.ring), algebraMap F.S R x ∈ Q ∧
      T.toRing (algebraMap F.S R x) = y ∧ y = w * b := by
    intro y hy
    obtain ⟨x, hxC, rfl⟩ := hts hy
    have hxQ : algebraMap F.S R x ∈ Q := hxC
    have : T.toRing (algebraMap F.S R x) ∈ Ideal.span {w} := by
      rw [hw]; exact Ideal.mem_map_of_mem _ hxQ
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨x, b, hxQ, rfl, by show T.toRing (algebraMap F.S R x) = _; rw [← hb, mul_comm]⟩
  choose! x0 b hxQ hxy hyb using hmemw
  have hone : ∑ y ∈ t, f y * b y = 1 := by
    have h5 : w * (∑ y ∈ t, f y * b y) = w * 1 := by
      rw [mul_one, Finset.mul_sum]
      conv_rhs => rw [← hsum.2]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [smul_eq_mul]
      calc w * (f y * b y) = f y * (w * b y) := by ring
        _ = f y * y := by rw [← hyb y hy]
    exact mul_left_cancel₀ hw0 h5
  have hex : ∃ y ∈ t, IsUnit (b y) := by
    by_contra hcon
    push Not at hcon
    have : ∑ y ∈ t, f y * b y ∈ maximalIdeal T.ring :=
      Ideal.sum_mem _ fun y hy => Ideal.mul_mem_left _ _
        ((IsLocalRing.mem_maximalIdeal _).mpr (hcon y hy))
    rw [hone] at this
    exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  obtain ⟨y, hy, hu⟩ := hex
  exact ⟨x0 y, hxQ y hy, hu.unit, (hxy y hy).trans ((hyb y hy).trans (by rw [IsUnit.unit_spec]))⟩

/-- p. 318, ring level (the core of the inductive step), assuming `z/w ∈ M₁` and that some element of
`Q ∩ S` is `w` times a unit (`hx₀`, "`w_t⁻¹(Q̂'_t ∩ T'_t)Ŝ'_{t+1}` is the unit ideal"). -/
theorem frame_step_core_of_exists {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (ν : ℕ) (hν : 0 < ν)
    (m : ℕ) (g : Fin m → R) (co : Fin m → Fin ν → F.S)
    (hshape : ∀ j, g j = z ^ ν + ∑ i : Fin ν,
      algebraMap F.S R (co j i) * z ^ (ν - ((i : ℕ) + 1)))
    (Q : Ideal R) [Q.IsPrime] [hQ : IsRegularLocalRing (R ⧸ Q)] (hgQ : ∀ j, g j ∈ Q ^ ν)
    (hzQ : z ∈ Q) (T : MonoidalTransform R Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (w : T.ring) (hw : Ideal.span {w} = Q.map T.toRing)
    (hζ : ∀ ζ : T.ring, T.toRing z = w * ζ → ζ ∈ maximalIdeal T.ring)
    (hx₀ : ∀ ζ : T.ring, T.toRing z = w * ζ → ζ ∈ maximalIdeal T.ring →
      ∃ x : F.S, algebraMap F.S R x ∈ Q ∧ ∃ ε : T.ringˣ, T.toRing (algebraMap F.S R x) = w * ε)
    (h : Fin m → T.ring)
    (hwh : ∀ j, w ^ ν * h j = T.toRing (g j)) :
    (∀ (j : Fin m) (i : Fin ν), co j i ∈ (Q.comap (algebraMap F.S R)) ^ ((i : ℕ) + 1)) ∧
      ∃ (F' : RegularFrame T.ring) (_hr' : F'.r = 1) (z' : T.ring) (ζ : T.ring)
        (co' : Fin m → Fin ν → F'.S),
        (∀ j, F'.z j = z') ∧ T.toRing z = w * ζ ∧ Associated z' ζ ∧
        z' ∈ maximalIdeal T.ring ∧
        (∀ j, ∃ u : T.ringˣ, (u : T.ring) * h j = z' ^ ν + ∑ i : Fin ν,
          algebraMap F'.S T.ring (co' j i) * z' ^ (ν - ((i : ℕ) + 1))) ∧
        (∀ (hm : 0 < m), co ⟨0, hm⟩ ⟨0, hν⟩ = 0 → co' ⟨0, hm⟩ ⟨0, hν⟩ = 0) ∧
        (∃ u : T.ringˣ, ∀ (j : Fin m) (i : Fin ν), T.toRing (algebraMap F.S R (co j i)) =
          algebraMap F'.S T.ring (co' j i) * (w * (u : T.ring)) ^ ((i : ℕ) + 1)) := by
  classical
  have hdomR := isDomain_of_isRegularLocalRing R
  have hdomT := isDomain_of_isRegularLocalRing T.ring
  have hcoef : ∀ (j : Fin m) (i : Fin ν),
      co j i ∈ (Q.comap (algebraMap F.S R)) ^ ((i : ℕ) + 1) := fun j =>
    frame_coeff_mem_pow F z hzF hr Q hQ hzQ ν (co j) (by rw [← hshape]; exact hgQ j)
  refine ⟨hcoef, ?_⟩
  have hzmem : T.toRing z ∈ Ideal.span {w} := by
    rw [hw]; exact Ideal.mem_map_of_mem _ hzQ
  obtain ⟨ζ, hζeq'⟩ := Ideal.mem_span_singleton'.mp hzmem
  have hζeq : T.toRing z = w * ζ := by rw [mul_comm]; exact hζeq'.symm
  have hζm := hζ ζ hζeq
  obtain ⟨x₀, hx₀Q, ε, hε⟩ := hx₀ ζ hζeq hζm
  have hadm : F.AdmitsFrameTransform T := by
    rw [RegularFrame.admitsFrameTransform_iff]
    refine ⟨x₀, hx₀Q, ?_, fun _ => (↑ε⁻¹ : T.ring) * ζ, fun j => ?_, fun j => ?_⟩
    · rw [hε, ← hw, Ideal.span_singleton_mul_right_unit ε.isUnit]
    · rw [hε, hzF j, hζeq]
      calc w * ↑ε * (↑ε⁻¹ * ζ) = w * (↑ε * ↑ε⁻¹) * ζ := by ring
        _ = w * ζ := by rw [Units.mul_inv, mul_one]
    · intro hu
      have := IsLocalRing.notMem_maximalIdeal.mpr hu
      exact this (Ideal.mul_mem_left _ _ hζm)
  obtain ⟨FT⟩ := hadm
  have := F.isDomain_S
  have := FT.isRegular
  set TS := FT.TS with hTS
  set β := FT.β with hβ
  have hcomm : ∀ s : F.S, β (TS.toRing s) = T.toRing (algebraMap F.S R s) := fun s =>
    RingHom.congr_fun FT.canonical.comm s
  -- the image of `x_S` generates `(Q ∩ S) R₁`
  set ξ : T.ring := T.toRing (algebraMap F.S R TS.x) with hξ
  have hξspan : Ideal.span {ξ} =
      (Q.comap (algebraMap F.S R)).map (T.toRing.comp (algebraMap F.S R)) := by
    have h1 : ξ = β TS.xR := (hcomm TS.x).symm
    have h2 : (Q.comap (algebraMap F.S R)).map (T.toRing.comp (algebraMap F.S R)) =
        (Q.comap (algebraMap F.S R)).map (β.comp TS.toRing) := by
      congr 1; exact (RingHom.ext fun s => (hcomm s).symm)
    rw [h2, ← Ideal.map_map, ← TS.span_xR_eq_map, Ideal.map_span, Set.image_singleton, h1]
  have hξ0 : ξ ≠ 0 := by
    have hinjS : Function.Injective (algebraMap F.S R) := fun a b hab =>
      F.quot_bijective.1 (by simp only [RingHom.comp_apply]; rw [hab])
    exact fun h0 => TS.x_ne_zero (hinjS (T.toRing_injective (by
      rw [← hξ, h0, map_zero, map_zero])))
  -- `(ξ) = (w)`
  have hξw : Ideal.span {ξ} = Ideal.span {w} := by
    rw [hw]
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mp TS.x_mem)
    · rw [← hw, Ideal.span_le, Set.singleton_subset_iff]
      have h1 : T.toRing (algebraMap F.S R x₀) ∈ Ideal.span {ξ} := by
        rw [hξspan]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mpr hx₀Q)
      have : w = (↑ε⁻¹ : T.ring) * T.toRing (algebraMap F.S R x₀) := by
        rw [hε]
        calc w = w * (↑ε * ↑ε⁻¹) := by rw [Units.mul_inv, mul_one]
          _ = ↑ε⁻¹ * (w * ↑ε) := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ h1
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hξw
  -- `z' = z/ξ`
  set z' : T.ring := (v : T.ring) * ζ with hz'
  have hξz' : ξ * z' = T.toRing z := by
    rw [hζeq, hz', ← mul_assoc, hv]
  have hξ0' : ξ ≠ 0 := hξ0
  -- the denominator of `FT` is associated to `ξ`
  have hFTx : Ideal.span {FT.x} = Ideal.span {ξ} := by rw [FT.span_x, ← hw, hξw]
  obtain ⟨u₂, hu₂⟩ := Ideal.span_singleton_eq_span_singleton.mp hFTx.symm
  have hFTx0 : FT.x ≠ 0 := by rw [← hu₂]; exact mul_ne_zero hξ0 u₂.ne_zero
  let j0 : Fin F.r := ⟨0, by rw [hr]; exact Nat.one_pos⟩
  have hFTw : ∀ j, FT.w j = FT.w j0 := fun j => by
    apply mul_left_cancel₀ hFTx0
    rw [FT.mul_w, FT.mul_w, hzF j, hzF j0]
  have hz'eq : FT.w j0 * (u₂ : T.ring) = z' := by
    apply mul_left_cancel₀ hξ0
    rw [hξz']
    calc ξ * (FT.w j0 * ↑u₂) = (ξ * ↑u₂) * FT.w j0 := by ring
      _ = T.toRing z := by rw [hu₂, FT.mul_w, hzF j0]
  have hassoc : Associated z' (FT.w j0) := (Associated.symm ⟨u₂, hz'eq⟩)
  have hFTrange : Set.range FT.w = {FT.w j0} := by
    ext a
    simp only [Set.mem_range, Set.mem_singleton_iff]
    exact ⟨fun ⟨j, hj⟩ => hj ▸ hFTw j, fun h => ⟨j0, h.symm⟩⟩
  have hspanz' : Ideal.span {FT.w j0} = Ideal.span {z'} :=
    Ideal.span_singleton_eq_span_singleton.mpr hassoc.symm
  have hext : ExtendsToRSOP T.ring (Finset.image (fun _ : Fin 1 => z') Finset.univ) := by
    have h1 := ExtendsToRSOP.image_of_associated FT.extends_rsop (fun _ => z')
      (fun a ha b hb _ => by
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨j', -, rfl⟩ := Finset.mem_image.mp hb
        rw [hFTw j, hFTw j']) (fun k hk => by
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hk
        rw [hFTw j]; exact hassoc.symm)
    have hne : (Finset.image FT.w Finset.univ).Nonempty := ⟨FT.w j0, Finset.mem_image.mpr ⟨j0,
        Finset.mem_univ _, rfl⟩⟩
    rwa [Finset.image_const hne, ← Finset.image_const (s := (Finset.univ : Finset (Fin 1)))
      Finset.univ_nonempty] at h1
  have hquot : Function.Bijective ((Ideal.Quotient.mk (Ideal.span (Set.range fun _ : Fin 1 =>
      z'))).comp
      β) := by
    have h1 := FT.quot_bijective
    rw [hFTrange] at h1
    have h2 : Set.range (fun _ : Fin 1 => z') = {z'} := Set.range_const
    rw [h2, ← hspanz']
    exact h1
  have hz'm : z' ∈ maximalIdeal T.ring := by
    have h1 : FT.w j0 ∈ maximalIdeal T.ring := by
      obtain ⟨s, hsub, hs⟩ := FT.extends_rsop
      rw [← hs.1]
      exact Ideal.subset_span (hsub (Finset.mem_image_of_mem _ (Finset.mem_univ j0)))
    rw [← hz'eq]
    exact Ideal.mul_mem_right _ _ h1
  -- the coefficients `co j i / x_S^{i+1}` in `S₁`
  have hmem : ∀ (j : Fin m) (i : Fin ν), ∃ c : TS.ring, c * TS.xR ^ ((i : ℕ) + 1) =
      TS.toRing (co j i) := by
    intro j i
    have h1 := Ideal.mem_map_of_mem TS.toRing (hcoef j i)
    rw [Ideal.map_pow, ← TS.span_xR_eq_map, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton'] at h1
    exact h1
  choose co' hco' using hmem
  have hxR0 : TS.xR ≠ 0 := by
    intro h0
    apply TS.x_ne_zero
    apply TS.toRing_injective
    rw [map_zero]
    exact h0
  have hβxR : β TS.xR = ξ := hcomm TS.x
  have hTco : ∀ j i, T.toRing (algebraMap F.S R (co j i)) = β (co' j i) * ξ ^ ((i : ℕ) + 1) := by
    intro j i
    rw [← hcomm, ← hco', map_mul, map_pow, hβxR]
  refine ⟨{ S := TS.ring
            algebra := β.toAlgebra
            isLocalHom := FT.canonical.isLocalHom
            r := 1
            z := fun _ => z'
            z_injective := Function.injective_of_subsingleton _
            extends_rsop := hext
            quot_bijective := hquot }, rfl, z', ζ, co', fun _ => rfl, hζeq, ?_, hz'm, ?_, ?_, ?_⟩
  · exact ⟨(v⁻¹ : T.ringˣ), by rw [hz', mul_comm (v : T.ring) ζ, mul_assoc, Units.mul_inv, mul_one]⟩
  · intro j
    refine ⟨v ^ ν, ?_⟩
    show ((v ^ ν : T.ringˣ) : T.ring) * h j = z' ^ ν + ∑ i : Fin ν, β (co' j i) * z' ^ (ν - ((i
        : ℕ) + 1))
    have hTg : T.toRing (g j) = ξ ^ ν * (z' ^ ν + ∑ i : Fin ν, β (co' j i) * z' ^ (ν - ((i : ℕ)
        + 1))) := by
      rw [hshape j, map_add, map_pow, map_sum, ← hξz', mul_pow, mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, ← hξz', hTco, mul_pow]
      have hi : (i : ℕ) + 1 ≤ ν := i.2
      have : ξ ^ ν = ξ ^ ((i : ℕ) + 1) * ξ ^ (ν - ((i : ℕ) + 1)) := by
        rw [← pow_add]; congr 1; omega
      rw [this]
      ring
    have hw' : w ^ ν = ξ ^ ν * ((v ^ ν : T.ringˣ) : T.ring) := by
      rw [← hv, mul_pow, Units.val_pow_eq_pow_val]
    apply mul_left_cancel₀ (pow_ne_zero ν hξ0)
    rw [← hTg, ← hwh j, hw']
    ring
  · intro hm h0
    have h1 := hco' ⟨0, hm⟩ ⟨0, hν⟩
    rw [h0, map_zero] at h1
    have h2 : co' ⟨0, hm⟩ ⟨0, hν⟩ * TS.xR ^ (0 + 1) = 0 := h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) hxR0
  · refine ⟨v⁻¹, fun j i => ?_⟩
    have hwξ : w * ((v⁻¹ : T.ringˣ) : T.ring) = ξ := by
      rw [← hv, mul_assoc, Units.mul_inv, mul_one]
    rw [hwξ]
    exact hTco j i

/-- p. 318, ring level (the core of the inductive step), assuming `z/w ∈ M₁`. -/
theorem frame_step_core' {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (ν : ℕ) (hν : 0 < ν)
    (m : ℕ) (g : Fin m → R) (co : Fin m → Fin ν → F.S)
    (hshape : ∀ j, g j = z ^ ν + ∑ i : Fin ν,
      algebraMap F.S R (co j i) * z ^ (ν - ((i : ℕ) + 1)))
    (Q : Ideal R) [Q.IsPrime] [hQ : IsRegularLocalRing (R ⧸ Q)] (hgQ : ∀ j, g j ∈ Q ^ ν)
    (hzQ : z ∈ Q) (T : MonoidalTransform R Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (w : T.ring) (hw : Ideal.span {w} = Q.map T.toRing)
    (hζ : ∀ ζ : T.ring, T.toRing z = w * ζ → ζ ∈ maximalIdeal T.ring) (hm : 0 < m)
    (h : Fin m → T.ring) (hh : ∀ j, h j ∈ maximalIdeal T.ring ^ ν)
    (hwh : ∀ j, w ^ ν * h j = T.toRing (g j)) :
    (∀ (j : Fin m) (i : Fin ν), co j i ∈ (Q.comap (algebraMap F.S R)) ^ ((i : ℕ) + 1)) ∧
      ∃ (F' : RegularFrame T.ring) (_hr' : F'.r = 1) (z' : T.ring) (ζ : T.ring)
        (co' : Fin m → Fin ν → F'.S),
        (∀ j, F'.z j = z') ∧ T.toRing z = w * ζ ∧ Associated z' ζ ∧
        z' ∈ maximalIdeal T.ring ∧
        (∀ j, ∃ u : T.ringˣ, (u : T.ring) * h j = z' ^ ν + ∑ i : Fin ν,
          algebraMap F'.S T.ring (co' j i) * z' ^ (ν - ((i : ℕ) + 1))) ∧
        (∀ (hm : 0 < m), co ⟨0, hm⟩ ⟨0, hν⟩ = 0 → co' ⟨0, hm⟩ ⟨0, hν⟩ = 0) ∧
        (∃ u : T.ringˣ, ∀ (j : Fin m) (i : Fin ν), T.toRing (algebraMap F.S R (co j i)) =
          algebraMap F'.S T.ring (co' j i) * (w * (u : T.ring)) ^ ((i : ℕ) + 1)) := by
  have hcoef : ∀ (j : Fin m) (i : Fin ν),
      co j i ∈ (Q.comap (algebraMap F.S R)) ^ ((i : ℕ) + 1) := fun j =>
    frame_coeff_mem_pow F z hzF hr Q hQ hzQ ν (co j) (by rw [← hshape]; exact hgQ j)
  exact frame_step_core_of_exists F z hzF hr ν hν m g co hshape Q hgQ hzQ T w hw hζ
    (fun ζ hζeq _ => exists_mem_comap_assoc_w F z hzF hr ν hν m g co hshape Q hcoef hzQ T w hw ζ
      hζeq hm h hh hwh) h hwh

/-- p. 318 (unrestricted case), ring level: "we apply Lemma 22 to
`g_1(t)/v_t^ν = z_{t+1}^ν + (g_{12}(t)/v_t²) z_{t+1}^{ν-2} + ⋯`, which is contained in the
`ν`th power
of the maximal ideal": `z/w ∈ M₁`.

Deviation from the paper (incomplete citation): Lemma 22 (p. 265) is applied to
`(T'_{t+1}; z_{t+1})` (p. 318), but by Definition 9 (p. 248) a regular frame requires `z_{t+1}` to be
part of a regular system of parameters, hence a non-unit, which is the conclusion sought.  The claim
is true (the characteristic-zero argument of the proof of Lemma 22, using `g_{11} = 0`: with `z/w` a
unit `u + (z/w - u)`, the shifted element and the coefficient `ν u` of `g_1^*`); it is proved in
MaximalContact.lean (see below).

Proved by `RegularFrame.zeta_mem_maximalIdeal_of_maximal_contact` (lem:IV.CD-4-maximal-contact,
MaximalContact.lean), along the proof of Lemma 22. -/
theorem frame_zeta_mem_maximalIdeal_of_unrestricted {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (ν : ℕ)
    (hν : 0 < ν) (m : ℕ) (g : Fin m → R) (co : Fin m → Fin ν → F.S)
    (hshape : ∀ j, g j = z ^ ν + ∑ i : Fin ν,
      algebraMap F.S R (co j i) * z ^ (ν - ((i : ℕ) + 1)))
    [CharZero (ResidueField F.S)] (hm : 0 < m) (h0 : co ⟨0, hm⟩ ⟨0, hν⟩ = 0)
    (Q : Ideal R) [Q.IsPrime] [IsRegularLocalRing (R ⧸ Q)] (hgQ : ∀ j, g j ∈ Q ^ ν) (hzQ : z ∈ Q)
    (T : MonoidalTransform R Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (w : T.ring) (hw : Ideal.span {w} = Q.map T.toRing)
    (h : Fin m → T.ring) (hh : ∀ j, h j ∈ maximalIdeal T.ring ^ ν)
    (hwh : ∀ j, w ^ ν * h j = T.toRing (g j)) :
    ∀ ζ : T.ring, T.toRing z = w * ζ → ζ ∈ maximalIdeal T.ring := by
  classical
  intro ζ hζ
  have hcoef : ∀ (j : Fin m) (i : Fin ν),
      co j i ∈ (Q.comap (algebraMap F.S R)) ^ ((i : ℕ) + 1) := fun j =>
    frame_coeff_mem_pow F z hzF hr Q inferInstance hzQ ν (co j) (by rw [← hshape]; exact hgQ j)
  obtain ⟨x₀, hx₀Q, ε, hε⟩ := exists_mem_comap_assoc_w F z hzF hr ν hν m g co hshape Q hcoef hzQ
    T w hw ζ hζ hm h hh hwh
  exact RegularFrame.zeta_mem_maximalIdeal_of_maximal_contact F z hzF hr ν hν m g co hshape hm h0
    Q hcoef hzQ T w hw x₀ hx₀Q ε hε h hh hwh ζ hζ

/-- p. 318, ring level (the core of the inductive step): let `(S; z)` be a regular frame (`r = 1`)
of `R`, `g_j = z^ν + g_{j1} z^{ν-1} + ⋯ + g_{jν}` (`g_{ji} ∈ S`, `g_{11} = 0` without restriction),
`Q` a prime of `R` with `R/Q` regular and `g_j ∈ Q^ν`, and `R₁ = T.ring` a monoidal transform of `R`
with center `Q`, with `Q R₁ = (w)` and `g_j/w^ν = h_j ∈ M₁^ν`.  Then `z ∈ Q` (clear in the closed
case, Lemma 22 otherwise), `g_{ji} ∈ (Q ∩ S)^i`, and `(S; z)` admits a frame transform
`(S₁; z₁)` in `R₁` (`admitsFrameTransform_iff`: some element of `Q ∩ S` is `w` times a unit, by the
paper's indirect argument `exists_mem_comap_assoc_w`, and `z/w ∈ M₁`), with `z₁` associated to `z/w`, non-unit, and `h_j = z₁^ν + g_{j1}'
z₁^{ν-1} + ⋯`
(up to a unit) with `g_{ji}' = g_{ji}/x^i ∈ S₁` (and `g_{11}' = 0`).  In the closed case `z/w ∈ M₁`
is the hypothesis `hζ` (`x'_{t+1} ∈ F(t+1)`); in the unrestricted case it is
`frame_zeta_mem_maximalIdeal_of_unrestricted`. -/
theorem frame_step_core [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (ν : ℕ) (hν : 0 < ν)
    (m : ℕ) (g : Fin m → R) (co : Fin m → Fin ν → F.S)
    (hshape : ∀ j, g j = z ^ ν + ∑ i : Fin ν,
      algebraMap F.S R (co j i) * z ^ (ν - ((i : ℕ) + 1)))
    (unr : Prop) (hunr : unr → (∃ (hm : 0 < m), co ⟨0, hm⟩ ⟨0, hν⟩ = 0) ∧
      CharZero (ResidueField F.S))
    (Q : Ideal R) [Q.IsPrime] [IsRegularLocalRing (R ⧸ Q)] (hgQ : ∀ j, g j ∈ Q ^ ν)
    (hzQ : ¬ unr → z ∈ Q)
    (T : MonoidalTransform R Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (w : T.ring) (hw : Ideal.span {w} = Q.map T.toRing)
    (hζ : ¬ unr → ∀ ζ : T.ring, T.toRing z = w * ζ → ζ ∈ maximalIdeal T.ring) (hm0 : 0 < m)
    (h : Fin m → T.ring) (hh : ∀ j, h j ∈ maximalIdeal T.ring ^ ν)
    (hwh : ∀ j, w ^ ν * h j = T.toRing (g j)) :
    z ∈ Q ∧
      (∀ (j : Fin m) (i : Fin ν), co j i ∈ (Q.comap (algebraMap F.S R)) ^ ((i : ℕ) + 1)) ∧
      ∃ (F' : RegularFrame T.ring) (_hr' : F'.r = 1) (z' : T.ring) (ζ : T.ring)
        (co' : Fin m → Fin ν → F'.S),
        (∀ j, F'.z j = z') ∧ T.toRing z = w * ζ ∧ Associated z' ζ ∧
        z' ∈ maximalIdeal T.ring ∧
        (∀ j, ∃ u : T.ringˣ, (u : T.ring) * h j = z' ^ ν + ∑ i : Fin ν,
          algebraMap F'.S T.ring (co' j i) * z' ^ (ν - ((i : ℕ) + 1))) ∧
        (unr → ∃ (hm : 0 < m), co' ⟨0, hm⟩ ⟨0, hν⟩ = 0) ∧
        (∃ u : T.ringˣ, ∀ (j : Fin m) (i : Fin ν), T.toRing (algebraMap F.S R (co j i)) =
          algebraMap F'.S T.ring (co' j i) * (w * (u : T.ring)) ^ ((i : ℕ) + 1)) := by
  classical
  by_cases hu : unr
  · obtain ⟨⟨hm, h0⟩, hchar⟩ := hunr hu
    have hzQ' : z ∈ Q := by
      have := hgQ ⟨0, hm⟩
      rw [hshape] at this
      have hF : F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ = z := hzF _
      have := frame_z_mem_of_mem_pow F hr ν hν (co ⟨0, hm⟩) h0 Q (by rwa [hF])
      rwa [hF] at this
    have hζ' := frame_zeta_mem_maximalIdeal_of_unrestricted F z hzF hr ν hν m g co hshape hm h0
      Q hgQ hzQ' T w hw h hh hwh
    obtain ⟨hc, F', hr', z', ζ, co', h1, h2, h3, h4, h5, h6, h7⟩ :=
      frame_step_core' F z hzF hr ν hν m g co hshape Q hgQ hzQ' T w hw hζ' hm h hh hwh
    exact ⟨hzQ', hc, F', hr', z', ζ, co', h1, h2, h3, h4, h5, fun _ => ⟨hm, h6 hm h0⟩, h7⟩
  · have hzQ' := hzQ hu
    obtain ⟨hc, F', hr', z', ζ, co', h1, h2, h3, h4, h5, h6, h7⟩ :=
      frame_step_core' F z hzF hr ν hν m g co hshape Q hgQ hzQ' T w hw (hζ hu) hm0 h hh hwh
    exact ⟨hzQ', hc, F', hr', z', ζ, co', h1, h2, h3, h4, h5, fun h => absurd h hu, h7⟩

/-- Closed case, p. 317 ("This is clear for the case in which `ℜ = (ℜ^N_II, F)`"): if `z_0 ∈ S_0`
generates the ideal of `F` at `x_0`, a point `P` of `Spec Ŝ_0` with `c_0(P) ∈ F` contains `z_0`. -/
theorem mem_of_c0_mem_closed (hx : X.IsSimpleAt x₀) (F : Subscheme X)
    (z₀ : X.presheaf.stalk x₀) (hF : F.stalkIdeal x₀ = Ideal.span {z₀}) (z : AB.Shat X x₀)
    (hz : algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀) z₀ = z) (P : AB.xHat0 X x₀)
    (hP : (AB.c0 X x₀).base P ∈ F.pts) : z ∈ (show PrimeSpectrum (AB.Shat X x₀) from P).asIdeal := by
  classical
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  have := isRegularLocalRing_adicCompletion_of_isRegularLocalRing (X.presheaf.stalk x₀)
  have hP' : P ∈ (Subscheme.totalTransform (AB.c0 X x₀) F).pts := by
    rw [FlatPreimm.pts_totalTransform]; exact hP
  rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top] at hP'
  have hH := stalkIdeal_comap_specMap_fromSpecStalk F x₀ (CommRingCat.of (AB.Shat X x₀))
    (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀))) P
  have hH' : Subscheme.stalkIdeal (Subscheme.totalTransform (AB.c0 X x₀) F) P =
      (((F.stalkIdeal x₀).map (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀))).map
        (algebraMap (AB.Shat X x₀) (Localization.AtPrime
          (show PrimeSpectrum (AB.Shat X x₀) from P).asIdeal))).map
        (Spec.stalkIso (CommRingCat.of (AB.Shat X x₀)) (show PrimeSpectrum (AB.Shat X x₀) from P)).inv.hom :=
    hH
  rw [hH', hF, Ideal.map_span, Set.image_singleton, hz, Ideal.map_span, Set.image_singleton,
    Ideal.map_span, Set.image_singleton] at hP'
  by_contra hzP
  apply hP'
  have hu : IsUnit (algebraMap (AB.Shat X x₀) (Localization.AtPrime
      (show PrimeSpectrum (AB.Shat X x₀) from P).asIdeal) z) :=
    IsLocalization.map_units _ (⟨z, hzP⟩ : (show PrimeSpectrum (AB.Shat X x₀) from P).asIdeal.primeCompl)
  exact Ideal.span_singleton_eq_top.mpr (hu.map _)

theorem equiv_mem_pow {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (ν : ℕ) {x : A} (hx : x ∈ maximalIdeal A ^ ν) :
    e x ∈ maximalIdeal B ^ ν := by
  have h := Ideal.mem_map_of_mem (e : A →+* B) hx
  rw [Ideal.map_pow] at h
  refine Ideal.pow_right_mono ?_ ν h
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at *
  intro hu
  exact ha (by simpa using (MulEquiv.isUnit_map e.toMulEquiv).mp hu)

/-- If `ν(J_{c_0(P)}) ≥ ν`, the extension of `Ĵ_0 = J_{x_0} Ŝ_0` to `(Ŝ_0)_P` lies in the `ν`-th power
of the maximal ideal. -/
theorem map_jHat0_le_pow (hx : X.IsSimpleAt x₀) (J : Subscheme X) (ν : ℕ)
    (P : AB.xHat0 X x₀) (hP : (ν : ℕ∞) ≤ Ideal.nu (J.stalkIdeal ((AB.c0 X x₀).base P))) :
    ((J.stalkIdeal x₀).map (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀))).map
      (algebraMap (AB.Shat X x₀) (Localization.AtPrime
        (show PrimeSpectrum (AB.Shat X x₀) from P).asIdeal)) ≤
      (maximalIdeal (Localization.AtPrime
        (show PrimeSpectrum (AB.Shat X x₀) from P).asIdeal)) ^ ν := by
  classical
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  have := isRegularLocalRing_adicCompletion_of_isRegularLocalRing (X.presheaf.stalk x₀)
  have hH := stalkIdeal_comap_specMap_fromSpecStalk J x₀ (CommRingCat.of (AB.Shat X x₀))
    (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀))) P
  have hC : Subscheme.stalkIdeal (Subscheme.totalTransform (AB.c0 X x₀) J) P =
      (J.stalkIdeal ((AB.c0 X x₀).base P)).map ((AB.c0 X x₀).stalkMap P).hom :=
    Subscheme.stalkIdeal_comap J (AB.c0 X x₀) P
  have hH' : Subscheme.stalkIdeal (Subscheme.totalTransform (AB.c0 X x₀) J) P =
      (((J.stalkIdeal x₀).map (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀))).map
        (algebraMap (AB.Shat X x₀) (Localization.AtPrime
          (show PrimeSpectrum (AB.Shat X x₀) from P).asIdeal))).map
        (Spec.stalkIso (CommRingCat.of (AB.Shat X x₀))
          (show PrimeSpectrum (AB.Shat X x₀) from P)).inv.hom := hH
  set Rl := Localization.AtPrime (show PrimeSpectrum (AB.Shat X x₀) from P).asIdeal
  set y := (AB.c0 X x₀).base P
  let sm := ((AB.c0 X x₀).stalkMap P).hom
  have hJy : J.stalkIdeal y ≤ maximalIdeal (X.presheaf.stalk y) ^ ν := Ideal.le_pow_of_le_ord hP
  have hsm : (maximalIdeal (X.presheaf.stalk y)).map sm ≤ maximalIdeal
      (((AB.xHat0 X x₀).presheaf.stalk P)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at *
    exact fun hu => ha (isUnit_of_map_unit sm a hu)
  have h1 : ((((J.stalkIdeal x₀).map (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀))).map
      (algebraMap (AB.Shat X x₀) Rl)).map
      (Spec.stalkIso (CommRingCat.of (AB.Shat X x₀))
        (show PrimeSpectrum (AB.Shat X x₀) from P)).inv.hom) ≤
      maximalIdeal ((AB.xHat0 X x₀).presheaf.stalk P) ^ ν := by
    rw [← hH', hC]
    calc (J.stalkIdeal y).map sm ≤ (maximalIdeal (X.presheaf.stalk y) ^ ν).map sm :=
          Ideal.map_mono hJy
      _ = ((maximalIdeal (X.presheaf.stalk y)).map sm) ^ ν := Ideal.map_pow _ _ _
      _ ≤ _ := Ideal.pow_right_mono hsm ν
  intro u hu
  have h2 := h1 (Ideal.mem_map_of_mem _ hu)
  have hlocS : IsLocalRing ((Spec (CommRingCat.of (AB.Shat X x₀))).presheaf.stalk
      (show PrimeSpectrum (AB.Shat X x₀) from P)) :=
    inferInstanceAs (IsLocalRing ((AB.xHat0 X x₀).presheaf.stalk P))
  have h3 := equiv_mem_pow (Spec.stalkIso (CommRingCat.of (AB.Shat X x₀))
    (show PrimeSpectrum (AB.Shat X x₀) from P)).commRingCatIsoToRingEquiv ν h2
  convert h3 using 1
  exact (ConcreteCategory.congr_hom (Spec.stalkIso (CommRingCat.of (AB.Shat X x₀))
    (show PrimeSpectrum (AB.Shat X x₀) from P)).inv_hom_id u).symm

/-- Unrestricted case, p. 317: "we refer to Lemma 22, §10, Ch. III. Namely, we have `g_1 = z_0^ν +
g_{12} z_0^{ν-2} + ⋯ + g_{1ν}` with `g_{1i} ∈ T_0` and `ν_{P(S_0)_P}(g_1) ≥ ν`, so that `z_0 ∈ P`":
here `(T_0; z_0)` is the genuine regular frame of `Ŝ_0`. -/
theorem mem_of_c0_nuAt_unrestricted [Hironaka.HironakaCitedResults.{u}] (hx : X.IsSimpleAt x₀) [IsRegularLocalRing (AB.Shat X x₀)]
    (ℜ : DatumII.Raw X) (Fr : RegularFrame (AB.Shat X x₀)) (hr : Fr.r = 1)
    [CharZero (ResidueField Fr.S)] (ν : ℕ) (hν : 0 < ν) (co : Fin ν → Fr.S)
    (hco : co ⟨0, hν⟩ = 0)
    (hfJ : (Fr.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ^ ν + ∑ i : Fin ν,
      algebraMap Fr.S (AB.Shat X x₀) (co i) *
        Fr.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ^ (ν - ((i : ℕ) + 1))) ∈ jHat0 ℜ x₀)
    (P : AB.xHat0 X x₀) (hP : (ν : ℕ∞) ≤ ℜ.nuAt ((AB.c0 X x₀).base P)) :
    Fr.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ∈ (show PrimeSpectrum (AB.Shat X x₀) from P).asIdeal := by
  have : (show PrimeSpectrum (AB.Shat X x₀) from P).asIdeal.IsPrime :=
    (show PrimeSpectrum (AB.Shat X x₀) from P).isPrime
  refine frame_z_mem_of_ordElem_ge Fr hr ν hν co hco _ ?_
  refine Ideal.le_ordElem (ν := ν) ?_
  have h := map_jHat0_le_pow hx ℜ.J ν P hP
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  exact h (Ideal.mem_map_of_mem _ hfJ)

theorem exists_closed_of_ne_unrestricted (r : Restriction X) (h : r ≠ .unrestricted) :
    ∃ F, r = .closed F := by
  cases r with
  | unrestricted => exact absurd rfl h
  | closed F => exact ⟨F, rfl⟩

theorem Frame.exists_eq_closed_of_restriction_eq_closed {s : ℕ} {F' : Subscheme (T.X s)}
    (h : restriction T r s = .closed F') :
    ∃ F : Subscheme X, r = .closed F ∧ F' = (T.pre s).strictTransform F := by
  cases r with
  | unrestricted => exact absurd h (by simp [restriction, Restriction.transformSucc])
  | closed F =>
    refine ⟨F, rfl, ?_⟩
    simpa [restriction, Restriction.transformSucc] using h.symm

/-- `c_s : X̂_s → X_s` is flat (base change of `c_0 : Spec Ŝ → X`, `X̂_s = X_s ×_X X̂_0`). -/
theorem flat_c_of_completion (𝒞 : AB.Completion T x₀) (hx : X.IsSimpleAt x₀) (s : ℕ) :
    Flat (𝒞.c s) := by
  have := AB.flat_c0 X x₀ hx
  have h := 𝒞.isPullback s
  rw [𝒞.c_zero] at h
  exact MorphismProperty.of_isPullback h.flip this

/-- Base case of p. 297: `X̄_0 = V(z) = c_0⁻¹(F)` when `z` generates the ideal of `F` at `x_0`
(`[a]`, p. 315).  (Used by `strictTransformZeroLocus_eq_totalTransform`.) -/
theorem vZ_eq_totalTransform_c0 (F : Subscheme X) (z₀ : X.presheaf.stalk x₀)
    (hF : F.stalkIdeal x₀ = Ideal.span {z₀}) :
    AB.vZ X x₀ (algebraMap _ (AB.Shat X x₀) z₀) = Subscheme.totalTransform (AB.c0 X x₀) F := by
  refine Subscheme.ext_stalkIdeal fun P => ?_
  have h1 := stalkIdeal_ofIdealTop_spec (CommRingCat.of (AB.Shat X x₀))
    (Ideal.span {algebraMap _ (AB.Shat X x₀) z₀}) P
  have h2 := stalkIdeal_comap_specMap_fromSpecStalk F x₀ (CommRingCat.of (AB.Shat X x₀))
    (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀))) P
  refine h1.trans (Eq.trans ?_ h2.symm)
  rw [hF]
  simp only [Ideal.map_span, Set.image_singleton]
  rfl

/-- **The closed case of p. 297**: "for the case in which `ℜ = (ℜ^N_II, F)`, we have
`X̄_s = c_s⁻¹(F(s))` for all `s ≥ 0`", for the strict transform `X̄_s` of `V(z)` along any
completion `𝒞` of the succession, when `z` generates the ideal of `F` at `x_0`.  General enough to
serve §3 (`lem:IV.3-construction-facts`) and §4.

Deviation from the paper (gap filled): the paper states this without proof.  Induction on `s`:
`X̄_0 = V(z) = c_0⁻¹(F)`, and the strict transform commutes with the flat base change `c_{s+1}`
(`totalTransform_strictTransform_of_flat_square`), using `B̂_s = c_s⁻¹(B_s)` and the commutative square
`c_s ∘ f̂_s = f_s ∘ c_{s+1}`. -/
theorem strictTransformZeroLocus_eq_totalTransform (𝒞 : AB.Completion T x₀)
    (hx : X.IsSimpleAt x₀) (z : AB.Shat X x₀) (F : Subscheme X)
    (h0 : AB.vZ X x₀ z = Subscheme.totalTransform (AB.c0 X x₀) F) (s : ℕ) :
    AB.strictTransformZeroLocus 𝒞.tHat z s =
      Subscheme.totalTransform (𝒞.c s) ((T.pre s).strictTransform F) := by
  induction s with
  | zero => rw [𝒞.c_zero]; exact h0
  | succ s ih =>
    have : Flat (show (𝒞.tHat.monoidalTransformation s).X' ⟶ (T.monoidalTransformation s).X' from
        𝒞.c (s + 1)) := flat_c_of_completion 𝒞 hx (s + 1)
    have e := MonoidalSuccession.strictTransform_snoc (T.pre s) (T.B s)
      (T.monoidalTransformation s) F
    show Subscheme.strictTransform (𝒞.tHat.monoidalTransformation s)
      (AB.strictTransformZeroLocus 𝒞.tHat z s) = Subscheme.totalTransform (𝒞.c (s + 1))
        ((MonoidalSuccession.snoc (T.pre s) (T.B s) (T.monoidalTransformation s)).strictTransform F)
    rw [e, ih]
    exact (MonoidalTransformation.totalTransform_strictTransform_of_flat_square
      (T.monoidalTransformation s) (𝒞.tHat.monoidalTransformation s) (𝒞.c s) (𝒞.c (s + 1))
      (𝒞.c_comm s).symm (𝒞.B_hat s).symm _).symm

/-- For the closed restriction `F(t)` of `ℜ(t)`, the centre `B_t ⊆ F(t)` (permissibility, Def. 6,
p. 168) satisfies `F(t)_y ⊆ (B_t)_y` on stalks: `F(t)` is non-singular (Remark 1, p. 169), hence reduced. -/
theorem Standing.stalkIdeal_le_of_restriction_eq_closed [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) (t : ℕ) {F' : Subscheme (T.X t)}
    (hF' : restriction T r t = .closed F') :
    ∀ y ∈ (T.B t).pts, F'.stalkIdeal y ≤ (T.B t).stalkIdeal y := by
  intro y _
  obtain ⟨F, hr, rfl⟩ := Frame.exists_eq_closed_of_restriction_eq_closed hF'
  have hX := hS.ambient
  have hfor := hS.isFor
  rw [hr] at hfor
  have hcl := MonoidalSuccession.isClosedRestriction_transformII (T.pre t) hX ℜ hS.isDatum F hfor
    (by have := hS.permissible t; rw [hr] at this; exact this)
  have hF'ns : ((T.pre t).strictTransform F).IsNonsingular := by
    rcases hcl.1 with h | h
    · rw [h]; exact Subscheme.isNonsingular_empty
    · exact h.1
  have hBpts : (T.B t).pts ⊆ ((T.pre t).strictTransform F).pts := by
    have h := hS.isPermissibleCenter_B t
    rw [hF'] at h
    exact h.2
  have hcont := isContainedIn_of_pts_subset_of_isReduced
    (DatumTransform.isReduced_of_isNonsingular (hS.isNonsingular_B t))
    (DatumTransform.isReduced_of_isNonsingular hF'ns) hBpts
  exact (Subscheme.le_iff_stalkIdeal_le.mp (fun U => hcont U)) y

/-- The total transform of a subscheme along `f`, read at `y'` over the equal point `q = f(y')`:
`(f⁻¹ D)_{y'} = D_q · O_{Y',y'}` through the stalk map composed with the identification of the
stalks at equal points. -/
theorem stalkIdeal_totalTransform_congr {Y' Y : Scheme.{u}} (f : Y' ⟶ Y) (y' : Y') (q : Y)
    (h : q = f.base y') (D : Subscheme Y) :
    (Subscheme.totalTransform f D).stalkIdeal y' =
      (D.stalkIdeal q).map ((Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ f.stalkMap y').hom := by
  subst h
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  exact stalkIdeal_totalTransform f D y'

/-- Colon by a power of the unit ideal. -/
theorem colon_top_pow {R : Type u} [CommRing R] (I E : Ideal R) (hE : E = ⊤) (n : ℕ) :
    I.colon ((E ^ n : Ideal R) : Set R) = I := by
  subst hE
  simp only [Ideal.top_pow, Submodule.top_coe, Submodule.colon_univ]

/-- The stalk of `I·P⁻ⁿ` (`divPow`) at a point where `P` is the unit ideal is that of `I`
(no invertibility is needed for this inclusion on stalks, `divPow` being the largest `K` with
`K Pⁿ ⊆ I` on stalks). -/
theorem stalkIdeal_divPow_of_stalkIdeal_eq_top {Y : Scheme.{u}} (I P : Subscheme Y) (n : ℕ) (y : Y)
    (hP : P.stalkIdeal y = ⊤) : (Subscheme.divPow I P n).stalkIdeal y = I.stalkIdeal y := by
  apply le_antisymm
  · rw [Subscheme.divPow, Subscheme.stalkIdeal_sSup_eq]
    refine iSup₂_le fun K hK => ?_
    have := hK y
    rwa [hP, Ideal.top_pow, Ideal.mul_top] at this
  · have hmem : I ∈ {K : Subscheme Y | ∀ x : Y, K.stalkIdeal x * (P.stalkIdeal x) ^ n ≤
        I.stalkIdeal x} := fun x => Ideal.mul_le_left
    exact Subscheme.stalkIdeal_mono (le_sSup hmem) y

/-- A closed subscheme's inclusion is injective on points. -/
theorem subscheme_ι_injective {Y : Scheme.{u}} (D : Subscheme Y) : Function.Injective D.ι.base := by
  exact D.ι.isClosedEmbedding.injective

/-- A regular frame `(S'; z)` of a regular local ring `R` receiving a ring map from a local ring `S`
with residue field of characteristic zero has `S'/N` of characteristic zero: every integer
`n ≠ 0` is a unit in `S`, hence in `R`, in `R/(z)`, and in `S' ≅ R/(z)` (Def. 9 (1), p. 248).

Deviation from the paper (gap filled): the paper uses characteristic zero tacitly (p. 313, p. 316);
here it is derived from the residue field of the base `S ∈ 𝔅` (p. 161). -/
theorem charZero_residueField_frame_of_ringHom {S R : Type u} [CommRing S] [IsLocalRing S]
    [CharZero (ResidueField S)] [CommRing R] [IsRegularLocalRing R] (φ : S →+* R)
    (F : RegularFrame R) : CharZero (ResidueField F.S) := by
  have hunit : ∀ n : ℕ, n ≠ 0 → IsUnit (n : F.S) := by
    intro n hn
    have h1 : IsUnit (n : S) := by
      by_contra h
      have h2 : (n : S) ∈ maximalIdeal S := (mem_maximalIdeal _).mpr h
      have h3 : residue S (n : S) = 0 := (residue_eq_zero_iff _).mpr h2
      rw [map_natCast] at h3
      exact (Nat.cast_ne_zero.mpr hn) h3
    have h2 : IsUnit (n : R) := by
      have := h1.map φ
      simpa using this
    have hb := F.quot_bijective
    let ψ : F.S →+* (R ⧸ Ideal.span (Set.range F.z)) :=
      (Ideal.Quotient.mk _).comp (algebraMap F.S R)
    have h3 : IsUnit (ψ (n : F.S)) := by
      simp only [ψ, map_natCast]
      have := h2.map (Ideal.Quotient.mk (Ideal.span (Set.range F.z)))
      simpa using this
    exact (isUnit_map_iff (RingEquiv.ofBijective ψ hb) _).mp h3
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra h0
  have := (hunit n h0).map (algebraMap F.S (ResidueField F.S))
  rw [map_natCast] at this
  rw [hn] at this
  exact not_isUnit_zero this

/-- Characteristic zero for frames of local rings of a scheme over an algebraic scheme `X`:
the local ring `O_{Y,y}` receives a ring map from the base `S ∈ 𝔅` of `X` (p. 161, p. 162).
Deviation from the paper (gap filled): see `charZero_residueField_frame_of_ringHom`. -/
theorem charZero_residueField_frame_of_hom [IsAlgebraicScheme X] {Y : Scheme.{u}} (q : Y ⟶ X)
    (y : Y) [IsRegularLocalRing (Y.presheaf.stalk y)] (F : RegularFrame (Y.presheaf.stalk y)) :
    CharZero (ResidueField F.S) := by
  obtain ⟨S, _, _, hbase, p, -, -⟩ := IsAlgebraicScheme.exists_base (X := X)
  exact charZero_residueField_frame_of_ringHom
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (q ≫ p).appTop ≫ Y.presheaf.germ ⊤ y trivial).hom F

/-- `Ŝ_0` has residue field of characteristic zero, and so has the coefficient ring `S` of a regular
frame `(S; z)` of `Ŝ_0`, `S/N = Ŝ_0/M` (Def. 9 (1), p. 248): `S_0` is a local ring of the algebraic
scheme `X` over `S ∈ 𝔅`, and the residue fields of `𝔅` are of characteristic zero (p. 161).

Deviation from the paper (gap filled): the paper uses "characteristic zero" tacitly (p. 313: ``we
assume char 0''; in the Tschirnhausen substitution, p. 316).  Here it is derived: every integer
`n ≠ 0` is a unit in the base `S ∈ 𝔅` (residue field of characteristic zero), hence in the
local ring of `X` at `x_0` (an `S`-algebra), in `Ŝ_0`, and in `Ŝ_0/(z) ≅ S_frame`. -/
theorem Standing.charZero_residueField_frame (hS : Standing N ℜ r ν T x₀)
    [IsRegularLocalRing (AB.Shat X x₀)] (F : RegularFrame (AB.Shat X x₀)) :
    CharZero (ResidueField F.S) := by
  have := hS.ambient.1
  obtain ⟨S, _, _, hbase, p, -, -⟩ := IsAlgebraicScheme.exists_base (X := X)
  let φ : S →+* X.presheaf.stalk x₀ :=
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ x₀ trivial).hom
  exact charZero_residueField_frame_of_ringHom
    ((algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀)).comp φ) F

namespace Frame
variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- p. 315: "non-singular irreducible algebraic schemes `X̂_s`" -/
theorem tHat_isNonsingular [Hironaka.HironakaCitedResults.{u}] (t : ℕ) : (𝒮.tHat.X t).IsNonsingular :=
  𝒮.toCompletion.isNonsingular_tHat (hS.ambient.2.1 x₀) hS.isNonsingular_X hS.isNonsingular_B t

instance instIsRegularLocalRingStalkTHat [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (xh : 𝒮.tHat.X t) :
    IsRegularLocalRing ((𝒮.tHat.X t).presheaf.stalk xh) :=
  𝒮.tHat_isNonsingular t xh

/-- The conditions (a)$_t$–(d)$_t$ of p. 317 at the point `x̂'_t = ι(x̄)` of `X̂_t`, in the local
ring `Ŝ'_t` of `X̂_t` at `x̂'_t` (a regular local ring since `X̂_t` is non-singular): there are a
regular frame `(T'_t; z_t)` of `Ŝ'_t` (`r = 1`) and elements `g_j(t) ∈ Ŝ'_t`,
`g_j(t) = z_t^ν + g_{j1}(t) z_t^{ν-1} + ⋯ + g_{jν}(t)` with `g_{ji}(t) ∈ T'_t` (here `co j i`), such
that: (a) `z_t` generates the kernel of `Ŝ'_t → T̄'_t`, the local ring of `X̄_t` (the ideal of
`X̄_t`);
(b) `(g_1(t), …, g_m(t))` is a base of `Ĵ'_t = J'_t Ŝ'_t`, the stalk of `c_t⁻¹(J(t))`; (c)
`g_{11}(t) = 0`
without restriction; (d) the stalk of `J̄(t)` is generated by the images of the `(b̄/i)`-th
powers of
the `g_{ji}(t)` in `T̄'_t`.  The last clause records the consequences used for `[vii]` (2), (3): if
`x̂'_t ∈ B̂_t` (`Q̂'_t ≠ (1)`) then `z_t ∈ Q̂'_t` and `g_{ji}(t) ∈ (Q̂'_t ∩ T'_t)^i`. -/
def StalkInvData [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (xb : (𝒮.xBar t).toScheme)
    (F : RegularFrame ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))) (hr : F.r = 1)
    (m : ℕ) (g : Fin m → (𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))
    (co : Fin m → Fin ν → F.S) : Prop :=
  (𝒮.xBar t).stalkIdeal ((𝒮.xBar t).ι.base xb) =
      Ideal.span {F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩} ∧
    Ideal.span (Set.range g) = (Subscheme.totalTransform (𝒮.c t)
      (datum T ℜ t).J).stalkIdeal ((𝒮.xBar t).ι.base xb) ∧
    (∀ j, g j = F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ^ ν + ∑ i : Fin ν,
      algebraMap F.S _ (co j i) * F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ^ (ν - ((i : ℕ) + 1))) ∧
    (r = .unrestricted → ∃ (hm : 0 < m) (hν : 0 < ν), co ⟨0, hm⟩ ⟨0, hν⟩ = 0) ∧
    (𝒮.jBar t).stalkIdeal xb = Ideal.span (Set.range fun p : Fin m × Fin ν =>
      ((𝒮.xBar t).ι.stalkMap xb).hom
        (algebraMap F.S _ (co p.1 p.2) ^ (𝒮.bBar / ((p.2 : ℕ) + 1))))

/-- The consequences of `B_t ⊆ S_ν(ℜ(t))` at the center (p. 318): if `x̂'_t ∈ B̂_t` (`Q̂'_t ≠ (1)`)
then `z_t ∈ Q̂'_t` and `g_{ji}(t) ∈ (Q̂'_t ∩ T'_t)^i`. -/
def CenterClause [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (xb : (𝒮.xBar t).toScheme)
    (F : RegularFrame ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))) (hr : F.r = 1)
    {m : ℕ} (co : Fin m → Fin ν → F.S) : Prop :=
  (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb) ≠ ⊤ →
    F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ∈ (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb) ∧
    ∀ (j : Fin m) (i : Fin ν), co j i ∈ ((𝒮.tHat.B t).stalkIdeal
      ((𝒮.xBar t).ι.base xb)).comap (algebraMap F.S _) ^ ((i : ℕ) + 1)

def StalkInv [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (xb : (𝒮.xBar t).toScheme) : Prop :=
  ∃ (F : RegularFrame ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))) (hr : F.r = 1)
    (m : ℕ) (g : Fin m → (𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))
    (co : Fin m → Fin ν → F.S),
    𝒮.StalkInvData t xb F hr m g co ∧ 𝒮.CenterClause t xb F hr co

/-- **The closed case `X̄_t = c_t⁻¹(F(t))`** (p. 297: "for the case in which `ℜ = (ℜ^N_II, F)`, we have
`X̄_s = c_s⁻¹(F(s))` for all `s ≥ 0`").

Deviation from the paper (gap filled): proved here (`strictTransformZeroLocus_eq_totalTransform`). -/
theorem xBar_eq_totalTransform_of_restriction_eq_closed (t : ℕ) {F' : Subscheme (T.X t)}
    (hF' : restriction T r t = .closed F') :
    𝒮.xBar t = Subscheme.totalTransform (𝒮.c t) F' := by
  obtain ⟨F, hr, rfl⟩ := Frame.exists_eq_closed_of_restriction_eq_closed hF'
  obtain ⟨Fr, h1, hz, hFz, -⟩ := 𝒮.frame
  obtain ⟨z₀, hz₀, hFz₀⟩ := hFz F hr
  refine strictTransformZeroLocus_eq_totalTransform 𝒮.toCompletion (hS.ambient.2.1 x₀) 𝒮.z F ?_ t
  rw [← hz₀]
  exact vZ_eq_totalTransform_c0 F z₀ hFz₀

/-- The closed case `B̂_t ⊆ X̄_t` at any point `ŷ` of `X̂_t` over `B_t`: the stalk of `X̄_t` at `ŷ` lies
in the stalk of `B̂_t` (from `X̄_t = c_t⁻¹(F(t))`, p. 297, and `B_t ⊆ F(t)`, p. 168). -/
theorem stalkIdeal_xBar_le_bHat_of_restriction_eq_closed [Hironaka.HironakaCitedResults.{u}] (t : ℕ) {F' : Subscheme (T.X t)}
    (hF' : restriction T r t = .closed F') (y : 𝒮.tHat.X t)
    (hy : (𝒮.c t).base y ∈ (T.B t).pts) :
    (𝒮.xBar t).stalkIdeal y ≤ (𝒮.tHat.B t).stalkIdeal y := by
  rw [𝒮.xBar_eq_totalTransform_of_restriction_eq_closed t hF', stalkIdeal_totalTransform,
    𝒮.B_hat t, stalkIdeal_totalTransform]
  exact Ideal.map_mono (hS.stalkIdeal_le_of_restriction_eq_closed t hF' _ hy)

/-- p. 318 (closed case): "`z_t ∈ Q_t` (clear in the closed case)": `B̂_t ⊆ X̄_t` at `x̂'_t`.  Here
`B_t ⊆ F(t)` (permissibility, Def. 6, p. 168) and "`X̄_s = c_s⁻¹(F(s))`" (p. 322, Remark 1, closed
case), so `X̄_t ∩ c_t⁻¹(B_t) = c_t⁻¹(B_t)`.

Deviation from the paper (gap filled): `X̄_s = c_s⁻¹(F(s))` is proved
(`xBar_eq_totalTransform_of_restriction_eq_closed`). -/
theorem ideal_xBar_le_bHat_of_closed [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (xb : (𝒮.xBar t).toScheme) {F' : Subscheme (T.X t)}
    (hF' : restriction T r t = .closed F')
    (hy : (𝒮.c t).base ((𝒮.xBar t).ι.base xb) ∈ (T.B t).pts) :
    (𝒮.xBar t).stalkIdeal ((𝒮.xBar t).ι.base xb) ≤
      (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb) := by
  exact 𝒮.stalkIdeal_xBar_le_bHat_of_restriction_eq_closed t hF' _ hy

/-- p. 318: "Since `B_t` is contained in `S_ν(h_t^*(ℜ))`, `Ĵ'_t` is contained in the `ν`th power of
the ideal `Q̂'_t`" at a point `ŷ` of `B̂_t` over `S_ν(ℜ(t))`.

Deviation from the paper (gap filled): proved at the generic point of `B_t` (`le_nu_generic_iff`: the
powers of the ideal of `B_t` are primary, `S'_t/Q'_t` being regular) and transported along `c_t`. -/
theorem stalkIdeal_totalTransform_J_le_pow [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (y : 𝒮.tHat.X t)
    (hy : y ∈ (𝒮.tHat.B t).pts)
    (hx : (𝒮.c t).base y ∈ sNu (datum T ℜ t) (restriction T r t) ν) :
    (Subscheme.totalTransform (𝒮.c t) (datum T ℜ t).J).stalkIdeal y ≤
      (𝒮.tHat.B t).stalkIdeal y ^ ν := by
  have hy' : (𝒮.c t).base y ∈ (T.B t).pts := by
    have := hy
    rw [𝒮.B_hat t, FlatPreimm.pts_totalTransform] at this
    exact this
  have hBirr : (T.B t).IsIrreducible := by
    have h := hS.isPermissibleCenter_B t
    have hc : (T.B t).IsCenter := by
      generalize restriction T r t = R at h
      cases R with
      | unrestricted => exact h.1
      | closed F => exact h.1.1
    rcases hc with h0 | h0
    · rw [h0, DatumTransform.pts_empty] at hy'; exact absurd hy' (Set.notMem_empty _)
    · exact h0.2
  obtain ⟨ξ, hξ⟩ := Subscheme.exists_isGenericPoint hBirr
  have hξS : ξ ∈ sNu (datum T ℜ t) (restriction T r t) ν :=
    hS.pts_B_subset_sNu t ⟨_, hx⟩ hξ.mem
  have hνξ : (ν : ℕ∞) ≤ Ideal.nu ((datum T ℜ t).J.stalkIdeal ξ) :=
    ((mem_Snu_iff _ _ _ _).mp hξS).2
  have hJle := (Subscheme.le_nu_generic_iff (hS.isNonsingular_X t) (hS.isNonsingular_B t) hξ hy'
    (datum T ℜ t).J ν).mp hνξ
  rw [stalkIdeal_totalTransform]
  have h2 := Ideal.map_mono (f := ((𝒮.c t).stalkMap y).hom) hJle
  rw [Ideal.map_pow] at h2
  have hBeq : (𝒮.tHat.B t).stalkIdeal y =
      ((T.B t).stalkIdeal ((𝒮.c t).base y)).map ((𝒮.c t).stalkMap y).hom := by
    rw [𝒮.B_hat t, stalkIdeal_totalTransform]
  rw [hBeq]
  exact h2

/-- The center clause (p. 318: "since `B_t` is contained in `S_ν(h_t^*(ℜ))`, `J'_t` is contained in
the `ν`th power of `Q'_t`", hence `J ⊆ Q^ν`; "`z_t ∈ Q_t`: clear in the closed case, Lemma 22
otherwise"; "it then follows that `g_{ji}(t) ∈ (Q̂'_t ∩ T'_t)^i`"): given (a)$_t$–(d)$_t$ at a point
of `X̂_t` over `S_ν(ℜ(t))`.  Ring-level content: `frame_z_mem_of_mem_pow`, `frame_coeff_mem_pow`;
the scheme-level inputs are: the stalk of `B̂_t` at `x̂'_t` is a prime `Q̂` with
`Ŝ'_t/Q̂` regular (`B_t` non-singular irreducible, `c_t` regular), `Ĵ'_t ⊆ Q̂^ν` (`B_t ⊆ S_ν(ℜ(t))`),
and, in the closed case, `z_t ∈ Q̂` (`B_t ⊆ F(t)`). -/
theorem centerClause_leaf [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (xb : (𝒮.xBar t).toScheme)
    (F : RegularFrame ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))) (hr : F.r = 1)
    (m : ℕ) (g : Fin m → (𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))
    (co : Fin m → Fin ν → F.S) (hdata : 𝒮.StalkInvData t xb F hr m g co)
    (hx : (𝒮.c t).base ((𝒮.xBar t).ι.base xb) ∈ sNu (datum T ℜ t) (restriction T r t) ν) :
    𝒮.CenterClause t xb F hr co := by
  classical
  intro hne
  obtain ⟨ha, hb, hsh, hun, hd⟩ := hdata
  have hXa := hS.ambient.1
  have hBhns : (𝒮.tHat.B t).IsNonsingular :=
    𝒮.toCompletion.isNonsingular_B (hS.ambient.2.1 x₀) hS.isNonsingular_X hS.isNonsingular_B t
  have hmem : ((𝒮.xBar t).ι.base xb) ∈ (𝒮.tHat.B t).pts := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr hne
  have hQp := Subscheme.isPrime_stalkIdeal_of_isNonsingular hBhns hmem
  have hQreg := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hBhns hmem
  have hy : (𝒮.c t).base ((𝒮.xBar t).ι.base xb) ∈ (T.B t).pts := by
    have := hmem
    rw [𝒮.B_hat t, FlatPreimm.pts_totalTransform] at this
    exact this
  have hgQ : ∀ j, g j ∈ (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb) ^ ν := by
    intro j
    have hj : g j ∈ Ideal.span (Set.range g) := Ideal.subset_span ⟨j, rfl⟩
    rw [hb] at hj
    exact 𝒮.stalkIdeal_totalTransform_J_le_pow t _ hmem hx hj
  have hzQ : F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ∈ (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb) := by
    by_cases hu : r = .unrestricted
    · obtain ⟨hm, hν, h0⟩ := hun hu
      have := charZero_residueField_frame_of_hom (𝒮.c t ≫ (T.pre t).composite) ((𝒮.xBar t).ι.base xb) F
      refine frame_z_mem_of_mem_pow F hr ν hν (co ⟨0, hm⟩) h0 _ ?_
      rw [← hsh]; exact hgQ _
    · obtain ⟨F0, hF0⟩ := exists_closed_of_ne_unrestricted r hu
      have hrF : restriction T r t = .closed ((T.pre t).strictTransform F0) := by
        subst hF0; rfl
      refine (𝒮.ideal_xBar_le_bHat_of_closed t xb hrF hy) ?_
      rw [ha]; exact Ideal.subset_span rfl
  refine ⟨hzQ, ?_⟩
  intro j i
  have hzF : ∀ j, F.z j = F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ := fun j => by
    congr 1
    apply Fin.ext
    have := j.2
    show (j : ℕ) = 0
    omega
  exact frame_coeff_mem_pow F _ hzF hr _ hQreg hzQ ν (co j) (by rw [← hsh]; exact hgQ j) i

/-- (a)$_0$–(d)$_0$ (p. 317) at any point `x̂'_0` of `X̄_0`: `z_0 ∈ P` since `x̂'_0 ∈ X̄_0`, and
`(T'_0; z_0)` is a regular frame of `Ŝ'_0 = (Ŝ_0)_P`, `g_j(0) = g_j`.  No bound on `ν(Ĵ'_0)` is used
(this is the starting point of the induction of Lemma (CD.5), p. 319: "Start with the frame and base
of the proof of Lemma (CD.4)"). -/
theorem stalkInvData_zero [Hironaka.HironakaCitedResults.{u}] (xb : (𝒮.xBar 0).toScheme) :
    ∃ (F : RegularFrame ((𝒮.tHat.X 0).presheaf.stalk ((𝒮.xBar 0).ι.base xb)))
      (hr : F.r = 1) (m : ℕ) (g : Fin m → (𝒮.tHat.X 0).presheaf.stalk ((𝒮.xBar 0).ι.base xb))
      (co : Fin m → Fin ν → F.S), 𝒮.StalkInvData 0 xb F hr m g co := by
  classical
  have hreg0 := 𝒮.regShat
  have hx : X.IsSimpleAt x₀ := hS.ambient.2.1 x₀
  obtain ⟨Fr, h1, hz, hF, -, m, g, co, hspan, -, hshape, hunr, hJgen⟩ := 𝒮.frame
  have hzF : ∀ j, Fr.z j = 𝒮.z := fun j => by
    have : j = ⟨0, by rw [h1]; exact Nat.one_pos⟩ := by
      apply Fin.ext
      have h2 := j.2
      show (j : ℕ) = 0
      omega
    rw [this]; exact hz
  let P : AB.xHat0 X x₀ := (𝒮.xBar 0).ι.base xb
  have hcP : (AB.c0 X x₀).base P = (𝒮.c 0).base ((𝒮.xBar 0).ι.base xb) := by rw [𝒮.c_zero]; rfl
  have hd0 : datum T ℜ 0 = ℜ := rfl
  have hr0 : restriction T r 0 = r := by
    cases r with
    | unrestricted => rfl
    | closed F => rfl
  have hzP : 𝒮.z ∈ (show PrimeSpectrum (AB.Shat X x₀) from P).asIdeal := by
    have hmem : P ∈ (𝒮.xBar 0).pts := Subscheme.mem_pts_ι _ xb
    have := (mem_pts_ofIdealTop_spec (CommRingCat.of (AB.Shat X x₀)) (Ideal.span {𝒮.z}) P).mp hmem
    exact (Ideal.span_singleton_le_iff_mem _).mp this
  set P' : Ideal (AB.Shat X x₀) := (show PrimeSpectrum (AB.Shat X x₀) from P).asIdeal with hP'
  have hPprime : P'.IsPrime := (show PrimeSpectrum (AB.Shat X x₀) from P).isPrime
  have hRP := isRegularLocalRing_localization_of_isRegularLocalRing (AB.Shat X x₀) P'
  have hz1 : Fr.z ⟨0, by rw [h1]; exact Nat.one_pos⟩ ∈ P' := by rw [hzF]; exact hzP
  obtain ⟨Fl, hrl, φ, hzl, hφ⟩ := exists_frame_localization Fr h1 P' hz1
  let e : Localization.AtPrime P' ≃+* (𝒮.tHat.X 0).presheaf.stalk P :=
    (Spec.stalkIso (CommRingCat.of (AB.Shat X x₀))
      (show PrimeSpectrum (AB.Shat X x₀) from P)).symm.commRingCatIsoToRingEquiv
  have he : ∀ s, e s = (Spec.stalkIso (CommRingCat.of (AB.Shat X x₀))
      (show PrimeSpectrum (AB.Shat X x₀) from P)).inv.hom s := fun s => rfl
  let Fs : RegularFrame ((𝒮.tHat.X 0).presheaf.stalk P) := Fl.transport e
  have hFsz : ∀ j, Fs.z j = e (algebraMap _ _ 𝒮.z) := by
    intro j
    show e (Fl.z j) = _
    have hj : j = ⟨0, by show 0 < Fl.r; omega⟩ := by
      apply Fin.ext
      have h2 := j.2
      show (j : ℕ) = 0
      change (j : ℕ) < Fl.r at h2
      omega
    rw [hj]
    exact congrArg e (hzl.trans (congrArg (algebraMap _ _) (hzF _)))
  have hFsalg : ∀ s : Fl.S, algebraMap Fs.S _ s = e (algebraMap Fl.S _ s) := fun s => rfl
  have hdata : 𝒮.StalkInvData 0 xb Fs hrl m (fun j => e (algebraMap _ _ (g j)))
      (fun j i => φ (co j i)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- (a)
      show Subscheme.stalkIdeal (AB.vZ X x₀ 𝒮.z) P = _
      have hG := stalkIdeal_ofIdealTop_spec (CommRingCat.of (AB.Shat X x₀)) (Ideal.span {𝒮.z}) P
      refine hG.trans ?_
      rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton, hFsz]
      rfl
    · -- (b)
      have hH := stalkIdeal_comap_specMap_fromSpecStalk ℜ.J x₀ (CommRingCat.of (AB.Shat X x₀))
        (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀))) P
      have hJ : (ℜ.J.stalkIdeal x₀).map (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀)) =
          Ideal.span (Set.range g) := hspan.symm
      have hH2 : Subscheme.stalkIdeal (Scheme.IdealSheafData.comap ℜ.J (AB.c0 X x₀)) P =
          ((Ideal.span (Set.range g)).map (algebraMap (AB.Shat X x₀)
            (Localization.AtPrime P'))).map (Spec.stalkIso (CommRingCat.of (AB.Shat X x₀))
            (show PrimeSpectrum (AB.Shat X x₀) from P)).inv.hom := by
        rw [← hJ]; exact hH
      show _ = Subscheme.stalkIdeal (Subscheme.totalTransform (𝒮.c 0) (datum T ℜ 0).J) P
      rw [hd0, 𝒮.c_zero]
      refine Eq.trans ?_ hH2.symm
      rw [Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
      rfl
    · -- shape
      intro j
      dsimp only
      rw [hshape j]
      simp only [map_add, map_pow, map_sum, map_mul, hFsz]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hFsalg (φ (co j x)), hφ]
    · exact fun hu => by
        obtain ⟨hm, hν0, h0⟩ := hunr hu
        exact ⟨hm, hν0, by show φ (co ⟨0, hm⟩ ⟨0, hν0⟩) = 0; rw [h0, map_zero]⟩
    · -- (d)
      show Subscheme.stalkIdeal (Subscheme.totalTransform (𝒮.xBar 0).ι
          (Scheme.IdealSheafData.ofIdealTop ((Ideal.span 𝒮.jGen).map
            (Scheme.ΓSpecIso (CommRingCat.of (AB.Shat X x₀))).inv.hom))) xb = _
      refine (Subscheme.stalkIdeal_comap _ _ _).trans ?_
      have hG := stalkIdeal_ofIdealTop_spec (CommRingCat.of (AB.Shat X x₀)) (Ideal.span 𝒮.jGen) P
      have hG2 : Subscheme.stalkIdeal (Scheme.IdealSheafData.ofIdealTop ((Ideal.span 𝒮.jGen).map
          (Scheme.ΓSpecIso (CommRingCat.of (AB.Shat X x₀))).inv.hom)) ((𝒮.xBar 0).ι.base xb) =
          ((Ideal.span 𝒮.jGen).map (algebraMap (AB.Shat X x₀) (Localization.AtPrime P'))).map
            (Spec.stalkIso (CommRingCat.of (AB.Shat X x₀))
              (show PrimeSpectrum (AB.Shat X x₀) from P)).inv.hom := hG
      refine (congrArg (Ideal.map ((𝒮.xBar 0).ι.stalkMap xb).hom) hG2).trans ?_
      simp only [Ideal.map_span]
      refine (Ideal.map_span _ _).trans ?_
      congr 1
      ext w
      constructor
      · rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩
        rw [hJgen] at ha
        obtain ⟨j, i, rfl⟩ := ha
        refine ⟨(j, i), ?_⟩
        show ((𝒮.xBar 0).ι.stalkMap xb).hom (algebraMap Fs.S _ (φ (co j i)) ^ _) = _
        rw [hFsalg, hφ]
        simp only [map_pow, he, Frame.bBar]
        rfl
      · rintro ⟨⟨j, i⟩, rfl⟩
        have hmem : algebraMap Fr.S (AB.Shat X x₀) (co j i) ^ (ν.factorial / ((i : ℕ) + 1)) ∈
            𝒮.jGen := by rw [hJgen]; exact ⟨j, i, rfl⟩
        refine ⟨_, ⟨_, ⟨_, hmem, rfl⟩, rfl⟩, ?_⟩
        show _ = ((𝒮.xBar 0).ι.stalkMap xb).hom (algebraMap Fs.S _ (φ (co j i)) ^ _)
        rw [hFsalg, hφ]
        simp only [map_pow, he, Frame.bBar]
        rfl
  exact ⟨Fs, hrl, m, _, _, hdata⟩

/-- (a)$_0$–(d)$_0$ (p. 317): at a point `x̂'_0` of `X̂_0` over `S_ν(ℜ)`, `z_0 ∈ P` (clear in the
closed case; Lemma 22, §10, Ch. III, otherwise), `x̂'_0 ∈ X̄_0`, and `(T'_0; z_0)`, with `T'_0` the
localization of `T_0` at `P ∩ T_0`, is a regular frame of `Ŝ'_0 = (Ŝ_0)_P`; `g_j(0) = g_j`. 
Ring-level
content: `exists_frame_localization` (localization of a regular frame (`r = 1`) at a prime
containing `z_0`) and `frame_z_mem_of_mem_pow` (Lemma 22, proved from
`mem_prime_of_ordElem_localization_ge`); scheme-level content: the stalk of `X̂_0 = Spec Ŝ_0` at
`P`, the stalks of `X̄_0` and of `J̄(0)`, and `X̂_0` non-singular. -/
theorem stalkInv_zero [Hironaka.HironakaCitedResults.{u}] (xh : 𝒮.tHat.X 0)
    (hxh : (𝒮.c 0).base xh ∈ sNu (datum T ℜ 0) (restriction T r 0) ν) :
    ∃ xb, (𝒮.xBar 0).ι.base xb = xh ∧ 𝒮.StalkInv 0 xb := by
  classical
  have hreg0 := 𝒮.regShat
  have hx : X.IsSimpleAt x₀ := hS.ambient.2.1 x₀
  obtain ⟨Fr, h1, hz, hF, -, m, g, co, hspan, -, hshape, hunr, hJgen⟩ := 𝒮.frame
  have hzF : ∀ j, Fr.z j = 𝒮.z := fun j => by
    have : j = ⟨0, by rw [h1]; exact Nat.one_pos⟩ := by
      apply Fin.ext
      have h2 := j.2
      show (j : ℕ) = 0
      omega
    rw [this]; exact hz
  let P : AB.xHat0 X x₀ := xh
  have hcP : (AB.c0 X x₀).base P = (𝒮.c 0).base xh := by rw [𝒮.c_zero]; rfl
  have hd0 : datum T ℜ 0 = ℜ := rfl
  have hr0 : restriction T r 0 = r := by
    cases r with
    | unrestricted => rfl
    | closed F => rfl
  have hxh' : (𝒮.c 0).base xh ∈ sNu ℜ r ν := by rw [hd0, hr0] at hxh; exact hxh
  have hxS : (AB.c0 X x₀).base P ∈ sNu ℜ r ν := by rw [hcP]; exact hxh'
  have hν : (ν : ℕ∞) ≤ ℜ.nuAt ((AB.c0 X x₀).base P) := ((mem_Snu_iff _ _ _ _).mp hxS).2
  have hzP : 𝒮.z ∈ (show PrimeSpectrum (AB.Shat X x₀) from P).asIdeal := by
    by_cases hu : r = .unrestricted
    · obtain ⟨hm, hν0, h0⟩ := hunr hu
      have hmem : g ⟨0, hm⟩ ∈ jHat0 ℜ x₀ := hspan ▸ Ideal.subset_span ⟨_, rfl⟩
      rw [hshape] at hmem
      have hz' : Fr.z ⟨0, by rw [h1]; exact Nat.one_pos⟩ = 𝒮.z := hzF _
      have hchar : CharZero (ResidueField Fr.S) := hS.charZero_residueField_frame Fr
      have := mem_of_c0_nuAt_unrestricted hx ℜ Fr h1 ν hν0 (co ⟨0, hm⟩) h0 (by rwa [hz']) P hν
      rwa [hz'] at this
    · obtain ⟨F, hF'⟩ := exists_closed_of_ne_unrestricted r hu
      obtain ⟨z₀, hz₀, hFz⟩ := hF F hF'
      have hPF : (AB.c0 X x₀).base P ∈ F.pts := by
        rw [hF'] at hxS; exact hxS.2
      exact mem_of_c0_mem_closed hx F z₀ hFz 𝒮.z hz₀ P hPF
  have hpts : P ∈ (𝒮.xBar 0).pts := by
    show P ∈ (AB.vZ X x₀ 𝒮.z).pts
    exact (mem_pts_ofIdealTop_spec (CommRingCat.of (AB.Shat X x₀)) (Ideal.span {𝒮.z}) P).mpr
      ((Ideal.span_singleton_le_iff_mem _).mpr hzP)
  obtain ⟨xb, hxb⟩ := Subscheme.exists_ι_eq_of_mem_pts (𝒮.xBar 0) hpts
  refine ⟨xb, hxb, ?_⟩
  subst hxb
  obtain ⟨Fs, hrl, m, g', co', hdata⟩ := 𝒮.stalkInvData_zero xb
  exact ⟨Fs, hrl, m, g', co', hdata, 𝒮.centerClause_leaf 0 xb Fs hrl m g' co' hdata hxh⟩

/-- (a)$_{t+1}$–(d)$_{t+1}$ from (a)$_t$–(d)$_t$ in the case (1) of p. 318: `x̂'_t ∉ B̂_t`, so that
`f̂_t` is an isomorphism of the local rings at `x̂'_{t+1}` and `x̂'_t` (p. 167: "`f` induces an
isomorphism of `X' − f⁻¹(B)` to `X − B`") and the data is carried over unchanged
(`RegularFrame.transport`).

Deviation from the paper (gap filled): the paper treats only the case `x̂'_t ∈ B̂_t` (it assumes
`B̂_t` non-empty and `x̂'` any point of `B̂_s`, p. 317), the points of `X̂_{t+1}` outside `f̂_t⁻¹(B̂_t)`
being implicit in "(1) is true for `s = 0` and can be verified for `s+1`" and in the induction
"`x'_t ∈ S_ν(h_t^*(ℜ))`" along the whole fibre. -/
theorem stalkInvData_succ_of_notMem [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (xh' : 𝒮.tHat.X (t + 1))
    (xb : (𝒮.xBar t).toScheme) (hxb : (𝒮.xBar t).ι.base xb = (𝒮.tHat.f t).base xh')
    (hnot : (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb) = ⊤)
    (hinv : ∃ (F : RegularFrame ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))) (hr : F.r = 1)
      (m : ℕ) (g : Fin m → (𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))
      (co : Fin m → Fin ν → F.S), 𝒮.StalkInvData t xb F hr m g co) :
    ∃ xb' : (𝒮.xBar (t + 1)).toScheme, (𝒮.xBar (t + 1)).ι.base xb' = xh' ∧
      ∃ (F₁ : RegularFrame ((𝒮.tHat.X (t + 1)).presheaf.stalk ((𝒮.xBar (t + 1)).ι.base xb')))
        (hr₁ : F₁.r = 1) (m : ℕ)
        (g₁ : Fin m → (𝒮.tHat.X (t + 1)).presheaf.stalk ((𝒮.xBar (t + 1)).ι.base xb'))
        (co₁ : Fin m → Fin ν → F₁.S), 𝒮.StalkInvData (t + 1) xb' F₁ hr₁ m g₁ co₁ := by
  classical
  obtain ⟨F, hr, m, g, co, ⟨ha, hb, hsh, hun, hd⟩⟩ := hinv
  have hBnot : (𝒮.tHat.f t).base xh' ∉ (𝒮.tHat.B t).pts := by
    rw [← hxb]; exact fun h => (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp h) hnot
  have hE : xh' ∉ (𝒮.tHat.monoidalTransformation t).exceptional.pts := by
    intro h
    exact hBnot (by
      have := h
      rw [MonoidalTransformation.exceptional, FlatPreimm.pts_totalTransform] at this
      exact this)
  have hmem : xh' ∈ (𝒮.xBar (t + 1)).pts := by
    show xh' ∈ (Subscheme.strictTransform (𝒮.tHat.monoidalTransformation t) (𝒮.xBar t)).pts
    refine (MonoidalTransformation.mem_pts_strictTransform_iff_of_notMem
      (𝒮.tHat.monoidalTransformation t) (𝒮.xBar t) hE).mpr ?_
    show (𝒮.tHat.f t).base xh' ∈ (𝒮.xBar t).pts
    rw [← hxb]; exact Subscheme.mem_pts_ι _ xb
  obtain ⟨xb', hxb'⟩ := Subscheme.exists_ι_eq_of_mem_pts (𝒮.xBar (t + 1)) hmem
  subst hxb'
  have hEc : (𝒮.c (t + 1)).base ((𝒮.xBar (t + 1)).ι.base xb') ∉
      (T.monoidalTransformation t).exceptional.pts := by
    intro h
    rw [MonoidalTransformation.exceptional, FlatPreimm.pts_totalTransform] at h
    apply hBnot
    have h2 : (𝒮.tHat.f t).base ((𝒮.xBar (t + 1)).ι.base xb') ∈ (𝒮.tHat.B t).pts := by
      rw [𝒮.B_hat t, FlatPreimm.pts_totalTransform]
      show (𝒮.c t).base ((𝒮.tHat.f t).base _) ∈ (T.B t).pts
      rw [← Scheme.Hom.comp_apply, 𝒮.c_comm t, Scheme.Hom.comp_apply]
      exact h
    exact h2
  have hfb : xb = (𝒮.fBar t).base xb' := by
    refine subscheme_ι_injective (𝒮.xBar t) ?_
    rw [hxb]
    exact (congrArg (fun φ => φ.base xb') (𝒮.fBar_comm t)).symm
  subst hfb
  have hbijf : Function.Bijective ((𝒮.tHat.f t).stalkMap ((𝒮.xBar (t + 1)).ι.base xb')).hom :=
    MonoidalTransformation.bijective_stalkMap_of_notMem (𝒮.tHat.monoidalTransformation t) _ hBnot
  let ρ : ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base ((𝒮.fBar t).base xb'))) ⟶
      ((𝒮.tHat.X (t + 1)).presheaf.stalk ((𝒮.xBar (t + 1)).ι.base xb')) :=
    ((𝒮.tHat.X t).presheaf.stalkCongr (Inseparable.of_eq hxb)).hom ≫
      (𝒮.tHat.f t).stalkMap ((𝒮.xBar (t + 1)).ι.base xb')
  have hρ : Function.Bijective ρ.hom := by
    have h2 : Function.Bijective
        (((𝒮.tHat.X t).presheaf.stalkCongr (Inseparable.of_eq hxb)).hom).hom :=
      ConcreteCategory.bijective_of_isIso _
    exact hbijf.comp h2
  let e := RingEquiv.ofBijective ρ.hom hρ
  refine ⟨xb', rfl, F.transport e, hr, m, fun j => e (g j), co, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a)
    have h1 : (𝒮.xBar (t + 1)).stalkIdeal ((𝒮.xBar (t + 1)).ι.base xb') =
        (Subscheme.totalTransform (𝒮.tHat.f t) (𝒮.xBar t)).stalkIdeal
          ((𝒮.xBar (t + 1)).ι.base xb') :=
      MonoidalTransformation.strictTransform_stalkIdeal_of_notMem
        (𝒮.tHat.monoidalTransformation t) (𝒮.xBar t) hE
    rw [h1, stalkIdeal_totalTransform_congr (𝒮.tHat.f t) _ _ hxb, ha, Ideal.map_span,
      Set.image_singleton]
    rfl
  · -- (b)
    have hdat : datum T ℜ (t + 1) = (datum T ℜ t).transform (T.monoidalTransformation t) :=
      MonoidalSuccession.transformII_snoc (T.pre t) (T.B t) (T.monoidalTransformation t) ℜ
    have hJ : (datum T ℜ (t + 1)).J = Subscheme.divPow
        (Subscheme.totalTransform (T.f t) (datum T ℜ t).J) (T.monoidalTransformation t).exceptional
        (datum T ℜ t).nu.toNat := by
      rw [hdat]
      rfl
    have hsq : 𝒮.c (t + 1) ≫ T.f t = 𝒮.tHat.f t ≫ 𝒮.c t := (𝒮.c_comm t).symm
    have hdiv := Subscheme.stalkIdeal_divPow
      (I := Subscheme.totalTransform (T.f t) (datum T ℜ t).J)
      (P := (T.monoidalTransformation t).exceptional) (T.monoidalTransformation t).invertible (datum T ℜ t).nu.toNat
      ((𝒮.c (t + 1)).base ((𝒮.xBar (t + 1)).ι.base xb'))
    have htop : (T.monoidalTransformation t).exceptional.stalkIdeal
        ((𝒮.c (t + 1)).base ((𝒮.xBar (t + 1)).ι.base xb')) = ⊤ :=
      Subscheme.stalkIdeal_eq_top_of_notMem_pts hEc
    have hcol : (Subscheme.divPow (Subscheme.totalTransform (T.f t) (datum T ℜ t).J)
        (T.monoidalTransformation t).exceptional (datum T ℜ t).nu.toNat).stalkIdeal
          ((𝒮.c (t + 1)).base ((𝒮.xBar (t + 1)).ι.base xb')) =
        (Subscheme.totalTransform (T.f t) (datum T ℜ t).J).stalkIdeal
          ((𝒮.c (t + 1)).base ((𝒮.xBar (t + 1)).ι.base xb')) := by
      exact hdiv.trans (colon_top_pow _ _ htop (datum T ℜ t).nu.toNat)
    have key : (Subscheme.totalTransform (𝒮.c (t + 1)) (datum T ℜ (t + 1)).J).stalkIdeal
        ((𝒮.xBar (t + 1)).ι.base xb') =
        (Subscheme.totalTransform (𝒮.tHat.f t) (Subscheme.totalTransform (𝒮.c t)
          (datum T ℜ t).J)).stalkIdeal ((𝒮.xBar (t + 1)).ι.base xb') := by
      rw [hJ, stalkIdeal_totalTransform, hcol, ← stalkIdeal_totalTransform,
        ← Subscheme.totalTransform_comp, hsq, Subscheme.totalTransform_comp]
    rw [key, stalkIdeal_totalTransform_congr (𝒮.tHat.f t) _ _ hxb, ← hb, Ideal.map_span,
      ← Set.range_comp]
    rfl
  · -- shape
    intro j
    show e (g j) = e (F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩) ^ ν + ∑ i : Fin ν,
      e (algebraMap F.S _ (co j i)) * e (F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩) ^ (ν - ((i : ℕ) + 1))
    rw [hsh j]
    simp only [map_add, map_pow, map_sum, map_mul]
  · intro hu
    exact hun hu
  · -- (d)
    have hpB : (𝒮.pBar t).stalkIdeal xb' = ⊤ := by
      refine by_contra fun h => hEc ?_
      have h2 := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr h
      unfold pBar at h2
      rw [FlatPreimm.pts_totalTransform, FlatPreimm.pts_totalTransform] at h2
      exact h2
    have hj : (𝒮.jBar (t + 1)).stalkIdeal xb' =
        (Subscheme.totalTransform (𝒮.fBar t) (𝒮.jBar t)).stalkIdeal xb' :=
      stalkIdeal_divPow_of_stalkIdeal_eq_top _ _ _ _ hpB
    rw [hj, stalkIdeal_totalTransform, hd, Ideal.map_span, ← Set.range_comp]
    obtain ⟨h, hh⟩ := AB.exists_stalkMap_comm (f := (𝒮.xBar t).ι) (fh := (𝒮.xBar (t + 1)).ι)
      (c := 𝒮.tHat.f t) (c' := 𝒮.fBar t) (𝒮.fBar_comm t).symm xb'
    have hsq2 : ∀ x, ((𝒮.fBar t).stalkMap xb').hom (((𝒮.xBar t).ι.stalkMap ((𝒮.fBar t).base xb')).hom x)
        = ((𝒮.xBar (t + 1)).ι.stalkMap xb').hom (e x) := by
      intro x
      have := congrArg (fun φ => φ.hom x) hh
      exact this
    congr 2
    funext p
    simp only [Function.comp, map_pow]
    rw [hsq2]
    rfl

/-- The stalks of `c_t⁻¹(J(t))` are non-zero (`J(t)` has non-zero stalks, Def. 3 (II), and the stalk maps
of the flat local morphism `c_t` are injective). -/
theorem stalkIdeal_totalTransform_J_ne_bot [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (y : 𝒮.tHat.X t) :
    (Subscheme.totalTransform (𝒮.c t) (datum T ℜ t).J).stalkIdeal y ≠ ⊥ := by
  have hXa := hS.ambient.1
  have hd := ((T.pre t).isAmbient_transformII hS.ambient ℜ hS.isDatum
    (hS.permissible t).isPermissibleII).2
  have hJ : ∀ x, (datum T ℜ t).J.stalkIdeal x ≠ ⊥ := hd.2.2.2
  have hflat : Flat (𝒮.c t) := flat_c_of_completion 𝒮.toCompletion (hS.ambient.2.1 x₀) t
  let : Algebra ((T.X t).presheaf.stalk ((𝒮.c t).base y)) ((𝒮.tHat.X t).presheaf.stalk y) :=
    ((𝒮.c t).stalkMap y).hom.toAlgebra
  have : Module.Flat ((T.X t).presheaf.stalk ((𝒮.c t).base y)) ((𝒮.tHat.X t).presheaf.stalk y) :=
    Flat.stalkMap (𝒮.c t) y
  have : IsLocalHom (algebraMap ((T.X t).presheaf.stalk ((𝒮.c t).base y))
      ((𝒮.tHat.X t).presheaf.stalk y)) := inferInstanceAs (IsLocalHom ((𝒮.c t).stalkMap y).hom)
  have : Module.FaithfullyFlat ((T.X t).presheaf.stalk ((𝒮.c t).base y))
      ((𝒮.tHat.X t).presheaf.stalk y) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (algebraMap ((T.X t).presheaf.stalk ((𝒮.c t).base y))
      ((𝒮.tHat.X t).presheaf.stalk y)) := FaithfulSMul.algebraMap_injective _ _
  rw [stalkIdeal_totalTransform]
  intro h0
  apply hJ ((𝒮.c t).base y)
  rw [eq_bot_iff]
  intro a ha
  have h1 : ((𝒮.c t).stalkMap y).hom a ∈
      ((datum T ℜ t).J.stalkIdeal ((𝒮.c t).base y)).map ((𝒮.c t).stalkMap y).hom :=
    Ideal.mem_map_of_mem _ ha
  rw [h0, Submodule.mem_bot] at h1
  rw [Submodule.mem_bot]
  exact hinj (h1.trans (map_zero _).symm)

/-- **The step `t → t+1` at a point `x̂'_{t+1}` over `x̂'_t ∈ B̂_t`** (case (2) of p. 318), before the
choice of the point of `X̄_{t+1}`: the stalk `Ŝ'_{t+1}` of `X̂_{t+1}` is a monoidal transform of `Ŝ'_t`
with center `Q̂'_t` (`exists_monoidalTransform_stalk`), and `frame_step_core` gives the frame
`(T'_{t+1}; z_{t+1})`, `z_{t+1}` a non-unit generating the ideal of `X̄_{t+1}`, with
`g_j(t+1) = g_j(t)/w_t^ν` a base of the stalk of `c_{t+1}⁻¹ J(t+1)`, `g_{ji}(t+1) = g_{ji}(t)/w_t^i`
up to a unit, and `W = w_t` generating the stalk of the exceptional divisor, `W ∉ (z_{t+1})`.

Deviation from the paper (gap filled): the paper says only "Taking `w_t` with `(w_t)Ŝ'_{t+1} = Q̂'_tŜ'_{t+1}`, the `g_j(t)/w_t^ν` form a base of `Ĵ'_{t+1}` lying in the `ν`th power of the
maximal ideal, so `w_t⁻¹(Q̂'_t ∩ T'_t)Ŝ'_{t+1}` is the unit ideal and there is `v_t ∈ T'_t` with `(v_t)Ŝ'_{t+1} = Q̂'_tŜ'_{t+1}`; `z_{t+1} = z_t/v_t` generates the ideal of `X̄_{t+1}`
and is a non-unit" (p. 318).  Lean proves: the stalk of `c_{t+1}⁻¹ J(t+1)` is `(g_j(t)/w^ν)` (colon ideals
commute with the flat extension `c_{t+1}`), the strict transform of `(z)` is `(z/w)` because
`z ∉ Q̂'²` (`z` is a regular parameter), and `W ∉ (z_{t+1})` (otherwise `z ∈ Q̂'²`). -/
theorem exists_stalk_data_succ_of_mem [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (xh' : 𝒮.tHat.X (t + 1))
    (hx : (𝒮.c (t + 1)).base xh' ∈ sNu (datum T ℜ (t + 1)) (restriction T r (t + 1)) ν)
    (xb : (𝒮.xBar t).toScheme) (hxb : (𝒮.xBar t).ι.base xb = (𝒮.tHat.f t).base xh')
    (hBne : (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb) ≠ ⊤)
    (hνt : (datum T ℜ t).nu = ν)
    (hinv : ∃ (F : RegularFrame ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))) (hr : F.r = 1)
      (m : ℕ) (g : Fin m → (𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))
      (co : Fin m → Fin ν → F.S), 𝒮.StalkInvData t xb F hr m g co) :
    ∃ (F : RegularFrame ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb)))
      (hr : F.r = 1) (m : ℕ) (g : Fin m → (𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))
      (co : Fin m → Fin ν → F.S) (_ : 𝒮.StalkInvData t xb F hr m g co)
      (F₁ : RegularFrame ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) (hr₁ : F₁.r = 1)
      (g₁ : Fin m → (𝒮.tHat.X (t + 1)).presheaf.stalk xh') (co₁ : Fin m → Fin ν → F₁.S),
      (𝒮.xBar (t + 1)).stalkIdeal xh' = Ideal.span {F₁.z ⟨0, by rw [hr₁]; exact Nat.one_pos⟩} ∧
      F₁.z ⟨0, by rw [hr₁]; exact Nat.one_pos⟩ ∈ maximalIdeal ((𝒮.tHat.X (t + 1)).presheaf.stalk xh') ∧
      Ideal.span (Set.range g₁) =
        (Subscheme.totalTransform (𝒮.c (t + 1)) (datum T ℜ (t + 1)).J).stalkIdeal xh' ∧
      (∀ j, g₁ j = F₁.z ⟨0, by rw [hr₁]; exact Nat.one_pos⟩ ^ ν + ∑ i : Fin ν,
        algebraMap F₁.S _ (co₁ j i) * F₁.z ⟨0, by rw [hr₁]; exact Nat.one_pos⟩ ^ (ν - ((i : ℕ) + 1))) ∧
      (r = .unrestricted → ∃ (hm : 0 < m) (hν : 0 < ν), co₁ ⟨0, hm⟩ ⟨0, hν⟩ = 0) ∧
      ∃ (W : (𝒮.tHat.X (t + 1)).presheaf.stalk xh') (U : ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')ˣ),
        Ideal.span {W} = (𝒮.tHat.monoidalTransformation t).exceptional.stalkIdeal xh' ∧
        W ∉ Ideal.span {F₁.z ⟨0, by rw [hr₁]; exact Nat.one_pos⟩} ∧
        ∀ (j : Fin m) (i : Fin ν),
          (((𝒮.tHat.X t).presheaf.stalkCongr (Inseparable.of_eq hxb)).hom ≫
              (𝒮.tHat.f t).stalkMap xh').hom (algebraMap F.S _ (co j i)) =
            algebraMap F₁.S _ (co₁ j i) * (W * (U : (𝒮.tHat.X (t + 1)).presheaf.stalk xh')) ^ ((i : ℕ) + 1) := by
  classical
  have := hS.ambient.1
  obtain ⟨F, hr, m, g, co, hdata⟩ := hinv
  obtain ⟨ha, hb, hsh, hun, hd⟩ := hdata
  have hBhns : (𝒮.tHat.B t).IsNonsingular :=
    𝒮.toCompletion.isNonsingular_B (hS.ambient.2.1 x₀) hS.isNonsingular_X hS.isNonsingular_B t
  have hmem0 : (𝒮.xBar t).ι.base xb ∈ (𝒮.tHat.B t).pts :=
    Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr hBne
  have hmem : (𝒮.tHat.f t).base xh' ∈ (𝒮.tHat.B t).pts := hxb ▸ hmem0
  have : IsRegularLocalRing ((𝒮.tHat.X t).presheaf.stalk
      ((𝒮.tHat.monoidalTransformation t).f.base xh')) :=
    𝒮.instIsRegularLocalRingStalkTHat t _
  have : IsDomain ((𝒮.tHat.X t).presheaf.stalk ((𝒮.tHat.monoidalTransformation t).f.base xh')) :=
    isDomain_of_isRegularLocalRing _
  have hQp : ((𝒮.tHat.B t).stalkIdeal
      ((𝒮.tHat.monoidalTransformation t).f.base xh')).IsPrime :=
    Subscheme.isPrime_stalkIdeal_of_isNonsingular hBhns hmem
  have hQreg : IsRegularLocalRing ((𝒮.tHat.X t).presheaf.stalk
      ((𝒮.tHat.monoidalTransformation t).f.base xh') ⧸ (𝒮.tHat.B t).stalkIdeal
        ((𝒮.tHat.monoidalTransformation t).f.base xh')) :=
    Subscheme.isRegularLocalRing_quotient_of_isNonsingular hBhns hmem
  obtain ⟨s, e, he, hE⟩ :=
    (𝒮.tHat.monoidalTransformation t).exists_monoidalTransform_stalk_exceptional xh'
  -- transport of the frame to the stalk at `f̂_t(x̂'_{t+1})`
  let κ : ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb)) ≃+*
      ((𝒮.tHat.X t).presheaf.stalk ((𝒮.tHat.monoidalTransformation t).f.base xh')) :=
    ((𝒮.tHat.X t).presheaf.stalkCongr (Inseparable.of_eq hxb)).commRingCatIsoToRingEquiv
  have hκD : ∀ D : Subscheme (𝒮.tHat.X t),
      D.stalkIdeal ((𝒮.tHat.monoidalTransformation t).f.base xh') =
        (D.stalkIdeal ((𝒮.xBar t).ι.base xb)).map κ.toRingHom := fun D =>
    Subscheme.stalkIdeal_eq_map_stalkCongr D hxb
  let F₀ := F.transport κ
  have hr₀ : F₀.r = 1 := hr
  let z₀ := F₀.z ⟨0, by rw [hr₀]; exact Nat.one_pos⟩
  have hzF₀ : ∀ j, F₀.z j = z₀ := fun j => by
    congr 1
    apply Fin.ext
    have := j.2
    show (j : ℕ) = 0
    omega
  let g₀ : Fin m → (𝒮.tHat.X t).presheaf.stalk ((𝒮.tHat.monoidalTransformation t).f.base xh') :=
    fun j => κ (g j)
  have hA : (𝒮.xBar t).stalkIdeal ((𝒮.tHat.monoidalTransformation t).f.base xh') =
      Ideal.span {z₀} := by
    rw [hκD, ha, Ideal.map_span, Set.image_singleton]
    rfl
  have hB : (Subscheme.totalTransform (𝒮.c t) (datum T ℜ t).J).stalkIdeal
      ((𝒮.tHat.monoidalTransformation t).f.base xh') = Ideal.span (Set.range g₀) := by
    rw [hκD, ← hb, Ideal.map_span, ← Set.range_comp]
    rfl
  have hsh₀ : ∀ j, g₀ j = z₀ ^ ν + ∑ i : Fin ν,
      algebraMap F₀.S _ (co j i) * z₀ ^ (ν - ((i : ℕ) + 1)) := by
    intro j
    show κ (g j) = κ (F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩) ^ ν + ∑ i : Fin ν,
      κ (algebraMap F.S _ (co j i)) * κ (F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩) ^ (ν - ((i : ℕ) + 1))
    rw [hsh j]
    simp only [map_add, map_pow, map_sum, map_mul]
  have hxt : (𝒮.c t).base ((𝒮.tHat.f t).base xh') ∈
      sNu (datum T ℜ t) (restriction T r t) ν := by
    have h1 := hS.f_mem_sNu t hx
    have hcomm : (𝒮.c t).base ((𝒮.tHat.f t).base xh') = (T.f t).base ((𝒮.c (t + 1)).base xh') := by
      rw [← Scheme.Hom.comp_apply, 𝒮.c_comm t, Scheme.Hom.comp_apply]
    rw [hcomm]; exact h1
  have hJQ := 𝒮.stalkIdeal_totalTransform_J_le_pow t _ hmem hxt
  have hgQ₀ : ∀ j, g₀ j ∈
      (𝒮.tHat.B t).stalkIdeal ((𝒮.tHat.monoidalTransformation t).f.base xh') ^ ν := fun j => by
    apply hJQ
    show g₀ j ∈ (Subscheme.totalTransform (𝒮.c t) (datum T ℜ t).J).stalkIdeal
      ((𝒮.tHat.monoidalTransformation t).f.base xh')
    rw [hB]; exact Ideal.subset_span ⟨j, rfl⟩
  -- the denominator `w = x` of the monoidal transform and the quotients `h_j = g_j / w^ν`
  have hw : Ideal.span {s.xR} =
      ((𝒮.tHat.B t).stalkIdeal ((𝒮.tHat.monoidalTransformation t).f.base xh')).map s.toRing :=
    s.span_xR_eq_map
  have hexh : ∀ j, ∃ hj : s.ring, s.xR ^ ν * hj = s.toRing (g₀ j) := fun j => by
    have h1 := Ideal.mem_map_of_mem s.toRing (hgQ₀ j)
    rw [Ideal.map_pow, ← hw, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, hc.symm⟩
  choose h hh using hexh
  have hdomX : IsDomain ((𝒮.tHat.X (t + 1)).presheaf.stalk xh') := by
    have := 𝒮.instIsRegularLocalRingStalkTHat (t + 1) xh'
    exact isDomain_of_isRegularLocalRing _
  have : IsDomain ((𝒮.tHat.monoidalTransformation t).X'.presheaf.stalk xh') := hdomX
  have : IsLocalRing ((𝒮.tHat.monoidalTransformation t).X'.presheaf.stalk xh') :=
    inferInstanceAs (IsLocalRing ((𝒮.tHat.X (t + 1)).presheaf.stalk xh'))
  have hw0 : e s.xR ≠ 0 := fun h0 =>
    s.x_ne_zero (s.toRing_injective (by
      have := e.injective (h0.trans (map_zero e).symm)
      rw [map_zero]; exact this))
  -- the stalk of `c_{t+1}⁻¹ J(t+1)` is generated by the `e (h_j)`
  have hJstalk : (Subscheme.totalTransform (𝒮.c (t + 1)) (datum T ℜ (t + 1)).J).stalkIdeal xh' =
      Ideal.span (Set.range fun j => e (h j)) := by
    have hdat : datum T ℜ (t + 1) = (datum T ℜ t).transform (T.monoidalTransformation t) :=
      MonoidalSuccession.transformII_snoc (T.pre t) (T.B t) (T.monoidalTransformation t) ℜ
    have hJ : (datum T ℜ (t + 1)).J = Subscheme.divPow
        (Subscheme.totalTransform (T.f t) (datum T ℜ t).J)
        (T.monoidalTransformation t).exceptional ν := by
      rw [hdat]
      show Subscheme.divPow _ _ (datum T ℜ t).nu.toNat = _
      rw [hνt]; rfl
    have hflat : Flat (𝒮.c (t + 1)) := flat_c_of_completion 𝒮.toCompletion (hS.ambient.2.1 x₀) (t + 1)
    have hdiv := Subscheme.stalkIdeal_divPow
      (I := Subscheme.totalTransform (T.f t) (datum T ℜ t).J)
      (P := (T.monoidalTransformation t).exceptional) (T.monoidalTransformation t).invertible ν
      ((𝒮.c (t + 1)).base xh')
    obtain ⟨a, haE, -⟩ := (T.monoidalTransformation t).invertible.exists_stalkIdeal_eq_span
      ((𝒮.c (t + 1)).base xh')
    let : Algebra ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh'))
        ((𝒮.tHat.X (t + 1)).presheaf.stalk xh') := ((𝒮.c (t + 1)).stalkMap xh').hom.toAlgebra
    have : Module.Flat ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh'))
        ((𝒮.tHat.X (t + 1)).presheaf.stalk xh') := Flat.stalkMap (𝒮.c (t + 1)) xh'
    have hsq : 𝒮.c (t + 1) ≫ T.f t = 𝒮.tHat.f t ≫ 𝒮.c t := (𝒮.c_comm t).symm
    have e1 : (Subscheme.totalTransform (𝒮.c (t + 1)) (datum T ℜ (t + 1)).J).stalkIdeal xh' =
        (((Subscheme.totalTransform (T.f t) (datum T ℜ t).J).stalkIdeal ((𝒮.c (t + 1)).base xh')).colon
          ({a ^ ν} : Set _)).map (algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) := by
      rw [stalkIdeal_totalTransform, hJ]
      exact congrArg (Ideal.map _) (hdiv.trans (Ideal.colon_pow_of_eq_span _ _ a haE ν))
    have e2 := Ideal.map_colon_singleton_eq_of_flat (A' := (𝒮.tHat.X (t + 1)).presheaf.stalk xh')
      ((Subscheme.totalTransform (T.f t) (datum T ℜ t).J).stalkIdeal ((𝒮.c (t + 1)).base xh'))
      (a ^ ν)
    have e3 : ((Subscheme.totalTransform (T.f t) (datum T ℜ t).J).stalkIdeal
        ((𝒮.c (t + 1)).base xh')).map (algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) =
        Ideal.span (Set.range fun j => (e s.xR) ^ ν * e (h j)) := by
      have h1 := (stalkIdeal_totalTransform (𝒮.c (t + 1))
        (Subscheme.totalTransform (T.f t) (datum T ℜ t).J) xh').symm
      have h2 : Subscheme.totalTransform (𝒮.c (t + 1))
          (Subscheme.totalTransform (T.f t) (datum T ℜ t).J) =
          Subscheme.totalTransform (𝒮.tHat.f t)
            (Subscheme.totalTransform (𝒮.c t) (datum T ℜ t).J) := by
        rw [← Subscheme.totalTransform_comp, hsq, Subscheme.totalTransform_comp]
      rw [h2, stalkIdeal_totalTransform (𝒮.tHat.f t)
        (Subscheme.totalTransform (𝒮.c t) (datum T ℜ t).J) xh'] at h1
      refine h1.trans ?_
      have hB' : (Subscheme.totalTransform (𝒮.c t) (datum T ℜ t).J).stalkIdeal
          ((𝒮.tHat.f t).base xh') = Ideal.span (Set.range g₀) := hB
      rw [hB']
      refine (Ideal.map_span _ _).trans ?_
      refine congrArg Ideal.span ((Set.range_comp _ _).symm.trans
        (congrArg Set.range (funext fun j => ?_)))
      have h1 := RingHom.congr_fun he (g₀ j)
      refine h1.symm.trans ?_
      show e (s.toRing (g₀ j)) = _
      rw [← hh j, map_mul, map_pow]
    have e4 : Ideal.span {(algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) a} = Ideal.span {e s.xR} := by
      have h1 : (Subscheme.totalTransform (𝒮.c (t + 1)) (T.monoidalTransformation t).exceptional).stalkIdeal
          xh' = ((T.monoidalTransformation t).exceptional.stalkIdeal ((𝒮.c (t + 1)).base xh')).map
            (algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) := stalkIdeal_totalTransform _ _ _
      have h2 := MonoidalTransformation.totalTransform_exceptional_of_square
        (T.monoidalTransformation t) (𝒮.tHat.monoidalTransformation t) (𝒮.c t) (𝒮.c (t + 1)) hsq
        (𝒮.B_hat t).symm
      have h3 := (congrArg (fun D => Subscheme.stalkIdeal D xh') h2).symm.trans h1
      have h4 : Ideal.span {e s.xR} = Ideal.map (algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) (Ideal.span {a}) :=
        hE.symm.trans (h3.trans (congrArg (Ideal.map (algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh'))) haE))
      have h5 := Ideal.map_span (algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) ({a} : Set ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')))
      exact (h4.trans (h5.trans (congrArg Ideal.span Set.image_singleton))).symm
    have e5 : Ideal.span {(algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) (a ^ ν)} = Ideal.span {e s.xR} ^ ν := by
      have h6 : (algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) (a ^ ν) = ((algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) a) ^ ν := map_pow _ _ _
      rw [h6, ← Ideal.span_singleton_pow, e4]
      rfl
    have e6 : ∀ I : Ideal ((𝒮.tHat.X (t + 1)).presheaf.stalk xh'),
        I.colon ({(algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) (a ^ ν)} : Set _) = I.colon ((Ideal.span ({(e s.xR : (𝒮.tHat.X (t + 1)).presheaf.stalk xh')} : Set ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) ^ ν : Ideal ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) : Set ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) :=
      fun I => by rw [← Ideal.colon_span, e5]; rfl
    refine e1.trans (e2.trans ?_)
    refine (congrArg (fun I => I.colon ({(algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) (a ^ ν)} : Set _)) e3).trans ?_
    exact (e6 _).trans (Ideal.colon_span_range_mul_pow (e s.xR) hw0 ν (fun j => e (h j)))
  have hhm : ∀ j, h j ∈ maximalIdeal s.ring ^ ν := fun j => by
    have hnu : (ν : ℕ∞) ≤ Ideal.nu ((datum T ℜ (t + 1)).J.stalkIdeal ((𝒮.c (t + 1)).base xh')) :=
      ((mem_Snu_iff _ _ _ _).mp hx).2
    have hJm := Ideal.le_pow_of_le_ord hnu
    have h1 : e (h j) ∈
        (Subscheme.totalTransform (𝒮.c (t + 1)) (datum T ℜ (t + 1)).J).stalkIdeal xh' := by
      rw [hJstalk]; exact Ideal.subset_span ⟨j, rfl⟩
    rw [stalkIdeal_totalTransform] at h1
    have h2 := Ideal.map_mono (f := ((𝒮.c (t + 1)).stalkMap xh').hom) hJm h1
    rw [Ideal.map_pow] at h2
    have h3 : (maximalIdeal ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh'))).map
        ((𝒮.c (t + 1)).stalkMap xh').hom ≤
        maximalIdeal ((𝒮.tHat.X (t + 1)).presheaf.stalk xh') := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).mp hx (IsUnit.of_map _ x hu)
    exact mem_pow_maximalIdeal_of_ringEquiv e (Ideal.pow_right_mono h3 ν h2)
  have hz2 : z₀ ∉ maximalIdeal ((𝒮.tHat.X t).presheaf.stalk
      ((𝒮.tHat.monoidalTransformation t).f.base xh')) ^ 2 :=
    F₀.extends_rsop.notMem_maximalIdeal_sq (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hstrict : ∀ ζ : s.ring, z₀ ∈ (𝒮.tHat.B t).stalkIdeal
      ((𝒮.tHat.monoidalTransformation t).f.base xh') → s.toRing z₀ = s.xR * ζ →
      (𝒮.xBar (t + 1)).stalkIdeal xh' = Ideal.span {e ζ} := by
    intro ζ hzQ hζ
    have h1 := MonoidalTransformation.stalkIdeal_strictTransform_eq_map
      (𝒮.tHat.monoidalTransformation t) xh' s e he (Or.inl ⟨hQp, hQreg⟩) (𝒮.xBar t)
    have hord := Ideal.ordElem_eq_one_of_mem_of_notMem_sq hQp.ne_top hzQ hz2
    have h2 : strictTransformIdeal s (Ideal.span {z₀}) = Ideal.span {ζ} := by
      refine strictTransformIdeal_span_singleton_eq s hQp hQreg z₀ ζ ?_
      rw [hord]; simpa using hζ.symm
    show (Subscheme.strictTransform (𝒮.tHat.monoidalTransformation t) (𝒮.xBar t)).stalkIdeal xh' = _
    rw [h1, hA, h2]
    exact (Ideal.map_span _ _).trans (congrArg Ideal.span Set.image_singleton)
  have hzQclosed : ¬ (r = .unrestricted) → z₀ ∈ (𝒮.tHat.B t).stalkIdeal
      ((𝒮.tHat.monoidalTransformation t).f.base xh') := fun hu => by
    obtain ⟨F0, hF0⟩ := exists_closed_of_ne_unrestricted r hu
    have hrF : restriction T r t = .closed ((T.pre t).strictTransform F0) := by subst hF0; rfl
    have hy' : (𝒮.c t).base ((𝒮.tHat.monoidalTransformation t).f.base xh') ∈ (T.B t).pts := by
      have := hmem
      rw [𝒮.B_hat t, FlatPreimm.pts_totalTransform] at this
      exact this
    have := 𝒮.stalkIdeal_xBar_le_bHat_of_restriction_eq_closed t hrF _ hy'
    exact this (by rw [hA]; exact Ideal.subset_span rfl)
  have hζcl : ¬ (r = .unrestricted) → ∀ ζ : s.ring, s.toRing z₀ = s.xR * ζ →
      ζ ∈ maximalIdeal s.ring := by
    intro hu ζ hζ
    obtain ⟨F0, hF0⟩ := exists_closed_of_ne_unrestricted r hu
    have hrF' : restriction T r (t + 1) = .closed ((T.pre (t + 1)).strictTransform F0) := by
      subst hF0; rfl
    have hFpts : (𝒮.c (t + 1)).base xh' ∈ ((T.pre (t + 1)).strictTransform F0).pts := by
      have h1 := hx
      rw [hrF'] at h1
      exact h1.2
    have hxpts : xh' ∈ (𝒮.xBar (t + 1)).pts := by
      rw [𝒮.xBar_eq_totalTransform_of_restriction_eq_closed (t + 1) hrF',
        FlatPreimm.pts_totalTransform]
      exact hFpts
    have hne := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hxpts
    rw [hstrict ζ (hzQclosed hu) hζ] at hne
    by_contra hζm
    apply hne
    exact Ideal.span_singleton_eq_top.mpr ((IsLocalRing.notMem_maximalIdeal.mp hζm).map e)
  have hregX := 𝒮.instIsRegularLocalRingStalkTHat (t + 1) xh'
  have : IsRegularLocalRing s.ring :=
    IsRegularLocalRing.of_ringEquiv (R := (𝒮.tHat.X (t + 1)).presheaf.stalk xh') e.symm
  have hm0 : 0 < m := by
    by_contra h0
    have hm : m = 0 := by omega
    have hempty : IsEmpty (Fin m) := by rw [hm]; infer_instance
    have h1 := 𝒮.stalkIdeal_totalTransform_J_ne_bot t ((𝒮.tHat.monoidalTransformation t).f.base xh')
    apply h1
    rw [hB]
    have : Set.range g₀ = ∅ := Set.range_eq_empty _
    rw [this, Ideal.span_empty]
  have hν0 : 0 < ν := hS.nu_pos
  have hunr : (r = .unrestricted) →
      (∃ (hm : 0 < m), co ⟨0, hm⟩ ⟨0, hν0⟩ = 0) ∧ CharZero (ResidueField F₀.S) := fun hu => by
    obtain ⟨hm, hν, h0⟩ := hun hu
    exact ⟨⟨hm, h0⟩, charZero_residueField_frame_of_hom (𝒮.c t ≫ (T.pre t).composite) _ F₀⟩
  obtain ⟨hz₀Q, hcoefQ, F', hr', z', ζ, co', hFz', hζeq, hassoc, hz'm, hu', hco0, u, hcoefrel⟩ :=
    frame_step_core F₀ z₀ hzF₀ hr₀ ν hν0 m g₀ co hsh₀ (r = .unrestricted) hunr
      ((𝒮.tHat.B t).stalkIdeal ((𝒮.tHat.monoidalTransformation t).f.base xh')) hgQ₀ hzQclosed s
      s.xR hw hζcl hm0 h hhm hh
  have hj0 : (0 : ℕ) < F'.r := by rw [hr']; exact Nat.one_pos
  have hz'0 : F'.z ⟨0, hj0⟩ = z' := hFz' _
  refine ⟨F, hr, m, g, co, ⟨ha, hb, hsh, hun, hd⟩, F'.transport e, hr',
    fun j => e (z' ^ ν + ∑ i : Fin ν, algebraMap F'.S s.ring (co' j i) * z' ^ (ν - ((i : ℕ) + 1))),
    co', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a)
    rw [hstrict ζ hz₀Q hζeq]
    show _ = Ideal.span {e (F'.z ⟨0, hj0⟩)}
    rw [hz'0]
    exact (Ideal.span_singleton_eq_span_singleton.mpr (hassoc.map e.toMonoidHom)).symm
  · show e (F'.z ⟨0, hj0⟩) ∈ _
    rw [hz'0]
    exact (ringEquiv_mem_maximalIdeal_iff e).mpr hz'm
  · -- (b)
    rw [hJstalk]
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      obtain ⟨v, hv⟩ := hu' j
      have h1 : e (z' ^ ν + ∑ i : Fin ν, algebraMap F'.S s.ring (co' j i) * z' ^ (ν - ((i : ℕ) + 1))) =
          e (v : s.ring) * e (h j) := by rw [← hv, map_mul]
      show e (z' ^ ν + ∑ i : Fin ν, algebraMap F'.S s.ring (co' j i) * z' ^ (ν - ((i : ℕ) + 1))) ∈
        Ideal.span (Set.range fun j => e (h j))
      rw [h1]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      obtain ⟨v, hv⟩ := hu' j
      have h1 : e (h j) = e ((v⁻¹ : s.ringˣ) : s.ring) *
          e (z' ^ ν + ∑ i : Fin ν, algebraMap F'.S s.ring (co' j i) * z' ^ (ν - ((i : ℕ) + 1))) := by
        rw [← hv, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
      show e (h j) ∈ Ideal.span (Set.range fun j => e (z' ^ ν + ∑ i : Fin ν,
        algebraMap F'.S s.ring (co' j i) * z' ^ (ν - ((i : ℕ) + 1))))
      rw [h1]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · intro j
    show e (z' ^ ν + ∑ i : Fin ν, algebraMap F'.S s.ring (co' j i) * z' ^ (ν - ((i : ℕ) + 1))) =
      e (F'.z ⟨0, hj0⟩) ^ ν + ∑ i : Fin ν, e (algebraMap F'.S s.ring (co' j i)) *
        e (F'.z ⟨0, hj0⟩) ^ (ν - ((i : ℕ) + 1))
    rw [hz'0]
    simp only [map_add, map_pow, map_sum, map_mul]
  · intro hu
    obtain ⟨hm, h0⟩ := hco0 hu
    exact ⟨hm, hν0, h0⟩
  · refine ⟨e s.xR, Units.map e.toMonoidHom u, hE.symm, ?_, fun j i => ?_⟩
    · -- the exceptional divisor is not contained in the strict transform
      intro hWin
      have h1 : e s.xR ∈ Ideal.span {e z'} := by
        have := hWin
        simp only [RegularFrame.transport] at this
        rw [show (F'.z ⟨0, hj0⟩) = z' from hz'0] at this
        exact this
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
      obtain ⟨v, hv⟩ := hassoc
      -- `xR = c₂ * ζ`
      have h2 : s.xR = (e.symm c * (v⁻¹ : s.ringˣ)) * ζ := by
        apply e.injective
        rw [map_mul, map_mul, ← hc, ← hv, map_mul, RingEquiv.apply_symm_apply]
        have h3 : e (v⁻¹ : s.ringˣ) * e (v : s.ring) = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        calc c * e z' = c * e z' * (e (v⁻¹ : s.ringˣ) * e (v : s.ring)) := by rw [h3, mul_one]
          _ = _ := by ring
      have hxR0 : s.xR ≠ 0 := fun h0 =>
        s.x_ne_zero (s.toRing_injective (by rw [map_zero]; exact h0))
      have hxprime : (Ideal.span {s.xR}).IsPrime := by
        have hreg := MonoidalTransform.isRegularLocalRing_quotient_span_xR s hQp hQreg
        have := isDomain_of_isRegularLocalRing (s.ring ⧸ Ideal.span {s.xR})
        exact (Ideal.Quotient.isDomain_iff_prime _).mp this
      have hmem2 : (e.symm c * (v⁻¹ : s.ringˣ)) * ζ ∈ Ideal.span {s.xR} := by
        rw [← h2]; exact Ideal.mem_span_singleton_self _
      have hζm : ζ ∈ maximalIdeal s.ring := by
        rw [← hv]; exact Ideal.mul_mem_right _ _ hz'm
      rcases hxprime.mem_or_mem hmem2 with hc2 | hζx
      · obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hc2
        -- `xR = c' xR ζ`
        have h4 : s.xR * (1 - c' * ζ) = 0 := by
          have : s.xR = c' * s.xR * ζ := by
            calc s.xR = _ := h2
              _ = (c' * s.xR) * ζ := by rw [hc']
          linear_combination this
        have h5 : c' * ζ = 1 := by
          rcases mul_eq_zero.mp h4 with h | h
          · exact absurd h hxR0
          · exact (sub_eq_zero.mp h).symm
        exact (IsLocalRing.mem_maximalIdeal _).mp hζm (IsUnit.mul_iff.mp (by rw [h5]; exact isUnit_one)).2
      · obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hζx
        have h6 : s.toRing z₀ ∈ Ideal.span {s.xR} ^ 2 := by
          rw [hζeq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
          exact ⟨d, by rw [← hd]; ring⟩
        have h7 := MonoidalTransform.mem_pow_of_toRing_mem s hQp hQreg h6
        exact hz2 (Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hQp.ne_top) 2 h7)
    have h1 := RingHom.congr_fun he (algebraMap F₀.S ((𝒮.tHat.X t).presheaf.stalk ((𝒮.tHat.monoidalTransformation t).f.base xh')) (co j i))
    refine (show _ = ((𝒮.tHat.f t).stalkMap xh').hom (algebraMap F₀.S ((𝒮.tHat.X t).presheaf.stalk ((𝒮.tHat.monoidalTransformation t).f.base xh')) (co j i)) from rfl).trans
      (h1.symm.trans ?_)
    show e (s.toRing (algebraMap F₀.S ((𝒮.tHat.X t).presheaf.stalk ((𝒮.tHat.monoidalTransformation t).f.base xh')) (co j i))) = _
    rw [hcoefrel j i]
    simp only [map_mul, map_pow]
    rfl
/-- **Deviation from the paper (gap filled).** For every point `ŷ` of `X̂_s` (not only over `x̂_0`),
if `J Ŝ'_s ⊆ (M̂'_s)^k` for an ideal `J` of `S'_s`, then `J ⊆ (M'_s)^k`.  This is the last step of
Lemma (CD.5) (p. 320): "We can see that the local homomorphism S'_s → Ŝ'_s transforms a regular system
of parameters of S'_s into a system of elements of Ŝ'_s which can be extended to a regular system of
parameters of Ŝ'_s. (This can be easily deduced from the fact that X̂_s = X_s ×_X Spec(Ŝ) and that S
belongs to the class 𝔅 defined in the introductory paragraphs of Ch. I, where S is the local ring of X
at the point x_0, and Ŝ is the completion of S.) Since Ĵ'_s = J'_sŜ'_s, we can conclude that J'_s is
contained in the νth power of the maximal ideal of S'_s."  The paper gives no proof of "easily
deduced"; in Lean it is deduced as follows: the pull-back square `X̂_s = X_s ×_X Spec(Ŝ)` factors
through `X_s ×_X Spec S`, whose stalk map is an isomorphism (a flat preimmersion); an affine chart
gives `Spec(A ⊗_S Ŝ)`; the ring-level `le_pow_maximalIdeal_of_map_le_pow_of_isHironakaBase` applies
(`orderDescends_stalkMap_of_isPullback_completion`).  The membership of `O_{X,x_0}` in the class 𝔅,
which the paper uses tacitly, is `isHironakaBase_stalk` (from the leaf
`IsHironakaBase.localization_atPrime_of_finiteType`, (c) of p. 161). -/
theorem le_pow_maximalIdeal_of_map_le_pow [Hironaka.HironakaCitedResults.{u}] (s : ℕ)
    (yh : 𝒮.tHat.X s)
    (J : Ideal ((T.X s).presheaf.stalk ((𝒮.c s).base yh))) (k : ℕ)
    (h : J.map ((𝒮.c s).stalkMap yh).hom ≤ maximalIdeal ((𝒮.tHat.X s).presheaf.stalk yh) ^ k) :
    J ≤ maximalIdeal ((T.X s).presheaf.stalk ((𝒮.c s).base yh)) ^ k := by
  have := hS.ambient.1
  have := isHironakaBase_stalk X x₀
  have : IsLocallyNoetherian X := IsAlgebraicScheme.isNoetherian X |>.toIsLocallyNoetherian
  have hfin : LocallyOfFiniteType (T.pre s).composite := by
    have := MonoidalSuccession.isProper_composite (T.pre s)
    infer_instance
  have hreg : IsRegularLocalRing ((T.X s).presheaf.stalk ((𝒮.c s).base yh)) :=
    hS.isNonsingular_X s _
  exact orderDescends_stalkMap_of_isPullback_completion (X := X) (Y := T.X s) (Ŷ := 𝒮.tHat.X s)
    x₀ (T.pre s).composite (𝒮.c s) (𝒮.tHat.pre s).composite
    (by have := 𝒮.isPullback s; rw [𝒮.c_zero] at this; exact this) yh J k h

/-- **The step `t → t+1` at a point `x̂'_{t+1}` of `X̄_{t+1}` over `x̂'_t ∈ B̂_t`**, from the
conditions (2), (3) of `[vii]` at `t` instead of `x̂'_{t+1} ∈ S_ν(ℜ(t+1))` (case (2) of p. 318,
used for Lemma (CD.5), where only "`J̄(s)` is defined" is available).

Deviation from the paper (gap filled), p. 318 and p. 320: the paper says "`z_t ∈ Q̂'_t`" (here
`IsCenterContained t`), "`g_{ji}(t) ∈ (Q̂'_t ∩ T'_t)^i`" (here from `IsJBarContained t`:
`mem_pow_sup_span_of_pow_mem` and `frame_mem_comap_pow_of_mem_pow_add`, the gr-domain argument), and
"`w_t⁻¹(Q̂'_t ∩ T'_t)Ŝ'_{t+1}` is the unit ideal" with `ν(Ĵ'_{t+1}) ≥ ν` as the reason; here the unit
ideal comes from Nakayama (`exists_mem_comap_assoc_w_of_mem_maximalIdeal`) using only that
`z_{t+1} = z_t/w_t` is a non-unit, which holds because `x̂'_{t+1} ∈ X̄_{t+1}`.  No `ν`-bound on
`Ĵ'_{t+1}` is used, so the argument is not circular. -/
theorem exists_stalk_data_succ_of_defined [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (xh' : 𝒮.tHat.X (t + 1))
    (hdefc : 𝒮.IsCenterContained t) (hJc : 𝒮.IsJBarContained t)
    (hxbar : xh' ∈ (𝒮.xBar (t + 1)).pts)
    (xb : (𝒮.xBar t).toScheme) (hxb : (𝒮.xBar t).ι.base xb = (𝒮.tHat.f t).base xh')
    (hBne : (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb) ≠ ⊤)
    (hinv : ∃ (F : RegularFrame ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))) (hr : F.r = 1)
      (m : ℕ) (g : Fin m → (𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))
      (co : Fin m → Fin ν → F.S), 𝒮.StalkInvData t xb F hr m g co) :
    ∃ (F : RegularFrame ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb)))
      (hr : F.r = 1) (m : ℕ) (g : Fin m → (𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))
      (co : Fin m → Fin ν → F.S) (_ : 𝒮.StalkInvData t xb F hr m g co)
      (F₁ : RegularFrame ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) (hr₁ : F₁.r = 1)
      (g₁ : Fin m → (𝒮.tHat.X (t + 1)).presheaf.stalk xh') (co₁ : Fin m → Fin ν → F₁.S),
      (𝒮.xBar (t + 1)).stalkIdeal xh' = Ideal.span {F₁.z ⟨0, by rw [hr₁]; exact Nat.one_pos⟩} ∧
      F₁.z ⟨0, by rw [hr₁]; exact Nat.one_pos⟩ ∈ maximalIdeal ((𝒮.tHat.X (t + 1)).presheaf.stalk xh') ∧
      Ideal.span (Set.range g₁) =
        (Subscheme.totalTransform (𝒮.c (t + 1)) (datum T ℜ (t + 1)).J).stalkIdeal xh' ∧
      (∀ j, g₁ j = F₁.z ⟨0, by rw [hr₁]; exact Nat.one_pos⟩ ^ ν + ∑ i : Fin ν,
        algebraMap F₁.S _ (co₁ j i) * F₁.z ⟨0, by rw [hr₁]; exact Nat.one_pos⟩ ^ (ν - ((i : ℕ) + 1))) ∧
      (r = .unrestricted → ∃ (hm : 0 < m) (hν : 0 < ν), co₁ ⟨0, hm⟩ ⟨0, hν⟩ = 0) ∧
      ∃ (W : (𝒮.tHat.X (t + 1)).presheaf.stalk xh') (U : ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')ˣ),
        Ideal.span {W} = (𝒮.tHat.monoidalTransformation t).exceptional.stalkIdeal xh' ∧
        W ∉ Ideal.span {F₁.z ⟨0, by rw [hr₁]; exact Nat.one_pos⟩} ∧
        ∀ (j : Fin m) (i : Fin ν),
          (((𝒮.tHat.X t).presheaf.stalkCongr (Inseparable.of_eq hxb)).hom ≫
              (𝒮.tHat.f t).stalkMap xh').hom (algebraMap F.S _ (co j i)) =
            algebraMap F₁.S _ (co₁ j i) * (W * (U : (𝒮.tHat.X (t + 1)).presheaf.stalk xh')) ^ ((i : ℕ) + 1) := by
  classical
  have := hS.ambient.1
  obtain ⟨F, hr, m, g, co, hdata⟩ := hinv
  obtain ⟨ha, hb, hsh, hun, hd⟩ := hdata
  have hBhns : (𝒮.tHat.B t).IsNonsingular :=
    𝒮.toCompletion.isNonsingular_B (hS.ambient.2.1 x₀) hS.isNonsingular_X hS.isNonsingular_B t
  have hmem0 : (𝒮.xBar t).ι.base xb ∈ (𝒮.tHat.B t).pts :=
    Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr hBne
  have hmem : (𝒮.tHat.f t).base xh' ∈ (𝒮.tHat.B t).pts := hxb ▸ hmem0
  have : IsRegularLocalRing ((𝒮.tHat.X t).presheaf.stalk
      ((𝒮.tHat.monoidalTransformation t).f.base xh')) :=
    𝒮.instIsRegularLocalRingStalkTHat t _
  have : IsDomain ((𝒮.tHat.X t).presheaf.stalk ((𝒮.tHat.monoidalTransformation t).f.base xh')) :=
    isDomain_of_isRegularLocalRing _
  have hQp : ((𝒮.tHat.B t).stalkIdeal
      ((𝒮.tHat.monoidalTransformation t).f.base xh')).IsPrime :=
    Subscheme.isPrime_stalkIdeal_of_isNonsingular hBhns hmem
  have hQreg : IsRegularLocalRing ((𝒮.tHat.X t).presheaf.stalk
      ((𝒮.tHat.monoidalTransformation t).f.base xh') ⧸ (𝒮.tHat.B t).stalkIdeal
        ((𝒮.tHat.monoidalTransformation t).f.base xh')) :=
    Subscheme.isRegularLocalRing_quotient_of_isNonsingular hBhns hmem
  obtain ⟨s, e, he, hE⟩ :=
    (𝒮.tHat.monoidalTransformation t).exists_monoidalTransform_stalk_exceptional xh'
  -- transport of the frame to the stalk at `f̂_t(x̂'_{t+1})`
  let κ : ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb)) ≃+*
      ((𝒮.tHat.X t).presheaf.stalk ((𝒮.tHat.monoidalTransformation t).f.base xh')) :=
    ((𝒮.tHat.X t).presheaf.stalkCongr (Inseparable.of_eq hxb)).commRingCatIsoToRingEquiv
  have hκD : ∀ D : Subscheme (𝒮.tHat.X t),
      D.stalkIdeal ((𝒮.tHat.monoidalTransformation t).f.base xh') =
        (D.stalkIdeal ((𝒮.xBar t).ι.base xb)).map κ.toRingHom := fun D =>
    Subscheme.stalkIdeal_eq_map_stalkCongr D hxb
  let F₀ := F.transport κ
  have hr₀ : F₀.r = 1 := hr
  let z₀ := F₀.z ⟨0, by rw [hr₀]; exact Nat.one_pos⟩
  have hzF₀ : ∀ j, F₀.z j = z₀ := fun j => by
    congr 1
    apply Fin.ext
    have := j.2
    show (j : ℕ) = 0
    omega
  let g₀ : Fin m → (𝒮.tHat.X t).presheaf.stalk ((𝒮.tHat.monoidalTransformation t).f.base xh') :=
    fun j => κ (g j)
  have hA : (𝒮.xBar t).stalkIdeal ((𝒮.tHat.monoidalTransformation t).f.base xh') =
      Ideal.span {z₀} := by
    rw [hκD, ha, Ideal.map_span, Set.image_singleton]
    rfl
  have hB : (Subscheme.totalTransform (𝒮.c t) (datum T ℜ t).J).stalkIdeal
      ((𝒮.tHat.monoidalTransformation t).f.base xh') = Ideal.span (Set.range g₀) := by
    rw [hκD, ← hb, Ideal.map_span, ← Set.range_comp]
    rfl
  have hsh₀ : ∀ j, g₀ j = z₀ ^ ν + ∑ i : Fin ν,
      algebraMap F₀.S _ (co j i) * z₀ ^ (ν - ((i : ℕ) + 1)) := by
    intro j
    show κ (g j) = κ (F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩) ^ ν + ∑ i : Fin ν,
      κ (algebraMap F.S _ (co j i)) * κ (F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩) ^ (ν - ((i : ℕ) + 1))
    rw [hsh j]
    simp only [map_add, map_pow, map_sum, map_mul]
  -- `z_t ∈ Q̂'_t` and `g_{ji}(t) ∈ (Q̂'_t ∩ T'_t)^i` from (2), (3) of `[vii]` at `t`
  have hzQx : F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ∈ (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb) := by
    have hle : (𝒮.xBar t) ≤ (𝒮.tHat.B t) := hdefc
    have := (Subscheme.le_iff_stalkIdeal_le.mp hle) ((𝒮.xBar t).ι.base xb)
    exact this (by rw [ha]; exact Ideal.subset_span rfl)
  have hz₀Q : z₀ ∈ (𝒮.tHat.B t).stalkIdeal ((𝒮.tHat.monoidalTransformation t).f.base xh') := by
    rw [hκD]
    exact Ideal.mem_map_of_mem κ.toRingHom hzQx
  have hmapκ : ∀ (a : (𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb)) (n : ℕ),
      a ∈ (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb) ^ n ⊔
          Ideal.span {F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩} →
      κ a ∈ (𝒮.tHat.B t).stalkIdeal ((𝒮.tHat.monoidalTransformation t).f.base xh') ^ n ⊔
          Ideal.span {z₀} := by
    intro a n ha'
    have h1 := Ideal.mem_map_of_mem κ.toRingHom ha'
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Set.image_singleton, ← hκD] at h1
    exact h1
  have hcoQ : ∀ (j : Fin m) (i : Fin ν),
      co j i ∈ ((𝒮.tHat.B t).stalkIdeal ((𝒮.tHat.monoidalTransformation t).f.base xh')).comap
        (algebraMap F₀.S _) ^ ((i : ℕ) + 1) := by
    intro j i
    have hdvd : ((i : ℕ) + 1) ∣ 𝒮.bBar := Nat.dvd_factorial (Nat.succ_pos _) i.2
    have hk : 0 < 𝒮.bBar / ((i : ℕ) + 1) :=
      Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) hdvd) (Nat.succ_pos _)
    set ψ := ((𝒮.xBar t).ι.stalkMap xb).hom with hψ
    have hsurj : Function.Surjective ψ := (𝒮.xBar t).ι.stalkMap_surjective xb
    have hker : RingHom.ker ψ = Ideal.span {F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩} := by
      rw [← ha, stalkIdeal_eq_ker_stalkMap]
    have h1 : ψ (algebraMap F.S _ (co j i) ^ (𝒮.bBar / ((i : ℕ) + 1))) ∈
        (𝒮.jBar t).stalkIdeal xb := by
      rw [hd]; exact Ideal.subset_span ⟨(j, i), rfl⟩
    have h2 := hJc xb h1
    have hQ : (𝒮.bBarOn t).stalkIdeal xb =
        ((𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb)).map ψ :=
      Subscheme.stalkIdeal_comap _ _ _
    rw [hQ, ← Ideal.map_pow] at h2
    have h3 : algebraMap F.S _ (co j i) ^ (𝒮.bBar / ((i : ℕ) + 1)) ∈
        (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb) ^ 𝒮.bBar ⊔
          Ideal.span {F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩} := by
      have := (Ideal.mem_comap).mpr h2
      rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, hker] at this
      exact this
    have h4 := hmapκ _ _ h3
    rw [map_pow] at h4
    have h5 : ((i : ℕ) + 1) * (𝒮.bBar / ((i : ℕ) + 1)) = 𝒮.bBar := Nat.mul_div_cancel' hdvd
    have h6 : (𝒮.bBar / ((i : ℕ) + 1)) * ((i : ℕ) + 1) = 𝒮.bBar := by rw [mul_comm]; exact h5
    have h4' : κ (algebraMap F.S _ (co j i)) ^ (𝒮.bBar / ((i : ℕ) + 1)) ∈
        (𝒮.tHat.B t).stalkIdeal ((𝒮.tHat.monoidalTransformation t).f.base xh') ^
          ((𝒮.bBar / ((i : ℕ) + 1)) * ((i : ℕ) + 1)) ⊔ Ideal.span {z₀} := by
      rw [h6]; exact h4
    have h7 := mem_pow_sup_span_of_pow_mem F₀ z₀ hzF₀ hr₀ _ hQreg hz₀Q
      (κ (algebraMap F.S _ (co j i))) (𝒮.bBar / ((i : ℕ) + 1)) ((i : ℕ) + 1) hk h4'
    exact frame_mem_comap_pow_of_mem_pow_add F₀ z₀ hzF₀ hr₀ _ hz₀Q ((i : ℕ) + 1) (co j i) h7
  have hgQ₀ : ∀ j, g₀ j ∈
      (𝒮.tHat.B t).stalkIdeal ((𝒮.tHat.monoidalTransformation t).f.base xh') ^ ν := fun j => by
    rw [hsh₀ j]
    refine Ideal.add_mem _ (Ideal.pow_mem_pow hz₀Q ν) (Ideal.sum_mem _ fun i _ => ?_)
    have h1 := Ideal.mem_map_of_mem (algebraMap F₀.S ((𝒮.tHat.X t).presheaf.stalk
      ((𝒮.tHat.monoidalTransformation t).f.base xh'))) (hcoQ j i)
    rw [Ideal.map_pow] at h1
    have h2 := Ideal.pow_right_mono Ideal.map_comap_le ((i : ℕ) + 1) h1
    have h3 := Ideal.mul_mem_mul h2 (Ideal.pow_mem_pow hz₀Q (ν - ((i : ℕ) + 1)))
    rw [← pow_add] at h3
    have e : (i : ℕ) + 1 + (ν - ((i : ℕ) + 1)) = ν := by have := i.2; omega
    rwa [e] at h3
  -- `ν(ℜ(t)) = ν` at the center (p. 318), derived locally: `Ĵ'_t ⊆ (Q̂'_t)^ν ⊆ (M̂'_t)^ν`
  have hνt : (datum T ℜ t).nu = ν := by
    have hMY : ∀ j, g₀ j ∈ maximalIdeal ((𝒮.tHat.X t).presheaf.stalk
        ((𝒮.tHat.monoidalTransformation t).f.base xh')) ^ ν := fun j =>
      Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hQp.ne_top) ν (hgQ₀ j)
    have hJm : ((datum T ℜ t).J.stalkIdeal ((𝒮.c t).base
        ((𝒮.tHat.monoidalTransformation t).f.base xh'))).map ((𝒮.c t).stalkMap
          ((𝒮.tHat.monoidalTransformation t).f.base xh')).hom ≤ maximalIdeal ((𝒮.tHat.X t).presheaf.stalk
            ((𝒮.tHat.monoidalTransformation t).f.base xh')) ^ ν := by
      rw [← stalkIdeal_totalTransform, hB, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hMY j
    have hfin := 𝒮.le_pow_maximalIdeal_of_map_le_pow t _ _ ν hJm
    have hnu : (ν : ℕ∞) ≤ (datum T ℜ t).nuAt ((𝒮.c t).base
        ((𝒮.tHat.monoidalTransformation t).f.base xh')) := Ideal.le_ord hfin
    have hyB : (𝒮.c t).base ((𝒮.tHat.monoidalTransformation t).f.base xh') ∈ (T.B t).pts := by
      have := hmem
      rw [𝒮.B_hat t, FlatPreimm.pts_totalTransform] at this
      exact this
    have h1 : (𝒮.c t).base ((𝒮.tHat.monoidalTransformation t).f.base xh') ∈
        (datum T ℜ t).sNu (datum T ℜ t).nu := hS.pts_B_subset_sStar t hyB
    refine le_antisymm (hS.nu_datum_le t) ?_
    exact hnu.trans (le_iSup₂ (f := fun x (_ : x ∈ (datum T ℜ t).S) => (datum T ℜ t).nuAt x) _ h1.1)
  -- the denominator `w = x` of the monoidal transform and the quotients `h_j = g_j / w^ν`
  have hw : Ideal.span {s.xR} =
      ((𝒮.tHat.B t).stalkIdeal ((𝒮.tHat.monoidalTransformation t).f.base xh')).map s.toRing :=
    s.span_xR_eq_map
  have hexh : ∀ j, ∃ hj : s.ring, s.xR ^ ν * hj = s.toRing (g₀ j) := fun j => by
    have h1 := Ideal.mem_map_of_mem s.toRing (hgQ₀ j)
    rw [Ideal.map_pow, ← hw, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, hc.symm⟩
  choose h hh using hexh
  have hdomX : IsDomain ((𝒮.tHat.X (t + 1)).presheaf.stalk xh') := by
    have := 𝒮.instIsRegularLocalRingStalkTHat (t + 1) xh'
    exact isDomain_of_isRegularLocalRing _
  have : IsDomain ((𝒮.tHat.monoidalTransformation t).X'.presheaf.stalk xh') := hdomX
  have : IsLocalRing ((𝒮.tHat.monoidalTransformation t).X'.presheaf.stalk xh') :=
    inferInstanceAs (IsLocalRing ((𝒮.tHat.X (t + 1)).presheaf.stalk xh'))
  have hw0 : e s.xR ≠ 0 := fun h0 =>
    s.x_ne_zero (s.toRing_injective (by
      have := e.injective (h0.trans (map_zero e).symm)
      rw [map_zero]; exact this))
  -- the stalk of `c_{t+1}⁻¹ J(t+1)` is generated by the `e (h_j)`
  have hJstalk : (Subscheme.totalTransform (𝒮.c (t + 1)) (datum T ℜ (t + 1)).J).stalkIdeal xh' =
      Ideal.span (Set.range fun j => e (h j)) := by
    have hdat : datum T ℜ (t + 1) = (datum T ℜ t).transform (T.monoidalTransformation t) :=
      MonoidalSuccession.transformII_snoc (T.pre t) (T.B t) (T.monoidalTransformation t) ℜ
    have hJ : (datum T ℜ (t + 1)).J = Subscheme.divPow
        (Subscheme.totalTransform (T.f t) (datum T ℜ t).J)
        (T.monoidalTransformation t).exceptional ν := by
      rw [hdat]
      show Subscheme.divPow _ _ (datum T ℜ t).nu.toNat = _
      rw [hνt]; rfl
    have hflat : Flat (𝒮.c (t + 1)) := flat_c_of_completion 𝒮.toCompletion (hS.ambient.2.1 x₀) (t + 1)
    have hdiv := Subscheme.stalkIdeal_divPow
      (I := Subscheme.totalTransform (T.f t) (datum T ℜ t).J)
      (P := (T.monoidalTransformation t).exceptional) (T.monoidalTransformation t).invertible ν
      ((𝒮.c (t + 1)).base xh')
    obtain ⟨a, haE, -⟩ := (T.monoidalTransformation t).invertible.exists_stalkIdeal_eq_span
      ((𝒮.c (t + 1)).base xh')
    let : Algebra ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh'))
        ((𝒮.tHat.X (t + 1)).presheaf.stalk xh') := ((𝒮.c (t + 1)).stalkMap xh').hom.toAlgebra
    have : Module.Flat ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh'))
        ((𝒮.tHat.X (t + 1)).presheaf.stalk xh') := Flat.stalkMap (𝒮.c (t + 1)) xh'
    have hsq : 𝒮.c (t + 1) ≫ T.f t = 𝒮.tHat.f t ≫ 𝒮.c t := (𝒮.c_comm t).symm
    have e1 : (Subscheme.totalTransform (𝒮.c (t + 1)) (datum T ℜ (t + 1)).J).stalkIdeal xh' =
        (((Subscheme.totalTransform (T.f t) (datum T ℜ t).J).stalkIdeal ((𝒮.c (t + 1)).base xh')).colon
          ({a ^ ν} : Set _)).map (algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) := by
      rw [stalkIdeal_totalTransform, hJ]
      exact congrArg (Ideal.map _) (hdiv.trans (Ideal.colon_pow_of_eq_span _ _ a haE ν))
    have e2 := Ideal.map_colon_singleton_eq_of_flat (A' := (𝒮.tHat.X (t + 1)).presheaf.stalk xh')
      ((Subscheme.totalTransform (T.f t) (datum T ℜ t).J).stalkIdeal ((𝒮.c (t + 1)).base xh'))
      (a ^ ν)
    have e3 : ((Subscheme.totalTransform (T.f t) (datum T ℜ t).J).stalkIdeal
        ((𝒮.c (t + 1)).base xh')).map (algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) =
        Ideal.span (Set.range fun j => (e s.xR) ^ ν * e (h j)) := by
      have h1 := (stalkIdeal_totalTransform (𝒮.c (t + 1))
        (Subscheme.totalTransform (T.f t) (datum T ℜ t).J) xh').symm
      have h2 : Subscheme.totalTransform (𝒮.c (t + 1))
          (Subscheme.totalTransform (T.f t) (datum T ℜ t).J) =
          Subscheme.totalTransform (𝒮.tHat.f t)
            (Subscheme.totalTransform (𝒮.c t) (datum T ℜ t).J) := by
        rw [← Subscheme.totalTransform_comp, hsq, Subscheme.totalTransform_comp]
      rw [h2, stalkIdeal_totalTransform (𝒮.tHat.f t)
        (Subscheme.totalTransform (𝒮.c t) (datum T ℜ t).J) xh'] at h1
      refine h1.trans ?_
      have hB' : (Subscheme.totalTransform (𝒮.c t) (datum T ℜ t).J).stalkIdeal
          ((𝒮.tHat.f t).base xh') = Ideal.span (Set.range g₀) := hB
      rw [hB']
      refine (Ideal.map_span _ _).trans ?_
      refine congrArg Ideal.span ((Set.range_comp _ _).symm.trans
        (congrArg Set.range (funext fun j => ?_)))
      have h1 := RingHom.congr_fun he (g₀ j)
      refine h1.symm.trans ?_
      show e (s.toRing (g₀ j)) = _
      rw [← hh j, map_mul, map_pow]
    have e4 : Ideal.span {(algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) a} = Ideal.span {e s.xR} := by
      have h1 : (Subscheme.totalTransform (𝒮.c (t + 1)) (T.monoidalTransformation t).exceptional).stalkIdeal
          xh' = ((T.monoidalTransformation t).exceptional.stalkIdeal ((𝒮.c (t + 1)).base xh')).map
            (algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) := stalkIdeal_totalTransform _ _ _
      have h2 := MonoidalTransformation.totalTransform_exceptional_of_square
        (T.monoidalTransformation t) (𝒮.tHat.monoidalTransformation t) (𝒮.c t) (𝒮.c (t + 1)) hsq
        (𝒮.B_hat t).symm
      have h3 := (congrArg (fun D => Subscheme.stalkIdeal D xh') h2).symm.trans h1
      have h4 : Ideal.span {e s.xR} = Ideal.map (algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) (Ideal.span {a}) :=
        hE.symm.trans (h3.trans (congrArg (Ideal.map (algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh'))) haE))
      have h5 := Ideal.map_span (algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) ({a} : Set ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')))
      exact (h4.trans (h5.trans (congrArg Ideal.span Set.image_singleton))).symm
    have e5 : Ideal.span {(algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) (a ^ ν)} = Ideal.span {e s.xR} ^ ν := by
      have h6 : (algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) (a ^ ν) = ((algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) a) ^ ν := map_pow _ _ _
      rw [h6, ← Ideal.span_singleton_pow, e4]
      rfl
    have e6 : ∀ I : Ideal ((𝒮.tHat.X (t + 1)).presheaf.stalk xh'),
        I.colon ({(algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) (a ^ ν)} : Set _) = I.colon ((Ideal.span ({(e s.xR : (𝒮.tHat.X (t + 1)).presheaf.stalk xh')} : Set ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) ^ ν : Ideal ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) : Set ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) :=
      fun I => by rw [← Ideal.colon_span, e5]; rfl
    refine e1.trans (e2.trans ?_)
    refine (congrArg (fun I => I.colon ({(algebraMap ((T.X (t + 1)).presheaf.stalk ((𝒮.c (t + 1)).base xh')) ((𝒮.tHat.X (t + 1)).presheaf.stalk xh')) (a ^ ν)} : Set _)) e3).trans ?_
    exact (e6 _).trans (Ideal.colon_span_range_mul_pow (e s.xR) hw0 ν (fun j => e (h j)))
  have hz2 : z₀ ∉ maximalIdeal ((𝒮.tHat.X t).presheaf.stalk
      ((𝒮.tHat.monoidalTransformation t).f.base xh')) ^ 2 :=
    F₀.extends_rsop.notMem_maximalIdeal_sq (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hstrict : ∀ ζ : s.ring, z₀ ∈ (𝒮.tHat.B t).stalkIdeal
      ((𝒮.tHat.monoidalTransformation t).f.base xh') → s.toRing z₀ = s.xR * ζ →
      (𝒮.xBar (t + 1)).stalkIdeal xh' = Ideal.span {e ζ} := by
    intro ζ hzQ hζ
    have h1 := MonoidalTransformation.stalkIdeal_strictTransform_eq_map
      (𝒮.tHat.monoidalTransformation t) xh' s e he (Or.inl ⟨hQp, hQreg⟩) (𝒮.xBar t)
    have hord := Ideal.ordElem_eq_one_of_mem_of_notMem_sq hQp.ne_top hzQ hz2
    have h2 : strictTransformIdeal s (Ideal.span {z₀}) = Ideal.span {ζ} := by
      refine strictTransformIdeal_span_singleton_eq s hQp hQreg z₀ ζ ?_
      rw [hord]; simpa using hζ.symm
    show (Subscheme.strictTransform (𝒮.tHat.monoidalTransformation t) (𝒮.xBar t)).stalkIdeal xh' = _
    rw [h1, hA, h2]
    exact (Ideal.map_span _ _).trans (congrArg Ideal.span Set.image_singleton)
  have hregX := 𝒮.instIsRegularLocalRingStalkTHat (t + 1) xh'
  have : IsRegularLocalRing s.ring :=
    IsRegularLocalRing.of_ringEquiv (R := (𝒮.tHat.X (t + 1)).presheaf.stalk xh') e.symm
  have hν0 : 0 < ν := hS.nu_pos
  have hζ : ∀ ζ : s.ring, s.toRing z₀ = s.xR * ζ → ζ ∈ maximalIdeal s.ring := by
    intro ζ hζ
    have hne := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hxbar
    rw [hstrict ζ hz₀Q hζ] at hne
    by_contra hζm
    apply hne
    exact Ideal.span_singleton_eq_top.mpr ((IsLocalRing.notMem_maximalIdeal.mp hζm).map e)
  have : IsLocalHom s.toRing := inferInstance
  obtain ⟨-, F', hr', z', ζ, co', hFz', hζeq, hassoc, hz'm, hu', hco0, u, hcoefrel⟩ :=
    frame_step_core_of_exists F₀ z₀ hzF₀ hr₀ ν hν0 m g₀ co hsh₀
      ((𝒮.tHat.B t).stalkIdeal ((𝒮.tHat.monoidalTransformation t).f.base xh')) hgQ₀ hz₀Q s
      s.xR hw hζ (fun ζ hζeq hζm =>
        exists_mem_comap_assoc_w_of_mem_maximalIdeal F₀ z₀ hzF₀ hr₀ _ hz₀Q s s.xR hw ζ hζeq hζm)
      h hh
  have hj0 : (0 : ℕ) < F'.r := by rw [hr']; exact Nat.one_pos
  have hz'0 : F'.z ⟨0, hj0⟩ = z' := hFz' _
  refine ⟨F, hr, m, g, co, ⟨ha, hb, hsh, hun, hd⟩, F'.transport e, hr',
    fun j => e (z' ^ ν + ∑ i : Fin ν, algebraMap F'.S s.ring (co' j i) * z' ^ (ν - ((i : ℕ) + 1))),
    co', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a)
    rw [hstrict ζ hz₀Q hζeq]
    show _ = Ideal.span {e (F'.z ⟨0, hj0⟩)}
    rw [hz'0]
    exact (Ideal.span_singleton_eq_span_singleton.mpr (hassoc.map e.toMonoidHom)).symm
  · show e (F'.z ⟨0, hj0⟩) ∈ _
    rw [hz'0]
    exact (ringEquiv_mem_maximalIdeal_iff e).mpr hz'm
  · -- (b)
    rw [hJstalk]
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      obtain ⟨v, hv⟩ := hu' j
      have h1 : e (z' ^ ν + ∑ i : Fin ν, algebraMap F'.S s.ring (co' j i) * z' ^ (ν - ((i : ℕ) + 1))) =
          e (v : s.ring) * e (h j) := by rw [← hv, map_mul]
      show e (z' ^ ν + ∑ i : Fin ν, algebraMap F'.S s.ring (co' j i) * z' ^ (ν - ((i : ℕ) + 1))) ∈
        Ideal.span (Set.range fun j => e (h j))
      rw [h1]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      obtain ⟨v, hv⟩ := hu' j
      have h1 : e (h j) = e ((v⁻¹ : s.ringˣ) : s.ring) *
          e (z' ^ ν + ∑ i : Fin ν, algebraMap F'.S s.ring (co' j i) * z' ^ (ν - ((i : ℕ) + 1))) := by
        rw [← hv, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
      show e (h j) ∈ Ideal.span (Set.range fun j => e (z' ^ ν + ∑ i : Fin ν,
        algebraMap F'.S s.ring (co' j i) * z' ^ (ν - ((i : ℕ) + 1))))
      rw [h1]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · intro j
    show e (z' ^ ν + ∑ i : Fin ν, algebraMap F'.S s.ring (co' j i) * z' ^ (ν - ((i : ℕ) + 1))) =
      e (F'.z ⟨0, hj0⟩) ^ ν + ∑ i : Fin ν, e (algebraMap F'.S s.ring (co' j i)) *
        e (F'.z ⟨0, hj0⟩) ^ (ν - ((i : ℕ) + 1))
    rw [hz'0]
    simp only [map_add, map_pow, map_sum, map_mul]
  · intro hu
    obtain ⟨hm, hν', h0⟩ := hun hu
    exact ⟨hm, hν0, hco0 hm h0⟩
  · refine ⟨e s.xR, Units.map e.toMonoidHom u, hE.symm, ?_, fun j i => ?_⟩
    · -- the exceptional divisor is not contained in the strict transform
      intro hWin
      have h1 : e s.xR ∈ Ideal.span {e z'} := by
        have := hWin
        simp only [RegularFrame.transport] at this
        rw [show (F'.z ⟨0, hj0⟩) = z' from hz'0] at this
        exact this
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
      obtain ⟨v, hv⟩ := hassoc
      -- `xR = c₂ * ζ`
      have h2 : s.xR = (e.symm c * (v⁻¹ : s.ringˣ)) * ζ := by
        apply e.injective
        rw [map_mul, map_mul, ← hc, ← hv, map_mul, RingEquiv.apply_symm_apply]
        have h3 : e (v⁻¹ : s.ringˣ) * e (v : s.ring) = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        calc c * e z' = c * e z' * (e (v⁻¹ : s.ringˣ) * e (v : s.ring)) := by rw [h3, mul_one]
          _ = _ := by ring
      have hxR0 : s.xR ≠ 0 := fun h0 =>
        s.x_ne_zero (s.toRing_injective (by rw [map_zero]; exact h0))
      have hxprime : (Ideal.span {s.xR}).IsPrime := by
        have hreg := MonoidalTransform.isRegularLocalRing_quotient_span_xR s hQp hQreg
        have := isDomain_of_isRegularLocalRing (s.ring ⧸ Ideal.span {s.xR})
        exact (Ideal.Quotient.isDomain_iff_prime _).mp this
      have hmem2 : (e.symm c * (v⁻¹ : s.ringˣ)) * ζ ∈ Ideal.span {s.xR} := by
        rw [← h2]; exact Ideal.mem_span_singleton_self _
      have hζm : ζ ∈ maximalIdeal s.ring := by
        rw [← hv]; exact Ideal.mul_mem_right _ _ hz'm
      rcases hxprime.mem_or_mem hmem2 with hc2 | hζx
      · obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hc2
        -- `xR = c' xR ζ`
        have h4 : s.xR * (1 - c' * ζ) = 0 := by
          have : s.xR = c' * s.xR * ζ := by
            calc s.xR = _ := h2
              _ = (c' * s.xR) * ζ := by rw [hc']
          linear_combination this
        have h5 : c' * ζ = 1 := by
          rcases mul_eq_zero.mp h4 with h | h
          · exact absurd h hxR0
          · exact (sub_eq_zero.mp h).symm
        exact (IsLocalRing.mem_maximalIdeal _).mp hζm (IsUnit.mul_iff.mp (by rw [h5]; exact isUnit_one)).2
      · obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hζx
        have h6 : s.toRing z₀ ∈ Ideal.span {s.xR} ^ 2 := by
          rw [hζeq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
          exact ⟨d, by rw [← hd]; ring⟩
        have h7 := MonoidalTransform.mem_pow_of_toRing_mem s hQp hQreg h6
        exact hz2 (Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hQp.ne_top) 2 h7)
    have h1 := RingHom.congr_fun he (algebraMap F₀.S ((𝒮.tHat.X t).presheaf.stalk ((𝒮.tHat.monoidalTransformation t).f.base xh')) (co j i))
    refine (show _ = ((𝒮.tHat.f t).stalkMap xh').hom (algebraMap F₀.S ((𝒮.tHat.X t).presheaf.stalk ((𝒮.tHat.monoidalTransformation t).f.base xh')) (co j i)) from rfl).trans
      (h1.symm.trans ?_)
    show e (s.toRing (algebraMap F₀.S ((𝒮.tHat.X t).presheaf.stalk ((𝒮.tHat.monoidalTransformation t).f.base xh')) (co j i))) = _
    rw [hcoefrel j i]
    simp only [map_mul, map_pow]
    rfl
/-- (a)$_{t+1}$–(d)$_{t+1}$ in the case (2) `x̂'_t ∈ B̂_t` (p. 318), with the point `x̄'_{t+1}` of
`X̄_{t+1}` over `x̂'_{t+1}` (it exists since `z_{t+1}` is a non-unit) and (d) obtained by dividing by
`P̄_{t+1}^{b̄}`: `J̄(t+1) = f̄_t⁻¹(J̄(t))/P̄_{t+1}^{b̄}`, where `ḡ_{ji}(t)^{b̄/i} = ḡ_{ji}(t+1)^{b̄/i}
w̄_t^{b̄}` and `w̄_t` is a non-zero-divisor of the domain `O_{X̄_{t+1}, x̄'_{t+1}}`.  The division is
computed with `P̄_{t+1}` locally principal (`Subscheme.stalkIdeal_divPow_of_isLocallyPrincipal`), so
the invertibility of `P̄_{t+1}` (`isNonsingular_xBar_zero_and_isMonoidalTransformationOf_fBar`) is not
used. -/
theorem stalkInvData_succ_of_mem [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (xh' : 𝒮.tHat.X (t + 1))
    (hx : (𝒮.c (t + 1)).base xh' ∈ sNu (datum T ℜ (t + 1)) (restriction T r (t + 1)) ν)
    (xb : (𝒮.xBar t).toScheme) (hxb : (𝒮.xBar t).ι.base xb = (𝒮.tHat.f t).base xh')
    (hBne : (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb) ≠ ⊤)
    (hνt : (datum T ℜ t).nu = ν)
    (hinv : ∃ (F : RegularFrame ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))) (hr : F.r = 1)
      (m : ℕ) (g : Fin m → (𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))
      (co : Fin m → Fin ν → F.S), 𝒮.StalkInvData t xb F hr m g co) :
    ∃ xb' : (𝒮.xBar (t + 1)).toScheme, (𝒮.xBar (t + 1)).ι.base xb' = xh' ∧
      ∃ (F₁ : RegularFrame ((𝒮.tHat.X (t + 1)).presheaf.stalk ((𝒮.xBar (t + 1)).ι.base xb')))
        (hr₁ : F₁.r = 1) (m : ℕ)
        (g₁ : Fin m → (𝒮.tHat.X (t + 1)).presheaf.stalk ((𝒮.xBar (t + 1)).ι.base xb'))
        (co₁ : Fin m → Fin ν → F₁.S), 𝒮.StalkInvData (t + 1) xb' F₁ hr₁ m g₁ co₁ := by
  classical
  obtain ⟨F, hr, m, g, co, hdata, F₁, hr₁, g₁, co₁, ha1, hz1, hb1, hsh1, hun1, W, U, hW, hWz, hcoef⟩ :=
    𝒮.exists_stalk_data_succ_of_mem t xh' hx xb hxb hBne hνt hinv
  obtain ⟨ha, hb, hsh, hun, hd⟩ := hdata
  have hmem : xh' ∈ (𝒮.xBar (t + 1)).pts := by
    rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, ha1]
    exact ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hz1)
  obtain ⟨xb', hxb'⟩ := Subscheme.exists_ι_eq_of_mem_pts (𝒮.xBar (t + 1)) hmem
  have hfb : xb = (𝒮.fBar t).base xb' := by
    refine subscheme_ι_injective (𝒮.xBar t) ?_
    rw [hxb, ← hxb']
    exact (congrArg (fun φ => φ.base xb') (𝒮.fBar_comm t)).symm
  subst hxb'
  subst hfb
  refine ⟨xb', rfl, F₁, hr₁, m, g₁, co₁, ha1, hb1, hsh1, hun1, ?_⟩
  -- (d)
  have hsq : 𝒮.c (t + 1) ≫ T.f t = 𝒮.tHat.f t ≫ 𝒮.c t := (𝒮.c_comm t).symm
  have hexc := MonoidalTransformation.totalTransform_exceptional_of_square
    (T.monoidalTransformation t) (𝒮.tHat.monoidalTransformation t) (𝒮.c t) (𝒮.c (t + 1)) hsq
    (𝒮.B_hat t).symm
  have hpB : (𝒮.pBar t).stalkIdeal xb' =
      Ideal.span {((𝒮.xBar (t + 1)).ι.stalkMap xb').hom W} := by
    have h1 : 𝒮.pBar t = Subscheme.totalTransform (𝒮.xBar (t + 1)).ι
        (𝒮.tHat.monoidalTransformation t).exceptional := by
      unfold pBar
      exact congrArg _ hexc
    have h2 : (Subscheme.totalTransform (𝒮.xBar (t + 1)).ι
        ((𝒮.tHat.monoidalTransformation t).exceptional : Subscheme (𝒮.tHat.X (t + 1)))).stalkIdeal
          xb' = (((𝒮.tHat.monoidalTransformation t).exceptional :
            Subscheme (𝒮.tHat.X (t + 1))).stalkIdeal ((𝒮.xBar (t + 1)).ι.base xb')).map
              ((𝒮.xBar (t + 1)).ι.stalkMap xb').hom := stalkIdeal_totalTransform _ _ _
    rw [h1]
    refine h2.trans ((congrArg (Ideal.map _) hW.symm).trans ?_)
    exact (Ideal.map_span _ _).trans (congrArg Ideal.span Set.image_singleton)
  have hlp : (𝒮.pBar t).IsLocallyPrincipal :=
    ((T.monoidalTransformation t).invertible.isLocallyPrincipal.totalTransform
      (𝒮.c (t + 1))).totalTransform (𝒮.xBar (t + 1)).ι
  have hj : (𝒮.jBar (t + 1)).stalkIdeal xb' =
      ((Subscheme.totalTransform (𝒮.fBar t) (𝒮.jBar t)).stalkIdeal xb').colon
        ((Ideal.span {((𝒮.xBar (t + 1)).ι.stalkMap xb').hom W} ^ 𝒮.bBar : Ideal _) : Set _) := by
    show (Subscheme.divPow _ (𝒮.pBar t) 𝒮.bBar).stalkIdeal xb' = _
    rw [Subscheme.stalkIdeal_divPow_of_isLocallyPrincipal hlp, hpB]
  -- the local ring of `X̄_{t+1}` is a domain and `ψ W ≠ 0`
  obtain ⟨eq⟩ := nonempty_stalk_quot_equiv (𝒮.xBar (t + 1)) xb'
  have hregq : IsRegularLocalRing ((𝒮.tHat.X (t + 1)).presheaf.stalk ((𝒮.xBar (t + 1)).ι.base xb') ⧸
      (𝒮.xBar (t + 1)).stalkIdeal ((𝒮.xBar (t + 1)).ι.base xb')) := by
    have h1 := F₁.extends_rsop.isRegularLocalRing_quotient_span_singleton
      (k := F₁.z ⟨0, by rw [hr₁]; exact Nat.one_pos⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    rw [ha1]
    exact h1
  have hregR : IsRegularLocalRing ((𝒮.xBar (t + 1)).toScheme.presheaf.stalk xb') :=
    IsRegularLocalRing.of_ringEquiv eq
  have hdomR : IsDomain ((𝒮.xBar (t + 1)).toScheme.presheaf.stalk xb') :=
    isDomain_of_isRegularLocalRing _
  have hWψ : ((𝒮.xBar (t + 1)).ι.stalkMap xb').hom W ≠ 0 := fun h0 => hWz (by
    rw [← ha1, stalkIdeal_eq_ker_stalkMap]; exact h0)
  obtain ⟨h, hh⟩ := AB.exists_stalkMap_comm (f := (𝒮.xBar t).ι) (fh := (𝒮.xBar (t + 1)).ι)
    (c := 𝒮.tHat.f t) (c' := 𝒮.fBar t) (𝒮.fBar_comm t).symm xb'
  have hsq2 : ∀ x, ((𝒮.fBar t).stalkMap xb').hom
      (((𝒮.xBar t).ι.stalkMap ((𝒮.fBar t).base xb')).hom x) =
      ((𝒮.xBar (t + 1)).ι.stalkMap xb').hom
        ((((𝒮.tHat.X t).presheaf.stalkCongr (Inseparable.of_eq hxb)).hom ≫
          (𝒮.tHat.f t).stalkMap ((𝒮.xBar (t + 1)).ι.base xb')).hom x) := fun x =>
    congrArg (fun φ => φ.hom x) hh
  have hK : (Subscheme.totalTransform (𝒮.fBar t) (𝒮.jBar t)).stalkIdeal xb' =
      Ideal.span (Set.range fun p : Fin m × Fin ν =>
        ((𝒮.xBar (t + 1)).ι.stalkMap xb').hom (algebraMap F₁.S _ (co₁ p.1 p.2)) ^
            (𝒮.bBar / ((p.2 : ℕ) + 1)) *
          (((𝒮.xBar (t + 1)).ι.stalkMap xb').hom W *
            ((𝒮.xBar (t + 1)).ι.stalkMap xb').hom (U : _)) ^ 𝒮.bBar) := by
    refine (stalkIdeal_totalTransform _ _ _).trans ?_
    refine (congrArg (Ideal.map _) hd).trans ?_
    refine (Ideal.map_span _ _).trans ?_
    refine congrArg Ideal.span ((Set.range_comp _ _).symm.trans
      (congrArg Set.range (funext fun p => ?_)))
    show ((𝒮.fBar t).stalkMap xb').hom (((𝒮.xBar t).ι.stalkMap ((𝒮.fBar t).base xb')).hom
      (algebraMap F.S _ (co p.1 p.2) ^ (𝒮.bBar / ((p.2 : ℕ) + 1)))) = _
    rw [map_pow, map_pow, hsq2, hcoef p.1 p.2, map_mul, map_pow, map_mul, mul_pow, ← pow_mul]
    congr 2
    have hdvd : ((p.2 : ℕ) + 1) ∣ 𝒮.bBar := Nat.dvd_factorial (Nat.succ_pos _) p.2.2
    rw [Nat.mul_div_cancel' hdvd]
  rw [hj, hK]
  refine (Ideal.colon_span_range_mul_pow_unit (((𝒮.xBar (t + 1)).ι.stalkMap xb').hom W) hWψ
    𝒮.bBar (Units.map ((𝒮.xBar (t + 1)).ι.stalkMap xb').hom.toMonoidHom U)
    (fun p : Fin m × Fin ν => ((𝒮.xBar (t + 1)).ι.stalkMap xb').hom (algebraMap F₁.S _ (co₁ p.1 p.2)) ^
      (𝒮.bBar / ((p.2 : ℕ) + 1)))).trans ?_
  exact congrArg Ideal.span (congrArg Set.range (funext fun p => (map_pow _ _ _).symm))

/-- The same as `stalkInvData_succ_of_mem`, from the conditions (2), (3) of `[vii]` at `t` and
`x̂'_{t+1} ∈ X̄_{t+1}` instead of `x̂'_{t+1} ∈ S_ν(ℜ(t+1))` (Lemma (CD.5), p. 319-320).
Original: (a)$_{t+1}$–(d)$_{t+1}$ in the case (2) `x̂'_t ∈ B̂_t` (p. 318), with the point `x̄'_{t+1}` of
`X̄_{t+1}` over `x̂'_{t+1}` (it exists since `z_{t+1}` is a non-unit) and (d) obtained by dividing by
`P̄_{t+1}^{b̄}`: `J̄(t+1) = f̄_t⁻¹(J̄(t))/P̄_{t+1}^{b̄}`, where `ḡ_{ji}(t)^{b̄/i} = ḡ_{ji}(t+1)^{b̄/i}
w̄_t^{b̄}` and `w̄_t` is a non-zero-divisor of the domain `O_{X̄_{t+1}, x̄'_{t+1}}`.  The division is
computed with `P̄_{t+1}` locally principal (`Subscheme.stalkIdeal_divPow_of_isLocallyPrincipal`), so
the invertibility of `P̄_{t+1}` (`isNonsingular_xBar_zero_and_isMonoidalTransformationOf_fBar`) is not
used. -/
theorem stalkInvData_succ_of_defined [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (xh' : 𝒮.tHat.X (t + 1))
    (hdefc : 𝒮.IsCenterContained t) (hJc : 𝒮.IsJBarContained t)
    (hxbar : xh' ∈ (𝒮.xBar (t + 1)).pts)
    (xb : (𝒮.xBar t).toScheme) (hxb : (𝒮.xBar t).ι.base xb = (𝒮.tHat.f t).base xh')
    (hBne : (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb) ≠ ⊤)
    (hinv : ∃ (F : RegularFrame ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))) (hr : F.r = 1)
      (m : ℕ) (g : Fin m → (𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))
      (co : Fin m → Fin ν → F.S), 𝒮.StalkInvData t xb F hr m g co) :
    ∃ xb' : (𝒮.xBar (t + 1)).toScheme, (𝒮.xBar (t + 1)).ι.base xb' = xh' ∧
      ∃ (F₁ : RegularFrame ((𝒮.tHat.X (t + 1)).presheaf.stalk ((𝒮.xBar (t + 1)).ι.base xb')))
        (hr₁ : F₁.r = 1) (m : ℕ)
        (g₁ : Fin m → (𝒮.tHat.X (t + 1)).presheaf.stalk ((𝒮.xBar (t + 1)).ι.base xb'))
        (co₁ : Fin m → Fin ν → F₁.S), 𝒮.StalkInvData (t + 1) xb' F₁ hr₁ m g₁ co₁ := by
  classical
  obtain ⟨F, hr, m, g, co, hdata, F₁, hr₁, g₁, co₁, ha1, hz1, hb1, hsh1, hun1, W, U, hW, hWz, hcoef⟩ :=
    𝒮.exists_stalk_data_succ_of_defined t xh' hdefc hJc hxbar xb hxb hBne hinv
  obtain ⟨ha, hb, hsh, hun, hd⟩ := hdata
  have hmem : xh' ∈ (𝒮.xBar (t + 1)).pts := by
    rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, ha1]
    exact ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hz1)
  obtain ⟨xb', hxb'⟩ := Subscheme.exists_ι_eq_of_mem_pts (𝒮.xBar (t + 1)) hmem
  have hfb : xb = (𝒮.fBar t).base xb' := by
    refine subscheme_ι_injective (𝒮.xBar t) ?_
    rw [hxb, ← hxb']
    exact (congrArg (fun φ => φ.base xb') (𝒮.fBar_comm t)).symm
  subst hxb'
  subst hfb
  refine ⟨xb', rfl, F₁, hr₁, m, g₁, co₁, ha1, hb1, hsh1, hun1, ?_⟩
  -- (d)
  have hsq : 𝒮.c (t + 1) ≫ T.f t = 𝒮.tHat.f t ≫ 𝒮.c t := (𝒮.c_comm t).symm
  have hexc := MonoidalTransformation.totalTransform_exceptional_of_square
    (T.monoidalTransformation t) (𝒮.tHat.monoidalTransformation t) (𝒮.c t) (𝒮.c (t + 1)) hsq
    (𝒮.B_hat t).symm
  have hpB : (𝒮.pBar t).stalkIdeal xb' =
      Ideal.span {((𝒮.xBar (t + 1)).ι.stalkMap xb').hom W} := by
    have h1 : 𝒮.pBar t = Subscheme.totalTransform (𝒮.xBar (t + 1)).ι
        (𝒮.tHat.monoidalTransformation t).exceptional := by
      unfold pBar
      exact congrArg _ hexc
    have h2 : (Subscheme.totalTransform (𝒮.xBar (t + 1)).ι
        ((𝒮.tHat.monoidalTransformation t).exceptional : Subscheme (𝒮.tHat.X (t + 1)))).stalkIdeal
          xb' = (((𝒮.tHat.monoidalTransformation t).exceptional :
            Subscheme (𝒮.tHat.X (t + 1))).stalkIdeal ((𝒮.xBar (t + 1)).ι.base xb')).map
              ((𝒮.xBar (t + 1)).ι.stalkMap xb').hom := stalkIdeal_totalTransform _ _ _
    rw [h1]
    refine h2.trans ((congrArg (Ideal.map _) hW.symm).trans ?_)
    exact (Ideal.map_span _ _).trans (congrArg Ideal.span Set.image_singleton)
  have hlp : (𝒮.pBar t).IsLocallyPrincipal :=
    ((T.monoidalTransformation t).invertible.isLocallyPrincipal.totalTransform
      (𝒮.c (t + 1))).totalTransform (𝒮.xBar (t + 1)).ι
  have hj : (𝒮.jBar (t + 1)).stalkIdeal xb' =
      ((Subscheme.totalTransform (𝒮.fBar t) (𝒮.jBar t)).stalkIdeal xb').colon
        ((Ideal.span {((𝒮.xBar (t + 1)).ι.stalkMap xb').hom W} ^ 𝒮.bBar : Ideal _) : Set _) := by
    show (Subscheme.divPow _ (𝒮.pBar t) 𝒮.bBar).stalkIdeal xb' = _
    rw [Subscheme.stalkIdeal_divPow_of_isLocallyPrincipal hlp, hpB]
  -- the local ring of `X̄_{t+1}` is a domain and `ψ W ≠ 0`
  obtain ⟨eq⟩ := nonempty_stalk_quot_equiv (𝒮.xBar (t + 1)) xb'
  have hregq : IsRegularLocalRing ((𝒮.tHat.X (t + 1)).presheaf.stalk ((𝒮.xBar (t + 1)).ι.base xb') ⧸
      (𝒮.xBar (t + 1)).stalkIdeal ((𝒮.xBar (t + 1)).ι.base xb')) := by
    have h1 := F₁.extends_rsop.isRegularLocalRing_quotient_span_singleton
      (k := F₁.z ⟨0, by rw [hr₁]; exact Nat.one_pos⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    rw [ha1]
    exact h1
  have hregR : IsRegularLocalRing ((𝒮.xBar (t + 1)).toScheme.presheaf.stalk xb') :=
    IsRegularLocalRing.of_ringEquiv eq
  have hdomR : IsDomain ((𝒮.xBar (t + 1)).toScheme.presheaf.stalk xb') :=
    isDomain_of_isRegularLocalRing _
  have hWψ : ((𝒮.xBar (t + 1)).ι.stalkMap xb').hom W ≠ 0 := fun h0 => hWz (by
    rw [← ha1, stalkIdeal_eq_ker_stalkMap]; exact h0)
  obtain ⟨h, hh⟩ := AB.exists_stalkMap_comm (f := (𝒮.xBar t).ι) (fh := (𝒮.xBar (t + 1)).ι)
    (c := 𝒮.tHat.f t) (c' := 𝒮.fBar t) (𝒮.fBar_comm t).symm xb'
  have hsq2 : ∀ x, ((𝒮.fBar t).stalkMap xb').hom
      (((𝒮.xBar t).ι.stalkMap ((𝒮.fBar t).base xb')).hom x) =
      ((𝒮.xBar (t + 1)).ι.stalkMap xb').hom
        ((((𝒮.tHat.X t).presheaf.stalkCongr (Inseparable.of_eq hxb)).hom ≫
          (𝒮.tHat.f t).stalkMap ((𝒮.xBar (t + 1)).ι.base xb')).hom x) := fun x =>
    congrArg (fun φ => φ.hom x) hh
  have hK : (Subscheme.totalTransform (𝒮.fBar t) (𝒮.jBar t)).stalkIdeal xb' =
      Ideal.span (Set.range fun p : Fin m × Fin ν =>
        ((𝒮.xBar (t + 1)).ι.stalkMap xb').hom (algebraMap F₁.S _ (co₁ p.1 p.2)) ^
            (𝒮.bBar / ((p.2 : ℕ) + 1)) *
          (((𝒮.xBar (t + 1)).ι.stalkMap xb').hom W *
            ((𝒮.xBar (t + 1)).ι.stalkMap xb').hom (U : _)) ^ 𝒮.bBar) := by
    refine (stalkIdeal_totalTransform _ _ _).trans ?_
    refine (congrArg (Ideal.map _) hd).trans ?_
    refine (Ideal.map_span _ _).trans ?_
    refine congrArg Ideal.span ((Set.range_comp _ _).symm.trans
      (congrArg Set.range (funext fun p => ?_)))
    show ((𝒮.fBar t).stalkMap xb').hom (((𝒮.xBar t).ι.stalkMap ((𝒮.fBar t).base xb')).hom
      (algebraMap F.S _ (co p.1 p.2) ^ (𝒮.bBar / ((p.2 : ℕ) + 1)))) = _
    rw [map_pow, map_pow, hsq2, hcoef p.1 p.2, map_mul, map_pow, map_mul, mul_pow, ← pow_mul]
    congr 2
    have hdvd : ((p.2 : ℕ) + 1) ∣ 𝒮.bBar := Nat.dvd_factorial (Nat.succ_pos _) p.2.2
    rw [Nat.mul_div_cancel' hdvd]
  rw [hj, hK]
  refine (Ideal.colon_span_range_mul_pow_unit (((𝒮.xBar (t + 1)).ι.stalkMap xb').hom W) hWψ
    𝒮.bBar (Units.map ((𝒮.xBar (t + 1)).ι.stalkMap xb').hom.toMonoidHom U)
    (fun p : Fin m × Fin ν => ((𝒮.xBar (t + 1)).ι.stalkMap xb').hom (algebraMap F₁.S _ (co₁ p.1 p.2)) ^
      (𝒮.bBar / ((p.2 : ℕ) + 1)))).trans ?_
  exact congrArg Ideal.span (congrArg Set.range (funext fun p => (map_pow _ _ _).symm))

/-- (a)$_{t+1}$–(d)$_{t+1}$ from (a)$_t$–(d)$_t$ (p. 318): the frame transform `(T'_{t+1}; z_{t+1})`
of `(T'_t; z_t)` with denominator `v_t ∈ T'_t`, `z_{t+1} = z_t/v_t`, `g_j(t+1) = g_j(t)/v_t^ν`;
`z_t ∈ Q̂'_t` (closed case clear, otherwise Lemma 22), `g_{ji}(t) ∈ (Q̂'_t ∩ T'_t)^i`,
`w_t^{-1}(Q̂'_t ∩ T'_t)Ŝ'_{t+1}` the unit ideal, `z_{t+1}` a non-unit (closed case:
`x'_{t+1} ∈ F(t+1)`; otherwise Lemma 22).  Ring-level content: `admitsFrameTransform_iff`
(FrameTransforms) and `mem_prime_of_ordElem_localization_ge` (JStabilityLemma22), packaged as the
ring-level `frame_step_core`; scheme-level content:
the stalk of `X̂_{t+1}` at `x̂'_{t+1}` is a monoidal transform of that of `X̂_t` at `x̂'_t` with
center `Q̂'_t` (`exists_monoidalTransform_stalk`), the stalks of `X̄_{t+1}`, of `J(t+1)`, and of
`J̄(t+1) = f̄_t⁻¹(J̄(t))/(P̄_{t+1})^{b̄}`. -/
theorem stalkInv_succ [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (xh' : 𝒮.tHat.X (t + 1))
    (hxh' : (𝒮.c (t + 1)).base xh' ∈ sNu (datum T ℜ (t + 1)) (restriction T r (t + 1)) ν)
    (xb : (𝒮.xBar t).toScheme) (hxb : (𝒮.xBar t).ι.base xb = (𝒮.tHat.f t).base xh')
    (hinv : 𝒮.StalkInv t xb) :
    ∃ xb', (𝒮.xBar (t + 1)).ι.base xb' = xh' ∧ 𝒮.StalkInv (t + 1) xb' := by
  classical
  have hne : (sNu (datum T ℜ t) (restriction T r t) ν).Nonempty := ⟨_, hS.f_mem_sNu t hxh'⟩
  have hνt : (datum T ℜ t).nu = ν := hS.nu_datum_eq t hne
  obtain ⟨F0, hr0, m0, g0, co0, hd0, -⟩ := hinv
  have hinv : ∃ (F : RegularFrame ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb)))
      (hr : F.r = 1) (m : ℕ) (g : Fin m → (𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))
      (co : Fin m → Fin ν → F.S), 𝒮.StalkInvData t xb F hr m g co := ⟨F0, hr0, m0, g0, co0, hd0⟩
  by_cases hB : (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb) = ⊤
  · -- case (1): `x̂'_t ∉ B̂_t`
    obtain ⟨xb', hxb', F₁, hr₁, m, g₁, co₁, hdata⟩ :=
      𝒮.stalkInvData_succ_of_notMem t xh' xb hxb hB hinv
    subst hxb'
    exact ⟨xb', rfl, F₁, hr₁, m, g₁, co₁, hdata,
      𝒮.centerClause_leaf (t + 1) xb' F₁ hr₁ m g₁ co₁ hdata hxh'⟩
  · -- case (2): `x̂'_t ∈ B̂_t`, monoidal transform of the local rings (`frame_step_core`)
    obtain ⟨xb', hxb', F₁, hr₁, m, g₁, co₁, hdata⟩ :=
      𝒮.stalkInvData_succ_of_mem t xh' hxh' xb hxb hB hνt hinv
    subst hxb'
    exact ⟨xb', rfl, F₁, hr₁, m, g₁, co₁, hdata,
      𝒮.centerClause_leaf (t + 1) xb' F₁ hr₁ m g₁ co₁ hdata hxh'⟩

/-- The induction of p. 317–318: (a)$_t$–(d)$_t$ hold at every point `x̂'_t` of `X̂_t` whose image
`c_t(x̂'_t)` lies in `S_ν(ℜ(t))`. -/
theorem exists_stalkInv [Hironaka.HironakaCitedResults.{u}] (t : ℕ) : ∀ xh : 𝒮.tHat.X t,
    (𝒮.c t).base xh ∈ sNu (datum T ℜ t) (restriction T r t) ν →
      ∃ xb, (𝒮.xBar t).ι.base xb = xh ∧ 𝒮.StalkInv t xb := by
  induction t with
  | zero => exact fun xh hxh => 𝒮.stalkInv_zero xh hxh
  | succ t ih =>
    intro xh' hxh'
    have hcomm : (𝒮.c t).base ((𝒮.tHat.f t).base xh') = (T.f t).base ((𝒮.c (t + 1)).base xh') := by
      rw [← Scheme.Hom.comp_apply, 𝒮.c_comm t, Scheme.Hom.comp_apply]
    have h1 : (𝒮.c t).base ((𝒮.tHat.f t).base xh') ∈ sNu (datum T ℜ t) (restriction T r t) ν := by
      rw [hcomm]; exact hS.f_mem_sNu t hxh'
    obtain ⟨xb, hxb, hinv⟩ := ih _ h1
    exact 𝒮.stalkInv_succ t xh' hxh' xb hxb hinv

/-- A point of `X̂_t` whose image lies in `S_ν(ℜ(t))`, for every `t ≤ s`, given a point `y` of
`S_ν(ℜ(s))` over `x_0` (by Lemma (CD.3), `c_s` is onto the fibre over `x_0`). -/
theorem exists_pt_sNu_of_le [Hironaka.HironakaCitedResults.{u}] {s : ℕ} {y : T.X s}
    (hy : y ∈ sNu (datum T ℜ s) (restriction T r s) ν)
    (hyx : (T.pre s).composite.base y = x₀) (t : ℕ) (ht : t ≤ s) :
    ∃ xh : 𝒮.tHat.X t, (𝒮.c t).base xh ∈ sNu (datum T ℜ t) (restriction T r t) ν := by
  have hdown : ∀ k t, t + k = s → ∃ xh : 𝒮.tHat.X t,
      (𝒮.c t).base xh ∈ sNu (datum T ℜ t) (restriction T r t) ν := by
    intro k
    induction k with
    | zero =>
      intro t htk
      obtain rfl : t = s := by omega
      obtain ⟨xh, -, hxh⟩ :=
        (hS.bijOn_and_mapsRSOP_and_exists_unique_totalTransform 𝒮.toCompletion t).1.surjOn
          (show y ∈ (T.pre t).composite.base ⁻¹' {x₀} from hyx)
      exact ⟨xh, hxh ▸ hy⟩
    | succ k ih =>
      intro t htk
      obtain ⟨xh', hxh'⟩ := ih (t + 1) (by omega)
      refine ⟨(𝒮.tHat.f t).base xh', ?_⟩
      have hcomm : (𝒮.c t).base ((𝒮.tHat.f t).base xh') =
          (T.f t).base ((𝒮.c (t + 1)).base xh') := by
        rw [← Scheme.Hom.comp_apply, 𝒮.c_comm t, Scheme.Hom.comp_apply]
      rw [hcomm]
      exact hS.f_mem_sNu t hxh'
  exact hdown (s - t) t (by omega)

/-- A point of `B̂_t` maps into `B_t ⊆ S_ν(ℜ(t))`. -/
theorem c_mem_sNu_of_mem_pts_B [Hironaka.HironakaCitedResults.{u}] {t : ℕ}
    (hne : (sNu (datum T ℜ t) (restriction T r t) ν).Nonempty) {x : 𝒮.tHat.X t}
    (hx : x ∈ (𝒮.tHat.B t).pts) :
    (𝒮.c t).base x ∈ sNu (datum T ℜ t) (restriction T r t) ν := by
  rw [𝒮.B_hat t, FlatPreimm.pts_totalTransform] at hx
  exact hS.pts_B_subset_sNu t hne hx

/-- [vii] (2) at `t` (p. 318: "`z_t ∈ Q̂'_t`"): `B̂_t ⊆ X̄_t`. -/
theorem isCenterContained_of [Hironaka.HironakaCitedResults.{u}] (t : ℕ)
    (hne : (sNu (datum T ℜ t) (restriction T r t) ν).Nonempty) : 𝒮.IsCenterContained t := by
  show (𝒮.xBar t) ≤ (𝒮.tHat.B t)
  rw [Subscheme.le_iff_stalkIdeal_le]
  intro x
  by_cases hx : (𝒮.tHat.B t).stalkIdeal x = ⊤
  · rw [hx]; exact le_top
  · have hxp : x ∈ (𝒮.tHat.B t).pts := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr hx
    obtain ⟨xb, rfl, F, hr, m, g, co, ⟨ha, -, -, -, -⟩, hz⟩ :=
      𝒮.exists_stalkInv t x (𝒮.c_mem_sNu_of_mem_pts_B hne hxp)
    rw [ha, Ideal.span_le]
    exact Set.singleton_subset_iff.mpr (hz hx).1

/-- [vii] (3) at `t` (p. 318: "`g_{ji}(t) ∈ (Q̂'_t ∩ T'_t)^i`"): `J̄(t)` lies in the `b̄`-th power
of the sheaf of prime ideals of `B̂_t` on `X̄_t`. -/
theorem isJBarContained_of [Hironaka.HironakaCitedResults.{u}] (t : ℕ)
    (hne : (sNu (datum T ℜ t) (restriction T r t) ν).Nonempty) : 𝒮.IsJBarContained t := by
  intro x
  have hQ : (𝒮.bBarOn t).stalkIdeal x = ((𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base x)).map
      ((𝒮.xBar t).ι.stalkMap x).hom := Subscheme.stalkIdeal_comap _ _ _
  by_cases hx : (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base x) = ⊤
  · rw [hQ, hx, Ideal.map_top, Ideal.top_pow]; exact le_top
  · have hxp : (𝒮.xBar t).ι.base x ∈ (𝒮.tHat.B t).pts :=
      Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr hx
    obtain ⟨xb, hxb, F, hr, m, g, co, ⟨-, -, -, -, hd⟩, hz⟩ :=
      𝒮.exists_stalkInv t _ (𝒮.c_mem_sNu_of_mem_pts_B hne hxp)
    obtain rfl : xb = x := (𝒮.xBar t).ι.isEmbedding.injective hxb
    rw [hd, hQ, Ideal.span_le]
    rintro _ ⟨⟨j, i⟩, rfl⟩
    set Q := (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base xb)
    let φ := algebraMap F.S ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))
    have h1 : φ (co j i) ∈ Q ^ ((i : ℕ) + 1) := by
      have h := Ideal.mem_map_of_mem φ ((hz hx).2 j i)
      rw [Ideal.map_pow] at h
      exact (Ideal.pow_right_mono Ideal.map_comap_le _) h
    have hdvd : ((i : ℕ) + 1) ∣ 𝒮.bBar := Nat.dvd_factorial (Nat.succ_pos _) i.2
    have h2 : (φ (co j i)) ^ (𝒮.bBar / ((i : ℕ) + 1)) ∈ Q ^ 𝒮.bBar := by
      have := Ideal.pow_mem_pow h1 (𝒮.bBar / ((i : ℕ) + 1))
      rwa [← pow_mul, mul_comm, Nat.div_mul_cancel hdvd] at this
    have h3 := Ideal.mem_map_of_mem ((𝒮.xBar t).ι.stalkMap xb).hom h2
    rwa [Ideal.map_pow] at h3

/-- [vii] (1) for `s = 0` (p. 316: `X̄_0 = Spec(T̄_0)` non-singular irreducible). -/
theorem isNonsingIrred_zero [Hironaka.HironakaCitedResults.{u}] : 𝒮.IsNonsingIrred 0 :=
  ⟨𝒮.xBar_zero_facts.1, 𝒮.xBar_zero_facts.2.1⟩

/-- [vii] (1) for `s + 1` from (1), (2) for `s` (p. 317: "(1) can be verified for `s + 1` if
both (1)
and (2) are done for some `s`"); `X̄_{s+1}` is irreducible when it is non-empty. -/
theorem isNonsingIrred_succ [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (h : 𝒮.IsNonsingIrred t) (hc : 𝒮.IsCenterContained t)
    (hpts : (𝒮.xBar (t + 1)).pts.Nonempty) : 𝒮.IsNonsingIrred (t + 1) :=
  ⟨(𝒮.isNonsingular_xBar_succ_and_isInvertibleIdeal_pBar t hc h).1,
    (𝒮.xBar_pts_eq_empty_or_isIrreducible (t + 1)).resolve_left hpts.ne_empty⟩

/-- [vii] (1) for `s = 0`, as printed. -/
theorem isNonsingIrredOrEmpty_zero [Hironaka.HironakaCitedResults.{u}] : 𝒮.IsNonsingIrredOrEmpty 0 :=
  ⟨𝒮.isNonsingIrred_zero.1, Or.inr 𝒮.isNonsingIrred_zero.2⟩

/-- [vii] (1) for `s + 1` from (1), (2) for `s`, as printed (p. 317: "(1) can be verified for
`s + 1` if both (1) and (2) are done for some `s`"): if `X̄_s` is empty so is `X̄_{s+1}` (a strict
transform of the empty scheme); otherwise `X̄_{s+1}` is non-singular (`B̂_s ⊆ X̄_s`) and is
irreducible or empty (agreement of p. 163). -/
theorem isNonsingIrredOrEmpty_succ [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (h : 𝒮.IsNonsingIrredOrEmpty t)
    (hc : 𝒮.IsCenterContained t) : 𝒮.IsNonsingIrredOrEmpty (t + 1) := by
  refine ⟨?_, 𝒮.xBar_pts_eq_empty_or_isIrreducible (t + 1)⟩
  rcases h.2 with he | hirr
  · have hE : (𝒮.xBar (t + 1)).pts = ∅ :=
      pts_strictTransform_eq_empty_of_subset (𝒮.tHat.monoidalTransformation t) (𝒮.xBar t)
        (he ▸ Set.empty_subset _)
    exact fun x => absurd (Subscheme.mem_pts_ι (𝒮.xBar (t + 1)) x) (by rw [hE]; exact Set.notMem_empty _)
  · exact (𝒮.isNonsingular_xBar_succ_and_isInvertibleIdeal_pBar t hc ⟨h.1, hirr⟩).1

/-- **Lemma (CD.4)** (p. 316), as printed: if `S_ν(ℜ(s))` is not empty, the conditions (1), (2),
(3) of `[vii]` hold at every `t ≤ s` (with (1) allowing the empty `X̄_t`).  (2) and (3) at `t` need
only `S_ν(ℜ(t)) ≠ ∅` (`isCenterContained_of`, `isJBarContained_of`: the stalk invariants hold at
every point of `X̂_t` over `S_ν(ℜ(t))`, in particular at the points of `B̂_t`), (1) is the induction
`isNonsingIrredOrEmpty_zero`, `isNonsingIrredOrEmpty_succ`. -/
theorem forall_le_conditions_orEmpty [Hironaka.HironakaCitedResults.{u}] {s : ℕ}
    (hne : (sNu (datum T ℜ s) (restriction T r s) ν).Nonempty) :
    ∀ t, t ≤ s → 𝒮.IsNonsingIrredOrEmpty t ∧ 𝒮.IsCenterContained t ∧ 𝒮.IsJBarContained t := by
  intro t
  induction t with
  | zero =>
    intro h0
    exact ⟨𝒮.isNonsingIrredOrEmpty_zero, 𝒮.isCenterContained_of 0 (hS.sNu_nonempty_of_le h0 hne),
      𝒮.isJBarContained_of 0 (hS.sNu_nonempty_of_le h0 hne)⟩
  | succ t ih =>
    intro hts
    obtain ⟨h1, h2, -⟩ := ih (by omega)
    exact ⟨𝒮.isNonsingIrredOrEmpty_succ t h1 h2,
      𝒮.isCenterContained_of (t + 1) (hS.sNu_nonempty_of_le hts hne),
      𝒮.isJBarContained_of (t + 1) (hS.sNu_nonempty_of_le hts hne)⟩

/-- `X̄_t ≠ ∅` for `t ≤ s`, given a point `y` of `S_ν(ℜ(s))` over `x_0`: a point of `X̂_t` over
`S_ν(ℜ(t))` (Lemma (CD.3)) carries the stalk invariants, in particular (a)$_t$: it lies on `X̄_t`. -/
theorem xBar_pts_nonempty_of_le [Hironaka.HironakaCitedResults.{u}] {s : ℕ} {y : T.X s}
    (hy : y ∈ sNu (datum T ℜ s) (restriction T r s) ν)
    (hyx : (T.pre s).composite.base y = x₀) (t : ℕ) (ht : t ≤ s) :
    (𝒮.xBar t).pts.Nonempty := by
  obtain ⟨xh, hxh⟩ := 𝒮.exists_pt_sNu_of_le hy hyx t ht
  obtain ⟨xb, -, -⟩ := 𝒮.exists_stalkInv t xh hxh
  exact ⟨_, Subscheme.mem_pts_ι _ xb⟩

/-- **Lemma (CD.4)** (p. 316), for a point `y` of `S_ν(ℜ(s))` over `x_0`: the conditions (1),
(2), (3)
of `[vii]` hold at every `t ≤ s`.  This is `forall_le_conditions_orEmpty`, with (1) strengthened
to a non-empty `X̄_t` (`xBar_pts_nonempty_of_le`). -/
theorem forall_le_conditions [Hironaka.HironakaCitedResults.{u}] {s : ℕ} {y : T.X s}
    (hy : y ∈ sNu (datum T ℜ s) (restriction T r s) ν)
    (hyx : (T.pre s).composite.base y = x₀) :
    ∀ t, t ≤ s → 𝒮.IsNonsingIrred t ∧ 𝒮.IsCenterContained t ∧ 𝒮.IsJBarContained t := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := 𝒮.forall_le_conditions_orEmpty ⟨y, hy⟩ t ht
  exact ⟨⟨h1.1, h1.2.resolve_left (𝒮.xBar_pts_nonempty_of_le hy hyx t ht).ne_empty⟩, h2, h3⟩

/-- **Lemma (CD.4)** (p. 316): if `x_0 ∈ h_s(S_ν(h_s^*(ℜ)))`, the conditions (1), (2), (3) of
`[vii]`
are satisfied at `s`. -/
theorem isAdmissibleAt_of_mem_image_sNu_aux [Hironaka.HironakaCitedResults.{u}] (s : ℕ)
    (hx : x₀ ∈ (T.pre s).composite.base '' sNu (datum T ℜ s) (restriction T r s) ν) :
    𝒮.IsAdmissibleAt s := by
  obtain ⟨y, hy, hyx⟩ := hx
  have h := 𝒮.forall_le_conditions hy hyx
  exact ⟨(h s le_rfl).1, (h s le_rfl).2.1, fun t ht => h t ht.le, (h s le_rfl).2.2⟩

end Frame

/-- **Lemma (CD.4)** (p. 316), as printed: "If `s` is any non-negative integer such that
`S_ν(h_s^*(ℜ))` is not empty, the above conditions (1), (2) and (3) of [vii] are satisfied.  (Note that
`B̂_s` may be empty.)"  `S_ν(h_s*(ℜ))` is `CD.sNu` of the transform `ℜ(s)` along `h_s`, and
"irreducible" in (1) allows the empty scheme (`IsNonsingIrredOrEmpty`, the agreement of p. 163).

The stalk invariants (a)$_t$–(d)$_t$ of the proof hold at every point of `X̂_t` whose image lies
in `S_ν(ℜ(t))` (`exists_stalkInv`); (2) and (3) at `t` need only `S_ν(ℜ(t)) ≠ ∅`
(`isCenterContained_of`, `isJBarContained_of`: the points of `B̂_t` map into `B_t ⊆ S_ν(ℜ(t))`),
and (1) is the induction of p. 316 (`isNonsingIrredOrEmpty_zero`, `isNonsingIrredOrEmpty_succ`). -/
@[blueprint "lem:IV.CD-4-paper"
  (statement := /-- \textbf{Lemma (CD.4)} (as printed). Notation as in \cref{def:IV.4-frame},
    \cref{def:IV.4-construction}. If $s$ is any non-negative integer such that
    $S_\nu(h_s^*(\mathfrak R))$ is not empty, the above conditions (1), (2) and (3) of [vii]
    are satisfied. (Note that $\hat B_s$ may be empty.) (p.~316.) Here, as on p.~163, the empty
    scheme counts as irreducible in (1): $\bar X_s$ is non-singular and either empty or
    irreducible. -/)
  (proof := /-- The proof of \cref{lem:IV.CD-4} (pp.~316--318), which is carried out at the points
    $\hat x'$ of $\hat B_t$: (a)$_t$--(d)$_t$ hold at every point of $\hat X_t$ whose image lies in
    $S_\nu(\mathfrak R(t))$, and $S_\nu(\mathfrak R(t))\ne\emptyset$ for $t\le s$ since
    $f_t(S_\nu(\mathfrak R(t+1)))\subseteq S_\nu(\mathfrak R(t))$, so that
    $\nu(\mathfrak R(t))=\nu$ and $B_t\subseteq S_\nu(\mathfrak R(t))$. Hence (2) and (3) hold
    at every $t\le s$ (``(2) and (3) are trivially true if $\hat B_s$ is empty''), and (1) follows
    by the induction of p.~316: (1) is true for $s=0$, and for $s+1$ if (1) and (2) hold for $s$,
    $\bar X_{s+1}$ being then the monoidal transform of $\bar X_s$ with the non-singular center
    $\hat B_s$, hence non-singular, and irreducible or empty (empty when $\bar X_s\subseteq
    \hat B_s$, or when $\bar X_s$ is empty).

    \textbf{Deviation from the paper (encoding).} ``Irreducible'' allows the empty scheme in
    (1), as on p.~163 (the Lean predicate \texttt{IsIrreducible} asks for a non-empty scheme, and
    \cref{lem:IV.CD-4} asks for $x_0\in h_s(S_\nu(\mathfrak R(s)))$ in order to have it). The
    $S_\nu(h_s^*(\mathfrak R))$ of the statement is a subset of $X_s$ that need not lie over
    $x_0$. -/)
  (proofUses := ["lem:IV.4-construction-facts"])
  (latexEnv := "lemma")]
theorem Frame.isAdmissibleAtOrEmpty_of_sNu_nonempty [Hironaka.HironakaCitedResults.{u}] {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)
    (s : ℕ) (hne : (sNu (datum T ℜ s) (restriction T r s) ν).Nonempty) :
    𝒮.IsAdmissibleAtOrEmpty s := by
  have h := 𝒮.forall_le_conditions_orEmpty hne
  exact ⟨(h s le_rfl).1, (h s le_rfl).2.1, fun t ht => h t ht.le, (h s le_rfl).2.2⟩

/-- **Lemma (CD.4)** (p. 316), for a point `x_0` of `h_s(S_ν(h_s^*(ℜ)))`.  `S_ν(h_s*(ℜ))` is `CD.sNu` of the
transform `ℜ(s)` along `h_s`.  The printed statement (`S_ν(h_s^*(ℜ))` not empty, `X̄_s` possibly empty)
is `Frame.isAdmissibleAtOrEmpty_of_sNu_nonempty` (node `lem:IV.CD-4-paper`); this one asks for a
non-empty `X̄_s` in (1) and is its consequence when `x_0 ∈ h_s(S_ν)` (`forall_le_conditions`). -/
@[blueprint "lem:IV.CD-4"
  (statement := /-- \textbf{Lemma (CD.4).} Notation as in \cref{def:IV.4-frame},
    \cref{def:IV.4-construction}. If $s$ is any non-negative integer such that
    $S_\nu(h_s^*(\mathfrak R))$ is not empty, the above conditions (1), (2) and (3) of [vii]
    are satisfied. (Note that $\hat B_s$ may be empty.) (p.~316.) -/)
  (proof := /-- (pp.~316--318.) (1) is true for $s=0$ and can be verified for $s+1$ if both (1)
    and (2) are done for some $s\ge0$, and (2), (3) are trivially true if $\hat B_s$ is empty
    (\cref{lem:IV.4-construction-facts}). Assume $\hat B_s$ non-empty, let $\hat x'$ be any point
    of $\hat B_s$ and $x'=c_s(\hat x')$, and $\hat x'_t$ (resp.\ $x'_t$) the image of $\hat x'$
    (resp.\ $x'$) in $\hat X_t$ (resp.\ $X_t$), $0\le t\le s$; $c_t(\hat x'_t)=x'_t$. Let $S'_t$,
    $\hat S'_t$ be the local rings of $X_t$ at $x'_t$ and $\hat X_t$ at $\hat x'_t$, $Q'_t$ the
    ideal of $B_t$ in $S'_t$, $\hat Q'_t=Q'_t\hat S'_t$ the ideal of $\hat B_t$, $J'_t=J(t)_{x'_t}$
    and $\hat J'_t=J'_t\hat S'_t$. One proves by induction on $t$ that there exist a regular frame
    $(T'_t;z_t)$ of $\hat S'_t$, elements $g_j(t)\in\hat S'_t$ and $v_t\in T'_t$ with: (a)$_t$
    $\hat x'_t\in\bar X_t$ and $z_t$ generates the kernel of $\hat S'_t\to\bar T'_t$ (the local
    ring of $\bar X_t$ at $\hat x'_t$); (b)$_t$ $(g_1(t),\dots,g_m(t))$ is a base of $\hat J'_t$
    and $g_j(t)=z_t^\nu+g_{j1}(t)z_t^{\nu-1}+\dots+g_{j\nu}(t)$ with $g_{ji}(t)\in T'_t$;
    (c)$_t$ $g_{11}(t)=0$ without restriction; (d)$_t$ $\bar J'_t=(g_{ji}(t)^{\bar b/i})\bar T'_t$;
    (e)$_t$ $z_{t+1}=z_t/v_t$, i.e.\ $(T'_{t+1};z_{t+1})$ is a frame transform of $(T'_t;z_t)$ in
    $\hat S'_{t+1}$ with denominator $v_t$ (\cref{def:III.8-frame-transform}); (f)$_t$
    $g_j(t+1)=g_j(t)/v_t^\nu$. By assumption $x'\in B_s\subseteq S_\nu(h_s^*(\mathfrak R))$, so
    $x'_t\in S_\nu(h_t^*(\mathfrak R))$ for all $t$; in particular $\hat J'_0$ lies in the $\nu$th
    power of the maximal ideal of $\hat S'_0=(\hat S_0)_{\hat P}$. The prime $\hat P$ of
    $\hat x'_0$ contains $z_0$: clear in the closed case, and in the other case by Lemma~22,
    \S10, Ch.~III (\cref{lem:III.22}) applied to $g_1=z_0^\nu+g_{12}z_0^{\nu-2}+\dots+g_{1\nu}$
    with $\nu_{\hat P(\hat S_0)_{\hat P}}(f_1)\ge\nu$ [sic; $g_1$]. With $T'_0$ the localization of
    $T_0$ at $\hat P\cap T_0$ and $g_j(0)=g_j$, (a)$_0$--(d)$_0$ hold. Inductively, since
    $B_t\subseteq S_\nu(h_t^*(\mathfrak R))$, $\hat J'_t\subseteq(\hat Q'_t)^\nu$; by (c)$_t$ and
    Lemma~22 (unrestricted case), or trivially (closed case), $z_t\in\hat Q'_t$ and then
    $g_{ji}(t)\in(\hat Q'_t\cap T'_t)^i$. Taking $w_t$ with $(w_t)\hat S'_{t+1}=\hat Q'_t\hat
    S'_{t+1}$, the $g_j(t)/w_t^\nu$ form a base of $\hat J'_{t+1}$ lying in the $\nu$th power of
    the maximal ideal, so $w_t^{-1}(\hat Q'_t\cap T'_t)\hat S'_{t+1}$ is the unit ideal and there is
    $v_t\in T'_t$ with $(v_t)\hat S'_{t+1}=\hat Q'_t\hat S'_{t+1}$; $z_{t+1}=z_t/v_t$ generates the
    ideal of $\bar X_{t+1}$ and is a non-unit (closed case: $x'_{t+1}\in
    S_\nu(h^*_{t+1}(\mathfrak R^N_{\mathrm{II}}))\cap F(t+1)$; other case: Lemma~22 applied to
    $g_1(t)/v_t$ [sic; $v_t^\nu$] $=z_{t+1}^\nu+(g_{12}(t)/v_t^2)z_{t+1}^{\nu-2}+\dots$). The
    conditions (1), (2), (3) of [vii] follow from (a)$_s$--(d)$_s$. \textsc{q.e.d.}

    \textbf{Paper misprint.} On p.~317 the paper writes $\nu_{\hat P(\hat S_0)_{\hat P}}(f_1)
    \ge\nu$ for $g_1$, and on p.~318 it applies Lemma~22 to ``$g_1(t)/v_t$'' for
    $g_1(t)/v_t^\nu$ (marked [sic] above).

    \textbf{Deviation from the paper (gap filled).} ``Since $B_t$ is contained in
    $S_\nu(h_t^*(\mathfrak R))$, $\hat J'_t$ is contained in the $\nu$th power of $\hat Q'_t$''
    (p.~318) is proved at the generic point of $B_t$ (the powers of the ideal of $B_t$ are primary,
    $S'_t/Q'_t$ being regular) and transported along $c_t$, whose stalk maps carry $Q'_t$ to
    $\hat Q'_t$. In the closed case, ``clear'' (p.~318) rests on $\bar X_t=c_t^{-1}(F(t))$
    (p.~297), which is proved by induction on $t$ ($\bar X_0=c_0^{-1}(F)$, and strict transforms
    commute with the flat base change $c_{t+1}$).

    \textbf{Deviation from the paper (statement modified).} The Lean statement assumes
    $x_0\in h_s(S_\nu(\mathfrak R(s)))$ (as in the conditions of \cref{def:IV.4-conditions}),
    not only that $S_\nu(h_s^*(\mathfrak R))$ is non-empty. In the paper ``irreducible'' allows the
    empty scheme (p.~163), so $\bar X_s=\emptyset$ is harmless there; in Lean (1) asserts that
    $\bar X_s$ is non-empty, which needs a point of $S_\nu(\mathfrak R(s))$ over $x_0$ (it is
    the point $\hat x'$ of the proof, taken over $\hat x_0$ by Lemma (CD.3)). The lemma as printed,
    with ``irreducible'' allowing the empty scheme, is \cref{lem:IV.CD-4-paper}; the present
    statement is the same with $\bar X_t\ne\emptyset$ for $t\le s$.

    \textbf{Deviation from the paper (incomplete citation).} On p.~318 Lemma~22 (p.~265) is applied
    to $(T'_{t+1};z_{t+1})$ to show that $z_{t+1}$ is a non-unit, but by Definition~9 (p.~248) a
    regular frame requires $z_{t+1}$ to be part of a regular system of parameters, hence a
    non-unit, which is the conclusion sought. The claim is true (the characteristic-zero argument of
    the proof of Lemma~22, using $g_{11}=0$) and is proved separately
    (\texttt{frame\_zeta\_mem\_maximalIdeal\_of\_unrestricted}).

    \textbf{Deviation from the paper (gap filled).} ``If $\mathfrak R=\mathfrak R^N_{\mathrm{II}}$,
    $(T'_0;z_0)$ is a regular frame of $S'_0$'' (p.~317) is proved
    (\texttt{exists\_frame\_localization}: $R_P/(z)R_P\simeq S_{P\cap S}$ and $z$ extends to a
    regular system of parameters of $R_P$). ``It then follows that $g_{ji}(t)\in(\hat Q'_t\cap
    T'_t)^i$'' (p.~318) is proved (\texttt{frame\_coeff\_mem\_pow}: modulo $z$, then $\nu_Q(z)=1$ and
    $\operatorname{gr}_Q(R)$ a domain). ``Hence $w_t^{-1}(\hat Q'_t\cap T'_t)\hat S'_{t+1}$ is the unit
    ideal'' and the existence of the frame transform with $z_{t+1}=z_t/v_t$ are proved
    (\texttt{exists\_mem\_comap\_assoc\_w}, \texttt{frame\_step\_core}).

    \textbf{Deviation from the paper (gap filled).} The paper's induction is carried out
    for the points $\hat x'_t$ over a single point of $\hat B_s$; Lean proves
    (a)$_t$--(d)$_t$ at every point $\hat x'_t$ of $\hat X_t$ with $c_t(\hat x'_t)\in
    S_\nu(\mathfrak R(t))$ (induction on $t$, using $f_t(S_\nu(\mathfrak R(t+1)))\subseteq
    S_\nu(\mathfrak R(t))$), and derives (2) and (3) at $t$ from the extra clauses ``$z_t\in\hat
    Q'_t$, $g_{ji}(t)\in(\hat Q'_t\cap T'_t)^i$'' at the points of $\hat B_t$ (whose images lie in
    $B_t\subseteq S_\nu(\mathfrak R(t))$, as $\nu(\mathfrak R(t))=\nu$), and (1) at $t+1$
    from (1), (2) at $t$ and the non-emptiness of $\bar X_{t+1}$
    (\cref{lem:IV.4-construction-facts}). The base case and the inductive step
    (\texttt{stalkInv\_zero}, \texttt{stalkInv\_succ}) and the non-singularity of $\hat X_t$ are
    proved in Lean. -/)
  (proofUses := ["lem:IV.4-construction-facts", "def:III.8-frame-transform"])
  (latexEnv := "lemma")]
theorem Frame.isAdmissibleAt_of_mem_image_sNu [Hironaka.HironakaCitedResults.{u}] {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)
    (s : ℕ)
    (hx : x₀ ∈ (T.pre s).composite.base '' sNu (datum T ℜ s) (restriction T r s) ν) :
    𝒮.IsAdmissibleAt s :=
  Frame.isAdmissibleAt_of_mem_image_sNu_aux 𝒮 s hx

/-- The reduced closed point `{x}` of a non-singular algebraic scheme is a center
(non-singular irreducible). -/
theorem _root_.Hironaka.Subscheme.isCenter_ofClosed_singleton {Y : Scheme.{u}}
    [IsAlgebraicScheme Y] (hY : Y.IsNonsingular) {x : Y} (hcl : IsClosed ({x} : Set Y)) :
    (Subscheme.ofClosed ⟨{x}, hcl⟩).IsCenter := by
  classical
  set B : Subscheme Y := Subscheme.ofClosed ⟨{x}, hcl⟩ with hBdef
  have hBpts : B.pts = {x} := Subscheme.pts_ofClosed _
  have hxB : x ∈ B.pts := by rw [hBpts]; rfl
  have hmax : B.stalkIdeal x = maximalIdeal (Y.presheaf.stalk x) :=
    AB.stalkIdeal_ofClosed_singleton_eq_maximalIdeal x hcl
  have : IsRegularLocalRing (Y.presheaf.stalk x) := hY x
  have hsimple : B.IsSimpleAt x := by
    refine ⟨hxB, ?_⟩
    rw [hmax]
    let _ : Field (Y.presheaf.stalk x ⧸ maximalIdeal (Y.presheaf.stalk x)) :=
      Ideal.Quotient.field _
    infer_instance
  have hBns : B.IsNonsingular := by
    refine Subscheme.isNonsingular_of_stalk_quot B fun y hy => ?_
    rw [hBpts] at hy
    obtain rfl : y = x := hy
    exact hsimple.2
  exact Or.inr ⟨hBns, Subscheme.isIrreducible_of_pts _ (by rw [hBpts]; exact isIrreducible_singleton)⟩

/-- "In this case, the monoidal transformation of `X_s` with center `x` is permissible for the
resolution datum `ℜ(s)`" (p. 319), for a closed point `x` of `S_*(ℜ)` of a type II datum: `{x}` is
non-singular and irreducible, contained in `S_*(ℜ)`, and `⋃ E_i` has only normal crossings with it
(its ideal is the maximal ideal, generated by the whole regular system of parameters).  The paper
gives no argument. -/
theorem _root_.Hironaka.DatumII.Raw.isPermissible_ofClosed_singleton {Y : Scheme.{u}}
    [IsAlgebraicScheme Y] (hY : Y.IsNonsingular) {ℜ : DatumII.Raw Y} (hℜ : ℜ.IsDatum) {x : Y}
    (hcl : IsClosed ({x} : Set Y)) (hx : x ∈ ℜ.sStar) :
    ℜ.IsPermissible (Subscheme.ofClosed ⟨{x}, hcl⟩) := by
  classical
  set B : Subscheme Y := Subscheme.ofClosed ⟨{x}, hcl⟩ with hBdef
  have hBpts : B.pts = {x} := Subscheme.pts_ofClosed _
  have hmax : B.stalkIdeal x = maximalIdeal (Y.presheaf.stalk x) :=
    AB.stalkIdeal_ofClosed_singleton_eq_maximalIdeal x hcl
  refine ⟨Subscheme.isCenter_ofClosed_singleton hY hcl, fun y hy => ?_, fun y hy => ?_⟩
  · rw [hBpts] at hy
    obtain rfl : y = x := hy
    exact hx
  · rw [hBpts] at hy
    obtain rfl : y = x := hy
    obtain ⟨z, hz, hcomp, -⟩ := hℜ.2.2.1 y
    exact ⟨z, hz, hcomp, z, subset_rfl, by rw [hmax, hz.1]⟩

/-- The reduced closed point `{x}` of `S_ν(ℜ(s))` is a permissible center for `(ℜ(s), F(s))`. -/
theorem Standing.isPermissibleCenter_ofClosed_singleton [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) (s : ℕ)
    {x : T.X s} (hx : x ∈ sNu (datum T ℜ s) (restriction T r s) ν)
    (hcl : IsClosed ({x} : Set (T.X s))) :
    (restriction T r s).IsPermissibleCenter (datum T ℜ s) (Subscheme.ofClosed ⟨{x}, hcl⟩) := by
  obtain ⟨hY, hd⟩ := (T.pre s).isAmbient_transformII hS.ambient ℜ hS.isDatum
    (hS.permissible s).isPermissibleII
  have := hY.1
  have hν := hS.nu_datum_eq s ⟨x, hx⟩
  have hpts : (Subscheme.ofClosed ⟨{x}, hcl⟩).pts = {x} := Subscheme.pts_ofClosed _
  have hxS : x ∈ (datum T ℜ s).sStar := by
    cases hR : restriction T r s with
    | unrestricted =>
      rw [hR] at hx
      rw [DatumII.Raw.sStar, hν]; exact hx
    | closed F =>
      rw [hR] at hx
      rw [DatumII.Raw.sStar, hν]; exact hx.1
  have hperm := DatumII.Raw.isPermissible_ofClosed_singleton hY.2.1 hd hcl hxS
  cases hR : restriction T r s with
  | unrestricted => exact hperm
  | closed F =>
    rw [hR] at hx
    refine ⟨hperm, fun y hy => ?_⟩
    rw [hpts] at hy
    obtain rfl : y = x := hy
    exact hx.2

/-- The members of `S_ν(ℜ(s))` lie on the permissible centers: a permissible center `B'` of
`(ℜ(s), F(s))` with a point in `S_ν(ℜ(s))` lies in `S_ν(ℜ(s))` (the same argument as
`Standing.pts_B_subset_sNu`, which is the case `B' = B_s`). -/
theorem Standing.pts_subset_sNu_of_isPermissibleCenter [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) (t : ℕ)
    (hne : (sNu (datum T ℜ t) (restriction T r t) ν).Nonempty) {B' : Subscheme (T.X t)}
    (h : (restriction T r t).IsPermissibleCenter (datum T ℜ t) B') :
    B'.pts ⊆ sNu (datum T ℜ t) (restriction T r t) ν := by
  have hν := hS.nu_datum_eq t hne
  generalize restriction T r t = R at h hne ⊢
  intro x hx
  cases R with
  | unrestricted =>
    have := h.2.1 hx
    rw [DatumII.Raw.sStar, hν] at this
    exact this
  | closed F =>
    have := h.1.2.1 hx
    rw [DatumII.Raw.sStar, hν] at this
    exact ⟨this, h.2 hx⟩

theorem Restriction.IsPermissibleCenter.isCenter {Y : Scheme.{u}} {r' : Restriction Y}
    {ℜ' : DatumII.Raw Y} {B' : Subscheme Y} (h : r'.IsPermissibleCenter ℜ' B') : B'.IsCenter := by
  cases r' with
  | unrestricted => exact h.1
  | closed F => exact h.1.1

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- "Since `B_t` is contained in `S_ν(h_t^*(ℜ))`, `Ĵ'_t` is contained in the `ν`th power of the
ideal `Q̂'_t`" (p. 318) for an arbitrary non-singular irreducible `B' ⊆ S_ν(ℜ(t))` in place of
`B_t` (only these properties of `B_t` are used): the case `B' = B_t` is
`stalkIdeal_totalTransform_J_le_pow`. -/
theorem stalkIdeal_totalTransform_J_le_pow_of_subset (t : ℕ) {B' : Subscheme (T.X t)}
    (hB'ns : B'.IsNonsingular) (hB'irr : B'.IsIrreducible)
    (hB'S : B'.pts ⊆ sNu (datum T ℜ t) (restriction T r t) ν) (y : 𝒮.tHat.X t)
    (hy : y ∈ (Subscheme.totalTransform (𝒮.c t) B').pts) :
    (Subscheme.totalTransform (𝒮.c t) (datum T ℜ t).J).stalkIdeal y ≤
      (Subscheme.totalTransform (𝒮.c t) B').stalkIdeal y ^ ν := by
  have hy' : (𝒮.c t).base y ∈ B'.pts := by
    have := hy
    rw [Subscheme.pts_totalTransform_eq_preimage] at this
    exact this
  obtain ⟨ξ, hξ⟩ := Subscheme.exists_isGenericPoint hB'irr
  have hξS : ξ ∈ sNu (datum T ℜ t) (restriction T r t) ν := hB'S hξ.mem
  have hνξ : (ν : ℕ∞) ≤ Ideal.nu ((datum T ℜ t).J.stalkIdeal ξ) :=
    ((mem_Snu_iff _ _ _ _).mp hξS).2
  have hJle := (Subscheme.le_nu_generic_iff (hS.isNonsingular_X t) hB'ns hξ hy'
    (datum T ℜ t).J ν).mp hνξ
  rw [stalkIdeal_totalTransform, stalkIdeal_totalTransform]
  have h2 := Ideal.map_mono (f := ((𝒮.c t).stalkMap y).hom) hJle
  rw [Ideal.map_pow] at h2
  exact h2

/-- The center clause (p. 318) for an arbitrary non-singular irreducible `B' ⊆ S_ν(ℜ(t))` (contained
in `F(t)` in the closed case) in place of `B_t`: "`z_t ∈ Q_t` (clear in the closed case, Lemma 22
otherwise)" and "`g_{ji}(t) ∈ (Q̂'_t ∩ T'_t)^i`", where `Q̂'_t` is the ideal of `c_t⁻¹(B')`. -/
theorem centerClause_of_subset [Hironaka.HironakaCitedResults.{u}] (t : ℕ) (xb : (𝒮.xBar t).toScheme)
    (F : RegularFrame ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))) (hr : F.r = 1)
    (m : ℕ) (g : Fin m → (𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))
    (co : Fin m → Fin ν → F.S) (hdata : 𝒮.StalkInvData t xb F hr m g co)
    {B' : Subscheme (T.X t)} (hB'ns : B'.IsNonsingular) (hB'irr : B'.IsIrreducible)
    (hB'S : B'.pts ⊆ sNu (datum T ℜ t) (restriction T r t) ν)
    (hB'F : ∀ F', restriction T r t = .closed F' → B'.pts ⊆ F'.pts)
    (hyh : (𝒮.tHat.pre t).composite.base ((𝒮.xBar t).ι.base xb) = hS.xh)
    (hmem : (𝒮.xBar t).ι.base xb ∈ (Subscheme.totalTransform (𝒮.c t) B').pts) :
    F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ∈
        (Subscheme.totalTransform (𝒮.c t) B').stalkIdeal ((𝒮.xBar t).ι.base xb) ∧
      ∀ (j : Fin m) (i : Fin ν), co j i ∈ ((Subscheme.totalTransform (𝒮.c t) B').stalkIdeal
        ((𝒮.xBar t).ι.base xb)).comap (algebraMap F.S _) ^ ((i : ℕ) + 1) := by
  classical
  obtain ⟨ha, hb, hsh, hun, hd⟩ := hdata
  have hXa := hS.ambient.1
  have hy : (𝒮.c t).base ((𝒮.xBar t).ι.base xb) ∈ B'.pts := by
    have := hmem
    rw [Subscheme.pts_totalTransform_eq_preimage] at this
    exact this
  -- `Ŝ'_t / Q̂'` is regular: `S'_t → Ŝ'_t` transforms a regular system of parameters into one
  -- (Lemma (CD.3), `Lemma 4` of Ch. III), the ideal `Q'` is prime with regular quotient
  obtain ⟨-, hα, -⟩ := 𝒮.toCompletion.isRegularLocalRing_and_mapsRSOP_stalkMap
    (hS.ambient.2.1 x₀) hS.isNonsingular_X hS.isNonsingular_B t _ hyh
  have : IsRegularLocalRing ((T.X t).presheaf.stalk ((𝒮.c t).base ((𝒮.xBar t).ι.base xb))) :=
    hS.isNonsingular_X t _
  have hQ' := Subscheme.isPrime_stalkIdeal_of_isNonsingular hB'ns hy
  have hQ'reg := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hB'ns hy
  obtain ⟨hQp0, hQreg0⟩ := hα.isPrime_map_and_isRegularLocalRing_quotient hQ' hQ'reg
  have hQeq : (Subscheme.totalTransform (𝒮.c t) B').stalkIdeal ((𝒮.xBar t).ι.base xb) =
      (B'.stalkIdeal ((𝒮.c t).base ((𝒮.xBar t).ι.base xb))).map ((𝒮.c t).stalkMap _).hom :=
    stalkIdeal_totalTransform _ _ _
  have hQp : ((Subscheme.totalTransform (𝒮.c t) B').stalkIdeal
      ((𝒮.xBar t).ι.base xb)).IsPrime := by rw [hQeq]; exact hQp0
  have hQreg : IsRegularLocalRing ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb) ⧸
      (Subscheme.totalTransform (𝒮.c t) B').stalkIdeal ((𝒮.xBar t).ι.base xb)) := by
    rw [hQeq]; exact hQreg0
  have hx : (𝒮.c t).base ((𝒮.xBar t).ι.base xb) ∈ sNu (datum T ℜ t) (restriction T r t) ν :=
    hB'S hy
  have hgQ : ∀ j, g j ∈ (Subscheme.totalTransform (𝒮.c t) B').stalkIdeal
      ((𝒮.xBar t).ι.base xb) ^ ν := by
    intro j
    have hj : g j ∈ Ideal.span (Set.range g) := Ideal.subset_span ⟨j, rfl⟩
    rw [hb] at hj
    exact 𝒮.stalkIdeal_totalTransform_J_le_pow_of_subset t hB'ns hB'irr hB'S _ hmem hj
  have hzQ : F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ∈
      (Subscheme.totalTransform (𝒮.c t) B').stalkIdeal ((𝒮.xBar t).ι.base xb) := by
    by_cases hu : r = .unrestricted
    · obtain ⟨hm, hν, h0⟩ := hun hu
      have := charZero_residueField_frame_of_hom (𝒮.c t ≫ (T.pre t).composite)
        ((𝒮.xBar t).ι.base xb) F
      refine frame_z_mem_of_mem_pow F hr ν hν (co ⟨0, hm⟩) h0 _ ?_
      rw [← hsh]; exact hgQ _
    · obtain ⟨F0, hF0⟩ := exists_closed_of_ne_unrestricted r hu
      have hrF : restriction T r t = .closed ((T.pre t).strictTransform F0) := by
        subst hF0; rfl
      -- `X̄_t = c_t⁻¹(F(t))` and `B' ⊆ F(t)`
      have hXF := 𝒮.xBar_eq_totalTransform_of_restriction_eq_closed t hrF
      have hFns : ((T.pre t).strictTransform F0).IsNonsingular := by
        obtain ⟨hY, hd⟩ := (T.pre t).isAmbient_transformII hS.ambient ℜ hS.isDatum
          (hS.permissible t).isPermissibleII
        have hfor := hS.isFor
        subst hF0
        have hcl := MonoidalSuccession.isClosedRestriction_transformII (T.pre t) hS.ambient ℜ
          hS.isDatum F0 hfor (hS.permissible t)
        rcases hcl.1 with h | h
        · rw [h]; exact Subscheme.isNonsingular_empty
        · exact h.1
      have hcont := isContainedIn_of_pts_subset_of_isReduced
        (DatumTransform.isReduced_of_isNonsingular hB'ns)
        (DatumTransform.isReduced_of_isNonsingular hFns) (hB'F _ hrF)
      have hle : ((T.pre t).strictTransform F0).stalkIdeal ((𝒮.c t).base ((𝒮.xBar t).ι.base xb)) ≤
          B'.stalkIdeal ((𝒮.c t).base ((𝒮.xBar t).ι.base xb)) :=
        (Subscheme.le_iff_stalkIdeal_le.mp (fun U => hcont U)) _
      have hzX : F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ∈
          (𝒮.xBar t).stalkIdeal ((𝒮.xBar t).ι.base xb) := by
        rw [ha]; exact Ideal.subset_span rfl
      have hX2 : ∀ y' : 𝒮.tHat.X t, (𝒮.xBar t).stalkIdeal y' =
          (Subscheme.totalTransform (𝒮.c t) ((T.pre t).strictTransform F0)).stalkIdeal y' :=
        fun y' => by rw [hXF]
      rw [hX2, stalkIdeal_totalTransform] at hzX
      rw [stalkIdeal_totalTransform]
      exact Ideal.map_mono hle hzX
  refine ⟨hzQ, ?_⟩
  intro j i
  have hzF : ∀ j, F.z j = F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ := fun j => by
    congr 1
    apply Fin.ext
    have := j.2
    show (j : ℕ) = 0
    omega
  exact frame_coeff_mem_pow F _ hzF hr _ hQreg hzQ ν (co j) (by rw [← hsh]; exact hgQ j) i

/-- **Lemma (CD.4) at the stage `s` for an arbitrary permissible center `B'`** (p. 318): for a point
`x̂` of `X̂_s` over `x ∈ B' ∩ S_ν(ℜ(s))` (`ĥ_s(x̂) = x̂_0`), `x̂` lies on `X̄_s`, `z_s ∈ Q̂'` and
`J̄(s)_{x̂} ⊆ Q̄'^{b̄}`, `Q̄'` the ideal of `B̄' = c_s⁻¹(B') ∩ X̄_s`.  The invariants (a)$_s$–(d)$_s$ are
those of the given succession up to `s` (the center `B_s` does not enter them), and the center
clause is `centerClause_of_subset`; the case `B' = B_s` is the assertion `[vii] (3)` at `s`. -/
theorem exists_jBar_le_bBar_pow_of_isPermissibleCenter [Hironaka.HironakaCitedResults.{u}] (s : ℕ) {B' : Subscheme (T.X s)}
    (hperm : (restriction T r s).IsPermissibleCenter (datum T ℜ s) B') (xh : 𝒮.tHat.X s)
    (hxh : (𝒮.tHat.pre s).composite.base xh = hS.xh)
    (hSnu : (𝒮.c s).base xh ∈ sNu (datum T ℜ s) (restriction T r s) ν)
    (hxB : (𝒮.c s).base xh ∈ B'.pts) :
    ∃ xb : (𝒮.xBar s).toScheme, (𝒮.xBar s).ι.base xb = xh ∧
      (𝒮.jBar s).stalkIdeal xb ≤ ((Subscheme.totalTransform (𝒮.xBar s).ι
        (Subscheme.totalTransform (𝒮.c s) B')).stalkIdeal xb) ^ 𝒮.bBar := by
  classical
  obtain ⟨xb, hxb, hinv⟩ := 𝒮.exists_stalkInv s xh hSnu
  subst hxb
  obtain ⟨F, hr, m, g, co, hdata, -⟩ := hinv
  have hne : (sNu (datum T ℜ s) (restriction T r s) ν).Nonempty := ⟨_, hSnu⟩
  have hB'c := hperm.isCenter
  have hB'ns : B'.IsNonsingular ∧ B'.IsIrreducible := by
    rcases hB'c with h0 | h0
    · rw [h0, DatumTransform.pts_empty] at hxB; exact absurd hxB (Set.notMem_empty _)
    · exact h0
  have hB'S := hS.pts_subset_sNu_of_isPermissibleCenter s hne hperm
  have hB'F : ∀ F', restriction T r s = .closed F' → B'.pts ⊆ F'.pts := by
    intro F' hF'
    have h := hperm
    rw [hF'] at h
    exact h.2
  have hmem : (𝒮.xBar s).ι.base xb ∈ (Subscheme.totalTransform (𝒮.c s) B').pts := by
    rw [Subscheme.pts_totalTransform_eq_preimage]; exact hxB
  obtain ⟨hzQ, hcoQ⟩ := 𝒮.centerClause_of_subset s xb F hr m g co hdata hB'ns.1 hB'ns.2 hB'S hB'F hxh hmem
  refine ⟨xb, rfl, ?_⟩
  obtain ⟨ha, hb, hsh, hun, hd⟩ := hdata
  have hbB : (Subscheme.totalTransform (𝒮.xBar s).ι
      (Subscheme.totalTransform (𝒮.c s) B')).stalkIdeal xb =
      ((Subscheme.totalTransform (𝒮.c s) B').stalkIdeal ((𝒮.xBar s).ι.base xb)).map
        ((𝒮.xBar s).ι.stalkMap xb).hom := stalkIdeal_totalTransform _ _ _
  rw [hd, hbB, ← Ideal.map_pow, Ideal.span_le]
  rintro _ ⟨⟨j, i⟩, rfl⟩
  refine Ideal.mem_map_of_mem _ ?_
  have h1 : algebraMap F.S ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb)) (co j i) ∈
      ((Subscheme.totalTransform (𝒮.c s) B').stalkIdeal ((𝒮.xBar s).ι.base xb)) ^
        ((i : ℕ) + 1) := by
    have := Ideal.mem_map_of_mem
      (algebraMap F.S ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb))) (hcoQ j i)
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono Ideal.map_comap_le _ this
  have hdvd : ((i : ℕ) + 1) ∣ 𝒮.bBar := Nat.dvd_factorial (Nat.succ_pos _) i.2
  have := Ideal.pow_mem_pow h1 (𝒮.bBar / ((i : ℕ) + 1))
  rwa [← pow_mul, mul_comm, Nat.div_mul_cancel hdvd] at this

/-- **Corollary of Lemma (CD.4) for a closed point `x`** (p. 319): "In this case, the monoidal
transformation of `X_s` with center `x` is permissible for the resolution datum `ℜ(s)`.  Applying
Lemma (CD.4) to `B_s = x`, we get the assertion of the corollary": `x̂` lies on `X̄_s` and
`J̄(s)_{x̂} ⊆ M̄^{b̄}`. -/
theorem exists_stalkIdeal_jBar_le_pow_and_bBar_le_nu_of_isClosed [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (x : T.X s)
    (hxS : x ∈ sNu (datum T ℜ s) (restriction T r s) ν) (hcl : IsClosed ({x} : Set (T.X s)))
    (xh : 𝒮.tHat.X s) (hxh : (𝒮.tHat.pre s).composite.base xh = hS.xh)
    (hcx : (𝒮.c s).base xh = x) :
    ∃ xb : (𝒮.xBar s).toScheme, (𝒮.xBar s).ι.base xb = xh ∧
      (𝒮.jBar s).stalkIdeal xb ≤ (maximalIdeal ((𝒮.xBar s).toScheme.presheaf.stalk xb)) ^ 𝒮.bBar ∧
      (𝒮.bBar : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal xb) := by
  classical
  have hperm := hS.isPermissibleCenter_ofClosed_singleton s hxS hcl
  have hxB : (𝒮.c s).base xh ∈ (Subscheme.ofClosed ⟨{x}, hcl⟩).pts := by
    rw [Subscheme.pts_ofClosed, hcx]; rfl
  obtain ⟨xb, hxb, hle⟩ := 𝒮.exists_jBar_le_bBar_pow_of_isPermissibleCenter s hperm xh hxh
    (hcx ▸ hxS) hxB
  refine ⟨xb, hxb, ?_⟩
  have hbpts : xb ∈ (Subscheme.totalTransform (𝒮.xBar s).ι
      (Subscheme.totalTransform (𝒮.c s) (Subscheme.ofClosed ⟨{x}, hcl⟩))).pts := by
    rw [Subscheme.pts_totalTransform_eq_preimage, Set.mem_preimage,
      Subscheme.pts_totalTransform_eq_preimage, Set.mem_preimage]
    rw [hxb]; exact hxB
  have hle' : (𝒮.jBar s).stalkIdeal xb ≤ (maximalIdeal ((𝒮.xBar s).toScheme.presheaf.stalk xb)) ^
      𝒮.bBar :=
    hle.trans (Ideal.pow_right_mono (stalkIdeal_le_maximalIdeal_of_mem_pts _ hbpts) _)
  exact ⟨hle', Ideal.le_ord hle'⟩

end Frame

/-- A closed subscheme `B` of `Z` lying over a point `y` of `Y` (for `f : Z → Y` locally of finite type)
is a Jacobson space: it is a closed subspace of the fibre `f⁻¹(y)`, an algebraic scheme over the
residue field of `y`.  (Used for "`B̂` is an algebraic scheme over a field", p. 319.) -/
theorem jacobsonSpace_toScheme_of_pts_subset_preimage {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [LocallyOfFiniteType f] (y : Y) (B : Subscheme Z) (h : B.pts ⊆ f ⁻¹' {y}) :
    JacobsonSpace B.toScheme := by
  have hmem : ∀ b : B.toScheme, B.ι b ∈ f ⁻¹' {y} := fun b => h (Subscheme.mem_pts_ι B b)
  have hemb : Topology.IsEmbedding (Set.codRestrict (fun b : B.toScheme => B.ι b) (f ⁻¹' {y}) hmem) :=
    B.ι.isClosedEmbedding.isEmbedding.codRestrict _ hmem
  have hclr : IsClosed (Set.range (Set.codRestrict (fun b : B.toScheme => B.ι b) (f ⁻¹' {y}) hmem)) := by
    have : Set.range (Set.codRestrict (fun b : B.toScheme => B.ι b) (f ⁻¹' {y}) hmem) =
        Subtype.val ⁻¹' B.pts := by
      ext ⟨z, hz⟩
      simp only [Set.mem_range, Set.mem_preimage]
      constructor
      · rintro ⟨b, hb⟩
        have : B.ι b = z := congrArg Subtype.val hb
        rw [← this]; exact Subscheme.mem_pts_ι B b
      · intro hzB
        obtain ⟨b, hb⟩ := Subscheme.exists_ι_eq_of_mem_pts B hzB
        exact ⟨b, Subtype.ext hb⟩
    rw [this]
    exact B.support.isClosed.preimage continuous_subtype_val
  have hce : Topology.IsClosedEmbedding (Set.codRestrict (fun b : B.toScheme => B.ι b) (f ⁻¹' {y}) hmem) :=
    ⟨hemb, hclr⟩
  have hce' : Topology.IsClosedEmbedding ((f.fiberHomeo y).symm ∘
      (Set.codRestrict (fun b : B.toScheme => B.ι b) (f ⁻¹' {y}) hmem)) :=
    (f.fiberHomeo y).symm.isClosedEmbedding.comp hce
  exact JacobsonSpace.of_isClosedEmbedding hce'

/-- `S_ν(ℜ(s))` (with the restriction `F(s)`, if any) is closed. -/
theorem Standing.isClosed_sNu_restriction [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) (s : ℕ) :
    IsClosed (sNu (datum T ℜ s) (restriction T r s) ν) := by
  obtain ⟨hY, hd⟩ := (T.pre s).isAmbient_transformII hS.ambient ℜ hS.isDatum
    (hS.permissible s).isPermissibleII
  have := hY.1
  have h1 : IsClosed ((datum T ℜ s).sNu (ν : ℕ∞)) := LocSucc.isClosed_sNu hY.2.1 _ _
  cases hR : restriction T r s with
  | unrestricted => exact h1
  | closed F => exact h1.inter F.support.isClosed

/-- The induction of Lemma (CD.5) (p. 319): (a*)$_t$–(c*)$_t$ hold at every point of `X̄_t`,
`t ≤ s`, as soon as `J̄(s)` is defined.  Start: `stalkInvData_zero`.  Step `t → t+1`, `t < s`: if `x̂'_t ∉ B̂_t` the stalks are
isomorphic (`stalkInvData_succ_of_notMem`); otherwise the frame transform
(`stalkInvData_succ_of_defined`), whose hypotheses are exactly (2), (3) of `[vii]` at `t`
(`IsDefined s`) and `x̂'_{t+1} ∈ X̄_{t+1}`.

Deviation from the paper (gap filled): the paper says "so `ν(J̄(s)_{x̂'}) ≥ b̄` implies
`J̄'_t ⊆ (M̄'_t)^{b̄}` for all `t`" and "`ν(Ĵ'_{t+1}) ≥ ν`" as the reason for the unit ideal; neither
is needed here (the frame transform is built from the non-unit property of `z_t/w_t` and the
definedness of `J̄(s)`), and `ν(ℜ(t)) = ν` is only needed, and derived locally, at the points of the
center (`Ĵ'_t ⊆ (M̂'_t)^ν` gives `ν ≤ ν(J(t)_{x'_t})`, `x'_t ∈ B_t ⊆ S*(ℜ(t))`). -/
theorem Frame.exists_stalkInvData_of_isDefined [Hironaka.HironakaCitedResults.{u}] {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS) {s : ℕ}
    (hdef : 𝒮.IsDefined s) :
    ∀ t, t ≤ s → ∀ xb : (𝒮.xBar t).toScheme,
      ∃ (F : RegularFrame ((𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))) (hr : F.r = 1)
        (m : ℕ) (g : Fin m → (𝒮.tHat.X t).presheaf.stalk ((𝒮.xBar t).ι.base xb))
        (co : Fin m → Fin ν → F.S), 𝒮.StalkInvData t xb F hr m g co := by
  classical
  intro t
  induction t with
  | zero => exact fun _ xb => 𝒮.stalkInvData_zero xb
  | succ t ih =>
    intro hts xb'
    obtain ⟨-, hC, hJ⟩ := hdef t (by omega)
    have hxb : (𝒮.xBar t).ι.base ((𝒮.fBar t).base xb') =
        (𝒮.tHat.f t).base ((𝒮.xBar (t + 1)).ι.base xb') :=
      congrArg (fun φ => φ.base xb') (𝒮.fBar_comm t)
    have hinv := ih (by omega) ((𝒮.fBar t).base xb')
    by_cases hB : (𝒮.tHat.B t).stalkIdeal ((𝒮.xBar t).ι.base ((𝒮.fBar t).base xb')) = ⊤
    · obtain ⟨xb'', hxb'', rest⟩ := 𝒮.stalkInvData_succ_of_notMem t
        ((𝒮.xBar (t + 1)).ι.base xb') ((𝒮.fBar t).base xb') hxb hB hinv
      obtain rfl : xb'' = xb' := subscheme_ι_injective (𝒮.xBar (t + 1)) hxb''
      exact rest
    · obtain ⟨xb'', hxb'', rest⟩ := 𝒮.stalkInvData_succ_of_defined t
        ((𝒮.xBar (t + 1)).ι.base xb') hC hJ (Subscheme.mem_pts_ι _ xb') ((𝒮.fBar t).base xb')
        hxb hB hinv
      obtain rfl : xb'' = xb' := subscheme_ι_injective (𝒮.xBar (t + 1)) hxb''
      exact rest

/-- **Lemma (CD.5)** (p. 319).  `x̂'` is a point of the scheme `X̄_s` and
`x' = c_s(x̂') = c̄_s(x̂')`.

Deviation from the paper (statement modified): the hypothesis that `J̄(s)` is defined
(conditions (1)–(3) of `[vii]` at all `t < s`), which the paper's statement presupposes and its
proof uses ("in order for `J̄(s)` to be defined, …"), is an explicit hypothesis `hdef`.

Deviation from the paper (gap filled), three steps (one line each): (i) the Nakayama step, p. 318/320
"`w_t^{-1}(Q̂'_t ∩ T'_t)Ŝ'_{t+1}` is the unit ideal" (`exists_mem_comap_assoc_w_of_mem_maximalIdeal`: from
`Q̂'_t Ŝ'_{t+1} = (z_t) + (Q̂'_t ∩ T'_t)Ŝ'_{t+1}` and `z_t/w_t` a non-unit, which holds as
`x̂'_{t+1} ∈ X̄_{t+1}`; no `ν`-bound on `Ĵ'_{t+1}`); (ii) the coefficient step, p. 318 "`g_{ji}(t) ∈
(Q̂'_t ∩ T'_t)^i`" (`mem_pow_sup_span_of_pow_mem`, the gr-domain argument, applied to the generators of
`J̄'_t ⊆ (Q̄'_t)^{b̄}`); (iii) the last step, p. 320 "can be easily deduced from the fact that X̂_s = X_s ×_X Spec(Ŝ) and
that S belongs to the class 𝔅", is `Frame.le_pow_maximalIdeal_of_map_le_pow` (Deviation from the paper
(gap filled): proved from the pull-back square through `X_s ×_X Spec S` and the ring-level statement for
the class 𝔅; the membership of `O_{X,x_0}` in 𝔅, tacit in the paper, is `isHironakaBase_stalk`); (iv)
`ν(ℜ(t)) = ν` is derived locally in the induction (not a hypothesis). -/
@[blueprint "lem:IV.CD-5"
  (statement := /-- \textbf{Lemma (CD.5).} Notation as in \cref{def:IV.4-frame},
    \cref{def:IV.4-construction}. Let $\hat x'$ be any point of $\bar X_s$ such that
    $\nu(\bar J(s)_{\hat x'})\ge\bar b$, and $x'=c_s(\hat x')$. Then we have
    $\nu(J(s)_{x'})\ge\nu$. (p.~319.)
    \textbf{Deviation from the paper (statement modified).} $\bar J(s)$ is assumed to be
    defined, i.e.\ the conditions (1), (2), (3) of [vii] hold at every $t<s$; the paper's
    statement presupposes this and its proof uses it. -/)
  (proof := /-- (pp.~319--320.) Let $\hat x'_t$ (resp.\ $x'_t$) be the image of $\hat x'$ (resp.\
    $x'$) in $\hat X_t$ (resp.\ $X_t$), and set $S'_t$, $\hat S'_t$, $Q'_t$, $\hat Q'_t$, $J'_t$,
    $\hat J'_t$ as in the proof of Lemma (CD.4); $\hat x'_t\in\bar X_t$, and $\bar T'_t$ is the
    local ring of $\bar X_t$ at $\hat x'_t$. One proves by induction on $t$ that there exist a
    regular frame $(T'_t;z_t)$ of $\hat S'_t$, elements $g_j(t)\in\hat S'_t$ (the paper prints
    $g_t(t)$ [sic]) and $v_t\in T'_t$ with (a*)$_t$ $z_t$ generates the kernel of
    $\hat S'_t\to\bar T'_t$; (b*)$_t$ $(g_1(t),\dots,g_m(t))$ is a base of $\hat J'_t$ and
    $g_j(t)=z_t^\nu+g_{j1}(t)z_t^{\nu-1}+\dots+g_{j\nu}(t)$ with $g_{ji}(t)\in T'_t$; (c*)$_t$ the
    stalk $\bar J'_t$ of $\bar J(t)$ at $\hat x'_t$ is $(g_{ji}(t)^{\bar b/i})\bar T'_t$; (d*)$_t$
    $z_{t+1}=z_t/v_t$ and $g_j(t+1)=g_j(t)/v_t^\nu$. For $\bar J(s)$ to be defined,
    $\hat Q'_t$ must contain the kernel of $\hat S'_t\to\bar T'_t$, $\bar J'_t\subseteq(\bar
    Q'_t)^{\bar b}$ and $\bar T'_{t+1}$ must be a monoidal transform of $\bar T'_t$ with center
    $\bar Q'_t$ for $t\le s-1$ (\cref{def:IV.4-construction}); so $\nu(\bar J(s)_{\hat x'})\ge\bar
    b$ implies $\bar J'_t\subseteq(\bar M'_t)^{\bar b}$ for all $t$. Start with the frame and base
    of the proof of Lemma (CD.4). If $\hat Q'_t$ is not the unit ideal, $\bar J'_t\subseteq(\bar
    Q'_t)^{\bar b}$ gives $g_{ji}(t)\in(\hat Q'_t\cap T'_t)^i$, and $z_t\in\hat Q'_t$ gives
    $\hat J'_t\subseteq(\hat Q'_t)^\nu$; then (a*)$_{t+1}$--(c*)$_{t+1}$ hold for the frame
    transform (\cref{def:III.8-frame-transform}) ``as it'' [sic; as in] (d*)$_t$. By (c*)$_s$,
    $g_{ji}(s)\in(\hat M'_s)^i$, hence by (b*)$_s$ $\hat J'_s\subseteq(\hat M'_s)^\nu$. The
    local homomorphism $S'_s\to\hat S'_s$ transforms a regular system of parameters of $S'_s$ into a
    system of elements extendable to a regular system of parameters of $\hat S'_s$ (``from the
    fact that $\hat X_s=X_s\times_X\operatorname{Spec}(\hat S)$ and that $S$ belongs to the class
    $\mathfrak B$ defined in the introductory paragraphs of Ch.~I'', \cref{def:class-A}); since
    $\hat J'_s=J'_s\hat S'_s$, $J'_s\subseteq (M'_s)^\nu$, i.e.\ $\nu(J(s)_{x'})\ge\nu$.
    \textsc{q.e.d.}

    \textbf{Deviation from the paper (gap filled).} The sentence ``This can be easily deduced from
    the fact that $\hat X_s=X_s\times_X\operatorname{Spec}(\hat S)$ and that $S$ belongs to the class
    $\mathfrak B$'' (p.~320) is deduced in Lean as follows: the pull-back square factors through
    $Y\times_X\operatorname{Spec}S$, whose stalk map is an isomorphism (a flat preimmersion); an
    affine chart gives $\operatorname{Spec}(A\otimes_S\hat S)$; the ring-level statement for the class
    $\mathfrak B$ (\texttt{le\_pow\_maximalIdeal\_of\_map\_le\_pow\_of\_isHironakaBase}) applies.
    The membership of $\mathcal O_{X,x_0}$ in $\mathfrak B$, tacit in the paper, is
    \texttt{isHironakaBase\_stalk}.
    \textbf{Paper misprint.} The paper writes ``elements $g_t(t)\in\hat S'_t$ $(1\le j\le m)$''
    for $g_j(t)$ (p.~319) and ``as it (d*)$_t$'' for ``as in (d*)$_t$'' (p.~320). -/)
  (proofUses := ["lem:IV.CD-4", "def:IV.4-construction", "def:III.8-frame-transform",
    "def:class-A"])
  (latexEnv := "lemma")]
theorem Frame.le_nuAt_cBar_of_bBar_le_nu [Hironaka.HironakaCitedResults.{u}] {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS) (s : ℕ) (hdef : 𝒮.IsDefined s)
    (xb : (𝒮.xBar s).toScheme) (hν : (𝒮.bBar : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal xb)) :
    (ν : ℕ∞) ≤ (datum T ℜ s).nuAt ((𝒮.cBar s).base xb) := by
  classical
  have := hS.ambient.1
  obtain ⟨F, hr, m, g, co, ha, hb, hsh, hun, hd⟩ :=
    𝒮.exists_stalkInvData_of_isDefined hdef s le_rfl xb
  have hregR := 𝒮.instIsRegularLocalRingStalkTHat s ((𝒮.xBar s).ι.base xb)
  have hresreg : IsRegularLocalRing (((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb)) ⧸ maximalIdeal ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb))) := by
    let _ : Field (((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb)) ⧸ maximalIdeal ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb))) := Ideal.Quotient.field _
    infer_instance
  have hz : F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ∈ maximalIdeal ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb)) := by
    have : F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ ∈ (𝒮.xBar s).stalkIdeal ((𝒮.xBar s).ι.base xb) := by
      rw [ha]; exact Ideal.subset_span rfl
    exact Subscheme.stalkIdeal_le_maximalIdeal _ (Subscheme.mem_pts_ι _ xb) this
  have hzF : ∀ j, F.z j = F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩ := fun j => by
    congr 1
    apply Fin.ext
    have := j.2
    show (j : ℕ) = 0
    omega
  -- `ν(J̄'_s) ≥ b̄` gives `g_{ji}(s) ∈ (M̂'_s ∩ T'_s)^i`
  have hψsurj : Function.Surjective ((𝒮.xBar s).ι.stalkMap xb).hom :=
    (𝒮.xBar s).ι.stalkMap_surjective xb
  have hker : RingHom.ker ((𝒮.xBar s).ι.stalkMap xb).hom =
      Ideal.span {F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩} := by
    rw [← ha, stalkIdeal_eq_ker_stalkMap]
  have hmaxT : maximalIdeal ((𝒮.xBar s).toScheme.presheaf.stalk xb) =
      (maximalIdeal ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb))).map
        ((𝒮.xBar s).ι.stalkMap xb).hom := by
    rw [← Ideal.map_comap_of_surjective _ hψsurj (maximalIdeal ((𝒮.xBar s).toScheme.presheaf.stalk xb))]
    congr 1
    ext a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, isUnit_map_iff]
  have hle : (𝒮.jBar s).stalkIdeal xb ≤ (maximalIdeal ((𝒮.xBar s).toScheme.presheaf.stalk xb)) ^ 𝒮.bBar :=
    Ideal.le_pow_of_le_ord hν
  have hcoef : ∀ (j : Fin m) (i : Fin ν),
      co j i ∈ ((maximalIdeal ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb))).comap
        (algebraMap F.S ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb)))) ^ ((i : ℕ) + 1) := by
    intro j i
    have hdvd : ((i : ℕ) + 1) ∣ 𝒮.bBar := Nat.dvd_factorial (Nat.succ_pos _) i.2
    have hk : 0 < 𝒮.bBar / ((i : ℕ) + 1) :=
      Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) hdvd) (Nat.succ_pos _)
    have h1 : ((𝒮.xBar s).ι.stalkMap xb).hom
        (algebraMap F.S ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb)) (co j i) ^
          (𝒮.bBar / ((i : ℕ) + 1))) ∈ (𝒮.jBar s).stalkIdeal xb := by
      rw [hd]; exact Ideal.subset_span ⟨(j, i), rfl⟩
    have h2 := hle h1
    rw [hmaxT, ← Ideal.map_pow] at h2
    have h6 : (𝒮.bBar / ((i : ℕ) + 1)) * ((i : ℕ) + 1) = 𝒮.bBar := Nat.div_mul_cancel hdvd
    have h3 : algebraMap F.S ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb)) (co j i) ^
        (𝒮.bBar / ((i : ℕ) + 1)) ∈
        maximalIdeal ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb)) ^
          ((𝒮.bBar / ((i : ℕ) + 1)) * ((i : ℕ) + 1)) ⊔
          Ideal.span {F.z ⟨0, by rw [hr]; exact Nat.one_pos⟩} := by
      have := (Ideal.mem_comap).mpr h2
      rw [Ideal.comap_map_of_surjective _ hψsurj, ← RingHom.ker_eq_comap_bot, hker] at this
      rw [h6]
      exact this
    have h7 := mem_pow_sup_span_of_pow_mem F _ hzF hr _ hresreg hz
      (algebraMap F.S ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb)) (co j i))
      (𝒮.bBar / ((i : ℕ) + 1)) ((i : ℕ) + 1) hk h3
    exact frame_mem_comap_pow_of_mem_pow_add F _ hzF hr _ hz ((i : ℕ) + 1) (co j i) h7
  -- `z_s ∈ M̂'_s` and `g_{ji}(s) ∈ (M̂'_s)^i` give `g_j(s) ∈ (M̂'_s)^ν`
  have hgM : ∀ j, g j ∈ maximalIdeal ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb)) ^ ν := by
    intro j
    rw [hsh j]
    refine Ideal.add_mem _ (Ideal.pow_mem_pow hz ν) (Ideal.sum_mem _ fun i _ => ?_)
    have h1 := Ideal.mem_map_of_mem (algebraMap F.S ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb))) (hcoef j i)
    rw [Ideal.map_pow] at h1
    have h2 := Ideal.pow_right_mono Ideal.map_comap_le ((i : ℕ) + 1) h1
    have h3 := Ideal.mul_mem_mul h2 (Ideal.pow_mem_pow hz (ν - ((i : ℕ) + 1)))
    rw [← pow_add] at h3
    have e : (i : ℕ) + 1 + (ν - ((i : ℕ) + 1)) = ν := by have := i.2; omega
    rwa [e] at h3
  -- `Ĵ'_s = J'_s Ŝ'_s ⊆ (M̂'_s)^ν`, hence `J'_s ⊆ (M'_s)^ν` (class `𝔅`)
  have hJ : ((datum T ℜ s).J.stalkIdeal ((𝒮.c s).base ((𝒮.xBar s).ι.base xb))).map
      ((𝒮.c s).stalkMap ((𝒮.xBar s).ι.base xb)).hom ≤
      maximalIdeal ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb)) ^ ν := by
    rw [← stalkIdeal_totalTransform, ← hb, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hgM j
  have hfin := 𝒮.le_pow_maximalIdeal_of_map_le_pow s ((𝒮.xBar s).ι.base xb) _ ν hJ
  exact Ideal.le_ord hfin

end CD

end

end Hironaka
