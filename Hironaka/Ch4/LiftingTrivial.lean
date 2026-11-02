/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Hironaka.Ch4.StageState
public import Hironaka.Compat.DatumRefinement
public import Hironaka.Statements

/-!
# Ch. IV §3 (p. 310): trivial steps along an extension, and transport of the auxiliary datum

Formalization infrastructure for p. 310:

> "By applying Theorem I₂^{N,n'} (with n' < n) to the resolution datum (ℜ^{N,n'}(s), U_s) …, we can
> resolve ℜ^{N,n'}(s) by a finite permissible succession … These monoidal transformations are
> successively permissible for ℜ(s) and induce trivial monoidal transformations of X̃ by Remarks 4
> and 5.  Therefore, by replacing the original succession g_s : X_s → X to include the above
> succession, we may assume that … the scheme X̃ and the datum ℜ^{N-1} are kept the same."

* `StageState.exists_iso_xTilde_fold_of_isPermissibleIOpen_extendBy`: along a succession `h`
  permissible for `(ℜ_Y.extendBy B, U_s)` (the datum `ℜ^{N,n'}(s)` with open restriction `U_s`)
  each step is a trivial step of `X̃` (`StageState.exists_iso_xTilde_step_of_forall_notMem`), since
  the centers lie in `B − U_s` and the `c̃`-preimage of `B` lies over `U_s`; the composite of the
  isomorphisms carries `J̄`, the `Ẽ_i` and the trace of `B` along;
  moreover the strict transform of `B` stays in the closure of the image of the transported trace;
* `StageState.sameChar_datumII_emptyIfBot_of_iso`: the emptied auxiliary datum of a state
  isomorphic (by such an isomorphism, with extra empty components) to another has, after pulling
  back, the same characteristic data as that of the other (so it is resolvable in as many steps).

No statement of the paper is formalized here, and nothing is cited.  The notation is that of
`Hironaka/Ch4/StageState.lean`.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits

namespace Hironaka

universe u

noncomputable section

namespace AB

/-- One trivial step carries the closure condition along: if `B ⊆ closure (c̃(B̃))` then the strict
transform of `B` lies in the closure of `c̃'(e⁻¹(B̃))` (formalization infrastructure for p. 310:
the strict transform of `B` is the same as `B` off the exceptional divisor, and the isomorphism
over the complement of the center identifies the closures). -/
theorem StageState.pts_strictTransform_subset_closure_step
    (b : ℕ) {Y : Scheme.{u}} (σ : StageState Y) {C : Subscheme Y}
    (t : MonoidalTransformation Y C) (hU : IsOpen σ.xHatPrimeStar)
    (hU' : IsOpen (σ.step b t).xHatPrimeStar)
    (e : (σ.step b t).xTilde hU' ≅ σ.xTilde hU)
    (he1 : e.hom ≫ σ.cTilde hU = (σ.step b t).cTilde hU' ≫ t.f)
    (hdisj : ∀ xt : σ.xTilde hU, (σ.cTilde hU).base xt ∉ C.pts)
    (B : Subscheme Y) (Bt : Subscheme (σ.xTilde hU))
    (hB : B.pts ⊆ closure ((σ.cTilde hU).base '' Bt.pts)) :
    (Subscheme.strictTransform t B).pts ⊆ closure (((σ.step b t).cTilde hU').base ''
      (Subscheme.totalTransform e.hom Bt).pts) := by
  classical
  set S : Set Y := (σ.cTilde hU).base '' Bt.pts with hS
  set S' : Set t.X' := ((σ.step b t).cTilde hU').base '' (Subscheme.totalTransform e.hom Bt).pts
    with hS'
  let Ω : Y.Opens := ⟨C.pts ᶜ, C.support.isClosed.isOpen_compl⟩
  have hf : IsMonoidalTransformationOf t.f C := ⟨t.invertible, t.universal⟩
  have hiso : IsIso (t.f ∣_ Ω) := hf.isIso_morphismRestrict_of_forall_notMem Ω (fun z hz => hz)
  let V : t.X'.Opens := t.f ⁻¹ᵁ Ω
  let g : (V : Scheme.{u}) ⟶ Y := V.ι ≫ t.f
  have hg : g = (t.f ∣_ Ω) ≫ Ω.ι := (morphismRestrict_ι t.f Ω).symm
  have : IsOpenImmersion g := by rw [hg]; infer_instance
  have hgemb := g.isOpenEmbedding
  intro p hp
  obtain ⟨q, hq, hqE, hqp⟩ := t.exists_generization_notMem_exceptional B hp
  have hqV : q ∈ V := fun h => hqE (by rw [MonoidalTransformation.pts_exceptional]; exact h)
  have hfq : t.f.base q ∈ closure S := hB (t.pts_strictTransform_subset B hq)
  let v : (V : Scheme.{u}) := ⟨q, hqV⟩
  have hgv : g.base v = t.f.base q := rfl
  have hv : v ∈ closure (g.base ⁻¹' S) := by
    rw [← hgemb.isOpenMap.preimage_closure_eq_closure_preimage g.continuous]
    show g.base v ∈ closure S
    rw [hgv]; exact hfq
  have hsub : V.ι.base '' (g.base ⁻¹' S) ⊆ S' := by
    rintro _ ⟨v₀, hv₀, rfl⟩
    obtain ⟨x₀, hx₀, hxx⟩ := hv₀
    refine ⟨e.inv.base x₀, ?_, ?_⟩
    · rw [Subscheme.pts_totalTransform_eq_preimage]
      show e.hom.base (e.inv.base x₀) ∈ Bt.pts
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
      exact hx₀
    · have hx : e.hom.base (e.inv.base x₀) = x₀ := by
        rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
      have h1 : t.f.base (((σ.step b t).cTilde hU').base (e.inv.base x₀)) =
          (σ.cTilde hU).base x₀ := by
        have := congrArg (fun k => k.base (e.inv.base x₀)) he1
        simp only [Scheme.Hom.comp_apply] at this
        rw [← this, hx]
      have h2 : t.f.base (V.ι.base v₀) = (σ.cTilde hU).base x₀ := hxx.symm.symm ▸ rfl
      have hwV : ((σ.step b t).cTilde hU').base (e.inv.base x₀) ∈ V := by
        show t.f.base (((σ.step b t).cTilde hU').base (e.inv.base x₀)) ∈ Ω
        rw [h1]; exact hdisj x₀
      let w : (V : Scheme.{u}) := ⟨_, hwV⟩
      have hvw : v₀ = w := hgemb.injective (by
        show t.f.base (V.ι.base v₀) = t.f.base (((σ.step b t).cTilde hU').base (e.inv.base x₀))
        rw [h1]; exact h2)
      rw [hvw]
      rfl
  have hqS' : q ∈ closure S' := by
    have h3 : V.ι.base v ∈ closure (V.ι.base '' (g.base ⁻¹' S)) :=
      image_closure_subset_closure_image V.ι.continuous ⟨v, hv, rfl⟩
    exact closure_mono hsub h3
  exact closure_minimal (Set.singleton_subset_iff.mpr hqS') isClosed_closure
    (specializes_iff_mem_closure.mp hqp)

/-- Trivial steps along a succession `h` (formalization infrastructure for p. 310: "These monoidal
transformations are successively permissible for ℜ(s) and induce trivial monoidal transformations of
X̃"). -/
theorem StageState.exists_iso_xTilde_fold_of_isPermissibleIOpen_extendBy [Hironaka.HironakaCitedResults.{u}]
    (b : ℕ) {Y Z : Scheme.{u}} (σ : StageState Y) (hU : IsOpen σ.xHatPrimeStar)
    (ℜY : DatumI.Raw Y) (B : Subscheme Y) (Us : Set Y) (h : MonoidalSuccession Y Z)
    (hperm : h.IsPermissibleIOpen (ℜY.extendBy B) Us)
    (hopen : σ.OpenAlong b h)
    (hBU : ∀ x : σ.xTilde hU, (σ.cTilde hU).base x ∈ B.pts → (σ.cTilde hU).base x ∈ Us) :
    ∃ (hUh : IsOpen (StageState.fold b h σ).xHatPrimeStar)
      (ε : (StageState.fold b h σ).xTilde hUh ≅ σ.xTilde hU),
      ε.hom ≫ σ.cTilde hU = (StageState.fold b h σ).cTilde hUh ≫ h.composite ∧
      Subscheme.totalTransform ε.hom (σ.jBarT hU) = (StageState.fold b h σ).jBarT hUh ∧
      (∀ i, Subscheme.totalTransform ε.hom (σ.eTildeAt hU i) =
        (StageState.fold b h σ).eTildeAt hUh i) ∧
      Subscheme.totalTransform ((StageState.fold b h σ).cTilde hUh) (h.strictTransform B) =
        Subscheme.totalTransform ε.hom (Subscheme.totalTransform (σ.cTilde hU) B) ∧
      (∀ Bt : Subscheme (σ.xTilde hU), B.pts ⊆ closure ((σ.cTilde hU).base '' Bt.pts) →
        (h.strictTransform B).pts ⊆ closure (((StageState.fold b h σ).cTilde hUh).base ''
          (Subscheme.totalTransform ε.hom Bt).pts)) := by
  induction h with
  | nil X =>
    refine ⟨hU, Iso.refl _, ?_, ?_, ?_, ?_, ?_⟩
    · exact Category.id_comp _
    · exact Subscheme.totalTransform_id _
    · intro i
      exact Subscheme.totalTransform_id _
    · exact (Subscheme.totalTransform_id _).symm
    · intro Bt hBt
      have h0 : Subscheme.totalTransform (𝟙 (σ.xTilde hU)) Bt = Bt :=
        Subscheme.totalTransform_id Bt
      show B.pts ⊆ closure
        ((σ.cTilde hU).base '' (Subscheme.totalTransform (𝟙 (σ.xTilde hU)) Bt).pts)
      rw [h0]
      exact hBt
  | @cons Y₀ C t Z₀ rest ih =>
    obtain ⟨hC, hrest⟩ := hperm
    obtain ⟨hU0, hopen'⟩ := hopen
    have hU' : IsOpen (σ.step b t).xHatPrimeStar := hopen'.isOpen_head
    have hdisj : ∀ xt : σ.xTilde hU, (σ.cTilde hU).base xt ∉ C.pts := by
      intro xt hxC
      have h1 := hC.2 hxC
      exact h1.2 (hBU xt h1.1)
    obtain ⟨e, he1, he2, he3, he4⟩ :=
      StageState.exists_iso_xTilde_step_of_forall_notMem b t hU hU' hdisj
    have hrest' : rest.IsPermissibleIOpen
        ((ℜY.transform t).extendBy (Subscheme.strictTransform t B))
        (DatumI.Raw.transformOpen t Us) := by
      rw [← DatumI.Raw.transform_extendBy]
      exact hrest
    have hBU' : ∀ x' : (σ.step b t).xTilde hU',
        ((σ.step b t).cTilde hU').base x' ∈ (Subscheme.strictTransform t B).pts →
        ((σ.step b t).cTilde hU').base x' ∈ DatumI.Raw.transformOpen t Us := by
      intro x' hx'
      have h1 : t.f.base (((σ.step b t).cTilde hU').base x') ∈ B.pts :=
        t.pts_strictTransform_subset B hx'
      have h2 : t.f.base (((σ.step b t).cTilde hU').base x') =
          (σ.cTilde hU).base (e.hom.base x') := by
        have := congrArg (fun g => g.base x') he1
        simpa [Scheme.Hom.comp_apply] using this.symm
      rw [h2] at h1
      show t.f.base (((σ.step b t).cTilde hU').base x') ∈ Us
      rw [h2]
      exact hBU _ h1
    obtain ⟨hUh, ε', hε1, hε2, hε3, hε4, hε5⟩ := ih (σ.step b t) hU' (ℜY.transform t)
      (Subscheme.strictTransform t B) (DatumI.Raw.transformOpen t Us) hrest' hopen' hBU'
    -- the new exceptional divisor misses `X̃_{s+1}`
    have hg : ∀ w : (σ.step b t).xTilde hU',
        ((σ.step b t).cTilde hU').base w ∉ t.exceptional.pts := by
      intro w hw
      have h1 : Subscheme.totalTransform ((σ.step b t).cTilde hU') t.exceptional =
          Subscheme.empty := by
        rw [← StageState.getD_boundary_step_length σ b t,
          ← StageState.eTildeAt_eq_totalTransform_cTilde]
        exact he4
      have h2 := Subscheme.pts_totalTransform_eq_preimage ((σ.step b t).cTilde hU') t.exceptional
      rw [h1, Subscheme.pts_empty] at h2
      have : w ∈ (∅ : Set ((σ.step b t).xTilde hU')) := by
        rw [h2]; exact hw
      exact this
    have k1 : (ε' ≪≫ e).hom ≫ σ.cTilde hU =
        (StageState.fold b rest (σ.step b t)).cTilde hUh ≫ (rest.composite ≫ t.f) := by
      rw [Iso.trans_hom, Category.assoc, he1, ← Category.assoc, hε1, Category.assoc]
    have k2 : Subscheme.totalTransform (ε' ≪≫ e).hom (σ.jBarT hU) =
        (StageState.fold b rest (σ.step b t)).jBarT hUh := by
      rw [Iso.trans_hom, Subscheme.totalTransform_comp, he2, hε2]
    have k3 : ∀ i, Subscheme.totalTransform (ε' ≪≫ e).hom (σ.eTildeAt hU i) =
        (StageState.fold b rest (σ.step b t)).eTildeAt hUh i := by
      intro i
      rw [Iso.trans_hom, Subscheme.totalTransform_comp, he3, hε3]
    have k4 : Subscheme.totalTransform ((StageState.fold b rest (σ.step b t)).cTilde hUh)
        (rest.strictTransform (Subscheme.strictTransform t B)) =
        Subscheme.totalTransform (ε' ≪≫ e).hom (Subscheme.totalTransform (σ.cTilde hU) B) := by
      have hct : Subscheme.totalTransform ((σ.step b t).cTilde hU')
          (Subscheme.strictTransform t B) =
          Subscheme.totalTransform e.hom (Subscheme.totalTransform (σ.cTilde hU) B) := by
        rw [Subscheme.totalTransform_strictTransform_eq_of_forall_notMem t B _ hg,
          ← Subscheme.totalTransform_comp, ← he1, Subscheme.totalTransform_comp]
      rw [hε4, Iso.trans_hom, Subscheme.totalTransform_comp, hct]
    have k5 : ∀ Bt : Subscheme (σ.xTilde hU), B.pts ⊆ closure ((σ.cTilde hU).base '' Bt.pts) →
        (rest.strictTransform (Subscheme.strictTransform t B)).pts ⊆
          closure (((StageState.fold b rest (σ.step b t)).cTilde hUh).base ''
            (Subscheme.totalTransform (ε' ≪≫ e).hom Bt).pts) := by
      intro Bt hBt
      rw [Iso.trans_hom, Subscheme.totalTransform_comp]
      exact hε5 _ (StageState.pts_strictTransform_subset_closure_step b σ t hU hU' e he1 hdisj
        B Bt hBt)
    exact ⟨hUh, ε' ≪≫ e, k1, k2, k3, k4, k5⟩

/-- Transport of the emptied auxiliary datum along an isomorphism of the `X̃`'s carrying `J̄` and
the `Ẽ_i` along, with extra (empty) components (formalization infrastructure for p. 310: "the
scheme `X̃` and the datum `ℜ^{N-1}` are kept the same").  The factorization
`J̃ ∏ Ẽ_j^{a_j} = J̄` transports (the extra components get the exponent `0`), and so does the
emptied datum, pulled back along the isomorphism, has the same characteristic data as that of the
transported state (`DatumII.Raw.SameChar`: the entries of the transported datum are the `emptyIfBot`
of the images, and the extra entries are empty). -/
theorem StageState.sameChar_datumII_emptyIfBot_of_iso
    (b : ℕ) {Y Y' : Scheme.{u}} (σ : StageState Y) (σ' : StageState Y')
    (hU : IsOpen σ.xHatPrimeStar) (hU' : IsOpen σ'.xHatPrimeStar)
    (ε : σ'.xTilde hU' ≅ σ.xTilde hU)
    (hJ : Subscheme.totalTransform ε.hom (σ.jBarT hU) = σ'.jBarT hU')
    (hE : ∀ i, Subscheme.totalTransform ε.hom (σ.eTildeAt hU i) = σ'.eTildeAt hU' i)
    (α₀ αT αT' : ℕ) (hα : αT ≤ αT')
    (hempty : ∀ i, α₀ + αT ≤ i → σ.eTildeAt hU i = Subscheme.empty)
    (a : Fin αT → ℕ) (Jt : Subscheme (σ.xTilde hU))
    (hJt : Jt * ∏ j : Fin αT, (σ.eTildeAt hU (α₀ + j)) ^ (a j) = σ.jBarT hU) :
    (Subscheme.totalTransform ε.hom Jt *
      ∏ j : Fin αT', (σ'.eTildeAt hU' (α₀ + j)) ^
        (if hj : (j : ℕ) < αT then a ⟨j, hj⟩ else 0) = σ'.jBarT hU') ∧
    DatumII.Raw.SameChar (((σ.datumII hU b α₀ αT a Jt).emptyIfBot).pullback ε.hom)
      ((σ'.datumII hU' b α₀ αT' (fun j => if hj : (j : ℕ) < αT then a ⟨j, hj⟩ else 0)
        (Subscheme.totalTransform ε.hom Jt)).emptyIfBot) := by
  classical
  constructor
  · refine Subscheme.ext_stalkIdeal fun z => ?_
    have hm : ∀ D : Subscheme (σ.xTilde hU), (Subscheme.totalTransform ε.hom D).stalkIdeal z =
        (D.stalkIdeal (ε.hom.base z)).map (ε.hom.stalkMap z).hom :=
      fun D => Hironaka.stalkIdeal_totalTransform ε.hom D z
    set φ := (ε.hom.stalkMap z).hom with hφ
    set F : ℕ → Ideal ((σ'.xTilde hU').presheaf.stalk z) := fun i =>
      ((σ.eTildeAt hU (α₀ + i)).stalkIdeal (ε.hom.base z)).map φ with hF
    set a₀ : ℕ → ℕ := fun i => if hi : i < αT then a ⟨i, hi⟩ else 0 with ha₀
    -- the right-hand side
    have hR : (σ'.jBarT hU').stalkIdeal z =
        (Jt.stalkIdeal (ε.hom.base z)).map φ * ∏ j : Fin αT, F j ^ a j := by
      rw [← hJ, ← hJt, hm, Subscheme.stalkIdeal_mul_eq, Subscheme.stalkIdeal_finset_prod,
        Ideal.map_mul, Ideal.map_finset_prod]
      refine congrArg _ (Finset.prod_congr rfl fun j _ => ?_)
      rw [Subscheme.stalkIdeal_pow_eq, Ideal.map_pow]
    have hL : (Subscheme.totalTransform ε.hom Jt *
        ∏ j : Fin αT', (σ'.eTildeAt hU' (α₀ + j)) ^
          (if hj : (j : ℕ) < αT then a ⟨j, hj⟩ else 0)).stalkIdeal z =
        (Jt.stalkIdeal (ε.hom.base z)).map φ * ∏ j : Fin αT', F j ^ a₀ j := by
      rw [Subscheme.stalkIdeal_mul_eq, Subscheme.stalkIdeal_finset_prod, hm]
      refine congrArg _ (Finset.prod_congr rfl fun j _ => ?_)
      rw [Subscheme.stalkIdeal_pow_eq, ← hE, hm]
    rw [hL, hR]
    refine congrArg _ ?_
    have h1 : ∏ j : Fin αT', F j ^ a₀ j = ∏ i ∈ Finset.range αT', F i ^ a₀ i :=
      Fin.prod_univ_eq_prod_range (fun i => F i ^ a₀ i) αT'
    have h2 : ∏ j : Fin αT, F j ^ a j = ∏ i ∈ Finset.range αT, F i ^ a₀ i := by
      rw [← Fin.prod_univ_eq_prod_range (fun i => F i ^ a₀ i) αT]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp [ha₀, j.2]
    rw [h1, h2]
    refine (Finset.prod_subset (Finset.range_subset_range.mpr hα) fun i _ hi => ?_).symm
    have : ¬ i < αT := fun h => hi (Finset.mem_range.mpr h)
    simp [ha₀, this]
  · -- an isomorphism preserves the whole space and `emptyIfBot`
    have hbot : ∀ E : Subscheme (σ.xTilde hU), Subscheme.totalTransform ε.hom E = ⊥ ↔ E = ⊥ := by
      intro E
      constructor
      · intro h
        have h2 := congrArg (Subscheme.totalTransform ε.inv) h
        have hb : Subscheme.totalTransform ε.inv (⊥ : Subscheme (σ'.xTilde hU')) = ⊥ :=
          Scheme.IdealSheafData.comap_bot _
        rwa [← Subscheme.totalTransform_comp, ε.inv_hom_id, Subscheme.totalTransform_id, hb] at h2
      · rintro rfl
        exact Scheme.IdealSheafData.comap_bot _
    have hemp : ∀ E : Subscheme (σ.xTilde hU),
        Subscheme.totalTransform ε.hom E.emptyIfBot =
          (Subscheme.totalTransform ε.hom E).emptyIfBot := by
      intro E
      by_cases hE0 : E = ⊥
      · rw [Subscheme.emptyIfBot_of_eq_bot hE0,
          Subscheme.emptyIfBot_of_eq_bot ((hbot E).mpr hE0), Subscheme.totalTransform_top]
      · rw [Subscheme.emptyIfBot_of_ne_bot hE0,
          Subscheme.emptyIfBot_of_ne_bot (fun h => hE0 ((hbot E).mp h))]
    set e₁ : ℕ → Subscheme (σ'.xTilde hU') := fun i =>
      Subscheme.totalTransform ε.hom ((σ.eTildeAt hU (α₀ + i)).emptyIfBot) with he₁
    set a₀ : ℕ → ℕ := fun i => if hi : i < αT then a ⟨i, hi⟩ else 0 with ha₀
    have hE2 : ∀ j : ℕ, (σ'.eTildeAt hU' (α₀ + j)).emptyIfBot = e₁ j := by
      intro j
      show (σ'.eTildeAt hU' (α₀ + j)).emptyIfBot =
        Subscheme.totalTransform ε.hom ((σ.eTildeAt hU (α₀ + j)).emptyIfBot)
      rw [hemp, hE]
    have hbig : ∀ j : ℕ, αT ≤ j → (e₁ j).pts = ∅ := by
      intro j hj
      rw [he₁]
      show (Subscheme.totalTransform ε.hom
        ((σ.eTildeAt hU (α₀ + j)).emptyIfBot)).pts = ∅
      rw [hempty (α₀ + j) (by omega)]
      show (Subscheme.totalTransform ε.hom (Subscheme.empty : Subscheme _).emptyIfBot).pts = ∅
      rw [show (Subscheme.empty : Subscheme (σ.xTilde hU)) = ⊤ from rfl, Subscheme.emptyIfBot_top,
        Subscheme.totalTransform_top]
      exact DatumTransform.pts_empty
    refine ⟨rfl, rfl, fun D hD => ⟨?_, ?_⟩⟩
    · constructor
      · rintro ⟨i, hi⟩
        refine ⟨Fin.castLE hα i, ?_⟩
        show (σ'.eTildeAt hU' (α₀ + (Fin.castLE hα i : ℕ))).emptyIfBot = D
        rw [hE2]
        exact hi
      · rintro ⟨j, hj⟩
        have hjα : (j : ℕ) < αT := by
          by_contra hge
          have := hbig j (not_lt.mp hge)
          have h2 : (e₁ j).pts = D.pts := by
            rw [← hE2 j]; exact congrArg Subscheme.pts hj
          rw [this] at h2
          exact absurd hD (by rw [← h2]; exact Set.not_nonempty_empty)
        refine ⟨⟨j, hjα⟩, ?_⟩
        have hj' : (σ'.eTildeAt hU' (α₀ + (j : ℕ))).emptyIfBot = D := hj
        rw [hE2] at hj'
        exact hj'
    · show ∑ i ∈ Finset.univ.filter (fun i : Fin αT => e₁ i = D), a i =
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin αT' => (σ'.eTildeAt hU' (α₀ + j)).emptyIfBot = D), a₀ j
      rw [Finset.sum_filter, Finset.sum_filter]
      have h2 : ∀ j : Fin αT', (if (σ'.eTildeAt hU' (α₀ + j)).emptyIfBot = D then a₀ j else 0) =
          (if e₁ j = D then a₀ j else 0) := fun j => by rw [hE2]
      have h2' : ∑ j : Fin αT', (if (σ'.eTildeAt hU' (α₀ + j)).emptyIfBot = D then a₀ j else 0) =
          ∑ j : Fin αT', (if e₁ j = D then a₀ j else 0) := Finset.sum_congr rfl fun j _ => h2 j
      rw [h2']
      have h3 : ∑ j : Fin αT', (if e₁ j = D then a₀ j else 0 : ℕ) =
          ∑ i ∈ Finset.range αT', (if e₁ i = D then a₀ i else 0 : ℕ) :=
        Fin.sum_univ_eq_sum_range (fun i => if e₁ i = D then a₀ i else 0) αT'
      have h4 : ∑ i : Fin αT, (if e₁ i = D then a i else 0 : ℕ) =
          ∑ i ∈ Finset.range αT, (if e₁ i = D then a₀ i else 0 : ℕ) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => if e₁ i = D then a₀ i else 0) αT]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [ha₀, i.2]
      rw [h3, h4]
      refine (Finset.sum_subset (f := fun i => (if e₁ i = D then a₀ i else 0 : ℕ))
        (Finset.range_subset_range.mpr hα) fun i _ hi => ?_)
      have : ¬ i < αT := fun h => hi (Finset.mem_range.mpr h)
      simp [ha₀, this]

end AB

end

end Hironaka
