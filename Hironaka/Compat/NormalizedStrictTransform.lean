/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Data.Nat.Nth
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch3.JStability
public import Hironaka.Ch3.FrameTransforms
public import Hironaka.Compat.TauZSingleton
public import Hironaka.Compat.TauOrderedFrame
public import Hironaka.Compat.TauZStandardBase
public import Hironaka.Compat.TauZSystem
public import Hironaka.Compat.NormalizedStandardBase
public import Hironaka.Compat.FrameWithElement
public import Hironaka.Compat.NormalizedStrictTransformComplete
public import Hironaka.Statements

/-!
# Normalized standard bases under strict transforms: the one-step theorem of Theorem 8

Infrastructure for Theorem 8 (pp. 264-265, `Hironaka/Ch3/JStableStandardBase.lean`).

* Normalized systems and standard bases, and regular `tau`-frames, are carried along ring
  isomorphisms (`RegularFrame.isNormalizedStandardBase_transport`,
  `RegularFrame.isRegularTauFrame_transport`, `RegularFrame.isRegularTauFrame_of_transport`).
  The sequences of monoidal transforms of Definition 11 identify `R_{alpha+1}` with the monoidal
  transform only up to a ring isomorphism (`MonoidalSequence.equiv`).
* Regular `tau`-frames are invariant under unit multiples of the frame
  (`RegularFrame.isRegularTauFrame_of_associated`): the paper identifies the `J`-stable `tau`-frame
  of Definition 12 with the frame of the chain of frame transforms of Remark 3 tacitly.
* The trivial monoidal transform with center `R` (needed because finite sequences are continued
  by trivial transforms): `RegularFrame.isNormalizedStandardBase_topFrameTransform`.
* Regular `τ`-frames are carried by base changes (`RegularFrame.isRegularTauFrame_of_map`), and
  `τ_{(w)}`- and `τ_{(w)_a}`-statements descend (`initialForm_mem_framePrefixSubalgebra_of_map`).
* The one-step theorem of the proof of Theorem 8
  (`isNormalizedStandardBase_strictTransform_of_isRegularTauFrame`), along the printed route: the
  reduction "we may assume that `R` is complete … so that `R = S{z₁, …, z_τ}`" (the base change of
  §8 for the identity of `S`) to `isNormalizedStandardBase_strictTransform_of_mvPowerSeries`
  (`Compat/NormalizedStrictTransformComplete.lean`, the induction on the blocks `a` with the partial
  frames `S^{(a)}`, Lemma 20 and Lemma 19), and the descent of the conclusions.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section Transport

variable {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B]

open MvPolynomial in
/-- The `E`-set of the system of initial forms of `(f_j)` with respect to `(z_1, …, z_r)` is
contained in that of `(e f_j)` with respect to `(e z_1, …, e z_r)`, for a ring isomorphism `e`
(the isomorphism `gr_M(A) ≅ gr_M(B)` carries the initial forms and the subalgebra `k[Z]`;
Remark 1 of §7 for the isomorphism of the coefficient fields). -/
theorem frameESet_subset_map_ringEquiv (e : A ≃+* B) {r : ℕ} (z : Fin r → A) (z' : Fin r → B)
    (hz : ∀ j, z' j = e (z j)) {i : ℕ} (f : Fin i → A) :
    frameESet z f ⊆ frameESet z' (fun j => e (f j)) := by
  classical
  have hM := map_ringEquiv_maximalIdeal e
  have hord := ordElem_maximalIdeal_ringEquiv_aux e
  obtain ⟨Γ, Ē, hΓ1, hΓ2⟩ := exists_assocGraded_ringHom_of_map_eq (e : A →+* B)
    (maximalIdeal A) (maximalIdeal B) hM hord
  have hĒ : Function.Injective Ē := by
    let _ : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
    exact Ē.injective
  have key : ∀ ψ : MvPolynomial (Fin r) (A ⧸ maximalIdeal A),
      Γ (frameAlgHom z ψ) = frameAlgHom z' (MvPolynomial.map Ē ψ) := by
    intro ψ
    induction ψ using MvPolynomial.induction_on with
    | C c =>
      simp only [frameAlgHom, MvPolynomial.aeval_C, MvPolynomial.map_C]
      exact hΓ2 c
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p j hp =>
      simp only [frameAlgHom, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X] at hp ⊢
      rw [hp]
      congr 1
      simp only [frameForm]
      rw [hΓ1, hz]
      rfl
  refine eSet_subset_of_map_le Ē hĒ _ _ ?_
  rw [frameInitialIdeal, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨ψ, ⟨j, hψ⟩, rfl⟩
  refine Ideal.subset_span ⟨j, ?_⟩
  rw [← key, hψ, hΓ1]
  rfl

end Transport

section TransportFrame

variable {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B]

/-- The ideal `(z)` of the transported frame is the image of `(z)`. -/
theorem RegularFrame.idealZ_transport (F : RegularFrame A) (e : A ≃+* B) :
    (F.transport e).idealZ = F.idealZ.map (e : A →+* B) := by
  show Ideal.span (Set.range fun j => e (F.z j)) = _
  rw [RegularFrame.idealZ, Ideal.map_span, ← Set.range_comp]
  rfl

/-- An expansion map of the transported frame composed with `e` is an expansion map of the frame. -/
theorem RegularFrame.IsExpansion.comp_transport (F : RegularFrame A) (e : A ≃+* B)
    {e' : B →+* MvPowerSeries (Fin (F.transport e).r) (F.transport e).S}
    (h : (F.transport e).IsExpansion e') :
    F.IsExpansion (e'.comp (e : A →+* B)) where
  map_algebraMap s := h.map_algebraMap s
  map_z j := h.map_z j
  map_pow n x hx := by
    refine h.map_pow n (e x) ?_
    rw [F.idealZ_transport e, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx

/-- "Normalized by" is invariant under ring isomorphisms (the frame being transported). -/
theorem RegularFrame.isNormalizedBy_transport (F : RegularFrame A) (e : A ≃+* B) {i : ℕ}
    (f : Fin i → A) (g : A) (h : F.IsNormalizedBy f g) :
    (F.transport e).IsNormalizedBy (fun j => e (f j)) (e g) := by
  intro e' he' Ar hAr
  have hsub := frameESet_subset_map_ringEquiv e.symm (F.transport e).z F.z
    (fun j => (e.symm_apply_apply (F.z j)).symm) (fun j => e (f j))
  have hfun : (fun j => e.symm (e (f j))) = f := funext fun j => e.symm_apply_apply (f j)
  rw [hfun] at hsub
  exact h (e'.comp (e : A →+* B)) (he'.comp_transport F e) Ar (hsub hAr)

/-- Initial forms in the associated subalgebra are carried by ring isomorphisms (for systems). -/
theorem initialForm_mem_assocSubalgebra_map (e : A ≃+* B) {r : ℕ} (z : Fin r → A)
    (z' : Fin r → B) (hz : ∀ j, z' j = e (z j)) (a : A)
    (h : initialForm (maximalIdeal A) a ∈ assocSubalgebra z) :
    initialForm (maximalIdeal B) (e a) ∈ assocSubalgebra z' := by
  classical
  have hM := map_ringEquiv_maximalIdeal e
  have hord := ordElem_maximalIdeal_ringEquiv_aux e
  obtain ⟨Γ, Ē, hΓ1, hΓ2⟩ := exists_assocGraded_ringHom_of_map_eq (e : A →+* B)
    (maximalIdeal A) (maximalIdeal B) hM hord
  have hadj : ∀ x ∈ assocSubalgebra z, Γ x ∈ assocSubalgebra z' := by
    intro x hx
    refine Algebra.adjoin_induction (p := fun x _ => Γ x ∈ assocSubalgebra z') ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, rfl⟩
      refine Algebra.subset_adjoin ⟨j, ?_⟩
      show initialForm (maximalIdeal B) (z' j) = Γ (initialForm (maximalIdeal A) (z j))
      rw [hΓ1, hz]
      rfl
    · intro c
      rw [hΓ2]
      exact Subalgebra.algebraMap_mem _ _
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro x y _ _ hx hy
      rw [map_mul]
      exact mul_mem hx hy
  have := hadj _ h
  rwa [hΓ1] at this

/-- Initial forms in the associated subalgebra are carried by ring isomorphisms. -/
theorem RegularFrame.initialForm_mem_assocSubalgebra_transport (F : RegularFrame A)
    (e : A ≃+* B) (a : A) (h : initialForm (maximalIdeal A) a ∈ F.assocSubalgebra) :
    initialForm (maximalIdeal B) (e a) ∈ (F.transport e).assocSubalgebra :=
  initialForm_mem_assocSubalgebra_map e F.z (F.transport e).z (fun _ => rfl) a h

/-- Normalized systems are carried by ring isomorphisms. -/
theorem RegularFrame.isNormalizedSystem_transport (F : RegularFrame A) (e : A ≃+* B) {m : ℕ}
    (f : Fin m → A) (h : F.IsNormalizedSystem f) :
    (F.transport e).IsNormalizedSystem (fun j => e (f j)) := by
  refine ⟨fun j => F.initialForm_mem_assocSubalgebra_transport e _ (h.1 j), fun j => ?_⟩
  exact F.isNormalizedBy_transport e (fun l : Fin (j : ℕ) => f (Fin.castLE j.2.le l)) (f j)
    (h.2 j)

/-- Normalized standard bases are carried by ring isomorphisms. -/
theorem RegularFrame.isNormalizedStandardBase_transport (F : RegularFrame A) (e : A ≃+* B)
    (J : Ideal A) {m : ℕ} (f : Fin m → A) (h : F.IsNormalizedStandardBase J f) :
    (F.transport e).IsNormalizedStandardBase (J.map (e : A →+* B)) (fun j => e (f j)) :=
  ⟨isStandardBase_map_of_bijective_aux (e : A →+* B) e.bijective J f h.1,
    F.isNormalizedSystem_transport e f h.2⟩

end TransportFrame

section TauFrameTransport

variable {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B]

/-- The members of a transported frame, with explicit `Fin.cast` indices (a `rfl` lemma used to
avoid dependent-type rewriting). -/
theorem RegularFrame.transport_z_cast (F : RegularFrame A) (e : A ≃+* B) {n n' : ℕ}
    (h1 : n = n') (hr : n' = F.r) (x : Fin n) :
    (F.transport e).z (Fin.cast (h1.trans hr) x) = e (F.z (Fin.cast hr (Fin.cast h1 x))) := rfl

/-- Regular `τ`-frames are carried by ring isomorphisms (Lemma 13 of §4 for the isomorphism). -/
theorem RegularFrame.isRegularTauFrame_transport [Hironaka.HironakaCitedResults.{u}] (F : RegularFrame A) (e : A ≃+* B) (J : Ideal A)
    (ht1 : 1 ≤ t A J) (h : F.IsRegularTauFrame J) :
    (F.transport e).IsRegularTauFrame (J.map (e : A →+* B)) := by
  classical
  obtain ⟨hr, hz, hsys⟩ := h
  have hloc : IsLocalHom (e : A →+* B) := IsLocalHom.of_surjective _ e.surjective
  obtain ⟨ht, hB, hmap⟩ := tauStar_map (e : A →+* B) (mapsRSOP_of_bijective_aux _ e.bijective)
    (isResiduallySeparable_of_bijective_aux _ e.bijective) J
  have htt : tau B (J.map (e : A →+* B)) (t B (J.map (e : A →+* B))) = tau A J (t A J) := by
    rw [ht]
    exact hB _ ht1 le_rfl
  have hz' : ∀ j, (F.transport e).z j ∈ maximalIdeal B := fun j =>
    map_nonunit (e : A →+* B) _ (hz j)
  refine ⟨htt.trans hr, hz', ?_⟩
  have key := hmap htt (fun i => ⟨F.z (Fin.cast hr i), hz _⟩) hsys
  have hfun : (fun i : Fin (tau B (J.map (e : A →+* B)) (t B (J.map (e : A →+* B)))) =>
      (⟨(F.transport e).z (Fin.cast (htt.trans hr) i), hz' _⟩ : maximalIdeal B)) =
      fun i => ⟨(e : A →+* B) ((fun i : Fin (tau A J (t A J)) =>
        (⟨F.z (Fin.cast hr i), hz _⟩ : maximalIdeal A)) (Fin.cast htt i)),
        map_nonunit (e : A →+* B) _ (hz _)⟩ := by
    funext i
    exact Subtype.ext (RegularFrame.transport_z_cast F e htt hr i)
  rw [hfun]
  exact key

end TauFrameTransport

section TauFrameAssoc

variable {B : Type u} [CommRing B] [IsRegularLocalRing B]

/-- `(r + I) • [x Xⁿ] = [r x Xⁿ]` in `gr_I(B)`. -/
theorem AssocGraded.smul_mk_quotient {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ) (r x : A)
    (hx : x ∈ I ^ n) :
    (Ideal.Quotient.mk I r) • AssocGraded.mk I n x hx =
      AssocGraded.mk I n (r * x) (Ideal.mul_mem_left _ r hx) := by
  rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]
  exact (map_smul (AssocGraded.mkLinear I n) r ⟨x, hx⟩).symm

/-- Multiplying the members of a system of elements of `M` by units does not change the
`k`-module generated by their classes in `gr¹_M`. -/
theorem span_mk_unit_mul_eq {n : ℕ} (x x' : Fin n → maximalIdeal B) (u : Fin n → Bˣ)
    (hu : ∀ i, (x' i : B) = u i * x i) (p : Fin n → Prop) :
    Submodule.span (B ⧸ maximalIdeal B)
        (Set.range fun i : {i : Fin n // p i} =>
          AssocGraded.mk (maximalIdeal B) 1 (x' i.1 : B) (by rw [pow_one]; exact (x' i.1).2)) =
      Submodule.span (B ⧸ maximalIdeal B)
        (Set.range fun i : {i : Fin n // p i} =>
          AssocGraded.mk (maximalIdeal B) 1 (x i.1 : B) (by rw [pow_one]; exact (x i.1).2)) := by
  have key : ∀ (y y' : B) (hy : y ∈ maximalIdeal B ^ 1) (hy' : y' ∈ maximalIdeal B ^ 1) (c : B),
      y' = c * y → AssocGraded.mk (maximalIdeal B) 1 y' hy' ∈
        Submodule.span (B ⧸ maximalIdeal B) {AssocGraded.mk (maximalIdeal B) 1 y hy} := by
    intro y y' hy hy' c hc
    subst hc
    have h := AssocGraded.smul_mk_quotient (maximalIdeal B) 1 c y hy
    have h2 : (Ideal.Quotient.mk (maximalIdeal B) c) • AssocGraded.mk (maximalIdeal B) 1 y hy ∈
        Submodule.span (B ⧸ maximalIdeal B) {AssocGraded.mk (maximalIdeal B) 1 y hy} :=
      Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    rw [h] at h2
    exact h2
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨i, rfl⟩
    have hk := key (x i.1 : B) (x' i.1 : B) (by rw [pow_one]; exact (x i.1).2)
      (by rw [pow_one]; exact (x' i.1).2) (u i.1) (hu i.1)
    refine Submodule.span_mono ?_ hk
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨i, rfl⟩
  · rintro _ ⟨i, rfl⟩
    have hk := key (x' i.1 : B) (x i.1 : B) (by rw [pow_one]; exact (x' i.1).2)
      (by rw [pow_one]; exact (x i.1).2) ((u i.1)⁻¹ : Bˣ)
      (by rw [hu i.1, ← mul_assoc, Units.inv_mul, one_mul])
    refine Submodule.span_mono ?_ hk
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨i, rfl⟩

/-- The members of associated frames, with explicit `Fin.cast` indices. -/
theorem RegularFrame.assoc_cast (G G' : RegularFrame B) (hr : G'.r = G.r) (u : Fin G'.r → Bˣ)
    (hu : ∀ j, G'.z j = u j * G.z (Fin.cast hr j)) {n : ℕ} (ht : n = G.r) (hr' : n = G'.r)
    (i : Fin n) :
    G'.z (Fin.cast hr' i) = u (Fin.cast hr' i) * G.z (Fin.cast ht i) := by
  rw [hu]
  rfl

/-- Being a regular `τ`-frame for `J` depends only on the members `z_j` up to unit multiples (the
`k`-module they span in `gr¹_M` does not change): a frame whose members are unit multiples of the
members of a regular `τ`-frame for `J` is again one.  (This is how the paper identifies the
`J`-stable `τ`-frames of Definition 12 with frame transforms of a given chain, p. 264.) -/
theorem RegularFrame.isRegularTauFrame_of_associated (G G' : RegularFrame B) (J : Ideal B)
    (hr : G'.r = G.r) (u : Fin G'.r → Bˣ)
    (hu : ∀ j, G'.z j = u j * G.z (Fin.cast hr j)) (h : G.IsRegularTauFrame J) :
    G'.IsRegularTauFrame J := by
  obtain ⟨ht, hz, hsys⟩ := h
  have hr' : tau B J (t B J) = G'.r := ht.trans hr.symm
  have hz' : ∀ j, G'.z j ∈ maximalIdeal B := fun j => by
    rw [hu j]
    exact Ideal.mul_mem_left _ _ (hz _)
  refine ⟨hr', hz', fun b hb1 hbt => ?_⟩
  have h := hsys b hb1 hbt
  have hspan := span_mk_unit_mul_eq (B := B) (fun i => ⟨G.z (Fin.cast ht i), hz _⟩)
    (fun i => ⟨G'.z (Fin.cast hr' i), hz' _⟩) (fun i => u (Fin.cast hr' i))
    (fun i => RegularFrame.assoc_cast G G' hr u hu ht hr' i) (fun i => (i : ℕ) < tau B J b)
  rw [← hspan] at h
  exact h

end TauFrameAssoc

section TauFrameBack

variable {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B]

omit [IsRegularLocalRing A] [IsRegularLocalRing B] in
/-- The image of an ideal under a ring isomorphism and then under its inverse. -/
theorem Ideal.map_map_symm_ringEquiv (e : A ≃+* B) (J : Ideal A) :
    (J.map (e : A →+* B)).map (e.symm : B →+* A) = J := by
  rw [Ideal.map_map]
  have : (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A :=
    RingHom.ext fun a => e.symm_apply_apply a
  rw [this, Ideal.map_id]

/-- Regular `τ`-frames descend along ring isomorphisms. -/
theorem RegularFrame.isRegularTauFrame_of_transport [Hironaka.HironakaCitedResults.{u}] (F : RegularFrame A) (e : A ≃+* B)
    (J : Ideal A) (ht1 : 1 ≤ t A J) (h : (F.transport e).IsRegularTauFrame (J.map (e : A →+* B))) :
    F.IsRegularTauFrame J := by
  have ht : t B (J.map (e : A →+* B)) = t A J :=
    (nuStar_t_tau_map_of_bijective_aux (e : A →+* B) e.bijective J).2.1
  have h1 := (F.transport e).isRegularTauFrame_transport e.symm (J.map (e : A →+* B))
    (by rw [ht]; exact ht1) h
  rw [Ideal.map_map_symm_ringEquiv] at h1
  refine RegularFrame.isRegularTauFrame_of_associated ((F.transport e).transport e.symm) F J rfl
    (fun _ => 1) (fun j => ?_) h1
  show F.z j = 1 * e.symm (e (F.z j))
  simp

end TauFrameBack

section PowerSeriesMap

/-- The map of power series rings induced by a ring homomorphism fixes the variables. -/
theorem mvPowerSeries_map_X {S S' : Type*} [CommRing S] [CommRing S'] (ρ : S →+* S') {r : ℕ}
    (j : Fin r) : MvPowerSeries.map ρ (MvPowerSeries.X j : MvPowerSeries (Fin r) S) =
      MvPowerSeries.X j := by
  simp [MvPowerSeries.map_X]

/-- The map of power series rings induced by a ring homomorphism preserves the powers of the
ideal `(X₁, …, X_r)`. -/
theorem mvPowerSeries_map_mem_pow_span_X {S S' : Type*} [CommRing S] [CommRing S'] (ρ : S →+* S')
    {r : ℕ} (n : ℕ) {x : MvPowerSeries (Fin r) S}
    (hx : x ∈ (Ideal.span (Set.range (MvPowerSeries.X : Fin r → MvPowerSeries (Fin r) S))) ^ n) :
    MvPowerSeries.map ρ x ∈
      (Ideal.span (Set.range (MvPowerSeries.X : Fin r → MvPowerSeries (Fin r) S'))) ^ n := by
  have h2 := Ideal.mem_map_of_mem (MvPowerSeries.map ρ) hx
  rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at h2
  have h3 : (MvPowerSeries.map ρ) ∘ (MvPowerSeries.X : Fin r → MvPowerSeries (Fin r) S) =
      MvPowerSeries.X := funext fun j => mvPowerSeries_map_X ρ j
  rw [h3] at h2
  exact h2

/-- The coefficients of the image of a power series under the map induced by a ring
homomorphism. -/
theorem psCoeff_map {S S' : Type u} [CommRing S] [CommRing S'] (ρ : S →+* S') {r : ℕ}
    (A : Fin r → ℕ) (f : MvPowerSeries (Fin r) S) :
    psCoeff A (MvPowerSeries.map ρ f) = ρ (psCoeff A f) := by
  simp [psCoeff, MvPowerSeries.coeff_map]

/-- The map of power series rings induced by a ring homomorphism, on constants. -/
theorem mvPowerSeries_map_C {S S' : Type*} [CommRing S] [CommRing S'] (ρ : S →+* S') {r : ℕ}
    (s : S) : MvPowerSeries.map ρ (MvPowerSeries.C s : MvPowerSeries (Fin r) S) =
      MvPowerSeries.C (ρ s) := by
  simp [MvPowerSeries.map_C]

end PowerSeriesMap

section TopStep

attribute [local instance] RegularFrame.isDomain_S

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {F : RegularFrame R}
  {P : Ideal R} {T : MonoidalTransform R P} [IsRegularLocalRing T.ring]

/-- "Normalized by" for a frame transform which is the image of the frame under a ring isomorphism
`e : R ≃ R₁` (with the coefficient ring identified by `ρ`): this is the case of the trivial monoidal
transform with center `R`. -/
theorem RegularFrame.FrameTransform.isNormalizedBy_of_iso (FT : F.FrameTransform T)
    (e : R ≃+* T.ring) (ρ : FT.TS.ring ≃+* F.S)
    (hw : ∀ j, FT.w j = e (F.z j))
    (hβ : ∀ s, FT.β s = e (algebraMap F.S R (ρ s))) {i : ℕ} (f : Fin i → R) (g : R)
    (h : F.IsNormalizedBy f g) :
    FT.toRegularFrame.IsNormalizedBy (fun j => e (f j)) (e g) := by
  intro e' he' Ar hAr
  have hsub := frameESet_subset_map_ringEquiv e.symm FT.w F.z
    (fun j => by rw [hw j, e.symm_apply_apply]) (fun j => e (f j))
  have hfun : (fun j => e.symm (e (f j))) = f := funext fun j => e.symm_apply_apply (f j)
  rw [hfun] at hsub
  have hAr' : Ar ∈ frameESet F.z f := hsub hAr
  -- the expansion of `F` obtained from that of the frame transform
  let ρh : FT.toRegularFrame.S →+* F.S := ρ.toRingHom
  let e₁ : R →+* MvPowerSeries (Fin F.r) F.S :=
    (MvPowerSeries.map ρh).comp (e'.comp (e : R →+* T.ring))
  have he₁ : F.IsExpansion e₁ := by
    refine ⟨fun s => ?_, fun j => ?_, fun n x hx => ?_⟩
    · have h1 : e (algebraMap F.S R s) = FT.β (ρ.symm s) := by rw [hβ, ρ.apply_symm_apply]
      have h2 := he'.map_algebraMap (ρ.symm s)
      show MvPowerSeries.map ρh (e' (e (algebraMap F.S R s))) = _
      rw [h1]
      have h3 : e' (FT.β (ρ.symm s)) = MvPowerSeries.C (ρ.symm s) := h2
      rw [h3]
      exact (mvPowerSeries_map_C ρh _).trans (congrArg MvPowerSeries.C (ρ.apply_symm_apply s))
    · show MvPowerSeries.map ρh (e' (e (F.z j))) = _
      rw [← hw j]
      have := he'.map_z j
      rw [show FT.toRegularFrame.z j = FT.w j from rfl] at this
      rw [this]
      exact mvPowerSeries_map_X ρh j
    · have hmem : e x ∈ FT.toRegularFrame.idealZ ^ n := by
        have : FT.toRegularFrame.idealZ = F.idealZ.map (e : R →+* T.ring) := by
          show Ideal.span (Set.range FT.w) = _
          rw [RegularFrame.idealZ, Ideal.map_span, ← Set.range_comp]
          congr 2
          funext j
          exact hw j
        rw [this, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hx
      have h1 := he'.map_pow n (e x) hmem
      show MvPowerSeries.map ρh (e' (e x)) ∈ _
      exact mvPowerSeries_map_mem_pow_span_X ρh n h1
  have := h e₁ he₁ Ar hAr'
  have h5 : ρh (psCoeff Ar (e' (e g))) = 0 :=
    (psCoeff_map ρh Ar (e' (e g))).symm.trans this
  exact (show Function.Injective ρh from ρ.injective) (h5.trans (map_zero ρh).symm)

end TopStep

section TopStep2

attribute [local instance] RegularFrame.isDomain_S

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- The frame transform of the trivial monoidal transform with center `R` is the image of the
frame under the isomorphism `R → R₁`, the coefficient ring being identified by an isomorphism. -/
theorem topFrameTransform_spec (F : RegularFrame R) {P : Ideal R} (hP : P = ⊤)
    (T : MonoidalTransform R P) [IsRegularLocalRing T.ring] :
    ∃ ρ : (RegularFrame.topFrameTransform F hP T).TS.ring ≃+* F.S,
      (∀ s, (RegularFrame.topFrameTransform F hP T).β s = T.toRing (algebraMap F.S R (ρ s))) ∧
      ∀ j, (RegularFrame.topFrameTransform F hP T).w j = T.toRing (F.z j) := by
  have hcomap : P.comap (algebraMap F.S R) = ⊤ := by rw [hP]; exact Ideal.comap_top
  exact ⟨(RingEquiv.ofBijective (RegularFrame.topFrameTransform F hP T).TS.toRing
    (MonoidalSequence.toRing_bijective_of_eq_top_aux _ hcomap)).symm, fun s => rfl, fun j => rfl⟩

/-- A normalized standard base is carried to a normalized standard base of the strict transform
`J R₁` by the trivial monoidal transform with center `R` and its frame transform. -/
theorem RegularFrame.isNormalizedStandardBase_topFrameTransform (F : RegularFrame R) {P : Ideal R}
    (hP : P = ⊤) (T : MonoidalTransform R P) [IsRegularLocalRing T.ring] (J : Ideal R) {m : ℕ}
    (f : Fin m → R) (h : F.IsNormalizedStandardBase J f) :
    (RegularFrame.topFrameTransform F hP T).toRegularFrame.IsNormalizedStandardBase
      (strictTransformIdeal T J) (fun j => T.toRing (f j)) := by
  obtain ⟨ρ, hβ, hw⟩ := topFrameTransform_spec F hP T
  have hbij := MonoidalSequence.toRing_bijective_of_eq_top_aux T hP
  let e : R ≃+* T.ring := RingEquiv.ofBijective T.toRing hbij
  rw [MonoidalSequence.strictTransformIdeal_eq_map_of_eq_top_aux T hP J]
  refine ⟨isStandardBase_map_of_bijective_aux T.toRing hbij J f h.1, ?_, ?_⟩
  · intro j
    exact initialForm_mem_assocSubalgebra_map e F.z (RegularFrame.topFrameTransform F hP T).w
      (fun j => hw j) (f j) (h.2.1 j)
  · intro j
    exact (RegularFrame.topFrameTransform F hP T).isNormalizedBy_of_iso e ρ hw hβ _ _ (h.2.2 j)

end TopStep2

section TauFrameMap

variable {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B]

/-- **Regular `τ`-frames are carried by base changes**: if `α : A → B` transforms a regular system
of parameters into one, with separable residue field extension, and the members of the frame `G`
of `B` are the images of those of a regular `τ`-frame `F` of `A` for `J`, then `G` is a regular
`τ`-frame of `B` for `JB` (Lemma 13 of §4, `tauStar_map`; used in the reduction "we may assume
that `R` is complete" of p. 264). -/
theorem RegularFrame.isRegularTauFrame_of_map [Hironaka.HironakaCitedResults.{u}] (α : A →+* B) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hsep : RingHom.IsResiduallySeparable α) (F : RegularFrame A)
    (G : RegularFrame B) (J : Ideal A) (ht1 : 1 ≤ t A J) (hr : G.r = F.r)
    (hz : ∀ j, G.z j = α (F.z (Fin.cast hr j))) (h : F.IsRegularTauFrame J) :
    G.IsRegularTauFrame (J.map α) := by
  classical
  obtain ⟨hr0, hz0, hsys⟩ := h
  obtain ⟨ht, hB, hmap⟩ := tauStar_map α hα hsep J
  have htt : tau B (J.map α) (t B (J.map α)) = tau A J (t A J) := by
    rw [ht]
    exact hB _ ht1 le_rfl
  have hz' : ∀ j, G.z j ∈ maximalIdeal B := fun j => by
    rw [hz j]
    exact map_nonunit α _ (hz0 _)
  refine ⟨htt.trans (hr0.trans hr.symm), hz', ?_⟩
  have key := hmap htt (fun i => ⟨F.z (Fin.cast hr0 i), hz0 _⟩) hsys
  have hfun : (fun i : Fin (tau B (J.map α) (t B (J.map α))) =>
      (⟨G.z (Fin.cast (htt.trans (hr0.trans hr.symm)) i), hz' _⟩ : maximalIdeal B)) =
      fun i => ⟨α ((fun i : Fin (tau A J (t A J)) =>
        (⟨F.z (Fin.cast hr0 i), hz0 _⟩ : maximalIdeal A)) (Fin.cast htt i)),
        map_nonunit α _ (hz0 _)⟩ := by
    funext i
    refine Subtype.ext ?_
    show G.z _ = α (F.z _)
    rw [hz]
    rfl
  rw [hfun]
  exact key

end TauFrameMap

section Descent

variable {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B]

open Classical in
/-- `τ_{(z)}(f) = 0` forces the initial form of `f` into `k[Z₁, …, Z_r]`, for a system `z` which
can be extended to a regular system of parameters (Definition 10*: then `T* = ⟨Z⟩`, so `T ⊆ ⟨Z⟩`,
and the initial form of `f` lies in `k[T]`). -/
theorem initialForm_mem_adjoin_of_tauZ_eq_zero' {r : ℕ} {z : Fin r → A}
    (hinj : Function.Injective z) (hz : ExtendsToRSOP A (Finset.image z Finset.univ)) (f : A)
    (h : tauZ A z (fun _ : Fin 1 => f) = 0) :
    initialForm (maximalIdeal A) f ∈ Hironaka.assocSubalgebra z := by
  have h1 := initialForm_mem_adjoin_tauZSubmoduleStar z f
  rw [tauZSubmoduleStar_eq_span_of_tauZ_eq_zero hinj hz _ h, Algebra.adjoin_span] at h1
  exact h1

open Classical in
/-- **Descent of `τ_{(w)_a}(g) = 0` along a base change** (the conclusions "are replaced by
equivalent ones", p. 254, for the reduction of p. 264): if `β : A → B` transforms a regular system
of parameters into one, with separable residue field extension, and `z' = β(z)` is a system of
`B` which can be extended to a regular system of parameters, then the initial form of `g` lies in
`k[Z₁, …, Z_k]` as soon as that of `β g` lies in `k'[Z'₁, …, Z'_k]` (`τ` is invariant,
`tauZ_map`, for the initial segments of the systems). -/
theorem initialForm_mem_framePrefixSubalgebra_of_map [Hironaka.HironakaCitedResults.{u}] (β : A →+* B) [IsLocalHom β]
    (hβ : RingHom.MapsRSOP β) (hsep : RingHom.IsResiduallySeparable β) {n : ℕ} (z : Fin n → A)
    (hinj : Function.Injective z) (hz : ExtendsToRSOP A (Finset.image z Finset.univ))
    (z' : Fin n → B) (hinj' : Function.Injective z')
    (hz'r : ExtendsToRSOP B (Finset.image z' Finset.univ)) (hz' : ∀ j, z' j = β (z j)) (k : ℕ)
    (g : A) (h : initialForm (maximalIdeal B) (β g) ∈ framePrefixSubalgebra z' k) :
    initialForm (maximalIdeal A) g ∈ framePrefixSubalgebra z k := by
  have hp : min k n ≤ n := min_le_right _ _
  set zp : Fin (min k n) → A := fun l => z (Fin.castLE hp l) with hzp
  set zp' : Fin (min k n) → B := fun l => z' (Fin.castLE hp l) with hzp'
  have hsub : ∀ {C : Type u} [CommRing C] [IsRegularLocalRing C] (w : Fin n → C),
      ExtendsToRSOP C (Finset.image w Finset.univ) →
        ExtendsToRSOP C (Finset.image (fun l => w (Fin.castLE hp l)) Finset.univ) := by
    intro C _ _ w ⟨s, hs, hrs⟩
    refine ⟨s, fun y hy => hs ?_, hrs⟩
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hinjp : Function.Injective zp := hinj.comp (Fin.castLE_injective hp)
  have hinjp' : Function.Injective zp' := hinj'.comp (Fin.castLE_injective hp)
  have e : ∀ {C : Type u} [CommRing C] [IsRegularLocalRing C] (w : Fin n → C),
      framePrefixSubalgebra w k = Hironaka.assocSubalgebra (fun l => w (Fin.castLE hp l)) :=
    fun w => ((assocSubalgebra_eq_framePrefixSubalgebra w _ hp fun _ => rfl).trans
      (framePrefixSubalgebra_min w k)).symm
  rw [e] at h ⊢
  have h1 := tauZ_eq_zero_of_initialForm_mem_adjoin hinjp' (hsub z' hz'r) (β g) h
  have h2 := tauZ_map β hβ hsep zp (fun _ : Fin 1 => g)
  have hfun : (fun j => β (zp j)) = zp' := funext fun j => (hz' _).symm
  rw [hfun] at h2
  exact initialForm_mem_adjoin_of_tauZ_eq_zero' hinjp (hsub z hz) g (h2.symm.trans h1)

end Descent

section LiftSeparable

variable {R R' : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CommRing R']
  [IsRegularLocalRing R'] [IsDomain R'] {α : R →+* R'} [IsLocalHom α] {P : Ideal R}
  {T : MonoidalTransform R P}

/-- The canonical lift `R̃₁` of a monoidal transform `R₁` residually separable algebraic over `R`
is residually separable algebraic over `R̃` (Lemma 4 (2): the residue field of `R̃₁` is generated by
those of `R₁` and `R̃`). -/
theorem BaseChangeLift.isResiduallySeparableAlgebraic_toRing [P.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] (L : BaseChangeLift α T)
    (hα : RingHom.MapsRSOP α)
    (hsepT : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing) :
    haveI := L.isRegularLocalRing hα
    RingHom.IsResiduallySeparableAlgebraic (R := R') (R' := L.T'.ring) L.T'.toRing := by
  have _ := L.isRegularLocalRing hα
  have _ := L.isLocalHom_toRing
  obtain ⟨-, -, h2, -⟩ := RingHom.MapsRSOP.canonicalLift_properties α hα
    (inferInstance : P.IsPrime) inferInstance
  exact isResiduallySeparableAlgebraic_of_closure_eq_top T.toRing α L.β L.T'.toRing
    L.isCanonicalLift.comm.symm hsepT
    (by rw [Set.union_comm]; exact (h2 T L.T' L.β L.isCanonicalLift).2.2.2.2)

end LiftSeparable

section OneStep

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- **The one-step theorem in the proof of Theorem 8** (p. 264), along the printed route.
Notation: `(S; z₁, …, z_τ)` a regular `τ`-frame of `R` for `J` (`hF`), `(f₁, …, f_m)` a
normalized standard base of `J` with respect to it, `Q` a permissible center for `J` with
`(z)R ⊆ Q`, `R₁` a monoidal transform of `R` with center `Q` which is residually separable algebraic
over `R`, `J₁` the strict transform of `J` in `R₁`, with `ν*(J₁) = ν*(J)` and
`τ^{(a)}(J₁) = τ^{(a)}(J)`, and `(S₁; w₁, …, w_τ)` a frame transform of `(S; z)` in `R₁` with
denominator `x ∈ Q ∩ S` which is a regular `τ`-frame for `J₁`.  With `ν_j = ν^{(j)}(J)` and
`g_j = x^{-ν_j} f_j`, "`(g₁, …, g_m)` is a normalized standard base of `J₁` with respect to
`(S₁; w₁, …, w_τ)`", and (the second assertion of the paper's induction)
"`τ_{(w)_a}(g₁, …, g_{m_a}) = 0`": the initial form of `g_j` lies in `k[W₁, …, W_{τ_a}]` for every
`j` with `ν_M(f_j) ≤ μ^{(a)}(J)`.

The proof is the printed one: "To prove that `(g₁, …, g_m)` is a normalized standard base of `J₁`,
we may assume that `R` is complete with respect to the topology defined by the powers of
`(z₁, …, z_τ)R`, so that `R = S{z₁, …, z_τ}`."  The reduction is the base change of §8 for the
identity `S → S` (`RegularFrame.baseChange`, `R̃ = S⟦z⟧`, `α = RegularFrame.baseChangeHom`), with
the canonical lift `R̃₁` of `R₁` (`BaseChangeLift`) and the lifted frame transform
(`RegularFrame.FrameTransform.exists_baseChange`); the complete case is
`isNormalizedStandardBase_strictTransform_of_mvPowerSeries` (the induction on `a` with the partial
frames `S^{(a)}`).  Gap filled (the paper does not carry out the reduction): the hypotheses hold for
the lifted data (`RegularFrame.isRegularTauFrame_of_map` for both frames, the invariance of `ν*`,
`τ*`, of normalization, standard bases, permissibility and the strict transform), and the
conclusions descend: standard bases along the faithfully flat `β : R₁ → R̃₁`
(`isStandardBase_iff_isStandardBase_map`), `τ_{(w)}` and `τ_{(w)_a}` by `tauZ_map`
(`initialForm_mem_framePrefixSubalgebra_of_map`), and normalization through the canonical map
`S₁ → S̃₁` of the coefficient rings, as for Lemma 20 (`RegularFrame.FrameTransform.exists_gamma`,
`RegularFrame.FrameTransform.frameESet_lift`, `RegularFrame.FrameTransform.expCoeff_lift`). -/
theorem isNormalizedStandardBase_strictTransform_of_isRegularTauFrame [Hironaka.HironakaCitedResults.{u}] (J : Ideal R)
    (F : RegularFrame R) (hF : F.IsRegularTauFrame J) (Q : Ideal R) [Q.IsPrime]
    (hQperm : IsPermissibleCenter R J Q)
    (hzQ : F.idealZ ≤ Q) (T : MonoidalTransform R Q) [IsLocalHom T.toRing]
    [IsRegularLocalRing T.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing)
    (x : F.S) (hxQ : algebraMap F.S R x ∈ Q)
    (hx : Q.map T.toRing = Ideal.span {T.toRing (algebraMap F.S R x)})
    (FT : F.FrameTransform T) (hFTx : FT.x = T.toRing (algebraMap F.S R x))
    (hnu : nuStar T.ring (strictTransformIdeal T J) = nuStar R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau T.ring (strictTransformIdeal T J) a = tau R J a)
    (hF₁ : FT.toRegularFrame.IsRegularTauFrame (strictTransformIdeal T J))
    {m : ℕ} (f : Fin m → R) (hf : F.IsNormalizedStandardBase J f)
    (hfQ : ∀ j : Fin m, Ideal.ordElem Q (f j) = nuI R J (j : ℕ).succPNat)
    (ν : Fin m → ℕ) (hν : ∀ j, (ν j : ℕ∞) = nuI R J (j : ℕ).succPNat)
    (g : Fin m → T.ring)
    (hg : ∀ j, T.toRing (algebraMap F.S R x) ^ ν j * g j = T.toRing (f j)) :
    FT.toRegularFrame.IsNormalizedStandardBase (strictTransformIdeal T J) g ∧
      ∀ a, 1 ≤ a → a ≤ t R J → ∀ j : Fin m,
        Ideal.ordElem (maximalIdeal R) (f j) ≤ (mu R J a : ℕ∞) →
          initialForm (maximalIdeal T.ring) (g j) ∈ Algebra.adjoin (T.ring ⧸ maximalIdeal T.ring)
            (Set.range fun q : {q : Fin F.r // (q : ℕ) < tau R J a} => frameForm FT.w q.1) := by
  classical
  have hnuI : ∀ i, nuI T.ring (strictTransformIdeal T J) i = nuI R J i :=
    fun i => congrFun (toLex.injective hnu) i
  -- the case `m = 0`
  by_cases hm : m = 0
  · subst hm
    refine ⟨⟨?_, fun j => j.elim0, fun j => j.elim0⟩, fun a _ _ j => j.elim0⟩
    obtain ⟨m₂, G, hG⟩ := exists_isStandardBase (strictTransformIdeal T J)
    have : m₂ = 0 := length_eq_of_nuI_eq hG hf.1 (fun i => hnuI i)
    subst this
    have : g = G := funext fun j => j.elim0
    rw [this]
    exact hG
  have ht1 : 1 ≤ t R J := one_le_t_of_isStandardBase hf.1 (Nat.pos_of_ne_zero hm)
  have hJQ : J ≤ Q := by
    rcases hQperm with hQtop | ⟨-, hJQ, -, -⟩
    · exact absurd hQtop (Ideal.IsPrime.ne_top ‹Q.IsPrime›)
    · exact hJQ
  have hQreg : IsRegularLocalRing (R ⧸ Q) := by
    rcases hQperm with hQtop | ⟨-, -, hreg, -⟩
    · exact absurd hQtop (Ideal.IsPrime.ne_top ‹Q.IsPrime›)
    · exact hreg
  -- "we may assume that `R` is complete … so that `R = S{z₁, …, z_τ}`": the base change for the
  -- identity `a = id : S → S`, `R̃ = S⟦z⟧`
  set a : F.S →+* F.S := RingHom.id F.S with hadef
  have ha : RingHom.MapsRSOP a := RingHom.mapsRSOP_id F.S
  have hsepa : RingHom.IsResiduallySeparableAlgebraic a :=
    RingHom.isResiduallySeparableAlgebraic_of_residueField_surjective (by
      intro c
      obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective c
      exact ⟨IsLocalRing.residue F.S s, by rw [ResidueField.map_residue]; rfl⟩)
  set α := F.baseChangeHom a with hαdef
  have hα : RingHom.MapsRSOP α := F.mapsRSOP_baseChangeHom a ha
  have hsepα : RingHom.IsResiduallySeparableAlgebraic α :=
    F.isResiduallySeparableAlgebraic_baseChangeHom a hsepa
  obtain ⟨L⟩ := BaseChangeLift.nonempty hα T
  obtain ⟨hQp, hQq⟩ := RingHom.MapsRSOP.isPrime_map_and_isRegularLocalRing_quotient hα
    (inferInstance : Q.IsPrime) hQreg
  have := hQp
  have := hQq
  have := L.isRegularLocalRing hα
  have := L.isLocalHom_toRing
  have hβ := L.mapsRSOP_β hα hsepα
  have hsepβ := (L.isResiduallySeparableAlgebraic_β hα hsepα).isResiduallySeparable
  obtain ⟨FT', hFT'x, hFT'w⟩ := RegularFrame.FrameTransform.exists_baseChange ha L FT x hxQ hx hFTx
  have hFT'w' : FT'.w = fun j => L.β (FT.w j) := funext hFT'w
  have hνnu : ∀ j : ℕ+, nuI (MvPowerSeries (Fin F.r) F.S) (J.map α) j = nuI R J j :=
    fun j => (nuI_map_eq_of_mapsRSOP α hα J j).symm
  obtain ⟨htα, hτα, -⟩ := tauStar_map α hα hsepα.isResiduallySeparable J
  have hstrict := L.strictTransformIdeal_map hα J hJQ
  have hxcomm : L.T'.toRing (algebraMap (RegularFrame.mvPowerSeries F.S F.r).S
      (MvPowerSeries (Fin F.r) F.S) (a x)) =
      L.β (T.toRing (algebraMap F.S R x)) := L.toRing_algebraMap_baseChange x
  -- the hypotheses for `R̃`
  have hfR : ∀ j, initialForm (maximalIdeal R) (f j) ∈ Set.range (frameAlgHom F.z) := fun j => by
    have h := hf.2.1 j
    unfold RegularFrame.assocSubalgebra Hironaka.assocSubalgebra at h
    rwa [Algebra.adjoin_range_eq_range_aeval] at h
  have hf' : (RegularFrame.mvPowerSeries F.S F.r).IsNormalizedStandardBase (J.map α)
      (fun j => α (f j)) := by
    refine ⟨(isStandardBase_iff_isStandardBase_map α hα J f).mp hf.1, fun j => ?_,
      fun j => F.isNormalizedBy_baseChangeHom ha _ (fun l => hfR _) (f j) (hf.2.2 j)⟩
    obtain ⟨q, hq⟩ := hfR j
    rw [initialForm_map_of_mapsRSOP α hα, ← hq,
      grMapMax_frameAlgHom α hα F.z (F.baseChange F.S).z
        (fun l => (F.baseChangeHom_z' a l).symm) q]
    unfold RegularFrame.assocSubalgebra Hironaka.assocSubalgebra
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact ⟨_, rfl⟩
  have hF' : (RegularFrame.mvPowerSeries F.S F.r).IsRegularTauFrame (J.map α) :=
    RegularFrame.isRegularTauFrame_of_map α hα hsepα.isResiduallySeparable F _ J ht1 rfl
      (fun j => (F.baseChangeHom_z' a j).symm) hF
  have ht₁ : 1 ≤ t T.ring (strictTransformIdeal T J) := by
    rw [t_congr_of_nuStar_eq hnu]; exact ht1
  have hF₁' : FT'.toRegularFrame.IsRegularTauFrame (strictTransformIdeal L.T' (J.map α)) := by
    rw [hstrict]
    exact RegularFrame.isRegularTauFrame_of_map L.β hβ hsepβ FT.toRegularFrame
      FT'.toRegularFrame _ ht₁ rfl (fun j => hFT'w j) hF₁
  have hnu' : nuStar L.T'.ring (strictTransformIdeal L.T' (J.map α)) =
      nuStar (MvPowerSeries (Fin F.r) F.S) (J.map α) := by
    rw [L.nuStar_strictTransformIdeal hα hsepα J hJQ, hnu]
    exact nuStar_map_eq_of_mapsRSOP α hα J
  have htau' : ∀ b, 1 ≤ b → b ≤ t _ (J.map α) →
      tau L.T'.ring (strictTransformIdeal L.T' (J.map α)) b = tau _ (J.map α) b := by
    intro b hb hbt
    rw [htα] at hbt
    rw [hstrict, tau_map_of_mapsRSOP L.β hβ hsepβ _ b hb, htau b hb hbt, hτα b hb hbt]
  have hsep' := L.isResiduallySeparableAlgebraic_toRing hα hsep
  obtain ⟨hnorm', hblk'⟩ := isNormalizedStandardBase_strictTransform_of_mvPowerSeries (J.map α)
    hF' (Q.map α) ((Hironaka.isPermissibleCenter_map_iff α hα J Q hJQ).2.2.2.mp hQperm)
    (by
      rw [RegularFrame.idealZ, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, ← F.baseChangeHom_z' a j]
      exact Ideal.mem_map_of_mem _ (hzQ (Ideal.subset_span ⟨j, rfl⟩)))
    L.T' hsep' (a x) (F.algebraMap_mem_map_baseChangeHom x hxQ) (L.map_eq_span_baseChange x hx)
    FT' hFT'x hnu' htau' hF₁' (fun j => α (f j)) hf'
    (fun j => by rw [ordElem_map_ideal_of_mapsRSOP α hα Q, hfQ j, hνnu])
    ν (fun j => by rw [hν j, hνnu]) (fun j => L.β (g j))
    (fun j => by rw [hxcomm, ← map_pow, ← map_mul, hg j, L.toRing_baseChangeHom])
  -- the conclusions descend from `R̃₁` to `R₁`
  rw [hstrict] at hnorm'
  have hassoc : ∀ j, initialForm (maximalIdeal T.ring) (g j) ∈
      FT.toRegularFrame.assocSubalgebra := fun j => by
    have h := hnorm'.2.1 j
    have e1 : FT'.toRegularFrame.assocSubalgebra =
        framePrefixSubalgebra FT'.w FT'.toRegularFrame.r :=
      assocSubalgebra_eq_framePrefixSubalgebra _ _ le_rfl fun l => congrArg _ (Fin.ext rfl)
    rw [e1] at h
    have h2 := initialForm_mem_framePrefixSubalgebra_of_map L.β hβ hsepβ FT.w
      FT.toRegularFrame.z_injective FT.extends_rsop FT'.w FT'.toRegularFrame.z_injective
      FT'.extends_rsop hFT'w _ (g j) h
    have e2 : FT.toRegularFrame.assocSubalgebra =
        framePrefixSubalgebra FT.w FT'.toRegularFrame.r :=
      assocSubalgebra_eq_framePrefixSubalgebra _ _ le_rfl fun l => congrArg _ (Fin.ext rfl)
    rw [e2]
    exact h2
  -- normalization descends through the canonical map `γ : S₁ → S̃₁`
  obtain ⟨γ, hγ⟩ := FT.exists_gamma (RingHom.MapsRSOP.injective a ha) L FT'
  have hβinj : Function.Injective FT.β := fun s t h =>
    FT.quot_bijective.1 (by rw [RingHom.comp_apply, RingHom.comp_apply, h])
  have hγinj : Function.Injective γ := fun s t h =>
    hβinj (L.injective_β hα (by rw [← hγ, ← hγ, h]))
  have hnorm : ∀ k : Fin m, FT.toRegularFrame.IsNormalizedBy
      (fun l : Fin (k : ℕ) => g (Fin.castLE k.2.le l)) (g k) := fun k => by
    have hginit : ∀ l : Fin (k : ℕ), initialForm (maximalIdeal T.ring) (g (Fin.castLE k.2.le l)) ∈
        Set.range (frameAlgHom FT.w) := fun l => by
      have h := hassoc (Fin.castLE k.2.le l)
      unfold RegularFrame.assocSubalgebra Hironaka.assocSubalgebra at h
      rwa [Algebra.adjoin_range_eq_range_aeval] at h
    have hE := FT.frameESet_lift L hβ FT' hFT'w _ hginit
    rw [FT.toRegularFrame.isNormalizedBy_iff_expCoeff]
    have hn' := (FT'.toRegularFrame.isNormalizedBy_iff_expCoeff _ _).mp (hnorm'.2.2 k)
    intro A hA
    have h1' := hn' A (hE ▸ hA)
    have h2 := FT.expCoeff_lift L FT' γ hγ hFT'w (g k) (Finsupp.equivFunOnFinite.symm A)
    exact hγinj ((h2.symm.trans h1').trans (map_zero γ).symm)
  refine ⟨⟨(isStandardBase_iff_isStandardBase_map L.β hβ _ g).mpr hnorm'.1, hassoc, hnorm⟩,
    fun b hb hbt j hj => ?_⟩
  -- the second assertion descends
  have hj' : Ideal.ordElem (maximalIdeal _) (α (f j)) ≤ (mu _ (J.map α) b : ℕ∞) := by
    rw [ordElem_map_of_mapsRSOP α hα, mu_map_of_mapsRSOP α hα]
    exact hj
  have h := hblk' b hb (by rw [htα]; exact hbt) j hj'
  rw [hτα b hb hbt] at h
  exact initialForm_mem_framePrefixSubalgebra_of_map L.β hβ hsepβ FT.w
    FT.toRegularFrame.z_injective FT.extends_rsop FT'.w FT'.toRegularFrame.z_injective
    FT'.extends_rsop hFT'w _ (g j) h

end OneStep

end Hironaka
