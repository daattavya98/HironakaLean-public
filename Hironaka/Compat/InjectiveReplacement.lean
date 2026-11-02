/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Hironaka.Compat.AcyclicClass

/-!
# Injective replacements of `ℕ`-indexed cochain complexes

For an abelian category `D`:

* `HomotopyCategory.bijective_quotient_map_comp`: if `s : M ⟶ M'` is a quasi-isomorphism of `ℕ`-indexed cochain
  complexes and `K` is a complex of injective objects, then precomposition with `s` is a bijection
  `(M' ⟶ K) ≃ (M ⟶ K)` in the homotopy category (`K` is K-injective; we use Mathlib's
  `CochainComplex.IsKInjective` for the extension of `K` by zero to `ℤ`, and the derived category as a tool);
* `CochainComplex.exists_mono_quasiIso_injective_nat` (`D` with enough injectives): every `ℕ`-indexed cochain complex
  `M` admits a degreewise monomorphic quasi-isomorphism `M ⟶ K` to a complex of injective objects.  (Mathlib's
  `CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective` gives a quasi-isomorphism of the extension of
  `M` to `ℤ` to a complex of injectives in degrees `≥ 0`; we restrict it to `ℕ` and make it a monomorphism by adding
  an acyclic complex of injectives built from injective hulls of the `M.X n`.)

General homological algebra, used for the Leray edge maps (`Hironaka.Compat.LerayEdgeAbstract`).
-/

@[expose] public section

open CategoryTheory Limits ZeroObject HomologicalComplex

namespace CategoryTheory

variable {D : Type*} [Category* D] [Abelian D]

/-- Precomposition with an isomorphism is bijective. -/
theorem bijective_comp_left_of_isIso {C : Type*} [Category* C] {X Y Z : C} (i : X ⟶ Y) [IsIso i] :
    Function.Bijective (fun g : Y ⟶ Z => i ≫ g) :=
  Function.bijective_iff_has_inverse.2 ⟨fun y => inv i ≫ y, fun x => by simp, fun y => by simp⟩

/-- **Lifting along quasi-isomorphisms into complexes of injectives.**  If `s : M ⟶ M'` is a quasi-isomorphism of
`ℕ`-indexed cochain complexes and `K` consists of injective objects, then every morphism `M ⟶ K` in the homotopy
category factors uniquely through `s`. -/
theorem HomotopyCategory.bijective_quotient_map_comp {M M' K : CochainComplex D ℕ} (s : M ⟶ M') [QuasiIso s]
    [∀ n, Injective (K.X n)] :
    Function.Bijective (fun g : (HomotopyCategory.quotient D (ComplexShape.up ℕ)).obj M' ⟶
        (HomotopyCategory.quotient D (ComplexShape.up ℕ)).obj K =>
      (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map s ≫ g) := by
  let e := ComplexShape.embeddingUpNat
  let Φ := e.extendHomotopyFunctor D
  have hΦ : Φ.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful Φ
  let := HasDerivedCategory.standard D
  have hs : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient D _).map (extendMap s e))) := by
    rw [DerivedCategory.isIso_Qh_map_iff]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff (extendMap s e)).2
      ((quasiIso_extendMap_iff s e).2 inferInstance)
  have hb₁ := CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient D _).obj (M'.extend e)) (K.extend e)
  have hb₂ := CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient D _).obj (M.extend e)) (K.extend e)
  have h1 : Function.Bijective (fun g : (HomotopyCategory.quotient D _).obj (M'.extend e) ⟶
      (HomotopyCategory.quotient D _).obj (K.extend e) =>
        (HomotopyCategory.quotient D _).map (extendMap s e) ≫ g) := by
    rw [← Function.Bijective.of_comp_iff' hb₂]
    have : (DerivedCategory.Qh.map ∘ fun g : (HomotopyCategory.quotient D _).obj (M'.extend e) ⟶
        (HomotopyCategory.quotient D _).obj (K.extend e) =>
          (HomotopyCategory.quotient D _).map (extendMap s e) ≫ g) =
        (fun y => DerivedCategory.Qh.map ((HomotopyCategory.quotient D _).map (extendMap s e)) ≫ y) ∘
          DerivedCategory.Qh.map := by
      funext g
      simp
    rw [this]
    exact (bijective_comp_left_of_isIso _).comp hb₁
  rw [← Function.Bijective.of_comp_iff' (hΦ.map_bijective _ _)]
  have : (Φ.map ∘ fun g : (HomotopyCategory.quotient D (ComplexShape.up ℕ)).obj M' ⟶
      (HomotopyCategory.quotient D (ComplexShape.up ℕ)).obj K =>
        (HomotopyCategory.quotient D (ComplexShape.up ℕ)).map s ≫ g) =
      (fun g => Φ.map ((HomotopyCategory.quotient D _).map s) ≫ g) ∘ Φ.map := by
    funext g
    simp
  rw [this]
  exact h1.comp (hΦ.map_bijective _ _)

/-- A morphism between zero objects is an isomorphism. -/
theorem isIso_of_isZero {X Y : D} (f : X ⟶ Y) (hX : IsZero X) (hY : IsZero Y) : IsIso f :=
  ⟨⟨0, hX.eq_of_src _ _, hY.eq_of_src _ _⟩⟩

/-- Every `ℕ`-indexed cochain complex admits a quasi-isomorphism to a complex of injective objects. -/
theorem CochainComplex.exists_quasiIso_injective_nat [EnoughInjectives D] (M : CochainComplex D ℕ) :
    ∃ (K : CochainComplex D ℕ) (q : M ⟶ K), QuasiIso q ∧ ∀ n, Injective (K.X n) := by
  let e := ComplexShape.embeddingUpNat
  obtain ⟨L, i, hi, hL, hL0⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective (M.extend e) 0
  let K := L.restriction e
  have hlift : e.HasLift (𝟙 K) := by
    intro j hj i' hi'
    have hj0 : j = 0 := by
      cases j with
      | zero => rfl
      | succ j => exact absurd (by simp [e] : (ComplexShape.up ℤ).Rel (e.f j) (e.f (j + 1))) (hj.2 j)
    subst hj0
    apply IsZero.eq_of_src
    exact L.isZero_of_isStrictlyGE 0 i' (by simp [e] at hi'; lia)
  let ψ : L ⟶ K.extend e := e.liftExtend (𝟙 K) hlift
  have hψ : IsIso ψ := by
    have : ∀ i', IsIso (ψ.f i') := by
      intro i'
      by_cases h : ∃ j, e.f j = i'
      · obtain ⟨j, hj⟩ := h
        exact (e.isIso_liftExtend_f_iff (𝟙 K) hlift hj).2 (inferInstanceAs (IsIso (𝟙 (K.X j))))
      · refine isIso_of_isZero _ ?_ (K.isZero_extend_X e i' (by simpa using h))
        refine L.isZero_of_isStrictlyGE 0 i' ?_
        by_contra hc
        exact h ⟨i'.toNat, by simp [e]; lia⟩
    exact HomologicalComplex.Hom.isIso_of_components ψ
  let q := (e.fullyFaithfulExtendFunctor D).preimage (i ≫ ψ)
  have hq : extendMap q e = i ≫ ψ := (e.fullyFaithfulExtendFunctor D).map_preimage (i ≫ ψ)
  refine ⟨K, q, ?_, fun n => hL (e.f n)⟩
  rw [← quasiIso_extendMap_iff q e, hq]
  infer_instance

section MonoReplacement

variable [EnoughInjectives D] (M : CochainComplex D ℕ)

/-- Auxiliary: `0` in degree `0`, the injective hull of `M.X n` in degree `n ≥ 1`. -/
noncomputable def monoAuxQ' : ℕ → D
  | 0 => 0
  | n + 1 => Injective.under (M.X (n + 1))

/-- Auxiliary: the identity of the injective hull of `M.X (n + 1)`, seen as a map to `monoAuxQ' M (n + 1)`. -/
noncomputable def monoAuxσ (n : ℕ) : Injective.under (M.X (n + 1)) ⟶ monoAuxQ' M (n + 1) := 𝟙 _

instance (n : ℕ) : IsIso (monoAuxσ M n) := inferInstanceAs (IsIso (𝟙 (Injective.under (M.X (n + 1)))))

/-- Auxiliary: the maps `M.X n ⟶ monoAuxQ' M n`. -/
noncomputable def monoAuxι' : ∀ n, M.X n ⟶ monoAuxQ' M n
  | 0 => 0
  | n + 1 => Injective.ι (M.X (n + 1)) ≫ monoAuxσ M n

/-- Unfolding `monoAuxι'` in positive degrees. -/
theorem monoAuxι'_succ (n : ℕ) : monoAuxι' M (n + 1) = Injective.ι (M.X (n + 1)) ≫ monoAuxσ M n := rfl

instance (n : ℕ) : Injective (monoAuxQ' M n) := by
  cases n with
  | zero => exact (inferInstance : Injective (0 : D))
  | succ n => exact (inferInstance : Injective (Injective.under (M.X (n + 1))))

/-- The acyclic complex of injectives `E^n = I(M^{n+1}) ⊞ I'(M^n)`, `d(x, y) = (0, x)` (a sum of disks on the
injective hulls `I(M^{n+1})` of the `M^{n+1}`). -/
noncomputable abbrev monoAuxE : CochainComplex D ℕ where
  X n := Injective.under (M.X (n + 1)) ⊞ monoAuxQ' M n
  d i j := if h : i + 1 = j then
      biprod.fst ≫ monoAuxσ M i ≫ biprod.inr ≫
        eqToHom (congrArg (fun n => Injective.under (M.X (n + 1)) ⊞ monoAuxQ' M n) h) else 0
  shape i j hij := by simp only [dite_eq_right_iff]; exact fun h => absurd h hij
  d_comp_d' i j k hij hjk := by
    obtain rfl : j = i + 1 := hij.symm
    obtain rfl : k = i + 1 + 1 := hjk.symm
    simp

/-- The differential of `monoAuxE M`. -/
theorem monoAuxE_d (n : ℕ) : (monoAuxE M).d n (n + 1) = biprod.fst ≫ monoAuxσ M n ≫ biprod.inr := by
  simp

omit [EnoughInjectives D] in
/-- The short complex `A ⊞ W ⟶ B ⊞ A' ⟶ C ⊞ B'` with maps `(x, w) ↦ (0, σ x)`, `(y, a) ↦ (0, σ' y)` (`σ`, `σ'`
isomorphisms) is exact. -/
theorem exact_biprod_shift {A W B A' C B' : D} (σ : A ⟶ A') (σ' : B ⟶ B') [IsIso σ] [IsIso σ']
    {hfg : ((biprod.fst : A ⊞ W ⟶ A) ≫ σ ≫ (biprod.inr : A' ⟶ B ⊞ A')) ≫
      ((biprod.fst : B ⊞ A' ⟶ B) ≫ σ' ≫ (biprod.inr : B' ⟶ C ⊞ B')) = 0} :
    (ShortComplex.mk _ _ hfg).Exact := by
  refine exact_of_factor (e := biprod.fst) (i := σ ≫ biprod.inr) (p := biprod.fst) (m := σ' ≫ biprod.inr)
    _ _ rfl rfl (hip := by simp) ?_
  refine exact_of_factor (e := σ) (i := biprod.inr) (p := biprod.fst) (m := 𝟙 _) _ _ rfl (by simp)
    (hip := by simp) ?_
  exact ShortComplex.exact_of_f_is_kernel _ (biprod.isKernelFstKernelFork B A')

/-- The complex `monoAuxE M` is acyclic. -/
theorem monoAuxE_acyclic : (monoAuxE M).Acyclic := by
  intro k
  cases k with
  | zero =>
    rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp)]
    refine (ShortComplex.exact_iff_mono _ ((monoAuxE M).shape 0 0 (by simp))).2 ?_
    show Mono ((monoAuxE M).d 0 1)
    rw [monoAuxE_d]
    have hz : IsZero (monoAuxQ' M 0) := isZero_zero D
    have : Mono (biprod.fst : Injective.under (M.X (0 + 1)) ⊞ monoAuxQ' M 0 ⟶ _) :=
      ⟨fun g h hgh => biprod.hom_ext _ _ hgh (hz.eq_of_tgt _ _)⟩
    exact mono_comp _ _
  | succ m =>
    rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 2) (by simp) (by simp)]
    refine ShortComplex.exact_of_iso ?_ (exact_biprod_shift (W := monoAuxQ' M m)
      (C := Injective.under (M.X (m + 1 + 1 + 1))) (monoAuxσ M m) (monoAuxσ M (m + 1))
      (hfg := by simp))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans ((monoAuxE_d M m).trans (Category.comp_id _).symm))
      ((Category.id_comp _).trans ((monoAuxE_d M (m + 1)).trans (Category.comp_id _).symm))

/-- The map `M ⟶ monoAuxE M`, `m ↦ (ι(d m), ι'(m))`. -/
noncomputable def monoAuxj : M ⟶ monoAuxE M where
  f n := biprod.lift (M.d n (n + 1) ≫ Injective.ι (M.X (n + 1))) (monoAuxι' M n)
  comm' i j hij := by
    obtain rfl : j = i + 1 := by simpa using hij.symm
    rw [monoAuxE_d]
    refine biprod.hom_ext (X := Injective.under (M.X (i + 1 + 1))) (Y := monoAuxQ' M (i + 1)) _ _ ?_ ?_
    · simp
    · simp [monoAuxι'_succ]

/-- In positive degrees, `monoAuxj M` is a monomorphism. -/
theorem mono_monoAuxj_f_succ (n : ℕ) : Mono ((monoAuxj M).f (n + 1)) := by
  have : Mono (biprod.lift (M.d (n + 1) (n + 1 + 1) ≫ Injective.ι (M.X (n + 1 + 1))) (monoAuxι' M (n + 1)) ≫
      biprod.snd) := by
    rw [biprod.lift_snd, monoAuxι'_succ]
    infer_instance
  exact @mono_of_mono _ _ _ _ _ _ biprod.snd this

end MonoReplacement

/-- Every `ℕ`-indexed cochain complex `M` admits a monomorphic quasi-isomorphism to a complex of injective objects. -/
theorem CochainComplex.exists_mono_quasiIso_injective_nat [EnoughInjectives D] (M : CochainComplex D ℕ) :
    ∃ (K : CochainComplex D ℕ) (q : M ⟶ K), Mono q ∧ QuasiIso q ∧ ∀ n, Injective (K.X n) := by
  obtain ⟨K, q, hq, hK⟩ := CochainComplex.exists_quasiIso_injective_nat M
  let E := monoAuxE M
  let q' : M ⟶ K ⊞ E := biprod.lift q (monoAuxj M)
  have hinj : ∀ n, Injective ((K ⊞ E).X n) := fun n =>
    Injective.of_iso (HomologicalComplex.biprodXIso K E n).symm inferInstance
  -- `biprod.fst : K ⊞ E ⟶ K` is a quasi-isomorphism, `E` being acyclic
  have hfst : QuasiIso (biprod.fst : K ⊞ E ⟶ K) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have hE : IsZero (E.homology n) := (monoAuxE_acyclic M n).isZero_homology
    refine ⟨homologyMap (biprod.inl : K ⟶ K ⊞ E) n, ?_, ?_⟩
    · have h1 : homologyMap (biprod.fst : K ⊞ E ⟶ K) n ≫ homologyMap biprod.inl n +
          homologyMap (biprod.snd : K ⊞ E ⟶ E) n ≫ homologyMap biprod.inr n = 𝟙 _ := by
        rw [← homologyMap_comp, ← homologyMap_comp, ← homologyMap_add, biprod.total, homologyMap_id]
      rw [← h1, hE.eq_of_tgt (homologyMap (biprod.snd : K ⊞ E ⟶ E) n) 0, zero_comp, add_zero]
    · rw [← homologyMap_comp, biprod.inl_fst, homologyMap_id]
  have hq'q : q' ≫ biprod.fst = q := biprod.lift_fst _ _
  have hq' : QuasiIso q' := by
    have : QuasiIso (q' ≫ biprod.fst) := by rw [hq'q]; exact hq
    exact quasiIso_of_comp_right q' biprod.fst
  refine ⟨K ⊞ E, q', ?_, hq', hinj⟩
  refine HomologicalComplex.mono_of_mono_f _ fun n => ?_
  cases n with
  | succ n =>
    have : Mono (q'.f (n + 1) ≫ (biprod.snd : K ⊞ E ⟶ E).f (n + 1)) := by
      rw [← HomologicalComplex.comp_f, biprod.lift_snd]
      exact mono_monoAuxj_f_succ M n
    exact mono_of_mono _ ((biprod.snd : K ⊞ E ⟶ E).f (n + 1))
  | zero =>
    refine Preadditive.mono_of_cancel_zero _ fun {T} x hx => ?_
    have hx₁ : x ≫ q.f 0 = 0 := by
      have := hx =≫ (biprod.fst : K ⊞ E ⟶ K).f 0
      rwa [Category.assoc, ← HomologicalComplex.comp_f, hq'q, zero_comp] at this
    have hj : x ≫ (monoAuxj M).f 0 = 0 := by
      have := hx =≫ (biprod.snd : K ⊞ E ⟶ E).f 0
      rwa [Category.assoc, ← HomologicalComplex.comp_f, biprod.lift_snd, zero_comp] at this
    have hj' : x ≫ biprod.lift (M.d 0 1 ≫ Injective.ι (M.X 1)) (monoAuxι' M 0) = 0 := hj
    have hx₂ : x ≫ M.d 0 1 = 0 := by
      have := hj' =≫ biprod.fst
      rw [Category.assoc, biprod.lift_fst, zero_comp, ← Category.assoc] at this
      exact (cancel_mono (Injective.ι (M.X 1))).1 (by rw [this, zero_comp])
    have hπM := M.isIso_homologyπ 0 0 (by simp) (M.shape _ _ (by simp))
    have hπK := K.isIso_homologyπ 0 0 (by simp) (K.shape _ _ (by simp))
    have hH : IsIso (homologyMap q 0) := (quasiIsoAt_iff_isIso_homologyMap q 0).1 (hq.quasiIsoAt 0)
    have hmono : Mono (cyclesMap q 0) := by
      have : cyclesMap q 0 ≫ K.homologyπ 0 = M.homologyπ 0 ≫ homologyMap q 0 :=
        (homologyπ_naturality q 0).symm
      have : Mono (cyclesMap q 0 ≫ K.homologyπ 0) := by rw [this]; infer_instance
      exact mono_of_mono _ (K.homologyπ 0)
    let x' := M.liftCycles x 1 (by simp) hx₂
    have hx' : x' = 0 := by
      refine (cancel_mono (cyclesMap q 0)).1 ?_
      refine (cancel_mono (K.iCycles 0)).1 ?_
      simp [x', hx₁]
    have : x = x' ≫ M.iCycles 0 := by simp [x']
    rw [this, hx', zero_comp]

end CategoryTheory
