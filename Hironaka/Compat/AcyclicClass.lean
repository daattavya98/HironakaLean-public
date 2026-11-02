/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# Classes of objects acyclic for an additive functor

Let `G : D ⥤ E` be an additive functor between abelian categories.  A class `P` of objects of `D` is *acyclic for `G`*
(`Functor.IsAcyclicClass`) if

* every injective object is in `P`;
* `G` maps a short exact sequence `0 → X₁ → X₂ → X₃ → 0` with `X₁ ∈ P` to a short exact sequence;
* if `0 → X₁ → X₂ → X₃ → 0` is short exact and `X₁, X₂ ∈ P`, then `X₃ ∈ P`.

(The example we have in mind: the flasque `O_X`-modules, for `G` a direct image functor; Hartshorne III.2.4, II Ex. 1.16.)

We prove, by splicing into short exact sequences (no long exact sequence of derived functors is needed):

* `Functor.IsAcyclicClass.acyclic_map`: `G` maps an acyclic `ℕ`-indexed cochain complex of objects of `P` to an
  acyclic complex;
* `Functor.IsAcyclicClass.quasiIso_map_of_mono`: `G` maps a degreewise monomorphic quasi-isomorphism between
  `ℕ`-indexed cochain complexes of objects of `P` to a quasi-isomorphism;
* `Functor.IsAcyclicClass.isZero_rightDerived`: the higher right derived functors of `G` vanish on `P`.

This is general homological algebra, used tacitly by the paper (Ch. 0 §5, consequence (2), p. 145) through the Leray
spectral sequence; see `Hironaka.Compat.LerayEdgeAbstract`.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

namespace CategoryTheory

variable {D E : Type*} [Category* D] [Category* E] [Abelian D] [Abelian E]

omit [Abelian D] in
/-- A morphism out of a zero object is a monomorphism. -/
theorem mono_of_isZero_src {X Y : D} (hX : IsZero X) (f : X ⟶ Y) : Mono f :=
  ⟨fun g h _ => hX.eq_of_tgt g h⟩

/-- If `f = e ≫ i` with `e` epi and `g = p ≫ m` with `m` mono, then `(f, g)` is exact if `(i, p)` is. -/
theorem exact_of_factor {A Z B W C : D} {e : A ⟶ Z} {i : Z ⟶ B} {p : B ⟶ W} {m : W ⟶ C} [Epi e] [Mono m]
    (f : A ⟶ B) (g : B ⟶ C) (hf : e ≫ i = f) (hg : p ≫ m = g) {hip : i ≫ p = 0} {hfg : f ≫ g = 0}
    (h : (ShortComplex.mk i p hip).Exact) : (ShortComplex.mk f g hfg).Exact := by
  let S₁ : ShortComplex D := ShortComplex.mk f p (by rw [← hf, Category.assoc, hip, comp_zero])
  let φ₁ : S₁ ⟶ ShortComplex.mk i p hip :=
    { τ₁ := e, τ₂ := 𝟙 _, τ₃ := 𝟙 _, comm₁₂ := by simp [S₁, hf] }
  let φ₂ : S₁ ⟶ ShortComplex.mk f g hfg :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := m, comm₂₃ := by simp [S₁, hg] }
  have : Epi φ₁.τ₁ := inferInstanceAs (Epi e)
  have : IsIso φ₁.τ₂ := inferInstanceAs (IsIso (𝟙 B))
  have : Mono φ₁.τ₃ := inferInstanceAs (Mono (𝟙 W))
  have : Epi φ₂.τ₁ := inferInstanceAs (Epi (𝟙 A))
  have : IsIso φ₂.τ₂ := inferInstanceAs (IsIso (𝟙 B))
  have : Mono φ₂.τ₃ := inferInstanceAs (Mono m)
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₂).1
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₁).2 h)

namespace ShortComplex.ShortExact

/-- In a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of homological complexes with `X₃` acyclic, the map `X₁ → X₂`
is a quasi-isomorphism (long exact homology sequence). -/
theorem quasiIso_f_of_acyclic_X₃ {ι : Type*} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex D c)} (hS : S.ShortExact) (h₃ : S.X₃.Acyclic) :
    _root_.QuasiIso S.f := by
  rw [_root_.quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hepi : Epi (HomologicalComplex.homologyMap S.f j) :=
    (hS.homology_exact₂ j).epi_f ((h₃ j).isZero_homology.eq_of_tgt _ _)
  have hmono : Mono (HomologicalComplex.homologyMap S.f j) := by
    by_cases hj : ∃ i, c.Rel i j
    · obtain ⟨i, hij⟩ := hj
      exact (hS.homology_exact₁ i j hij).mono_g ((h₃ i).isZero_homology.eq_of_src _ _)
    · have := hS.mono_f
      exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f j (by simpa using hj)
  exact isIso_of_mono_of_epi _

end ShortComplex.ShortExact

/-- A class `P` of objects of `D` is *acyclic* for the additive functor `G : D ⥤ E` if it contains the injective
objects, `G` maps every short exact sequence whose first term is in `P` to a short exact sequence, and `P` is closed
under cokernels of monomorphisms between its objects.  (Example: flasque sheaves, for direct image functors.) -/
structure Functor.IsAcyclicClass (G : D ⥤ E) [G.Additive] (P : ObjectProperty D) : Prop where
  /-- Injective objects are in `P`. -/
  injective (X : D) [Injective X] : P X
  /-- `G` is exact on short exact sequences whose first term is in `P`. -/
  shortExact_map {S : ShortComplex D} (hS : S.ShortExact) (h₁ : P S.X₁) : (S.map G).ShortExact
  /-- `P` is closed under cokernels of monomorphisms. -/
  of_shortExact {S : ShortComplex D} (hS : S.ShortExact) (h₁ : P S.X₁) (h₂ : P S.X₂) : P S.X₃

namespace Functor.IsAcyclicClass

variable {G : D ⥤ E} [G.Additive] {P : ObjectProperty D}

/-- **Composition.**  If `P` is acyclic for `G`, `Q` is acyclic for `H` and `G` maps `P` into `Q`, then `P` is
acyclic for `G ⋙ H`. -/
theorem comp {T : Type*} [Category* T] [Abelian T] {H : E ⥤ T} [H.Additive] {Q : ObjectProperty E}
    (h : G.IsAcyclicClass P) (hQ : H.IsAcyclicClass Q) (hPQ : ∀ X, P X → Q (G.obj X)) :
    (G ⋙ H).IsAcyclicClass P where
  injective X _ := h.injective X
  shortExact_map hS h₁ := hQ.shortExact_map (h.shortExact_map hS h₁) (hPQ _ h₁)
  of_shortExact := h.of_shortExact

/-- Zero objects are in an acyclic class (they are injective). -/
theorem of_isZero (h : G.IsAcyclicClass P) {X : D} (hX : IsZero X) : P X := by
  have : Injective X := Injective.of_iso hX.isoZero.symm inferInstance
  exact h.injective X

/-- An acyclic class is closed under isomorphisms. -/
theorem of_iso (h : G.IsAcyclicClass P) {X Y : D} (e : X ≅ Y) (hX : P X) : P Y := by
  let S : ShortComplex D := ShortComplex.mk (0 : (0 : D) ⟶ X) e.hom zero_comp
  have : Mono S.f := mono_of_isZero_src (isZero_zero D) _
  have hS : S.ShortExact :=
    { exact := (ShortComplex.exact_iff_mono S rfl).2 (inferInstance : Mono e.hom) }
  exact h.of_shortExact hS (h.of_isZero (isZero_zero D)) hX

/-- The short exact sequence `0 → ker d^n → M^n → ker d^{n+1} → 0` of an acyclic `ℕ`-indexed cochain complex. -/
noncomputable abbrev spliceSc (M : CochainComplex D ℕ) (n : ℕ) : ShortComplex D :=
  ShortComplex.mk (kernel.ι (M.d n (n + 1))) (kernel.lift (M.d (n + 1) (n + 2)) (M.d n (n + 1)) (by simp))
    (by ext; simp)

/-- For an acyclic complex `M`, the sequence `0 → ker d^n → M^n → ker d^{n+1} → 0` is short exact. -/
theorem spliceSc_shortExact {M : CochainComplex D ℕ} (hM : M.Acyclic) (n : ℕ) :
    (spliceSc M n).ShortExact := by
  have hex : (M.sc' n (n + 1) (n + 2)).Exact :=
    (M.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).1 (hM (n + 1))
  have hepi : Epi (spliceSc M n).g := hex.epi_kernelLift
  have : Mono (spliceSc M n).f := by dsimp [spliceSc]; infer_instance
  refine { exact := ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι _ _
    (fun x hx => kernel.lift _ x ?_) (fun x hx => kernel.lift_ι _ _ _) (fun x hx m hm => ?_)) }
  · have := hx =≫ kernel.ι (M.d (n + 1) (n + 2))
    rwa [Category.assoc, kernel.lift_ι, zero_comp] at this
  · refine (cancel_mono (kernel.ι (M.d n (n + 1)))).1 ?_
    rw [kernel.lift_ι]
    exact hm

/-- For an acyclic `ℕ`-indexed cochain complex, `d⁰` is a monomorphism, i.e. `ker d⁰ = 0`. -/
theorem isZero_kernel_d_zero {M : CochainComplex D ℕ} (hM : M.Acyclic) : IsZero (Limits.kernel (M.d 0 1)) := by
  have hex : (M.sc' 0 0 1).Exact := (M.exactAt_iff' 0 0 1 (by simp) (by simp)).1 (hM 0)
  have : Mono (M.d 0 1) := hex.mono_g (M.shape _ _ (by simp))
  exact isZero_kernel_of_mono _

/-- The kernels of the differentials of an acyclic complex of objects of `P` are in `P`. -/
theorem prop_kernel (h : G.IsAcyclicClass P) {M : CochainComplex D ℕ} (hM : M.Acyclic)
    (hP : ∀ n, P (M.X n)) : ∀ n, P (Limits.kernel (M.d n (n + 1)))
  | 0 => h.of_isZero (isZero_kernel_d_zero hM)
  | n + 1 => h.of_shortExact (spliceSc_shortExact hM n) (prop_kernel h hM hP n) (hP n)

/-- **`G` preserves acyclicity of complexes of objects of `P`.**  An acyclic `ℕ`-indexed cochain complex `M` with all
`M.X n ∈ P` is mapped by `G` to an acyclic complex. -/
theorem acyclic_map (h : G.IsAcyclicClass P) {M : CochainComplex D ℕ} (hM : M.Acyclic)
    (hP : ∀ n, P (M.X n)) : ((G.mapHomologicalComplex _).obj M).Acyclic := by
  have hS : ∀ n, ((spliceSc M n).map G).ShortExact := fun n =>
    h.shortExact_map (spliceSc_shortExact hM n) (prop_kernel h hM hP n)
  intro j
  cases j with
  | zero =>
    rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp)]
    refine (ShortComplex.exact_iff_mono _ ?_).2 ?_
    · exact ((G.mapHomologicalComplex _).obj M).shape 0 0 (by simp)
    · have h0 : Mono (G.map (kernel.lift (M.d 1 2) (M.d 0 1) (by simp))) := by
        exact (hS 0).exact.mono_g ((G.map_isZero (isZero_kernel_d_zero hM)).eq_of_src _ _)
      have h1 : Mono (G.map (kernel.ι (M.d 1 2))) := (hS 1).mono_f
      have : G.map (M.d 0 1) = G.map (kernel.lift (M.d 1 2) (M.d 0 1) (by simp)) ≫
          G.map (kernel.ι (M.d 1 2)) := by rw [← G.map_comp, kernel.lift_ι]
      show Mono (G.map (M.d 0 1))
      rw [this]
      exact mono_comp _ _
  | succ n =>
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
    have he : Epi (G.map (kernel.lift (M.d (n + 1) (n + 2)) (M.d n (n + 1)) (by simp))) := (hS n).epi_g
    have hm : Mono (G.map (kernel.ι (M.d (n + 2) (n + 3)))) := (hS (n + 2)).mono_f
    exact exact_of_factor (e := G.map (kernel.lift (M.d (n + 1) (n + 2)) (M.d n (n + 1)) _))
      (i := G.map (kernel.ι (M.d (n + 1) (n + 2))))
      (p := G.map (kernel.lift (M.d (n + 2) (n + 3)) (M.d (n + 1) (n + 2)) (M.d_comp_d _ _ _)))
      (m := G.map (kernel.ι (M.d (n + 2) (n + 3)))) (G.map (M.d n (n + 1))) (G.map (M.d (n + 1) (n + 2)))
      (by rw [← G.map_comp, kernel.lift_ι]) (by rw [← G.map_comp, kernel.lift_ι]) (hS (n + 1)).exact

/-- **`G` preserves degreewise monomorphic quasi-isomorphisms between complexes of objects of `P`.**  If
`β : M ⟶ K` is a monomorphism and a quasi-isomorphism of `ℕ`-indexed cochain complexes whose terms are in `P`, then
`G β` is a quasi-isomorphism.  (The cokernel of `β` is an acyclic complex of objects of `P`.) -/
theorem quasiIso_map_of_mono (h : G.IsAcyclicClass P) {M K : CochainComplex D ℕ} (β : M ⟶ K) [Mono β]
    [QuasiIso β] (hM : ∀ n, P (M.X n)) (hK : ∀ n, P (K.X n)) :
    QuasiIso ((G.mapHomologicalComplex _).map β) := by
  let S : ShortComplex (CochainComplex D ℕ) := ShortComplex.mk β (cokernel.π β) (cokernel.condition β)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel β }
  have hSn : ∀ n, (S.map (HomologicalComplex.eval D _ n)).ShortExact := fun n =>
    hS.map_of_exact (HomologicalComplex.eval D _ n)
  have hN : ∀ n, P (S.X₃.X n) := fun n => h.of_shortExact (hSn n) (hM n) (hK n)
  have hNac : ((G.mapHomologicalComplex _).obj S.X₃).Acyclic :=
    h.acyclic_map (hS.acyclic_X₃ (inferInstance : QuasiIso β)) hN
  have hS' : (S.map (G.mapHomologicalComplex _)).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
      h.shortExact_map (hSn n) (hM n)
  exact hS'.quasiIso_f_of_acyclic_X₃ hNac

/-- **The higher right derived functors of `G` vanish on `P`.** -/
theorem isZero_rightDerived (h : G.IsAcyclicClass P) [HasInjectiveResolutions D] {X : D} (hX : P X)
    (i : ℕ) (hi : 0 < i) : IsZero ((G.rightDerived i).obj X) := by
  let I := injectiveResolution X
  have : Mono I.ι := HomologicalComplex.mono_of_mono_f _ fun n => by
    cases n with
    | zero => exact inferInstance
    | succ n =>
      exact mono_of_isZero_src (HomologicalComplex.isZero_single_obj_X _ 0 X (n + 1) (by simp)) _
  have hq := h.quasiIso_map_of_mono I.ι
    (fun n => by
      cases n with
      | zero => exact h.of_iso (HomologicalComplex.singleObjXSelf _ 0 X).symm hX
      | succ n => exact h.of_isZero (HomologicalComplex.isZero_single_obj_X _ 0 X (n + 1) (by simp)))
    (fun n => h.injective _)
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj G i)
  have hiso : IsIso (HomologicalComplex.homologyMap ((G.mapHomologicalComplex _).map I.ι) i) :=
    (quasiIsoAt_iff_isIso_homologyMap _ i).1 (hq.quasiIsoAt i)
  refine IsZero.of_iso ?_ (asIso (HomologicalComplex.homologyMap
    ((G.mapHomologicalComplex _).map I.ι) i)).symm
  refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
  exact G.map_isZero (HomologicalComplex.isZero_single_obj_X _ 0 X i (by lia))

end Functor.IsAcyclicClass

end CategoryTheory
