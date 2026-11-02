/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Architect

/-!
# Compatibility layer: `Tor₁^A(M, A/I)` and the multiplication map `M ⊗_A I → M`

Lemma 2 of Ch. II §1 (p. 182) states its condition (ii) as "`Tor₁^A(M, A/I) = 0`".  Mathlib's
`Tor` (`Mathlib/CategoryTheory/Monoidal/Tor.lean`) is the left derived functor of `M ⊗_A -`
and has almost no API (no long exact sequence), so we identify `Tor₁^A(M, A/I)` concretely:
from `0 → I → A → A/I → 0` and `Tor₁^A(M, A) = 0`, it is the kernel of the multiplication map
`M ⊗_A I → M`.  We prove the vanishing statement needed in Lean:
`Tor₁^A(M, A/I) = 0` if and only if `M ⊗_A I → M` is injective.

The comparison is done by hand on Mathlib's chosen projective resolution
`X₂ → X₁ → X₀ → A/I → 0` (`isZero_torOne_quotient_of_exact_complex`): lifting `X₀ → A/I` to `φ₀ : X₀ → A` gives a
map from the homology of `M ⊗ X₂ → M ⊗ X₁ → M ⊗ X₀` at `M ⊗ X₁` to `M ⊗_A I`, which is a
bijection onto the kernel of `M ⊗_A I → M`.
-/

@[expose] public section

open TensorProduct

namespace Hironaka

universe u

/-- Linear-algebra core of `Tor₁^A(M, A/I) ≅ ker (M ⊗_A I → M)`: for a presentation
`X₂ → X₁ → X₀ → A/I → 0` with `X₀` projective, the homology of `M ⊗ X₂ → M ⊗ X₁ → M ⊗ X₀`
at `M ⊗ X₁` maps injectively onto the kernel of `M ⊗_A I → M`. -/
private theorem isZero_torOne_quotient_of_exact_complex {A : Type u} [CommRing A] (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] {X₀ X₁ X₂ : Type u} [AddCommGroup X₀] [Module A X₀]
    [AddCommGroup X₁] [Module A X₁] [AddCommGroup X₂] [Module A X₂] [Module.Projective A X₀]
    (d₁ : X₁ →ₗ[A] X₀) (d₂ : X₂ →ₗ[A] X₁) (π₀ : X₀ →ₗ[A] A ⧸ I)
    (hπ : Function.Surjective π₀) (h₀ : LinearMap.range d₁ = LinearMap.ker π₀)
    (h₁ : LinearMap.range d₂ = LinearMap.ker d₁)
    (h : ∀ y, LinearMap.lTensor M d₁ (LinearMap.lTensor M d₂ y) = 0) :
    ∃ Φ : (LinearMap.ker (LinearMap.lTensor M d₁) ⧸ LinearMap.range
        ((LinearMap.lTensor M d₂).codRestrict (LinearMap.ker (LinearMap.lTensor M d₁)) h)) →ₗ[A]
        M ⊗[A] I,
      Function.Injective Φ ∧
        (∀ t, TensorProduct.rid A M (LinearMap.lTensor M I.subtype (Φ t)) = 0) ∧
        ∀ w : M ⊗[A] I, TensorProduct.rid A M (LinearMap.lTensor M I.subtype w) = 0 →
          ∃ t, Φ t = w := by
  obtain ⟨φ₀, hφ₀⟩ := Module.projective_lifting_property I.mkQ π₀ (Submodule.mkQ_surjective I)
  have hφ₀K : ∀ x ∈ LinearMap.ker π₀, φ₀ x ∈ I := fun x hx => by
    have : I.mkQ (φ₀ x) = 0 := by rw [← LinearMap.comp_apply, hφ₀]; exact hx
    exact (Submodule.Quotient.mk_eq_zero I).mp this
  set K₀ := LinearMap.ker π₀ with hK₀
  have hd₁K : ∀ x, d₁ x ∈ K₀ := fun x => h₀ ▸ LinearMap.mem_range_self d₁ x
  let φK : K₀ →ₗ[A] I := (φ₀ ∘ₗ K₀.subtype).codRestrict I (fun x => hφ₀K _ x.2)
  let d₁' : X₁ →ₗ[A] K₀ := d₁.codRestrict K₀ hd₁K
  let φ₁ : X₁ →ₗ[A] I := φK ∘ₗ d₁'
  have hd₁ : d₁ = K₀.subtype ∘ₗ d₁' := by ext x; rfl
  have hsurj : Function.Surjective d₁' := by
    rintro ⟨k, hk⟩
    rw [← h₀] at hk
    obtain ⟨y, rfl⟩ := hk
    exact ⟨y, rfl⟩
  obtain ⟨x₀, hx₀⟩ := hπ 1
  let ψA : A →ₗ[A] X₀ := LinearMap.toSpanSingleton A X₀ x₀
  have hψA : ∀ a, π₀ (ψA a) = I.mkQ a := fun a => by
    simp only [ψA, LinearMap.toSpanSingleton_apply, map_smul, hx₀]
    rw [Submodule.mkQ_apply, Algebra.smul_def, mul_one]
    rfl
  let κ : I →ₗ[A] K₀ := (ψA ∘ₗ I.subtype).codRestrict K₀ (fun a => by
    show π₀ (ψA a) = 0
    rw [hψA, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact a.2)
  let h' : X₀ →ₗ[A] K₀ := (ψA ∘ₗ φ₀ - LinearMap.id).codRestrict K₀ (fun x => by
    show π₀ (ψA (φ₀ x) - x) = 0
    rw [map_sub, hψA, ← LinearMap.comp_apply I.mkQ φ₀, hφ₀, sub_self])
  have hκ : κ ∘ₗ φK = LinearMap.id + h' ∘ₗ K₀.subtype := by
    ext k
    simp [κ, φK, h']
  -- `Φ₀ : ker (M ⊗ d₁) → M ⊗ I`, `z ↦ (M ⊗ φ₁) z`
  let Φ₀ : LinearMap.ker (LinearMap.lTensor M d₁) →ₗ[A] M ⊗[A] I :=
    LinearMap.lTensor M φ₁ ∘ₗ (LinearMap.ker (LinearMap.lTensor M d₁)).subtype
  have hφ₁d₂ : φ₁ ∘ₗ d₂ = 0 := by
    ext y
    have : d₁ (d₂ y) = 0 := by
      have : d₂ y ∈ LinearMap.range d₂ := LinearMap.mem_range_self d₂ y
      rw [h₁] at this
      exact this
    show φ₀ (d₁ (d₂ y)) = 0
    rw [this, map_zero]
  have hΦ₀ : LinearMap.range ((LinearMap.lTensor M d₂).codRestrict
      (LinearMap.ker (LinearMap.lTensor M d₁)) h) ≤ LinearMap.ker Φ₀ := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    show LinearMap.lTensor M φ₁ (LinearMap.lTensor M d₂ y) = 0
    rw [← LinearMap.lTensor_comp_apply, hφ₁d₂, LinearMap.lTensor_zero, LinearMap.zero_apply]
  refine ⟨Submodule.liftQ _ Φ₀ hΦ₀, ?_, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot']
    refine le_antisymm hΦ₀ ?_
    rintro ⟨z, hz⟩ hΦz
    have hΦz' : LinearMap.lTensor M φ₁ z = 0 := hΦz
    set w := LinearMap.lTensor M d₁' z with hw
    have hw1 : LinearMap.lTensor M K₀.subtype w = 0 := by
      rw [hw, ← LinearMap.lTensor_comp_apply, ← hd₁]
      exact hz
    have hw2 : LinearMap.lTensor M φK w = 0 := by
      rw [hw, ← LinearMap.lTensor_comp_apply]
      exact hΦz'
    have hw0 : w = 0 := by
      have := congrArg (LinearMap.lTensor M κ) hw2
      rw [map_zero, ← LinearMap.lTensor_comp_apply, hκ, LinearMap.lTensor_add,
        LinearMap.add_apply, LinearMap.lTensor_id, LinearMap.id_apply,
        LinearMap.lTensor_comp_apply, hw1, map_zero, add_zero] at this
      exact this
    have hex : Function.Exact d₂ d₁' := by
      intro y
      rw [← LinearMap.coe_range, SetLike.mem_coe, h₁, LinearMap.mem_ker]
      constructor
      · intro hy
        exact congrArg Subtype.val hy
      · intro hy
        exact Subtype.ext hy
    obtain ⟨y, hy⟩ := (lTensor_exact M hex hsurj z).mp hw0
    exact ⟨y, Subtype.ext hy⟩
  · intro t
    induction t using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.liftQ_apply]
      show TensorProduct.rid A M (LinearMap.lTensor M I.subtype
        (LinearMap.lTensor M φ₁ (z : M ⊗[A] X₁))) = 0
      rw [← LinearMap.lTensor_comp_apply]
      have hc : I.subtype ∘ₗ φ₁ = φ₀ ∘ₗ d₁ := by ext x; rfl
      rw [hc, LinearMap.lTensor_comp_apply, show LinearMap.lTensor M d₁ (z : M ⊗[A] X₁) = 0
        from z.2, map_zero, map_zero]
  · -- surjectivity onto the kernel of `M ⊗_A I → M`
    intro w hw
    have hw' : LinearMap.lTensor M I.subtype w = 0 :=
      (TensorProduct.rid A M).injective (by rw [hw, map_zero])
    -- `u := φ₀ x₀ ≡ 1 mod I`, so the composite `I → K₀ → I` is the identity plus a map
    -- factoring through `I.subtype : I → A`.
    set u := φ₀ x₀ with hu_def
    have hu : u - 1 ∈ I := by
      refine (Submodule.Quotient.eq I).mp ?_
      have h1 := hψA 1
      simp only [ψA, LinearMap.toSpanSingleton_apply, one_smul] at h1
      rw [← Submodule.mkQ_apply, ← Submodule.mkQ_apply, hu_def, ← LinearMap.comp_apply, hφ₀,
        ← h1]
    let g : A →ₗ[A] I := LinearMap.toSpanSingleton A I ⟨u - 1, hu⟩
    have hφκ : φK ∘ₗ κ = LinearMap.id + g ∘ₗ I.subtype := by
      ext a
      simp [φK, κ, ψA, g, hu_def]
      ring
    obtain ⟨z, hz⟩ := LinearMap.lTensor_surjective M hsurj (LinearMap.lTensor M κ w)
    have hzker : z ∈ LinearMap.ker (LinearMap.lTensor M d₁) := by
      rw [LinearMap.mem_ker, hd₁, LinearMap.lTensor_comp_apply, hz,
        ← LinearMap.lTensor_comp_apply]
      have hc : K₀.subtype ∘ₗ κ = ψA ∘ₗ I.subtype := by ext a; rfl
      rw [hc, LinearMap.lTensor_comp_apply, hw', map_zero]
    refine ⟨Submodule.Quotient.mk ⟨z, hzker⟩, ?_⟩
    rw [Submodule.liftQ_apply]
    show LinearMap.lTensor M φ₁ z = w
    rw [show φ₁ = φK ∘ₗ d₁' from rfl, LinearMap.lTensor_comp_apply, hz,
      ← LinearMap.lTensor_comp_apply, hφκ, LinearMap.lTensor_add, LinearMap.add_apply,
      LinearMap.lTensor_id, LinearMap.id_apply, LinearMap.lTensor_comp_apply, hw', map_zero,
      add_zero]

open CategoryTheory in
/-- `Tor₁^A(M, A/I)` maps injectively onto the kernel of the multiplication map
`M ⊗_A I → M`. -/
theorem exists_torOne_quotient_injective_onto_ker {A : Type u} [CommRing A] (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] :
    ∃ Φ : ↑(((Tor (ModuleCat.{u} A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ I))) →ₗ[A] M ⊗[A] I,
      Function.Injective Φ ∧
        (∀ t, TensorProduct.rid A M (LinearMap.lTensor M I.subtype (Φ t)) = 0) ∧
        ∀ w : M ⊗[A] I, TensorProduct.rid A M (LinearMap.lTensor M I.subtype w) = 0 →
          ∃ t, Φ t = w := by
  let N := ModuleCat.of A (A ⧸ I)
  let R : ProjectiveResolution N := projectiveResolution N
  let F := (MonoidalCategory.tensoringLeft (ModuleCat.{u} A)).obj (ModuleCat.of A M)
  let K := (F.mapHomologicalComplex _).obj R.complex
  let S := K.sc' 2 1 0
  let e : ((Tor (ModuleCat.{u} A) 1).obj (ModuleCat.of A M)).obj N ≅
      S.moduleCatLeftHomologyData.H :=
    R.isoLeftDerivedObj F 1 ≪≫ K.homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
      S.moduleCatHomologyIso
  have hsurj : Function.Surjective (R.π.f 0).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have h₀ : LinearMap.range (R.complex.d 1 0).hom = LinearMap.ker (R.π.f 0).hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
      (ShortComplex.exact_of_g_is_cokernel
        (ShortComplex.mk _ _ R.complex_d_comp_π_f_zero) R.isColimitCokernelCofork)
  have h₁ : LinearMap.range (R.complex.d 2 1).hom = LinearMap.ker (R.complex.d 1 0).hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp (R.exact_succ 0)
  obtain ⟨Φ, hinj, hμ, hsurjΦ⟩ := isZero_torOne_quotient_of_exact_complex I M (R.complex.d 1 0).hom
    (R.complex.d 2 1).hom (R.π.f 0).hom hsurj h₀ h₁ S.moduleCat_zero_apply
  have he : Function.Surjective e.hom.hom := (ModuleCat.epi_iff_surjective e.hom).mp inferInstance
  refine ⟨Φ ∘ₗ e.hom.hom, hinj.comp ?_, fun t => hμ _, fun w hw => ?_⟩
  · exact (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  · obtain ⟨t', ht'⟩ := hsurjΦ w hw
    obtain ⟨t, rfl⟩ := he t'
    exact ⟨t, ht'⟩

/-- `Tor₁^A(M, A/I)` embeds into the kernel of the multiplication map `M ⊗_A I → M`. -/
theorem exists_torOne_quotient_injective {A : Type u} [CommRing A] (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] :
    ∃ Φ : ↑(((CategoryTheory.Tor (ModuleCat.{u} A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ I))) →ₗ[A] M ⊗[A] I,
      Function.Injective Φ ∧
        ∀ t, TensorProduct.rid A M (LinearMap.lTensor M I.subtype (Φ t)) = 0 := by
  obtain ⟨Φ, hinj, hμ, -⟩ := exists_torOne_quotient_injective_onto_ker I M
  exact ⟨Φ, hinj, hμ⟩

/-- `Tor₁^A(M, A/I) = 0` if and only if the multiplication map `M ⊗_A I → M` is injective. -/
@[blueprint "compat:tor-one-quotient"
  (statement := /-- Let $A$ be a ring, $I$ an ideal of $A$ and $M$ an $A$-module. Then
    $\operatorname{Tor}_1^A(M,A/I)=0$ if and only if the multiplication map
    $M\otimes_AI\to M$, $x\otimes a\mapsto ax$, is injective. (Formalization note:
    $\operatorname{Tor}$ is Mathlib's left derived functor of $M\otimes_A-$; this identifies
    the condition $\operatorname{Tor}_1^A(M,A/I)=0$ of \cref{lem:II.1-2} concretely.) -/)
  (proof := /-- Let $X_2\to X_1\to X_0\to A/I\to0$ be the chosen projective resolution, with
    kernel $K_0$ of $X_0\to A/I$. Lifting $X_0\to A/I$ to $\varphi_0\colon X_0\to A$ and
    $1\in A/I$ to $x_0\in X_0$ compares $0\to K_0\to X_0\to A/I\to0$ with
    $0\to I\to A\to A/I\to0$. The induced map from the homology of
    $M\otimes X_2\to M\otimes X_1\to M\otimes X_0$ at $M\otimes X_1$ to $M\otimes_AI$ is
    injective with image in the kernel of $M\otimes_AI\to M$, and it is onto that kernel:
    for $w$ in the kernel, the composite $I\to K_0\to I$ is multiplication by
    $\varphi_0(x_0)\in1+I$, and multiplication by an element of $I$ kills $w$. -/)
  (latexEnv := "lemma")]
theorem isZero_torOne_quotient_iff {A : Type u} [CommRing A] (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] :
    CategoryTheory.Limits.IsZero (((CategoryTheory.Tor (ModuleCat.{u} A) 1).obj
      (ModuleCat.of A M)).obj (ModuleCat.of A (A ⧸ I))) ↔
    Function.Injective (fun x : M ⊗[A] I =>
      TensorProduct.rid A M (LinearMap.lTensor M I.subtype x)) := by
  obtain ⟨Φ, hinj, hμ, hsurj⟩ := exists_torOne_quotient_injective_onto_ker I M
  rw [ModuleCat.isZero_iff_subsingleton]
  constructor
  · intro hsub x y hxy
    simp only at hxy
    have hxy' : TensorProduct.rid A M (LinearMap.lTensor M I.subtype (x - y)) = 0 := by
      rw [map_sub, map_sub, hxy, sub_self]
    obtain ⟨t, ht⟩ := hsurj (x - y) hxy'
    rw [Subsingleton.elim t 0, map_zero] at ht
    exact sub_eq_zero.mp ht.symm
  · intro hμinj
    refine ⟨fun s t => hinj ?_⟩
    have h0 : ∀ r, Φ r = 0 := fun r => hμinj (by simp only [hμ r, map_zero])
    rw [h0 s, h0 t]

end Hironaka
