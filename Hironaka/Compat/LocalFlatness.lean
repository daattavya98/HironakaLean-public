/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Architect

/-!
# Compatibility layer: the local criterion of flatness

Lemma 2 of Ch. II §1 (p. 182) is cited from Grothendieck (Théorème 5.6 of the seminar note
"Séminaire de Géométrie Algébrique de l'IHES, No. IV (1960)", p. 181).  Mathlib does
not have the local criterion of flatness, so we prove the two implications it needs, with
`Tor₁^A(M, A/I) = 0` written concretely as injectivity of the multiplication map
`M ⊗_A I → M` (see `Hironaka/Compat/TorOne.lean`):

* (ii) ⇒ (i) (`flat_of_flat_quotient_of_mul_injective`): if `M ⊗_A A/I` is `A/I`-flat and
  `M ⊗_A I → M` is injective, then `M` is `A`-flat;
* (iii) ⇒ (ii) (`mul_injective_of_forall_gr`): if every canonical map
  `M ⊗_A Iⁿ/Iⁿ⁺¹ → IⁿM/Iⁿ⁺¹M` is injective, then `M ⊗_A I → M` is injective.

Both need the standing hypotheses of Lemma 2: `A → B` a homomorphism of noetherian rings,
`IB` contained in the Jacobson radical of `B`, and `M` a `B`-module of finite type (Krull's
intersection theorem then applies to the finite `B`-modules `M ⊗_A J`).

For (ii) ⇒ (i) we need `Tor₁^A(M, N) = 0` for more general `N` than `A/I`, together with
its behaviour in short exact sequences.  We avoid Mathlib's categorical `Tor` and use the
private predicate `TorOneZero A M N`: `M ⊗_A -` keeps `K → E` injective in every short exact
sequence `0 → K → E → N → 0`.  Its two-out-of-three property for extensions and its
comparison along a presentation are proved by direct diagram chases (the latter through the
pullback `E ×_N F`).
-/

@[expose] public section

open TensorProduct

namespace Hironaka

universe u

/-- `Tor₁^A(M, N) = 0`, written concretely (avoiding Mathlib's categorical `Tor`): for every short
exact sequence `0 → K → E → N → 0` of `A`-modules, `M ⊗_A K → M ⊗_A E` is injective. -/
private def TorOneZero (A : Type u) [CommRing A] (M N : Type u) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] : Prop :=
  ∀ (K E : Type u) [AddCommGroup K] [Module A K] [AddCommGroup E] [Module A E]
    (f : K →ₗ[A] E) (g : E →ₗ[A] N), Function.Injective f → Function.Exact f g →
    Function.Surjective g → Function.Injective (LinearMap.lTensor M f)

section TorOneZero

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]

/-- `M ⊗_A -` preserves injectivity in a split short exact sequence. -/
private theorem lTensor_injective_of_section {K E N : Type u}
    [AddCommGroup K] [Module A K] [AddCommGroup E] [Module A E] [AddCommGroup N] [Module A N]
    (f : K →ₗ[A] E) (g : E →ₗ[A] N) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (s : N →ₗ[A] E) (hs : g ∘ₗ s = LinearMap.id) :
    Function.Injective (LinearMap.lTensor M f) := by
  have hg : Function.Surjective g := fun y => ⟨s y, LinearMap.congr_fun hs y⟩
  have htfae := (hfg.split_tfae hf hg).out 1 2
  obtain ⟨r, hr⟩ := htfae.mp ⟨s, hs⟩
  intro x y hxy
  have := congrArg (LinearMap.lTensor M r) hxy
  rwa [← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply, hr,
    LinearMap.lTensor_id, LinearMap.id_apply, LinearMap.id_apply] at this

/-- `Tor₁^A(M, A) = 0`: every surjection onto `A` splits. -/
private theorem torOneZero_self : TorOneZero A M A := by
  intro K E _ _ _ _ f g hf hfg hg
  obtain ⟨e, he⟩ := hg 1
  refine lTensor_injective_of_section f g hf hfg (LinearMap.toSpanSingleton A E e) ?_
  apply LinearMap.ext_ring
  simp [he]

/-- `Tor₁^A(M, 0) = 0`. -/
private theorem torOneZero_of_subsingleton (N : Type u) [AddCommGroup N] [Module A N]
    [Subsingleton N] : TorOneZero A M N := by
  intro K E _ _ _ _ f g hf hfg hg
  exact lTensor_injective_of_section f g hf hfg 0 (LinearMap.ext fun _ => Subsingleton.elim _ _)

/-- `Tor₁` vanishing is invariant under isomorphism. -/
private theorem torOneZero_of_equiv {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (e : N ≃ₗ[A] N') (h : TorOneZero A M N) :
    TorOneZero A M N' := by
  intro K E _ _ _ _ f g hf hfg hg
  refine h K E f (e.symm.toLinearMap ∘ₗ g) hf ?_ (e.symm.surjective.comp hg)
  exact (e.symm.injective.comp_exact_iff_exact (f := f) (g := g)).mpr hfg

/-- Extensions: `Tor₁` vanishing passes from `N'` and `N''` to `N` in `0 → N' → N → N'' → 0`. -/
private theorem torOneZero_of_exact {N' N N'' : Type u} [AddCommGroup N'] [Module A N']
    [AddCommGroup N] [Module A N] [AddCommGroup N''] [Module A N'']
    (a : N' →ₗ[A] N) (b : N →ₗ[A] N'') (ha : Function.Injective a) (hab : Function.Exact a b)
    (hb : Function.Surjective b) (h' : TorOneZero A M N') (h'' : TorOneZero A M N'') :
    TorOneZero A M N := by
  intro K E _ _ _ _ f g hf hfg hg
  -- `E'` is the preimage of `N'` in `E`; then `K ↪ E'` and `E' ↪ E` stay injective after `M ⊗ -`
  -- by `Tor₁^A(M, N') = 0` (for `E' ↠ N'`) and `Tor₁^A(M, N'') = 0` (for `E ↠ N''`)
  let E' : Submodule A E := (LinearMap.range a).comap g
  have hfE : ∀ k, f k ∈ E' := fun k => by
    simp only [E', Submodule.mem_comap, hfg.apply_apply_eq_zero]
    exact zero_mem _
  let f' : K →ₗ[A] E' := LinearMap.codRestrict E' f hfE
  let g₀ : E' →ₗ[A] LinearMap.range a :=
    LinearMap.codRestrict (LinearMap.range a) (g ∘ₗ E'.subtype) (fun x => x.2)
  have h₁ : Function.Injective (LinearMap.lTensor M f') := by
    refine torOneZero_of_equiv (LinearEquiv.ofInjective a ha) h' K E' f' g₀
      (fun x y hxy => hf (congrArg Subtype.val hxy)) ?_ ?_
    · intro x
      constructor
      · intro hx
        have hx' : g x = 0 := congrArg Subtype.val hx
        obtain ⟨k, hk⟩ := (hfg x).mp hx'
        exact ⟨k, Subtype.ext hk⟩
      · rintro ⟨k, rfl⟩
        exact Subtype.ext (hfg.apply_apply_eq_zero k)
    · rintro ⟨_, n, rfl⟩
      obtain ⟨e, he⟩ := hg (a n)
      exact ⟨⟨e, ⟨n, he.symm⟩⟩, Subtype.ext he⟩
  have h₂ : Function.Injective (LinearMap.lTensor M E'.subtype) := by
    refine h'' E' E E'.subtype (b ∘ₗ g) Subtype.val_injective ?_ (hb.comp hg)
    intro x
    rw [LinearMap.comp_apply, hab (g x)]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩
  have hff : f = E'.subtype ∘ₗ f' := rfl
  rw [hff, LinearMap.lTensor_comp]
  exact h₂.comp h₁

/-- Comparison: `Tor₁` vanishing passes from `F` to `N` along a presentation `0 → K' → F → N → 0`
for which `M ⊗ K' → M ⊗ F` is injective. -/
private theorem torOneZero_of_presentation {K' F N : Type u} [AddCommGroup K'] [Module A K']
    [AddCommGroup F] [Module A F] [AddCommGroup N] [Module A N]
    (i : K' →ₗ[A] F) (q : F →ₗ[A] N) (hiq : Function.Exact i q) (hq : Function.Surjective q)
    (hF : TorOneZero A M F) (hMi : Function.Injective (LinearMap.lTensor M i)) :
    TorOneZero A M N := by
  intro K E _ _ _ _ f g hf hfg hg
  -- the pullback `P = E ×_N F`: `0 → K → P → F → 0` and `0 → K' → P → E → 0` are exact
  let P : Submodule A (E × F) :=
    LinearMap.ker (g ∘ₗ LinearMap.fst A E F - q ∘ₗ LinearMap.snd A E F)
  have memP : ∀ x : E × F, x ∈ P ↔ g x.1 = q x.2 := by
    intro x
    simp [P, sub_eq_zero]
  let πE : P →ₗ[A] E := LinearMap.fst A E F ∘ₗ P.subtype
  let πF : P →ₗ[A] F := LinearMap.snd A E F ∘ₗ P.subtype
  let j : K →ₗ[A] P := LinearMap.codRestrict P (LinearMap.inl A E F ∘ₗ f)
    (fun k => (memP _).mpr (by simp [hfg.apply_apply_eq_zero]))
  let i' : K' →ₗ[A] P := LinearMap.codRestrict P (LinearMap.inr A E F ∘ₗ i)
    (fun k => (memP _).mpr (by simp [hiq.apply_apply_eq_zero]))
  have hj : Function.Injective (LinearMap.lTensor M j) := by
    refine hF K P j πF (fun x y hxy => hf (congrArg (fun p : P => (p : E × F).1) hxy)) ?_ ?_
    · rintro ⟨⟨e, x⟩, hp⟩
      have hp' := (memP _).mp hp
      constructor
      · intro hx
        change x = 0 at hx
        subst hx
        rw [map_zero] at hp'
        obtain ⟨k, hk⟩ := (hfg e).mp hp'
        exact ⟨k, Subtype.ext (Prod.ext hk rfl)⟩
      · rintro ⟨k, hk⟩
        rw [← hk]
        rfl
    · intro x
      obtain ⟨e, he⟩ := hg (q x)
      exact ⟨⟨(e, x), (memP _).mpr he⟩, rfl⟩
  have hex : Function.Exact (LinearMap.lTensor M i') (LinearMap.lTensor M πE) := by
    refine lTensor_exact M ?_ ?_
    · rintro ⟨⟨e, x⟩, hp⟩
      have hp' := (memP _).mp hp
      constructor
      · intro he
        change e = 0 at he
        subst he
        rw [map_zero] at hp'
        obtain ⟨k, hk⟩ := (hiq x).mp hp'.symm
        exact ⟨k, Subtype.ext (Prod.ext rfl hk)⟩
      · rintro ⟨k, hk⟩
        rw [← hk]
        rfl
    · intro e
      obtain ⟨x, hx⟩ := hq (g e)
      exact ⟨⟨(e, x), (memP _).mpr hx.symm⟩, rfl⟩
  have hπEj : πE ∘ₗ j = f := rfl
  have hπFj : πF ∘ₗ j = 0 := rfl
  have hπFi' : πF ∘ₗ i' = i := rfl
  -- diagram chase: if `x ↦ 0` in `M ⊗ E`, its image in `M ⊗ P` comes from `y ∈ M ⊗ K'`, which
  -- maps to `0` in `M ⊗ F`, so `y = 0`
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h₁ : LinearMap.lTensor M πE (LinearMap.lTensor M j x) = 0 := by
    rw [← LinearMap.lTensor_comp_apply, hπEj, hx]
  obtain ⟨y, hy⟩ := (hex _).mp h₁
  have h₂ : LinearMap.lTensor M i y = 0 := by
    rw [← hπFi', LinearMap.lTensor_comp_apply, hy, ← LinearMap.lTensor_comp_apply, hπFj,
      LinearMap.lTensor_zero, LinearMap.zero_apply]
  have hy0 : y = 0 := (injective_iff_map_eq_zero _).mp hMi y h₂
  have h₃ : LinearMap.lTensor M j x = 0 := by rw [← hy, hy0, map_zero]
  exact (injective_iff_map_eq_zero _).mp hj x h₃

/-- `Tor₁^A(M, N₁ × N₂) = 0` when `Tor₁^A(M, N₁) = Tor₁^A(M, N₂) = 0`. -/
private theorem torOneZero_prod {N₁ N₂ : Type u} [AddCommGroup N₁] [Module A N₁]
    [AddCommGroup N₂] [Module A N₂] (h₁ : TorOneZero A M N₁) (h₂ : TorOneZero A M N₂) :
    TorOneZero A M (N₁ × N₂) :=
  torOneZero_of_exact (LinearMap.inl A N₁ N₂) (LinearMap.snd A N₁ N₂) LinearMap.inl_injective
    Function.Exact.inl_snd LinearMap.snd_surjective h₁ h₂

/-- `Tor₁^A(M, Xᵏ) = 0` when `Tor₁^A(M, X) = 0`. -/
private theorem torOneZero_pi {X : Type u} [AddCommGroup X] [Module A X] (h : TorOneZero A M X) :
    ∀ k : ℕ, TorOneZero A M (Fin k → X)
  | 0 => torOneZero_of_subsingleton _
  | k + 1 => torOneZero_of_equiv (Fin.consLinearEquiv A (fun _ : Fin (k + 1) => X))
      (torOneZero_prod h (torOneZero_pi h k))

/-- For `A/I`-modules, `M ⊗_A -` is `(M/IM) ⊗_{A/I} -`, so it preserves injectivity when `M/IM`
is `A/I`-flat. -/
private theorem lTensor_injective_of_flat_quotient (I : Ideal A)
    (hflat : Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M))
    {X Y : Type u} [AddCommGroup X] [Module (A ⧸ I) X] [Module A X] [IsScalarTower A (A ⧸ I) X]
    [AddCommGroup Y] [Module (A ⧸ I) Y] [Module A Y] [IsScalarTower A (A ⧸ I) Y]
    (i : X →ₗ[A ⧸ I] Y) (hi : Function.Injective i) :
    Function.Injective (LinearMap.lTensor M (i.restrictScalars A)) := by
  have h₁ : Function.Injective (LinearMap.rTensor ((A ⧸ I) ⊗[A] M) i) :=
    Module.Flat.rTensor_preserves_injective_linearMap i hi
  let eX := TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) X M
  let eY := TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) Y M
  have hnat : ∀ z, eY (LinearMap.rTensor _ i z) =
      LinearMap.rTensor M (i.restrictScalars A) (eX z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x w =>
      induction w using TensorProduct.inductionOn with
      | tmul a m => simp [eX, eY]
      | add w w' hw hw' => simp only [tmul_add, map_add] at hw hw' ⊢; rw [hw, hw']
    | add z z' hz hz' => simp only [map_add, hz, hz']
  have h₂ : Function.Injective (LinearMap.rTensor M (i.restrictScalars A)) := by
    intro z₁ z₂ h
    obtain ⟨w₁, rfl⟩ := eX.surjective z₁
    obtain ⟨w₂, rfl⟩ := eX.surjective z₂
    rw [← hnat, ← hnat] at h
    rw [h₁ (eY.injective h)]
  rw [← LinearMap.comm_comp_rTensor_comp_comm_eq]
  exact (TensorProduct.comm A Y M).injective.comp (h₂.comp (TensorProduct.comm A M X).injective)

/-- `Tor₁^A(M, A/I) = 0` when `M ⊗_A I → M` is injective. -/
private theorem torOneZero_quotient (I : Ideal A)
    (hinj : Function.Injective (fun x : M ⊗[A] I =>
      TensorProduct.rid A M (LinearMap.lTensor M I.subtype x))) :
    TorOneZero A M (A ⧸ I) :=
  torOneZero_of_presentation I.subtype I.mkQ (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective
    torOneZero_self (fun _ _ hxy => hinj (congrArg (TensorProduct.rid A M) hxy))

/-- `Tor₁^A(M, N) = 0` for every finite `A`-module `N` with a compatible `A/I`-module structure. -/
private theorem torOneZero_of_quotientModule (I : Ideal A)
    (hflat : Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M)) (hA : TorOneZero A M (A ⧸ I))
    (N : Type u) [AddCommGroup N] [Module (A ⧸ I) N] [Module A N] [IsScalarTower A (A ⧸ I) N]
    [Module.Finite A N] : TorOneZero A M N := by
  have : Module.Finite (A ⧸ I) N := Module.Finite.of_restrictScalars_finite A (A ⧸ I) N
  obtain ⟨k, q, hq⟩ := Module.Finite.exists_fin' (A ⧸ I) N
  exact torOneZero_of_presentation ((LinearMap.ker q).subtype.restrictScalars A)
    (q.restrictScalars A) (LinearMap.exact_subtype_ker_map q) hq (torOneZero_pi hA k)
    (lTensor_injective_of_flat_quotient I hflat _ Subtype.val_injective)

/-- Dévissage: `Tor₁^A(M, N) = 0` for every finite `A`-module `N` killed by a power of `I`. -/
private theorem torOneZero_of_pow_smul_eq_bot [IsNoetherianRing A] (I : Ideal A)
    (h₁ : ∀ (N : Type u) [AddCommGroup N] [Module (A ⧸ I) N] [Module A N]
      [IsScalarTower A (A ⧸ I) N] [Module.Finite A N], TorOneZero A M N) :
    ∀ (n : ℕ) (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N],
      I ^ n • (⊤ : Submodule A N) = ⊥ → TorOneZero A M N := by
  intro n
  induction n with
  | zero =>
    intro N _ _ _ hN
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hN
    have : Subsingleton N := ⟨fun x y => by
      have hx : x ∈ (⊥ : Submodule A N) := hN ▸ Submodule.mem_top
      have hy : y ∈ (⊥ : Submodule A N) := hN ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at hx hy
      rw [hx, hy]⟩
    exact torOneZero_of_subsingleton N
  | succ n ih =>
    intro N _ _ _ hN
    have : IsNoetherian A N := isNoetherian_of_isNoetherianRing_of_finite A N
    have : Module.Finite A ↥(I • (⊤ : Submodule A N)) :=
      Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    have hP : I ^ n • (⊤ : Submodule A ↥(I • (⊤ : Submodule A N))) = ⊥ := by
      apply Submodule.map_injective_of_injective (I • (⊤ : Submodule A N)).injective_subtype
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype, Submodule.map_bot,
        ← Submodule.mul_smul, ← pow_succ, hN]
    exact torOneZero_of_exact (I • (⊤ : Submodule A N)).subtype (I • (⊤ : Submodule A N)).mkQ
      (I • (⊤ : Submodule A N)).injective_subtype (LinearMap.exact_subtype_mkQ _)
      (Submodule.mkQ_surjective _) (ih _ hP) (h₁ _)

end TorOneZero

/-- Elements of `M ⊗_A P` mapping into `a • N` land in `a • (M ⊗_A N)`. -/
private theorem lTensor_mem_smul_top {A M N P : Type u} [CommRing A] [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P] (a : Ideal A)
    (g : P →ₗ[A] N) (hg : ∀ p, g p ∈ a • (⊤ : Submodule A N)) (v : M ⊗[A] P) :
    LinearMap.lTensor M g v ∈ a • (⊤ : Submodule A (M ⊗[A] N)) := by
  induction v using TensorProduct.inductionOn with
  | tmul m p =>
    have key : a • (⊤ : Submodule A N) ≤
        (a • (⊤ : Submodule A (M ⊗[A] N))).comap (TensorProduct.mk A M N m) := by
      rw [Submodule.smul_le]
      intro r hr n _
      rw [Submodule.mem_comap, map_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    exact key (hg p)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- `M ⊗_A N` is a finite `B`-module for a finite `B`-module `M` and a finite `A`-module `N`. -/
private theorem finite_tensor_left {A B M N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] [Module.Finite B M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] : Module.Finite B (M ⊗[A] N) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A N
  have hs : Function.Surjective (TensorProduct.AlgebraTensorModule.lTensor B M f) :=
    LinearMap.lTensor_surjective M hf
  have : Module.Finite B (M ⊗[A] (Fin n → A)) :=
    Module.Finite.equiv (TensorProduct.piScalarRight A B M (Fin n)).symm
  exact Module.Finite.of_surjective _ hs

/-- `P M = (P B) M` for a `B`-module `M`. -/
private theorem restrictScalars_map_smul_top {A B M : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M] (P : Ideal A) :
    ((P.map (algebraMap A B)) • (⊤ : Submodule B M)).restrictScalars A =
      (P • ⊤ : Submodule A M) := by
  have hstab : ∀ (b : B) (x : M), x ∈ (P • ⊤ : Submodule A M) →
      b • x ∈ (P • ⊤ : Submodule A M) := by
    intro b x hx
    refine Submodule.smul_induction_on hx (fun p hp m _ => ?_) (fun x y hx hy => ?_)
    · rw [smul_comm b p m]
      exact Submodule.smul_mem_smul hp Submodule.mem_top
    · rw [smul_add]
      exact add_mem hx hy
  apply le_antisymm
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule.smul_induction_on hx (fun j hj m _ => ?_) (fun x y hx hy => add_mem hx hy)
    have hj' : j ∈ Submodule.span B (algebraMap A B '' P) := hj
    clear hj
    induction hj' using Submodule.span_induction with
    | mem j hj =>
      obtain ⟨p, hp, rfl⟩ := hj
      rw [algebraMap_smul]
      exact Submodule.smul_mem_smul hp Submodule.mem_top
    | zero => rw [zero_smul]; exact zero_mem _
    | add j k _ _ hj hk => rw [add_smul]; exact add_mem hj hk
    | smul b j _ hj =>
      rw [smul_eq_mul, mul_smul]
      exact hstab b _ hj
  · rw [Submodule.smul_le]
    intro p hp m _
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul B p m]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hp) Submodule.mem_top

/-- Krull's intersection theorem for `M ⊗_A N`: an element of `⋂ₙ Iⁿ (M ⊗_A N)` is zero. -/
private theorem eq_zero_of_forall_mem_pow_smul_top {A B M N : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing B] [Algebra A B] [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] [Module.Finite B M] [AddCommGroup N] [Module A N] [Module.Finite A N]
    (I : Ideal A) (hI : I.map (algebraMap A B) ≤ Ring.jacobson B) (x : M ⊗[A] N)
    (hx : ∀ n : ℕ, x ∈ (I ^ n • ⊤ : Submodule A (M ⊗[A] N))) : x = 0 := by
  have : Module.Finite B (M ⊗[A] N) := finite_tensor_left
  have hJ : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥ := by rwa [Ideal.jacobson_bot]
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M ⊗[A] N) _ hJ
  have hmem : x ∈ (⨅ i : ℕ, (I.map (algebraMap A B)) ^ i • ⊤ : Submodule B (M ⊗[A] N)) := by
    rw [Submodule.mem_iInf]
    intro i
    have := hx i
    rw [← restrictScalars_map_smul_top (B := B), Ideal.map_pow] at this
    exact this
  rw [hK] at hmem
  exact hmem

/-- Local criterion of flatness, (ii) ⇒ (i): `M ⊗_A A/I` flat over `A/I` and `M ⊗_A I → M`
injective imply `M` flat over `A`. -/
@[blueprint "compat:local-flatness-criterion"
  (statement := /-- Let $A\to B$ be a homomorphism of noetherian rings, $I$ an ideal of $A$
    such that $IB$ is contained in the Jacobson radical of $B$, and $M$ a $B$-module of finite
    type. If $M\otimes_AA/I$ is a flat $A/I$-module and the multiplication map
    $M\otimes_AI\to M$ is injective, then $M$ is a flat $A$-module. -/)
  (proof := /-- Write $\operatorname{Tor}_1^A(M,N)=0$ for the statement that
    $M\otimes_AK\to M\otimes_AE$ is injective for every short exact sequence
    $0\to K\to E\to N\to0$; it holds for $N=A$ (the sequence splits), and it passes to
    extensions and along presentations $0\to K'\to F\to N\to0$ with
    $\operatorname{Tor}_1^A(M,F)=0$ and $M\otimes_AK'\to M\otimes_AF$ injective (a diagram
    chase through $E\times_NF$). Applied to $0\to I\to A\to A/I\to0$ this gives
    $\operatorname{Tor}_1^A(M,A/I)=0$, hence $\operatorname{Tor}_1^A(M,(A/I)^k)=0$. Next,
    $\operatorname{Tor}_1^A(M,N)=0$ for every $A$-module $N$ of finite type
    killed by $I$: present $N$ as a quotient of $(A/I)^k$ with kernel $K$; then
    $M\otimes_AK\to M\otimes_A(A/I)^k$ is $(M/IM)\otimes_{A/I}K\to(M/IM)\otimes_{A/I}(A/I)^k$,
    injective by flatness of $M/IM$, so the comparison applies. By
    d\'evissage along $N\supseteq IN\supseteq\dots$ the same holds for $N$ killed by a power
    of $I$. Now let $J$ be an ideal of $A$ and $u$ in the kernel of $M\otimes_AJ\to M$. For
    each $n$, $\operatorname{Tor}_1^A(M,A/(J+I^n))=0$ shows that
    $M\otimes_A(J+I^n)/I^n\to M\otimes_AA/I^n$ is injective, so $u$ comes from
    $M\otimes_A(J\cap I^n)$. By Artin--Rees, $J\cap I^n\subseteq I^{n-c}J$, so
    $u\in I^{n-c}(M\otimes_AJ)$ for all $n$; by Krull's intersection theorem for the finite
    $B$-module $M\otimes_AJ$ (with $IB$ in the Jacobson radical of $B$), $u=0$. Hence $M$ is
    flat by the ideal criterion. -/)
  (latexEnv := "lemma")]
theorem flat_of_flat_quotient_of_mul_injective (A : Type u) [CommRing A] [IsNoetherianRing A]
    (B : Type u) [CommRing B] [IsNoetherianRing B] [Algebra A B] (I : Ideal A)
    (hI : I.map (algebraMap A B) ≤ Ring.jacobson B)
    (M : Type u) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M]
    (hflat : Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M))
    (hinj : Function.Injective (fun x : M ⊗[A] I =>
      TensorProduct.rid A M (LinearMap.lTensor M I.subtype x))) :
    Module.Flat A M := by
  have hpow := torOneZero_of_pow_smul_eq_bot I
    (torOneZero_of_quotientModule I hflat (torOneZero_quotient I hinj))
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  have : Module.Finite A J := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian J)
  rw [injective_iff_map_eq_zero]
  intro u hu
  -- Artin–Rees for `J ⊆ A`
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I J
  apply eq_zero_of_forall_mem_pow_smul_top (B := B) I hI u
  intro n
  -- the image `K₀` of `J` in `A/Iⁿ⁺ᵏ`; `Tor₁^A(M, (A/Iⁿ⁺ᵏ)/K₀) = 0` as `(A/Iⁿ⁺ᵏ)/K₀` is
  -- killed by `Iⁿ⁺ᵏ`
  let K₀ : Submodule A (A ⧸ I ^ (n + k)) := Submodule.map (I ^ (n + k)).mkQ J
  have hK₀ : TorOneZero A M ((A ⧸ I ^ (n + k)) ⧸ K₀) := by
    refine hpow (n + k) _ (eq_bot_iff.mpr (Submodule.smul_le.mpr fun a ha x _ => ?_))
    obtain ⟨y, rfl⟩ := K₀.mkQ_surjective x
    obtain ⟨b, rfl⟩ := (I ^ (n + k)).mkQ_surjective y
    have hab : (I ^ (n + k)).mkQ (a • b) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mul_mem_right b _ ha)
    rw [Submodule.mem_bot, ← map_smul, ← map_smul, hab, map_zero]
  have hinjK : Function.Injective (LinearMap.lTensor M K₀.subtype) :=
    hK₀ K₀ (A ⧸ I ^ (n + k)) K₀.subtype K₀.mkQ K₀.injective_subtype
      (LinearMap.exact_subtype_mkQ K₀) K₀.mkQ_surjective
  -- hence `u` comes from `M ⊗_A (J ∩ Iⁿ⁺ᵏ)`
  let ρ : J →ₗ[A] K₀ := (I ^ (n + k)).mkQ.submoduleMap J
  have hρ : K₀.subtype ∘ₗ ρ = (I ^ (n + k)).mkQ ∘ₗ J.subtype := rfl
  have hρu : LinearMap.lTensor M ρ u = 0 := by
    apply hinjK
    rw [map_zero, ← LinearMap.lTensor_comp_apply, hρ, LinearMap.lTensor_comp_apply, hu, map_zero]
  let S : Submodule A J := Submodule.comap J.subtype (I ^ (n + k))
  have hex : Function.Exact S.subtype ρ := by
    intro x
    constructor
    · intro hx
      have : (I ^ (n + k)).mkQ (x : A) = 0 := congrArg Subtype.val hx
      exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero (I ^ (n + k))).mp this⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext ((Submodule.Quotient.mk_eq_zero (I ^ (n + k))).mpr y.2)
  obtain ⟨w, hw⟩ := (lTensor_exact M hex (LinearMap.submoduleMap_surjective _ _) u).mp hρu
  rw [← hw]
  -- by Artin–Rees, `J ∩ Iⁿ⁺ᵏ ⊆ Iⁿ J`
  refine lTensor_mem_smul_top (I ^ n) S.subtype (fun p => ?_) w
  rw [Submodule.mem_smul_top_iff]
  have hp : ((p : J) : A) ∈ I ^ (n + k) • (⊤ : Submodule A A) ⊓ J :=
    ⟨by rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact p.2, (p : J).2⟩
  rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at hp
  exact Submodule.smul_mono le_rfl inf_le_right hp

/-- Local criterion of flatness, (iii) ⇒ (ii): if every canonical map
`M ⊗_A Iⁿ/Iⁿ⁺¹ → IⁿM/Iⁿ⁺¹M` is injective, then `M ⊗_A I → M` is injective.  The hypothesis
`hgr` is the injectivity of `M ⊗_A Iⁿ/Iⁿ⁺¹ → IⁿM/Iⁿ⁺¹M` read through
`M ⊗_A Iⁿ ↠ M ⊗_A Iⁿ/Iⁿ⁺¹`: an element of `M ⊗_A Iⁿ` whose image in `IⁿM` lies in `Iⁿ⁺¹M`
maps to zero in `M ⊗_A Iⁿ/Iⁿ⁺¹`. -/
@[blueprint "compat:gr-injective-mul-injective"
  (statement := /-- Let $A\to B$ be a homomorphism of noetherian rings, $I$ an ideal of $A$
    such that $IB$ is contained in the Jacobson radical of $B$, and $M$ a $B$-module of finite
    type. If the canonical homomorphisms $M\otimes_AI^n/I^{n+1}\to I^nM/I^{n+1}M$ are injective
    for all $n$, then the multiplication map $M\otimes_AI\to M$ is injective. -/)
  (proof := /-- Let $u$ be in the kernel of $M\otimes_AI\to M$. By induction on $n\ge1$, $u$
    is the image of some $v_n\in M\otimes_AI^n$: the image of $v_n$ in $I^nM$ is $0$, so its
    class in $M\otimes_AI^n/I^{n+1}$ vanishes by injectivity, and right exactness of
    $M\otimes_A-$ on $I^{n+1}\to I^n\to I^n/I^{n+1}\to0$ gives $v_{n+1}$. Hence
    $u\in I^{n-1}(M\otimes_AI)$ for all $n$, and $u=0$ by Krull's intersection theorem for
    the finite $B$-module $M\otimes_AI$. -/)
  (latexEnv := "lemma")]
theorem mul_injective_of_forall_gr (A : Type u) [CommRing A] [IsNoetherianRing A]
    (B : Type u) [CommRing B] [IsNoetherianRing B] [Algebra A B] (I : Ideal A)
    (hI : I.map (algebraMap A B) ≤ Ring.jacobson B)
    (M : Type u) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M]
    (hgr : ∀ (n : ℕ) (s : M ⊗[A] ↥(I ^ n)),
      TensorProduct.rid A M (LinearMap.lTensor M (I ^ n).subtype s) ∈
        I ^ (n + 1) • (⊤ : Submodule A M) →
      LinearMap.lTensor M (Submodule.comap (I ^ n).subtype (I ^ (n + 1))).mkQ s = 0) :
    Function.Injective (fun x : M ⊗[A] I =>
      TensorProduct.rid A M (LinearMap.lTensor M I.subtype x)) := by
  have : Module.Finite A I := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian I)
  have hle : ∀ n : ℕ, I ^ (n + 1) ≤ I := fun n => Ideal.pow_le_self n.succ_ne_zero
  change Function.Injective ((TensorProduct.rid A M).toLinearMap ∘ₗ LinearMap.lTensor M I.subtype)
  rw [injective_iff_map_eq_zero]
  intro u hu
  -- `u` lifts to `M ⊗_A Iⁿ⁺¹` for every `n`
  have hlift : ∀ n : ℕ, ∃ v : M ⊗[A] ↥(I ^ (n + 1)),
      LinearMap.lTensor M (Submodule.inclusion (hle n)) v = u := by
    intro n
    induction n with
    | zero =>
      have h0 : I ≤ I ^ (0 + 1) := by rw [zero_add, pow_one]
      refine ⟨LinearMap.lTensor M (Submodule.inclusion h0) u, ?_⟩
      rw [← LinearMap.lTensor_comp_apply]
      have : Submodule.inclusion (hle 0) ∘ₗ Submodule.inclusion h0 = LinearMap.id := by
        ext; rfl
      rw [this, LinearMap.lTensor_id, LinearMap.id_apply]
    | succ n ih =>
      obtain ⟨v, rfl⟩ := ih
      have hle' : I ^ (n + 1 + 1) ≤ I ^ (n + 1) := Ideal.pow_le_pow_right (Nat.le_succ _)
      have hv : LinearMap.lTensor M
          (Submodule.comap (I ^ (n + 1)).subtype (I ^ (n + 1 + 1))).mkQ v = 0 := by
        apply hgr (n + 1) v
        have : TensorProduct.rid A M (LinearMap.lTensor M (I ^ (n + 1)).subtype v) = 0 := by
          rw [← hu, LinearMap.comp_apply, ← LinearMap.lTensor_comp_apply,
            Submodule.subtype_comp_inclusion]
          rfl
        rw [this]
        exact zero_mem _
      have hex := lTensor_exact M (f := Submodule.inclusion hle')
        (LinearMap.exact_iff.mpr (by rw [Submodule.ker_mkQ, Submodule.range_inclusion]))
        (Submodule.mkQ_surjective _)
      obtain ⟨w, hw⟩ := (hex v).mp hv
      refine ⟨w, ?_⟩
      rw [← hw, ← LinearMap.lTensor_comp_apply]
      rfl
  apply eq_zero_of_forall_mem_pow_smul_top (B := B) I hI u
  intro n
  obtain ⟨v, rfl⟩ := hlift n
  refine lTensor_mem_smul_top (I ^ n) _ (fun p => ?_) v
  rw [Submodule.mem_smul_top_iff]
  change (p : A) ∈ I ^ n • I
  rw [Ideal.smul_eq_mul, ← pow_succ]
  exact p.2

end Hironaka
