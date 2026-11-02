/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Architect
public import Hironaka.Compat.Graded
public import Hironaka.Compat.GradedModule
public import Hironaka.Ch2.Flatness

/-!
# Ch. II §2: the exact sequences of graded modules in the proof of Theorem 2 (pp. 195-196)

The proof of Theorem 2 (p. 195-196) shows that the canonical homomorphism `φ` of Lemma 2 of §1
is an isomorphism for the module `gr_P̄(O) = gr_P(R)/gr_P(J, R)` by a diagram chase on the
commutative diagram of doubly graded `O/Q̄`-algebras of p. 196 and, for each of the double grades
`(p, q)`, on the `3 × 3` diagram with exact columns
`0 → Q̄ᵖ⁺¹ M → Q̄ᵖ M → grᵖ_Q̄(M) → 0` (`M = gr^q_P(J, R), gr^q_P(R), gr^q_P̄(O)`).  This file
contains these two chases for modules over a ring `A` with an ideal `I`, and the passage from the
homogeneous parts `gr^q_P̄(O)` to `gr_P̄(O) = ⨁_q gr^q_P̄(O)` (Corollary to Lemma 2 of §1, p. 182:
"the homomorphism `φ` is the direct sum of the canonical homomorphisms `φₙ`").

* `GrModPiece.map` is the map `grᵐ_I(M) → grᵐ_I(N)` induced by an `A`-linear map; the canonical
  `φ` is natural for it (`GrModPiece.grModMap_comp_rTensor`).
* `GrModPiece.exact_map_of_inf_le`: in the diagram of p. 196 for the double grade `(p, q)`, "in
  order to prove `Ker(ε) = Im(δ)` for this diagram, it suffices that `Ker(ε') = Im(δ')`".
* `injective_grModMap_of_exact`: "it is easy to see that if the right vertical sequence is proved
  exact, then `φ` is an isomorphism".
* `bijective_grModMap_directSum`, `bijective_grModMap_assocGraded`: `φ` for `⨁_q M_q` and for
  `gr_P(O)`.
-/

@[expose] public section

open TensorProduct
open scoped DirectSum

namespace Hironaka

universe u

section GradedModuleSequence

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### Functoriality of `grᵐ_I(M)` -/

section Functoriality

variable {M N P : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P] [Module A P]

/-- The homomorphism `grᵐ_I(M) → grᵐ_I(N)` induced by an `A`-linear map `f : M → N` (which maps
`IᵐM` into `IᵐN` and `Iᵐ⁺¹M` into `Iᵐ⁺¹N`). -/
noncomputable def GrModPiece.map (m : ℕ) (f : M →ₗ[A] N) : GrModPiece I M m →ₗ[A] GrModPiece I N m :=
  Submodule.mapQ _ _
    (f.restrict fun _ hx => Submodule.smul_top_le_comap_smul_top (I ^ m) f hx)
    (fun _ hx => Submodule.smul_top_le_comap_smul_top (I ^ (m + 1)) f hx)

theorem GrModPiece.map_mk (m : ℕ) (f : M →ₗ[A] N) (x : ↥(I ^ m • (⊤ : Submodule A M))) :
    GrModPiece.map I m f (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨f x, Submodule.smul_top_le_comap_smul_top (I ^ m) f x.2⟩ :=
  rfl

theorem GrModPiece.map_comp (m : ℕ) (f : M →ₗ[A] N) (g : N →ₗ[A] P) :
    GrModPiece.map I m (g ∘ₗ f) = GrModPiece.map I m g ∘ₗ GrModPiece.map I m f := by
  refine LinearMap.ext fun z => ?_
  induction z using Submodule.Quotient.induction_on with
  | H x => rfl

theorem GrModPiece.map_id (m : ℕ) :
    GrModPiece.map I m (LinearMap.id : M →ₗ[A] M) = LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  induction z using Submodule.Quotient.induction_on with
  | H x => rfl

/-- `grᵐ_I` of an isomorphism is an isomorphism. -/
theorem GrModPiece.map_bijective_of_linearEquiv (m : ℕ) (e : M ≃ₗ[A] N) :
    Function.Bijective (GrModPiece.map I m (e : M →ₗ[A] N)) := by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨GrModPiece.map I m (e.symm : N →ₗ[A] M), fun z => ?_, fun z => ?_⟩
  · rw [← LinearMap.comp_apply, ← GrModPiece.map_comp]
    simp [GrModPiece.map_id]
  · rw [← LinearMap.comp_apply, ← GrModPiece.map_comp]
    simp [GrModPiece.map_id]

/-- If `f : M → N` is surjective, so is `grᵐ_I(f)`: `f` maps `IᵐM` onto `IᵐN`. -/
theorem GrModPiece.map_surjective (m : ℕ) {f : M →ₗ[A] N} (hf : Function.Surjective f) :
    Function.Surjective (GrModPiece.map I m f) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H y =>
    have hmap : (I ^ m • (⊤ : Submodule A M)).map f = I ^ m • ⊤ := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]
    have hy : (y : N) ∈ (I ^ m • (⊤ : Submodule A M)).map f := by rw [hmap]; exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
    rw [GrModPiece.map_mk]
    exact congrArg Submodule.Quotient.mk (Subtype.ext hxy)

/-- The canonical homomorphisms are natural in `M`:
`φ_N ∘ (f ⊗ 1) = grᵐ_I(f) ∘ φ_M` (p. 181, where `φ` is "induced by the operation of `A` on `M`"). -/
theorem GrModPiece.grModMap_comp_rTensor (m : ℕ) (f : M →ₗ[A] N) :
    grModMap I N m ∘ₗ LinearMap.rTensor (GrPiece I m) f =
      GrModPiece.map I m f ∘ₗ grModMap I M m := by
  refine TensorProduct.ext' fun x a => ?_
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, grModMap_tmul, GrModPiece.map_mk]
    exact congrArg Submodule.Quotient.mk (Subtype.ext (map_smul f a.1 x).symm)

/-- Bijectivity of the canonical `φ` is invariant under isomorphisms of the module. -/
theorem bijective_grModMap_of_linearEquiv (m : ℕ) (e : M ≃ₗ[A] N)
    (h : Function.Bijective (grModMap I M m)) : Function.Bijective (grModMap I N m) := by
  have h1 := GrModPiece.grModMap_comp_rTensor I m (e : M →ₗ[A] N)
  have h2 : Function.Bijective (LinearMap.rTensor (GrPiece I m) (e : M →ₗ[A] N)) :=
    (e.rTensor (GrPiece I m)).bijective
  have h3 : Function.Bijective (GrModPiece.map I m (e : M →ₗ[A] N)) :=
    GrModPiece.map_bijective_of_linearEquiv I m e
  have h4 : Function.Bijective ⇑(GrModPiece.map I m (e : M →ₗ[A] N) ∘ₗ grModMap I M m) :=
    h3.comp h
  rw [← h1, LinearMap.coe_comp] at h4
  exact (Function.Bijective.of_comp_iff _ h2).mp h4

end Functoriality

/-! ### The right-hand column of the diagram of Theorem 2 (p. 196) -/

section ExactSequence

variable {L F M : Type u} [AddCommGroup L] [Module A L] [AddCommGroup F] [Module A F]
  [AddCommGroup M] [Module A M]

/-- **Exactness of the right vertical sequence** of the diagram of Theorem 2 (p. 196).  For the
modules `L → F → M` (`L = gr_P(J, R)`, `F = gr_P(R)`, `M = gr_P̄(O)`, with `f : F → M` onto), the
sequence `grᵖ_I(L) → grᵖ_I(F) → grᵖ_I(M)` is exact in the middle as soon as `Ker(ε') = Im(δ')`,
that is, `IᵖF ∩ Ker f = IᵖL`, in the commutative diagram with exact columns
`0 → Iᵖ⁺¹N → IᵖN → grᵖ_I(N) → 0` (`N = L, F, M`) and rows `δ'' : Iᵖ⁺¹L → Iᵖ⁺¹F`,
`ε'' : Iᵖ⁺¹F → Iᵖ⁺¹M` and `δ'`, `ε'` in degree `p`; `ε''` is onto since `f` is. -/
@[blueprint "lem:II.2-2-right-exact"
  (statement := /-- Let $A$ be a ring, $I$ an ideal in $A$, and $i\colon L\to F$, $f\colon F\to M$
    homomorphisms of $A$-modules with $f$ surjective and $f\circ i=0$. Let $p\ge0$ and assume
    that every $x\in I^pF$ with $f(x)=0$ lies in $i(I^pL)$ (that is,
    $\operatorname{Ker}(\varepsilon')=\operatorname{Im}(\delta')$ in the diagram of p.~196). Then the
    sequence $\operatorname{gr}^p_I(L)\to\operatorname{gr}^p_I(F)\to\operatorname{gr}^p_I(M)$ is
    exact in the middle. (Theorem 2, p.~196: ``In order to prove $\operatorname{Ker}(\varepsilon)=
    \operatorname{Im}(\delta)$ for this diagram, it suffices that $\operatorname{Ker}(\varepsilon')=
    \operatorname{Im}(\delta')$.'') -/)
  (proof := /-- Let $x\in I^pF$ have class $\bar x\in\operatorname{gr}^p_I(F)$ with
    $\varepsilon(\bar x)=0$, that is $f(x)\in I^{p+1}M$. Since $f$ maps $I^{p+1}F$ onto $I^{p+1}M$
    ($\varepsilon''$ is surjective), there is $y\in I^{p+1}F$ with $f(y)=f(x)$. Then
    $x-y\in I^pF$ and $f(x-y)=0$, so $x-y=i(w)$ with $w\in I^pL$ by the assumption
    $\operatorname{Ker}(\varepsilon')=\operatorname{Im}(\delta')$; as $y\in I^{p+1}F$, $\bar x$ is the
    image of the class of $w$. Conversely $f\circ i=0$. This is the diagram chase left to the
    reader on p.~196. -/)
  (latexEnv := "lemma")]
theorem GrModPiece.exact_map_of_inf_le (i : L →ₗ[A] F) (f : F →ₗ[A] M)
    (hf : Function.Surjective f) (hif : ∀ x, f (i x) = 0) (p : ℕ)
    (hε : ∀ x ∈ I ^ p • (⊤ : Submodule A F), f x = 0 →
      x ∈ (I ^ p • (⊤ : Submodule A L)).map i) :
    Function.Exact (GrModPiece.map I p i) (GrModPiece.map I p f) := by
  intro z
  constructor
  · induction z using Submodule.Quotient.induction_on with
    | H x =>
      intro hx
      rw [GrModPiece.map_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.subtype_apply] at hx
      -- `ε''` is onto: `f x = f y` with `y ∈ Iᵖ⁺¹F`
      have hmap : (I ^ (p + 1) • (⊤ : Submodule A F)).map f = I ^ (p + 1) • ⊤ := by
        rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]
      obtain ⟨y, hy, hyx⟩ : (f x : M) ∈ (I ^ (p + 1) • (⊤ : Submodule A F)).map f := by
        rw [hmap]; exact hx
      have hyp : y ∈ I ^ p • (⊤ : Submodule A F) :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right p.le_succ) hy
      -- `x - y ∈ Ker f ∩ IᵖF = Im(δ')`
      obtain ⟨w, hw, hwx⟩ := hε (x - y) (sub_mem x.2 hyp) (by rw [map_sub, hyx, sub_self])
      refine ⟨Submodule.Quotient.mk ⟨w, hw⟩, ?_⟩
      rw [GrModPiece.map_mk]
      refine (Submodule.Quotient.eq _).mpr ?_
      rw [Submodule.mem_comap]
      show i w - (x : F) ∈ I ^ (p + 1) • (⊤ : Submodule A F)
      rw [hwx, sub_sub_cancel_left]
      exact neg_mem hy
  · rintro ⟨z, rfl⟩
    induction z using Submodule.Quotient.induction_on with
    | H w =>
      rw [GrModPiece.map_mk, GrModPiece.map_mk]
      refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
      rw [Submodule.mem_comap, Submodule.subtype_apply]
      show f (i w) ∈ _
      rw [hif]
      exact zero_mem _

end ExactSequence

/-! ### `φ` is an isomorphism for a quotient (p. 196) -/

section PhiChase

variable {L F M : Type u} [AddCommGroup L] [Module A L] [AddCommGroup F] [Module A F]
  [AddCommGroup M] [Module A M]

/-- **The diagram chase of p. 196**, "It is easy to see that if the right vertical sequence is
proved exact, then `φ` is an isomorphism": in the commutative diagram
`L ⊗ G → F ⊗ G → M ⊗ G → 0` over `grᵐ_I(L) → grᵐ_I(F) → grᵐ_I(M)` (`G = grᵐ_I(A)`), with `φ_F`
an isomorphism, `φ_L` onto and the second row exact in the middle, `φ_M` is injective. -/
@[blueprint "lem:II.2-2-phi-injective"
  (statement := /-- Let $A$ be a ring, $I$ an ideal in $A$, $m\ge0$, and $i\colon L\to F$,
    $f\colon F\to M$ homomorphisms of $A$-modules with $f$ surjective and $f\circ i=0$. Assume that
    $\varphi_F\colon F\otimes_A\operatorname{gr}^m_I(A)\to\operatorname{gr}^m_I(F)$ is injective,
    $\varphi_L$ is surjective, and that $\operatorname{gr}^m_I(L)\to\operatorname{gr}^m_I(F)\to
    \operatorname{gr}^m_I(M)$ is exact in the middle. Then $\varphi_M$ is injective. (Theorem 2,
    p.~196: ``It is easy to see that if the right vertical sequence is proved exact, then
    $\varphi$ is an isomorphism.'') -/)
  (proof := /-- Let $z\in M\otimes_A\operatorname{gr}^m_I(A)$ with $\varphi_M(z)=0$. Since $f$ is
    surjective, $z=(f\otimes1)(t)$ for some $t\in F\otimes\operatorname{gr}^m_I(A)$ (right
    exactness of the tensor product). By naturality of $\varphi$,
    $\operatorname{gr}(f)(\varphi_F(t))=\varphi_M(z)=0$, so $\varphi_F(t)=\operatorname{gr}(i)(w)$
    with $w=\varphi_L(u)$, and $\varphi_F(t)=\varphi_F((i\otimes1)(u))$. As $\varphi_F$ is
    injective, $t=(i\otimes1)(u)$, hence $z=((f\circ i)\otimes1)(u)=0$. -/)
  (latexEnv := "lemma")]
theorem injective_grModMap_of_exact (i : L →ₗ[A] F) (f : F →ₗ[A] M)
    (hf : Function.Surjective f) (hif : ∀ x, f (i x) = 0) (m : ℕ)
    (hF : Function.Injective (grModMap I F m)) (hL : Function.Surjective (grModMap I L m))
    (hex : Function.Exact (GrModPiece.map I m i) (GrModPiece.map I m f)) :
    Function.Injective (grModMap I M m) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨t, rfl⟩ := LinearMap.rTensor_surjective (GrPiece I m) hf z
  have h1 : GrModPiece.map I m f (grModMap I F m t) = 0 := by
    rw [← LinearMap.comp_apply, ← GrModPiece.grModMap_comp_rTensor, LinearMap.comp_apply]
    exact hz
  obtain ⟨w, hw⟩ := (hex _).mp h1
  obtain ⟨u, rfl⟩ := hL w
  have h2 : t = LinearMap.rTensor (GrPiece I m) i u := by
    apply hF
    rw [← LinearMap.comp_apply (grModMap I F m), GrModPiece.grModMap_comp_rTensor,
      LinearMap.comp_apply, hw]
  have hfi : f ∘ₗ i = 0 := LinearMap.ext hif
  rw [h2, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hfi, LinearMap.rTensor_zero,
    LinearMap.zero_apply]

end PhiChase

/-! ### Direct sums and `gr_P(O)` -/

section DirectSumPieces

variable {ι : Type} [DecidableEq ι] (N : ι → Type u) [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]

/-- The `i`th component of `(⨁ N) ⊗ G ≅ ⨁ (N i ⊗ G)` is `(component i) ⊗ 1`. -/
theorem directSumLeft_apply_eq_rTensor_component (G : Type u) [AddCommGroup G] [Module A G]
    (x : (⨁ i, N i) ⊗[A] G) (i : ι) :
    TensorProduct.directSumLeft A A N G x i =
      LinearMap.rTensor G (DirectSum.component A ι N i) x := by
  induction x with
  | tmul n g => rw [TensorProduct.directSumLeft_tmul]; rfl
  | add a b ha hb => rw [map_add, DirectSum.add_apply, ha, hb, map_add]

/-- The canonical `φ` of a direct sum is injective if it is so for every summand
(Corollary to Lemma 2, p. 182: "`φ` is the direct sum of the canonical homomorphisms `φₙ`"). -/
theorem injective_grModMap_directSum (m : ℕ)
    (h : ∀ i, Function.Injective (grModMap I (N i) m)) :
    Function.Injective (grModMap I (⨁ i, N i) m) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply (TensorProduct.directSumLeft A A N (GrPiece I m)).injective
  rw [map_zero]
  refine DirectSum.ext_component A fun i => ?_
  have h1 := LinearMap.congr_fun
    (GrModPiece.grModMap_comp_rTensor I m (DirectSum.component A ι N i)) x
  simp only [LinearMap.comp_apply, hx, map_zero] at h1
  have h2 : LinearMap.rTensor (GrPiece I m) (DirectSum.component A ι N i) x = 0 :=
    h i (by rw [map_zero]; exact h1)
  rw [map_zero]
  show TensorProduct.directSumLeft A A N (GrPiece I m) x i = 0
  exact (directSumLeft_apply_eq_rTensor_component N _ x i).trans h2

/-- The canonical `φ` of a direct sum is bijective if it is so for every summand. -/
theorem bijective_grModMap_directSum (m : ℕ)
    (h : ∀ i, Function.Bijective (grModMap I (N i) m)) :
    Function.Bijective (grModMap I (⨁ i, N i) m) :=
  ⟨injective_grModMap_directSum I N m fun i => (h i).1, grModMap_surjective I _ m⟩

end DirectSumPieces

/-- **`φ` for `gr_P(O)`** (p. 182: "`φ` is the direct sum of the canonical homomorphisms `φₙ`"):
for `gr_P(O) = ⨁ₚ grᵖ_P(O)`, the canonical `φ` of an ideal `K` of `O/P` is bijective in degree `m`
as soon as it is so for each homogeneous part `grᵖ_P(O)`. -/
theorem bijective_grModMap_assocGraded {O : Type u} [CommRing O] (P : Ideal O)
    (K : Ideal (O ⧸ P)) (m : ℕ)
    (h : ∀ q, Function.Bijective (grModMap K (GrPiece P q) m)) :
    Function.Bijective (grModMap K (AssocGraded P) m) :=
  bijective_grModMap_of_linearEquiv K m
    (LinearEquiv.ofBijective (toGr P) (toGr_bijective P))
    (bijective_grModMap_directSum K (fun q => GrPiece P q) m h)

end GradedModuleSequence

end Hironaka
