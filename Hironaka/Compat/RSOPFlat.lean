/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.RegularLocalRing
public import Hironaka.Compat.RegularQuotient
public import Hironaka.Compat.LocalFlatness

/-!
# Compatibility layer: flatness of RSOP-preserving local homomorphisms (p. 207)

Hironaka (p. 207, proof of the Corollary to Lemma 2) asserts, without proof, that if a local
homomorphism `α : R → R'` of regular local rings transforms a regular system of parameters of `R`
into one of `R'`, then `R'` is flat over `R`; the fact is used again on p. 216.  We prove it here
(Matsumura, *Commutative Ring Theory*, Theorem 23.1, specialised), by induction on the number `n`
of parameters:

* `n = 0`: `R` is a field, so every `R`-module is flat;
* `n + 1`: for `x ∈ s`, the quotients `R/xR` and `R'/α(x)R'` are regular local rings, `α` induces
  a local homomorphism between them which again maps a regular system of parameters (the images of
  `s \ {x}`) onto a regular system of parameters, so `R'/xR'` is flat over `R/xR` by induction;
  and `x` acts injectively on `R'` (a domain, `α x ≠ 0`), so `R' ⊗_R (x) → R'` is injective.  The
  local criterion of flatness `flat_of_flat_quotient_of_mul_injective` then gives that `R'` is
  flat over `R`.

This file does not import `Hironaka.Ch3.*`; the theorem is stated for an explicit system of
parameters `s` and is used (in `Hironaka/Ch3/Basic.lean`) to discharge `RingHom.MapsRSOP.flat`.
-/

@[expose] public section

open IsLocalRing TensorProduct
open scoped Classical

namespace Hironaka
universe u

/-- For a regular system of parameters `s` of a regular local ring, `|s|` is the minimal number of
generators of the maximal ideal. -/
theorem IsRegularSystemOfParameters.spanFinrank_maximalIdeal_eq_card {A : Type u} [CommRing A] [IsRegularLocalRing A]
    {s : Finset A} (hs : IsRegularSystemOfParameters A s) :
    (maximalIdeal A).spanFinrank = s.card := by
  have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
  rw [← hs.2] at h
  exact_mod_cast h

/-- A member `x` of a regular system of parameters lies outside `M²` (otherwise `s \ {x}` would
generate `M`, which needs `|s|` generators). -/
theorem IsRegularSystemOfParameters.notMem_maximalIdeal_sq {A : Type u} [CommRing A] [IsRegularLocalRing A]
    {s : Finset A} (hs : IsRegularSystemOfParameters A s) {x : A} (hx : x ∈ s) :
    x ∉ maximalIdeal A ^ 2 := by
  intro h2
  have hspan := span_erase_eq_of_mem hs.1 hx (Ideal.mem_sup_right h2)
  have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := A)
    (s := ((s.erase x : Finset A) : Set A)) (Finset.finite_toSet _)
  have h3 := IsRegularSystemOfParameters.spanFinrank_maximalIdeal_eq_card hs
  have h4 : (maximalIdeal A).spanFinrank ≤ (s.erase x).card := by
    have := h1
    rw [Set.ncard_coe_finset] at this
    simpa [← hspan] using this
  rw [Finset.card_erase_of_mem hx] at h4
  have := Finset.card_pos.mpr ⟨x, hx⟩
  omega

/-- Quotient of an RSOP by one of its elements. -/
theorem IsRegularSystemOfParameters.isRegularLocalRing_and_isRegularSystemOfParameters_quotient_span_singleton {A : Type u} [CommRing A] [IsRegularLocalRing A]
    {s : Finset A} (hs : IsRegularSystemOfParameters A s) {x : A} (hx : x ∈ s)
    [IsLocalRing (A ⧸ Ideal.span {x})] :
    IsRegularLocalRing (A ⧸ Ideal.span {x}) ∧
    IsRegularSystemOfParameters (A ⧸ Ideal.span {x})
      ((s.erase x).image (Ideal.Quotient.mk (Ideal.span {x}))) ∧
    Set.InjOn (Ideal.Quotient.mk (Ideal.span {x})) (s.erase x : Set A) := by
  have hxM : x ∈ maximalIdeal A := hs.1 ▸ Ideal.subset_span hx
  obtain ⟨hQ, hrk⟩ := quotient_span_singleton_regular hxM (IsRegularSystemOfParameters.notMem_maximalIdeal_sq hs hx)
  set mk := Ideal.Quotient.mk (Ideal.span {x}) with hmk
  have hcard := IsRegularSystemOfParameters.spanFinrank_maximalIdeal_eq_card hs
  have hn : (s.erase x).card + 1 = s.card := Finset.card_erase_add_one hx
  have hspan : Ideal.span (((s.erase x).image mk : Finset _) : Set (A ⧸ Ideal.span {x}))
      = maximalIdeal (A ⧸ Ideal.span {x}) := by
    rw [← map_maximalIdeal_of_surjective mk Ideal.Quotient.mk_surjective, ← hs.1]
    rw [Finset.coe_image, ← Ideal.map_span]
    apply le_antisymm
    · exact Ideal.map_mono (Ideal.span_mono (by simp))
    · rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        have h0 : mk y = 0 := by rw [hmk, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
        rw [SetLike.mem_coe, Ideal.mem_comap, h0]; exact Ideal.zero_mem _
      · exact Ideal.mem_map_of_mem mk (Ideal.subset_span (Finset.mem_erase.mpr ⟨hyx, hy⟩))
  have hle : (maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank ≤ ((s.erase x).image mk).card := by
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := A ⧸ Ideal.span {x})
      (s := (((s.erase x).image mk : Finset _) : Set (A ⧸ Ideal.span {x}))) (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at this
    have h5 : Submodule.span (A ⧸ Ideal.span {x}) (((s.erase x).image mk : Finset _) : Set (A ⧸ Ideal.span {x})) = maximalIdeal (A ⧸ Ideal.span {x}) := hspan
    rwa [h5] at this
  have hle2 := Finset.card_image_le (s := s.erase x) (f := mk)
  have hcardQ : ((s.erase x).image mk).card = (s.erase x).card := by omega
  refine ⟨hQ, ⟨hspan, ?_⟩, Finset.card_image_iff.mp hcardQ⟩
  have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A ⧸ Ideal.span {x})
  rw [h.symm]
  have : (maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank = ((s.erase x).image mk).card := by omega
  rw [this]

/-- The map induced on quotients by a local homomorphism is local. -/
theorem isLocalHom_quotientMap_of_le_comap {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (f : A →+* B) [IsLocalHom f] (I : Ideal A) (J : Ideal B) (h : I ≤ J.comap f)
    [IsLocalRing (A ⧸ I)] [IsLocalRing (B ⧸ J)] :
    IsLocalHom (Ideal.quotientMap J f h) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.quotientMap_mk] at ha
  have : IsLocalHom (Ideal.Quotient.mk J) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have h1 : IsUnit (f a) := IsLocalHom.map_nonunit _ ha
  exact (Ideal.Quotient.mk I).isUnit_map (IsLocalHom.map_nonunit a h1)

/-- `M ⊗_A (x) → M` is injective when `A` is a domain, `x ≠ 0`, and `x` acts injectively on `M`
(as `(x) ≅ A`). -/
theorem injective_tmul_span_singleton_of_injective_smul {A : Type u} [CommRing A] [IsDomain A] {x : A}
    (hx : x ≠ 0) (M : Type u) [AddCommGroup M] [Module A M]
    (hM : Function.Injective (fun m : M => x • m)) :
    Function.Injective (fun y : M ⊗[A] (Ideal.span {x}) =>
      TensorProduct.rid A M (LinearMap.lTensor M (Ideal.span {x}).subtype y)) := by
  let f : A →ₗ[A] Ideal.span {x} :=
    { toFun := fun r => ⟨r * x, Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩⟩
      map_add' := fun a b => by ext; simp [add_mul]
      map_smul' := fun a b => by ext; simp [mul_assoc] }
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      have := congrArg Subtype.val h
      exact mul_right_cancel₀ hx this
    · rintro ⟨y, hy⟩
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      exact ⟨r, rfl⟩
  let e := LinearEquiv.ofBijective f hf
  let φ : M ⊗[A] (Ideal.span {x}) →ₗ[A] M :=
    (TensorProduct.rid A M).toLinearMap ∘ₗ LinearMap.lTensor M (Ideal.span {x}).subtype
  let ψ : M ⊗[A] A →ₗ[A] M := (x • (LinearMap.id : M →ₗ[A] M)) ∘ₗ (TensorProduct.rid A M).toLinearMap
  have key : φ ∘ₗ LinearMap.lTensor M e.toLinearMap = ψ := by
    apply TensorProduct.ext'
    intro m r
    simp [φ, ψ, e, f, mul_comm, mul_smul]
  have hψ : Function.Injective ψ := by
    intro a b h
    apply (TensorProduct.rid A M).injective
    exact hM h
  intro a b h
  have hφ : φ a = φ b := h
  obtain ⟨a', rfl⟩ : ∃ a', LinearMap.lTensor M e.toLinearMap a' = a :=
    ⟨LinearMap.lTensor M e.symm.toLinearMap a, by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]; simp⟩
  obtain ⟨b', rfl⟩ : ∃ b', LinearMap.lTensor M e.toLinearMap b' = b :=
    ⟨LinearMap.lTensor M e.symm.toLinearMap b, by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]; simp⟩
  have : ψ a' = ψ b' := by
    rw [← key]; exact hφ
  rw [hψ this]

/-- `IsRegularSystemOfParameters.isRegularLocalRing_and_isRegularSystemOfParameters_quotient_span_singleton` for a quotient by an ideal `J` known to equal `(x)`. -/
theorem IsRegularSystemOfParameters.isRegularLocalRing_and_isRegularSystemOfParameters_quotient_of_eq_span_singleton {A : Type u} [CommRing A] [IsRegularLocalRing A]
    {s : Finset A} (hs : IsRegularSystemOfParameters A s) {x : A} (hx : x ∈ s)
    (J : Ideal A) (hJ : J = Ideal.span {x}) [IsLocalRing (A ⧸ J)] :
    IsRegularLocalRing (A ⧸ J) ∧
    IsRegularSystemOfParameters (A ⧸ J) ((s.erase x).image (Ideal.Quotient.mk J)) ∧
    Set.InjOn (Ideal.Quotient.mk J) (s.erase x : Set A) := by
  subst hJ
  exact IsRegularSystemOfParameters.isRegularLocalRing_and_isRegularSystemOfParameters_quotient_span_singleton hs hx

/-- Transport of flatness of `B/IB` over `A/I` (through `Ideal.quotientMap`) to the tensor product
`(A/I) ⊗_A B`. -/
theorem flat_quotient_tensor_of_flat_quotientMap (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A)
    (h : letI := (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map : A ⧸ I →+* B ⧸ I.map (algebraMap A B)).toAlgebra
      Module.Flat (A ⧸ I) (B ⧸ I.map (algebraMap A B))) :
    Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] B) := by
  have hinst : (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map : A ⧸ I →+* B ⧸ I.map (algebraMap A B)).toAlgebra =
      (inferInstance : Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B))) := by
    apply Algebra.algebra_ext
    intro r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    rfl
  rw [hinst] at h
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv

/-- Induction core of `flat_of_isRegularSystemOfParameters_image`, on `n = |s|`. -/
theorem flat_of_card_eq_of_isRegularSystemOfParameters_image : ∀ (n : ℕ) (R R' : Type u) [CommRing R] [CommRing R'] [IsRegularLocalRing R]
    [IsRegularLocalRing R'] (α : R →+* R') [IsLocalHom α] (s : Finset R),
    s.card = n → IsRegularSystemOfParameters R s → IsRegularSystemOfParameters R' (s.image α) →
    Set.InjOn α s → @Module.Flat R R' _ _ α.toAlgebra.toModule := by
  intro n
  induction n with
  | zero =>
    intro R R' _ _ _ _ α _ s hcard hs hs' hinj
    have hbot : maximalIdeal R = ⊥ := by
      rw [← hs.1, Finset.card_eq_zero.mp hcard]; simp
    let _ : Field R := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot).toField
    let := α.toAlgebra
    exact Module.Flat.of_free
  | succ n ih =>
    intro R R' _ _ _ _ α _ s hcard hs hs' hinj
    obtain ⟨x, hx⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
    have hxM : x ∈ maximalIdeal R := hs.1 ▸ Ideal.subset_span hx
    have hx' : α x ∈ s.image α := Finset.mem_image_of_mem α hx
    have hxM' : α x ∈ maximalIdeal R' := hs'.1 ▸ Ideal.subset_span hx'
    have hxsq := IsRegularSystemOfParameters.notMem_maximalIdeal_sq hs hx
    have hxsq' := IsRegularSystemOfParameters.notMem_maximalIdeal_sq hs' hx'
    set I : Ideal R := Ideal.span {x} with hI
    obtain ⟨J, hJdef⟩ : ∃ J : Ideal R', J = I.map α := ⟨_, rfl⟩
    have hJ : J = Ideal.span {α x} := by
      rw [hJdef, hI, Ideal.map_span, Set.image_singleton]
    have hIle : I ≤ maximalIdeal R := by
      rw [hI, Ideal.span_le, Set.singleton_subset_iff]; exact hxM
    have hJle : J ≤ maximalIdeal R' := by
      rw [hJ, Ideal.span_le, Set.singleton_subset_iff]; exact hxM'
    have : IsLocalRing (R ⧸ I) := isLocalRing_quotient_of_le hIle
    have : IsLocalRing (R' ⧸ J) := isLocalRing_quotient_of_le hJle
    obtain ⟨hQ, hQs, hQinj⟩ := IsRegularSystemOfParameters.isRegularLocalRing_and_isRegularSystemOfParameters_quotient_of_eq_span_singleton hs hx I rfl
    obtain ⟨hQ', hQs', hQinj'⟩ := IsRegularSystemOfParameters.isRegularLocalRing_and_isRegularSystemOfParameters_quotient_of_eq_span_singleton hs' hx' J hJ
    have hle : I ≤ J.comap α := by
      rw [hJdef]; exact Ideal.le_comap_map
    let ᾱ : R ⧸ I →+* R' ⧸ J := Ideal.quotientMap J α hle
    have : IsLocalHom ᾱ := isLocalHom_quotientMap_of_le_comap α I J hle
    have herase : (s.image α).erase (α x) = (s.erase x).image α := by
      ext y
      simp only [Finset.mem_erase, Finset.mem_image]
      constructor
      · rintro ⟨hy, z, hz, rfl⟩
        exact ⟨z, ⟨fun h => hy (by rw [h]), hz⟩, rfl⟩
      · rintro ⟨z, ⟨hzx, hz⟩, rfl⟩
        exact ⟨fun h => hzx (hinj hz hx h), z, hz, rfl⟩
    have himg : ((s.erase x).image (Ideal.Quotient.mk I)).image ᾱ =
        ((s.image α).erase (α x)).image (Ideal.Quotient.mk J) := by
      rw [herase, Finset.image_image, Finset.image_image]
      apply Finset.image_congr
      intro z _
      simp [ᾱ]
    have hn1 : ((s.erase x).image (Ideal.Quotient.mk I)).card = n := by
      rw [Finset.card_image_iff.mpr hQinj, Finset.card_erase_of_mem hx]; omega
    have hn2 : (((s.image α).erase (α x)).image (Ideal.Quotient.mk J)).card = n := by
      rw [Finset.card_image_iff.mpr hQinj', Finset.card_erase_of_mem hx',
        Finset.card_image_of_injOn hinj]; omega
    have hflatQ : @Module.Flat (R ⧸ I) (R' ⧸ J) _ _ ᾱ.toAlgebra.toModule := by
      refine ih (R ⧸ I) (R' ⧸ J) ᾱ _ hn1 hQs ?_ ?_
      · rw [himg]; exact hQs'
      · apply Finset.card_image_iff.mp
        rw [himg, hn1, hn2]
    let := α.toAlgebra
    have hR'dom : IsDomain R' := isDomain_of_isRegularLocalRing R'
    have hαx0 : α x ≠ 0 := by
      intro h0; exact hxsq' (h0 ▸ Ideal.zero_mem _)
    have hx0 : x ≠ 0 := by
      intro h0; exact hxsq (h0 ▸ Ideal.zero_mem _)
    have hRdom : IsDomain R := isDomain_of_isRegularLocalRing R
    have hαx0' : algebraMap R R' x ≠ 0 := hαx0
    subst hJdef
    refine flat_of_flat_quotient_of_mul_injective R R' I ?_ R' ?_ ?_
    · refine hJle.trans ?_
      rw [← Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · exact flat_quotient_tensor_of_flat_quotientMap R R' I hflatQ
    · exact injective_tmul_span_singleton_of_injective_smul hx0 R' (fun a b h =>
        mul_left_cancel₀ hαx0' (by simpa [Algebra.smul_def] using h))

/-- p. 207 (proof of the Corollary to Lemma 2): "The assumption on `α` implies that `R'` is flat
over `R`."  Here `α : R → R'` is a local homomorphism of regular local rings and `s` is a regular
system of parameters of `R` such that `α` is injective on `s` and `α(s)` is a regular system of
parameters of `R'`.

Deviation from the paper (gap filled): the paper asserts this without proof (and uses it again on
p. 216).  Lean proves it: induction on `|s|` (Matsumura, Theorem 23.1, specialised), the case
`|s| = 0` being a field, and the inductive step passing to `R/xR → R'/α(x)R'` for `x ∈ s` and
applying the local criterion of flatness `flat_of_flat_quotient_of_mul_injective`. -/
@[blueprint "lem:III.2-rsop-flat"
  (statement := /-- Let $\alpha\colon R\to R'$ be a local homomorphism of regular local rings and
    $s$ a regular system of parameters of $R$ on which $\alpha$ is injective and such that
    $\alpha(s)$ is a regular system of parameters of $R'$ (\cref{def:III.rsop-map}). Then $R'$ is
    flat over $R$ (p.~207). -/)
  (proof := /-- Induction on the number $n=|s|$ of parameters. If $n=0$, $R$ is a field and every
    $R$-module is flat. Let $n>0$ and $x\in s$. Then $x\notin M^2$ and $\alpha(x)\notin M'^2$, so
    $\bar R=R/xR$ and $\bar R'=R'/\alpha(x)R'$ are regular local rings (\cref{lem:regular-quotient-hyperplane}),
    the induced map $\bar R\to\bar R'$ is local, and the images of $s\smallsetminus\{x\}$
    form regular systems of parameters of $\bar R$ and $\bar R'$ (their number is at most $n-1$
    and generate the maximal ideals, which need $n-1$ generators). By induction $\bar R'$ is flat
    over $\bar R$. Since $R'$ is a domain and $\alpha(x)\neq0$, multiplication by $\alpha(x)$ is
    injective on $R'$; as $xR\cong R$ this says $R'\otimes_R xR\to R'$ is injective. As
    $\alpha(x)R'$ lies in the radical of $R'$, the local criterion of flatness
    (\cref{compat:local-flatness-criterion}) shows that $R'$ is flat over $R$.

    \textbf{Deviation from the paper (gap filled).} The paper asserts on p.~207 ``The assumption
    on $\alpha$ implies that $R'$ is flat over $R$'' without proof. Lean proves this fact
    (Matsumura, Theorem~23.1, specialised) by the induction and the local flatness criterion
    described above. -/)
  (latexEnv := "lemma")]
theorem flat_of_isRegularSystemOfParameters_image {R R' : Type u} [CommRing R] [CommRing R']
    [IsRegularLocalRing R] [IsRegularLocalRing R'] (α : R →+* R') [IsLocalHom α] (s : Finset R)
    (hs : IsRegularSystemOfParameters R s) (hs' : IsRegularSystemOfParameters R' (s.image α))
    (hinj : Set.InjOn α s) :
    letI := α.toAlgebra
    Module.Flat R R' :=
  flat_of_card_eq_of_isRegularSystemOfParameters_image s.card R R' α s rfl hs hs' hinj

end Hironaka

