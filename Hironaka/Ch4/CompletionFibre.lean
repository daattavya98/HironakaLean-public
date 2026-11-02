/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch4.ImplicationsAB

/-!
# Ch. IV §3 (pp. 295–296, 316): the Corollary of (AB.3) for `B̂` not necessarily reduced

> LEMMA (CD.3) … Moreover, if `B̂` is any irreducible subscheme of `X̂_s` such that
> `ĝ_s(B̂) = x̂₀`, there exists a unique irreducible subscheme `B` of `X_s` such that
> `B̂ = c_s⁻¹(B)`, that `B = c_s(B̂)` and that `c_s` induces an isomorphism `B̂ → B`. (p. 316)

The paper's justification is the Corollary of (AB.3) (p. 296), which `ImplicationsAB` proves for
**reduced** `B̂` (`AB.Completion.exists_unique_isReduced_totalTransform`).  This file proves it
for arbitrary (possibly non-reduced) `B̂`, in the following way.

* At a point `ŷ` of `B̂` (a point of `ĝ_s⁻¹(x̂₀)`) the stalk ideal `I` of `B̂` contains a power
  `(M̂Ŝ_s)^k` of the ideal of the fibre (`exists_pow_fiberIdeal_le_stalkIdeal`: the radical of
  `I` is the stalk of the reduced structure on `B̂`, which contains `M̂Ŝ_s`).
* By `S_s/MS_s ≅ Ŝ_s/M̂Ŝ_s` (`Completion.comap_map_le_and_exists_sub_mem_fiberIdeal`) one has
  `Ŝ_s = S_s + M̂^k Ŝ_s` for all `k`, hence `S_s → Ŝ_s/I` is onto and `I = (I ∩ S_s)Ŝ_s`
  (`Completion.surjective_and_map_comap_eq`), while `S_s → Ŝ_s` is faithfully flat
  (`Completion.comap_map_stalkMap`: MapsRSOP, Lemma 2 of Ch. III §2), so `(JŜ_s) ∩ S_s = J`.
* Therefore `c_s ∘ ι_{B̂} : B̂ → X_s` is a closed immersion (the points: `c_s` is a homeomorphism
  from `ĝ_s⁻¹(x̂₀)` onto `g_s⁻¹(x₀)` and `x₀` is closed), `B` is its kernel (image), `B̂ ≅ B`,
  `B̂ = c_s⁻¹(B)` stalkwise, and uniqueness follows from faithful flatness.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits

namespace Hironaka

universe u

namespace AB

section PowerAlgebra

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)

/-- If `B = f(A) + N B`, then `B = f(A) + N^n B` for every `n`. -/
theorem exists_sub_mem_map_pow (N : Ideal A) (h : ∀ b, ∃ a, f a - b ∈ N.map f) (n : ℕ) :
    ∀ b, ∃ a, f a - b ∈ (N.map f) ^ n := by
  induction n with
  | zero => intro b; exact ⟨0, by simp⟩
  | succ n ih =>
    have key : ∀ x ∈ (N.map f) ^ n, ∃ a, f a - x ∈ (N.map f) ^ (n + 1) := by
      intro x hx
      rw [← Ideal.map_pow] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, -, rfl⟩ := hx
        exact ⟨m, by simp⟩
      | zero => exact ⟨0, by simp⟩
      | add x y hx hy ex ey =>
        obtain ⟨a, ha⟩ := ex
        obtain ⟨a', ha'⟩ := ey
        refine ⟨a + a', ?_⟩
        have := add_mem ha ha'
        convert this using 1
        rw [map_add]; ring
      | smul r x hx ex =>
        obtain ⟨a, ha⟩ := ex
        obtain ⟨ar, har⟩ := h r
        refine ⟨ar * a, ?_⟩
        have e : f (ar * a) - r • x = f ar * (f a - x) + (f ar - r) * x := by
          rw [smul_eq_mul, map_mul]; ring
        rw [e]
        refine add_mem (Ideal.mul_mem_left _ _ ha) ?_
        rw [pow_succ']
        exact Ideal.mul_mem_mul har (by
          have hx' : x ∈ Ideal.map f (N ^ n) := hx
          rwa [Ideal.map_pow] at hx')
    intro b
    obtain ⟨a₀, ha₀⟩ := ih b
    obtain ⟨a₁, ha₁⟩ := key (b - f a₀) (by
      have := neg_mem ha₀
      convert this using 1; ring)
    refine ⟨a₀ + a₁, ?_⟩
    convert ha₁ using 1
    rw [map_add]; ring

/-- Elementwise form of "`I ⊇ N̂^k` and `B = f(A) + N̂`": surjectivity of `A → B/I` and
`I = (f⁻¹ I) B`. -/
theorem exists_sub_mem_and_map_comap_eq (N : Ideal A) (h : ∀ b, ∃ a, f a - b ∈ N.map f)
    (I : Ideal B) (k : ℕ) (hI : (N.map f) ^ k ≤ I) :
    (∀ b, ∃ a, f a - b ∈ I) ∧ (I.comap f).map f = I := by
  refine ⟨fun b => ?_, le_antisymm Ideal.map_comap_le fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := exists_sub_mem_map_pow f N h k b
    exact ⟨a, hI ha⟩
  · obtain ⟨a, ha⟩ := exists_sub_mem_map_pow f N h k x
    have h1 : f a - x ∈ I := hI ha
    have h2 : f a ∈ I := by
      have := add_mem h1 hx
      simpa using this
    have hNk : N ^ k ≤ I.comap f := by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact hI
    have h3 : f a - x ∈ (I.comap f).map f := by
      have h4 : f a - x ∈ (N ^ k).map f := by rwa [Ideal.map_pow]
      exact Ideal.map_mono hNk h4
    have h5 : f a ∈ (I.comap f).map f := Ideal.mem_map_of_mem f h2
    have := sub_mem h5 h3
    simpa using this

end PowerAlgebra

section Nullstellensatz

open Subscheme

/-- The stalk of the radical of an ideal sheaf lies in the radical of the stalk. -/
theorem stalkIdeal_radical_le {Y : Scheme.{u}} (D : Subscheme Y) (y : Y) :
    Subscheme.stalkIdeal (Scheme.IdealSheafData.radical D) y ≤ (D.stalkIdeal y).radical := by
  obtain ⟨W, hW⟩ := exists_affineOpen_mem y
  rw [stalkIdeal_eq_map_germ_affine _ W hW, stalkIdeal_eq_map_germ_affine _ W hW]
  exact Ideal.map_radical_le _

/-- If the points of a subscheme `D` lie over `x₀`, then at a point `y` over `x₀` some power of the
ideal `m_{x₀} O_y` of the fibre lies in the stalk of the ideal of `D`. -/
theorem exists_pow_fiberIdeal_le_stalkIdeal {Y X : Scheme.{u}} (g : Y ⟶ X) {x₀ : X}
    (D : Subscheme Y) (hD : D.pts ⊆ g.base ⁻¹' {x₀}) (y : Y) (hy : g.base y = x₀)
    [IsNoetherianRing (Y.presheaf.stalk y)] :
    ∃ k : ℕ, fiberIdeal g y ^ k ≤ D.stalkIdeal y := by
  have h1 := fiberIdeal_le_stalkIdeal_ofClosed g D.support hD y hy
  have h2 : (ofClosed D.support).stalkIdeal y ≤ (D.stalkIdeal y).radical := by
    have : ofClosed D.support = Scheme.IdealSheafData.radical D :=
      Scheme.IdealSheafData.vanishingIdeal_support
    rw [this]
    exact stalkIdeal_radical_le D y
  exact Ideal.exists_pow_le_of_le_radical_of_fg (h1.trans h2)
    (IsNoetherian.noetherian _)

end Nullstellensatz

section Stalks

variable {X : Scheme.{u}} {T : Tower X} {x₀ : X}

/-- At a point `ŷ` of `ĝ_s⁻¹(x̂_0)`: if `I ⊇ (M̂Ŝ_s)^k`, then `S_s → Ŝ_s/I` is surjective and
`I = (f⁻¹ I)Ŝ_s` (powers of `M` in place of `M` in the Corollary of (AB.3)). -/
theorem Completion.surjective_and_map_comap_eq (𝒞 : Completion T x₀) (hx : X.IsSimpleAt x₀)
    (hX : ∀ s, (T.X s).IsNonsingular) (hB : ∀ s, (T.B s).IsNonsingular) (s : ℕ)
    (yh : 𝒞.tHat.X s) (hyh : (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx)
    (I : Ideal ((𝒞.tHat.X s).presheaf.stalk yh)) (k : ℕ)
    (hI : fiberIdeal (𝒞.tHat.pre s).composite yh ^ k ≤ I) :
    (∀ b, ∃ a, ((𝒞.c s).stalkMap yh).hom a - b ∈ I) ∧
      (I.comap ((𝒞.c s).stalkMap yh).hom).map ((𝒞.c s).stalkMap yh).hom = I := by
  obtain ⟨heq, -⟩ := 𝒞.fiberIdeal_eq_and_bijective_quotientMap hx hX hB s yh hyh
  obtain ⟨-, hsurj⟩ := 𝒞.comap_map_le_and_exists_sub_mem_fiberIdeal hx hX hB s yh hyh
  rw [heq] at hI
  exact exists_sub_mem_and_map_comap_eq _ _ hsurj I k hI

/-- `S_s → Ŝ_s` is faithfully flat at a point over `x̂_0`: `(J Ŝ_s) ∩ S_s = J`. -/
theorem Completion.comap_map_stalkMap (𝒞 : Completion T x₀) (hx : X.IsSimpleAt x₀)
    (hX : ∀ s, (T.X s).IsNonsingular) (hB : ∀ s, (T.B s).IsNonsingular) (s : ℕ)
    (yh : 𝒞.tHat.X s) (hyh : (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx)
    (J : Ideal ((T.X s).presheaf.stalk ((𝒞.c s).base yh))) :
    (J.map ((𝒞.c s).stalkMap yh).hom).comap ((𝒞.c s).stalkMap yh).hom = J := by
  obtain ⟨hreg, hα, -⟩ := 𝒞.isRegularLocalRing_and_mapsRSOP_stalkMap hx hX hB s yh hyh
  have : IsRegularLocalRing ((T.X s).presheaf.stalk ((𝒞.c s).base yh)) := hX s _
  have _ := hreg
  have hloc : IsLocalHom ((𝒞.c s).stalkMap yh).hom := inferInstance
  have hflat := hα.flat
  let _ := ((𝒞.c s).stalkMap yh).hom.toAlgebra
  have : Module.Flat ((T.X s).presheaf.stalk ((𝒞.c s).base yh))
      ((𝒞.tHat.X s).presheaf.stalk yh) := hflat
  have : IsLocalHom (algebraMap ((T.X s).presheaf.stalk ((𝒞.c s).base yh))
      ((𝒞.tHat.X s).presheaf.stalk yh)) := hloc
  have : Module.FaithfullyFlat ((T.X s).presheaf.stalk ((𝒞.c s).base yh))
      ((𝒞.tHat.X s).presheaf.stalk yh) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Ideal.comap_map_eq_self_of_faithfullyFlat J

end Stalks

section Iso

/-- If `c` induces an isomorphism `e : D̂ ≅ D` of subschemes (`e ≫ ι_D = ι_{D̂} ≫ c`), the stalk
ideal of `D` at `c(ŷ)` is the contraction of that of `D̂` at `ŷ`. -/
theorem stalkIdeal_eq_comap_of_iso {Y Yh : Scheme.{u}} (c : Yh ⟶ Y) (D : Subscheme Y)
    (Dh : Subscheme Yh) (e : Dh.toScheme ⟶ D.toScheme) [IsIso e] (he : e ≫ D.ι = Dh.ι ≫ c)
    (p : Dh.toScheme) :
    D.stalkIdeal (c.base (Dh.ι.base p)) =
      (Dh.stalkIdeal (Dh.ι.base p)).comap (c.stalkMap (Dh.ι.base p)).hom := by
  obtain ⟨h, hsq⟩ := exists_stalkMap_comm he.symm p
  set q := e.base p
  let σ := (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom
  have hsq' : ∀ a', (e.stalkMap p).hom ((D.ι.stalkMap q).hom a') =
      (Dh.ι.stalkMap p).hom ((c.stalkMap (Dh.ι.base p)).hom (σ.hom a')) := fun a' =>
    congrArg (fun g => g.hom a') hsq
  have hkerD : RingHom.ker (D.ι.stalkMap q).hom = D.stalkIdeal (D.ι.base q) :=
    (stalkIdeal_eq_ker_stalkMap D q).symm
  have hkerDh : RingHom.ker (Dh.ι.stalkMap p).hom = Dh.stalkIdeal (Dh.ι.base p) :=
    (stalkIdeal_eq_ker_stalkMap Dh p).symm
  have hσ : (D.stalkIdeal (D.ι.base q)).map σ.hom = D.stalkIdeal (c.base (Dh.ι.base p)) :=
    stalkIdeal_map_stalkCongr D h
  have hbij : Function.Bijective σ.hom := (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hebij : Function.Injective (e.stalkMap p).hom :=
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
  ext a
  obtain ⟨a', rfl⟩ := hbij.2 a
  rw [Ideal.mem_comap, ← hkerDh, RingHom.mem_ker, ← hsq', ← hσ]
  constructor
  · intro h
    have h2 : a' ∈ ((D.stalkIdeal (D.ι.base q)).map σ.hom).comap σ.hom := h
    rw [Ideal.comap_map_of_bijective _ hbij, ← hkerD] at h2
    rw [RingHom.mem_ker.mp h2, map_zero]
  · intro h0
    have h1 : (D.ι.stalkMap q).hom a' = 0 := (map_eq_zero_iff _ hebij).mp h0
    have h2 : a' ∈ D.stalkIdeal (D.ι.base q) := by rw [← hkerD]; exact h1
    exact Ideal.mem_map_of_mem _ h2

end Iso

section Main

variable {X : Scheme.{u}} {T : Tower X} {x₀ : X}

/-- **Corollary of Lemma (AB.3), second assertion, for `B̂` not necessarily reduced**: a
subscheme `B̂` of `X̂_s` with `ĝ_s(B̂) = x̂_0` is `c_s⁻¹(B)` for a unique subscheme `B` of `X_s` with
`g_s(B) = x_0`; `B = c_s(B̂)` and `c_s` induces `B̂ ≅ B`.

Deviation from the paper (gap filled): Lemma (CD.3), third assertion, is stated for any irreducible
`B̂` and justified by "Here we remark, as in the previous section, the following fact" (p. 316),
i.e. the Corollary of (AB.3) (p. 296), whose proof in `ImplicationsAB`
(`Completion.exists_unique_isReduced_totalTransform`) needs `B̂` reduced.  For non-reduced `B̂`
the ideal of `B̂` contains only a power `(M̂Ŝ_s)^k` of the ideal of the fibre, and the argument needs
`Ŝ_s = S_s + (M̂Ŝ_s)^k` (from `Ŝ_s = S_s + M̂Ŝ_s`) and the faithful flatness of `S_s → Ŝ_s`
(Lemma 2 of Ch. III §2 for the maps transforming a regular system of parameters). -/
@[blueprint "lem:IV.CD-3-as-printed-fibre"
  (statement := /-- In the situation of \cref{def:IV.3-setup}, let $\hat B$ be a subscheme of
    $\hat X_s$ (not necessarily reduced) with $\hat g_s(\hat B)=\{\hat x_0\}$. Then there is a
    unique subscheme $B$ of $X_s$ with $g_s(B)=\{x_0\}$ and $\hat B=c_s^{-1}(B)$; moreover
    $B=c_s(\hat B)$ and $c_s$ induces an isomorphism $\hat B\to B$. -/)
  (proof := /-- At a point $\hat y$ of $\hat B$ the ideal $I$ of $\hat B$ contains a power
    $(\hat M\hat S_s)^k$ of the ideal of the fibre (the radical of $I$ is the ideal of the reduced
    subscheme on $\hat B$, contained in the fibre). By the first assertion of the Corollary of
    \cref{lem:IV.AB-3}, $\hat S_s=S_s+\hat M\hat S_s$ locally, hence
    $\hat S_s=S_s+(\hat M\hat S_s)^k\subseteq S_s+I$, so $S_s\to\hat S_s/I$ is onto and
    $I=(I\cap S_s)\hat S_s$. The map $c_s\circ\iota_{\hat B}$ is a closed immersion ($c_s$ maps
    $\hat g_s^{-1}(\hat x_0)$ homeomorphically onto $g_s^{-1}(x_0)$, a closed set); let $B$ be its
    image. Its stalk ideals are $I\cap S_s$, so $c_s^{-1}(B)=\hat B$. Uniqueness: $S_s\to\hat S_s$
    is flat and local, hence faithfully flat, so $(J\hat S_s)\cap S_s=J$.

    \textbf{Deviation from the paper (gap filled).} The paper justifies the third assertion of
    Lemma (CD.3) for any irreducible $\hat B$ ``as in the previous section'' (p.~316), but the
    Corollary of (AB.3) (p.~296) is available only for reduced $\hat B$; the non-reduced case needs
    the powers of $\hat M\hat S_s$ and the faithful flatness of $S_s\to\hat S_s$. -/)
  (proofUses := ["cor:IV.AB-3", "lem:IV.AB-2"])
  (latexEnv := "lemma")]
theorem Completion.exists_unique_totalTransform (𝒞 : Completion T x₀)
    (hx : X.IsSimpleAt x₀) (hX : ∀ s, (T.X s).IsNonsingular) (hB : ∀ s, (T.B s).IsNonsingular)
    (hclosed : IsClosed ({x₀} : Set X)) (s : ℕ) (Bh : Subscheme (𝒞.tHat.X s))
    (himg : (𝒞.tHat.pre s).composite.base '' Bh.pts = {xhat0 X x₀ hx}) :
    ∃ B : Subscheme (T.X s),
      ((T.pre s).composite.base '' B.pts = {x₀} ∧
        Bh = Subscheme.totalTransform (𝒞.c s) B) ∧
      B.pts = (𝒞.c s).base '' Bh.pts ∧
      (∀ B' : Subscheme (T.X s), (T.pre s).composite.base '' B'.pts = {x₀} →
        Bh = Subscheme.totalTransform (𝒞.c s) B' → B' = B) ∧
      ∃ e : Bh.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bh.ι ≫ 𝒞.c s := by
  have hbij := 𝒞.bijOn_c_of_isNonsingular hx hX hB s
  have hBhF : ∀ yh ∈ Bh.pts, (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx :=
    fun yh hyh => by
      have : (𝒞.tHat.pre s).composite.base yh ∈ (𝒞.tHat.pre s).composite.base '' Bh.pts :=
        ⟨yh, hyh, rfl⟩
      rw [himg] at this
      exact this
  have hpre : ∀ yh : 𝒞.tHat.X s, (T.pre s).composite.base ((𝒞.c s).base yh) = x₀ →
      (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx := 𝒞.composite_tHat_eq_xhat0 hx s
  have hmaps : ∀ yh : 𝒞.tHat.X s, (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx →
      (T.pre s).composite.base ((𝒞.c s).base yh) = x₀ := fun yh h => hbij.mapsTo h
  have hc0 : (𝒞.c 0).base (xhat0 X x₀ hx) = x₀ := by
    rw [𝒞.c_zero]; exact c0_apply_xhat0 X x₀ hx
  have hres : IsIso ((𝒞.c 0).residueFieldMap (xhat0 X x₀ hx)) := by
    rw [𝒞.c_zero]; exact isIso_residueFieldMap_c0_xhat0 X x₀ hx
  obtain ⟨H, hH⟩ := exists_homeomorph_preimage_of_isPullback (𝒞.isPullback s) (xhat0 X x₀ hx) hres
  have hFcl : IsClosed ((T.pre s).composite.base ⁻¹' {(𝒞.c 0).base (xhat0 X x₀ hx)}) := by
    rw [hc0]; exact hclosed.preimage (T.pre s).composite.continuous
  have hZ : IsClosed ((𝒞.c s).base '' Bh.pts) := by
    have h1 : IsClosed ((Subtype.val : ((𝒞.tHat.pre s).composite.base ⁻¹'
        {xhat0 X x₀ hx}) → 𝒞.tHat.X s) ⁻¹' Bh.pts) :=
      Bh.support.isClosed.preimage continuous_subtype_val
    have h2 := hFcl.isClosedMap_subtype_val _ (H.isClosedMap _ h1)
    convert h2 using 1
    ext y
    constructor
    · rintro ⟨yh, hyh, rfl⟩
      exact ⟨H ⟨yh, hBhF yh hyh⟩, ⟨⟨yh, hBhF yh hyh⟩, hyh, rfl⟩, hH _⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p.1, hp, (hH p).symm⟩
  have hZF : ((𝒞.c s).base '' Bh.pts) ⊆ (T.pre s).composite.base ⁻¹' {x₀} := by
    rintro _ ⟨yh, hyh, rfl⟩
    exact hmaps yh (hBhF yh hyh)
  have hpreZ : (𝒞.c s).base ⁻¹' ((𝒞.c s).base '' Bh.pts) = Bh.pts := by
    ext yh
    constructor
    · rintro ⟨yh₁, hyh₁, he⟩
      have h1 : (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx :=
        hpre yh (he ▸ hmaps yh₁ (hBhF yh₁ hyh₁))
      have := hbij.injOn (hBhF yh₁ hyh₁) h1 he
      exact this ▸ hyh₁
    · intro hyh
      exact ⟨yh, hyh, rfl⟩
  have hBhpts : ∀ p : Bh.toScheme, Bh.ι.base p ∈ Bh.pts := fun p => by
    have : Bh.ι.base p ∈ Set.range Bh.ι.base := ⟨p, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι] at this
    exact this
  -- the stalk data at the points of `B̂`
  have hnoeth : ∀ yh ∈ Bh.pts, IsNoetherianRing ((𝒞.tHat.X s).presheaf.stalk yh) :=
    fun yh hyh => by
      have := (𝒞.isRegularLocalRing_and_mapsRSOP_stalkMap hx hX hB s yh (hBhF yh hyh)).1
      infer_instance
  have hk : ∀ yh ∈ Bh.pts, ∃ k : ℕ,
      fiberIdeal (𝒞.tHat.pre s).composite yh ^ k ≤ Bh.stalkIdeal yh := fun yh hyh => by
    have := hnoeth yh hyh
    exact exists_pow_fiberIdeal_le_stalkIdeal (𝒞.tHat.pre s).composite Bh
      (fun y hy => hBhF y hy) yh (hBhF yh hyh)
  have hsm : ∀ yh ∈ Bh.pts,
      (∀ b, ∃ a, ((𝒞.c s).stalkMap yh).hom a - b ∈ Bh.stalkIdeal yh) ∧
        ((Bh.stalkIdeal yh).comap ((𝒞.c s).stalkMap yh).hom).map ((𝒞.c s).stalkMap yh).hom =
          Bh.stalkIdeal yh := fun yh hyh => by
    obtain ⟨k, hk'⟩ := hk yh hyh
    exact 𝒞.surjective_and_map_comap_eq hx hX hB s yh (hBhF yh hyh) _ k hk'
  -- `c_s` restricted to `B̂` is a closed immersion
  have hembBh : Topology.IsEmbedding ((𝒞.c s).base ∘ Bh.ι.base) := by
    have hk0 := Bh.ι.isClosedEmbedding.isEmbedding.codRestrict
      ((𝒞.tHat.pre s).composite.base ⁻¹' {xhat0 X x₀ hx}) fun p => hBhF _ (hBhpts p)
    have h3 := Topology.IsEmbedding.subtypeVal.comp (H.isEmbedding.comp hk0)
    convert h3 using 1
    funext p
    exact (hH ⟨Bh.ι.base p, hBhF _ (hBhpts p)⟩).symm
  have hrange : Set.range ((𝒞.c s).base ∘ Bh.ι.base) = (𝒞.c s).base '' Bh.pts := by
    rw [Set.range_comp]
    congr 1
    exact Scheme.IdealSheafData.range_subschemeι (I := Bh)
  have hclosedEmb : Topology.IsClosedEmbedding ((𝒞.c s).base ∘ Bh.ι.base) :=
    ⟨hembBh, by rw [hrange]; exact hZ⟩
  have hsurjSt : ∀ p : Bh.toScheme, Function.Surjective ((Bh.ι ≫ 𝒞.c s).stalkMap p).hom := by
    intro p w
    obtain ⟨b, rfl⟩ := Bh.ι.stalkMap_surjective p w
    obtain ⟨a, ha⟩ := (hsm _ (hBhpts p)).1 b
    refine ⟨a, ?_⟩
    rw [Scheme.Hom.stalkMap_comp]
    show (Bh.ι.stalkMap p).hom (((𝒞.c s).stalkMap (Bh.ι.base p)).hom a) = _
    have h1 : ((𝒞.c s).stalkMap (Bh.ι.base p)).hom a - b ∈ RingHom.ker (Bh.ι.stalkMap p).hom := by
      rw [← stalkIdeal_eq_ker_stalkMap]; exact ha
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h1
    exact h1
  have hCI : IsClosedImmersion (Bh.ι ≫ 𝒞.c s) :=
    { stalkMap_surjective := fun p => hsurjSt p
      isClosedEmbedding := hclosedEmb }
  -- the subscheme `B`, the image of `B̂`
  let B : Subscheme (T.X s) := (Bh.ι ≫ 𝒞.c s).ker
  have hker : (Bh.ι ≫ 𝒞.c s).ker = B.ι.ker := (Scheme.IdealSheafData.ker_subschemeι (I := B)).symm
  have : IsIso (IsClosedImmersion.lift (Bh.ι ≫ 𝒞.c s) B.ι hker.le) :=
    IsClosedImmersion.isIso_lift _ _ hker
  let e' : B.toScheme ≅ Bh.toScheme := asIso (IsClosedImmersion.lift (Bh.ι ≫ 𝒞.c s) B.ι hker.le)
  have he' : e'.hom ≫ (Bh.ι ≫ 𝒞.c s) = B.ι := IsClosedImmersion.lift_fac _ _ _
  have he : e'.inv ≫ B.ι = Bh.ι ≫ 𝒞.c s := by rw [← he']; simp
  have hBstalk : ∀ p : Bh.toScheme, B.stalkIdeal ((𝒞.c s).base (Bh.ι.base p)) =
      (Bh.stalkIdeal (Bh.ι.base p)).comap ((𝒞.c s).stalkMap (Bh.ι.base p)).hom :=
    fun p => stalkIdeal_eq_comap_of_iso (𝒞.c s) B Bh e'.inv he p
  have hBpts : B.pts = (𝒞.c s).base '' Bh.pts := by
    have h1 : B.pts = Set.range B.ι.base := (Scheme.IdealSheafData.range_subschemeι (I := B)).symm
    have hsurj : Function.Surjective e'.hom.base := e'.hom.homeomorph.surjective
    rw [h1, ← he', Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq,
      Set.image_univ]
    exact hrange
  have hnot : ∀ yh : 𝒞.tHat.X s, yh ∉ Bh.pts → (𝒞.c s).base yh ∉ B.pts := fun yh hyh hB' => by
    rw [hBpts] at hB'
    exact hyh (hpreZ ▸ hB')
  have hEq : Bh = Subscheme.totalTransform (𝒞.c s) B := by
    refine Subscheme.ext_stalkIdeal fun yh => ?_
    rw [stalkIdeal_totalTransform]
    by_cases hyh : yh ∈ Bh.pts
    · have : yh ∈ Set.range Bh.ι.base := by
        rw [Scheme.IdealSheafData.range_subschemeι]; exact hyh
      obtain ⟨p, rfl⟩ := this
      rw [hBstalk p]
      exact (hsm _ hyh).2.symm
    · rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hyh,
        Subscheme.stalkIdeal_eq_top_of_notMem_pts (hnot yh hyh), Ideal.map_top]
  refine ⟨B, ⟨?_, hEq⟩, hBpts, ?_, ⟨e'.symm, he⟩⟩
  · rw [hBpts]
    ext y
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨yh, hyh, rfl⟩, rfl⟩
      exact hmaps yh (hBhF yh hyh)
    · rintro rfl
      obtain ⟨yh, hyh⟩ : Bh.pts.Nonempty := by
        by_contra hne
        rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne, Set.image_empty] at himg
        exact (Set.singleton_ne_empty _) himg.symm
      exact ⟨_, ⟨yh, hyh, rfl⟩, hmaps yh (hBhF yh hyh)⟩
  · intro B' hB'img hB'eq
    refine Subscheme.ext_stalkIdeal fun y => ?_
    by_cases hy : y ∈ (𝒞.c s).base '' Bh.pts
    · obtain ⟨yh, hyh, rfl⟩ := hy
      have hp : yh ∈ Set.range Bh.ι.base := by
        rw [Scheme.IdealSheafData.range_subschemeι]; exact hyh
      obtain ⟨p, hpy⟩ := hp
      have h1 : Bh.stalkIdeal yh =
          (B'.stalkIdeal ((𝒞.c s).base yh)).map ((𝒞.c s).stalkMap yh).hom := by
        have := congrArg (fun D : Subscheme (𝒞.tHat.X s) => D.stalkIdeal yh) hB'eq
        simpa only [stalkIdeal_totalTransform] using this
      have h2 := hBstalk p
      rw [hpy] at h2
      rw [h2, h1, 𝒞.comap_map_stalkMap hx hX hB s yh (hBhF yh hyh)]
    · have hyB : y ∉ B.pts := by rw [hBpts]; exact hy
      rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts (D := B) hyB]
      apply Subscheme.stalkIdeal_eq_top_of_notMem_pts
      intro hy'
      have hyF : (T.pre s).composite.base y = x₀ := by
        have : (T.pre s).composite.base y ∈ (T.pre s).composite.base '' B'.pts := ⟨y, hy', rfl⟩
        rw [hB'img] at this
        exact this
      obtain ⟨yh, -, rfl⟩ := hbij.surjOn hyF
      apply hy
      refine ⟨yh, ?_, rfl⟩
      have : yh ∈ (Subscheme.totalTransform (𝒞.c s) B').pts := by
        rw [FlatPreimm.pts_totalTransform]; exact hy'
      rwa [← hB'eq] at this

/-- The Corollary of Lemma (AB.3) in the form of the third assertion of Lemma (CD.3) as printed:
for **irreducible** (not necessarily reduced) `B̂` with `ĝ_s(B̂) = x̂_0`, there is a unique
irreducible `B` with `B̂ = c_s⁻¹(B)` (and `B = c_s(B̂)`, `c_s` inducing `B̂ ≅ B`), where uniqueness
is among the irreducible `B'` with `B̂ = c_s⁻¹(B')`, `B' = c_s(B̂)` and `B̂ ≅ B'` via `c_s`.

Deviation from the paper (gap filled): see `Completion.exists_unique_totalTransform`; the paper's
"as in the previous section" covers only reduced `B̂`. -/
@[blueprint "lem:IV.CD-3-as-printed-irreducible"
  (statement := /-- In the situation of \cref{def:IV.3-setup} with $x_0$ closed, let $\hat B$ be an
    irreducible subscheme of $\hat X_s$ with $\hat g_s(\hat B)=\{\hat x_0\}$. Then there is a unique
    irreducible subscheme $B$ of $X_s$ with $\hat B=c_s^{-1}(B)$, $B=c_s(\hat B)$ and $c_s$
    inducing an isomorphism $\hat B\to B$. -/)
  (proof := /-- By \cref{lem:IV.CD-3-as-printed-fibre}; $B$ is irreducible as the image of $\hat B$
    under the isomorphism, and a competitor $B'$ with $B'=c_s(\hat B)$ satisfies
    $g_s(B')=\{x_0\}$ by $g_s\circ c_s=c_0\circ\hat g_s$.

    \textbf{Deviation from the paper (gap filled).} The non-reduced case, which the paper's
    ``as in the previous section'' (p.~316) does not cover. -/)
  (proofUses := ["lem:IV.CD-3-as-printed-fibre"])
  (latexEnv := "lemma")]
theorem Completion.exists_unique_irreducible_totalTransform (𝒞 : Completion T x₀)
    (hx : X.IsSimpleAt x₀) (hX : ∀ s, (T.X s).IsNonsingular) (hB : ∀ s, (T.B s).IsNonsingular)
    (hclosed : IsClosed ({x₀} : Set X)) (s : ℕ) (Bh : Subscheme (𝒞.tHat.X s))
    (hirr : Bh.IsIrreducible)
    (himg : (𝒞.tHat.pre s).composite.base '' Bh.pts = {xhat0 X x₀ hx}) :
    ∃ B : Subscheme (T.X s),
      (B.IsIrreducible ∧ Bh = Subscheme.totalTransform (𝒞.c s) B ∧
        B.pts = (𝒞.c s).base '' Bh.pts ∧
        ∃ e : Bh.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bh.ι ≫ 𝒞.c s) ∧
      ∀ B' : Subscheme (T.X s), B'.IsIrreducible →
        Bh = Subscheme.totalTransform (𝒞.c s) B' → B'.pts = (𝒞.c s).base '' Bh.pts →
        (∃ e : Bh.toScheme ≅ B'.toScheme, e.hom ≫ B'.ι = Bh.ι ≫ 𝒞.c s) → B' = B := by
  obtain ⟨B, ⟨-, hBh⟩, hBpts, huniq, e, he⟩ :=
    𝒞.exists_unique_totalTransform hx hX hB hclosed s Bh himg
  have hirrB : B.IsIrreducible := by
    have : IrreducibleSpace Bh.toScheme := hirr
    exact Function.Surjective.irreducibleSpace e.hom.continuous e.hom.homeomorph.surjective
  refine ⟨B, ⟨hirrB, hBh, hBpts, e, he⟩, ?_⟩
  intro B' _ hB' hB'pts _
  refine huniq B' ?_ hB'
  have hw := (𝒞.isPullback s).w
  have hfun : ⇑(T.pre s).composite.base ∘ ⇑(𝒞.c s).base =
      ⇑(𝒞.c 0).base ∘ ⇑(𝒞.tHat.pre s).composite.base := by
    funext y
    exact (Scheme.Hom.comp_apply _ _ y).symm.trans
      ((congrArg (fun f => f.base y) hw).trans (Scheme.Hom.comp_apply _ _ y))
  rw [hB'pts, ← Set.image_comp, hfun]
  have h3 : ⇑(𝒞.c 0).base '' ({xhat0 X x₀ hx} : Set (𝒞.tHat.X 0)) = {x₀} := by
    have hc : (𝒞.c 0).base (xhat0 X x₀ hx) = x₀ := by
      rw [𝒞.c_zero]; exact c0_apply_xhat0 X x₀ hx
    exact Set.image_singleton.trans (congrArg _ hc)
  exact (Set.image_comp _ _ _).trans ((congrArg _ himg).trans h3)

end Main

end AB

end Hironaka
