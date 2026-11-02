/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch3.PermissibleEffects
public import Hironaka.Ch4.CompletionFibre
public import Hironaka.Ch4.ImplicationsAB
public import Hironaka.Statements

/-!
# Ch. IV §3 (p. 306): the assembly of Lemma (AB.6) from the permissibility of `P̂` at the completion

> LEMMA (AB.6). Let `B̄'` be any non-singular irreducible subscheme of `X̄'_s` such that
> `ĝ_s(B̄')` consists of only the point `x̂₀`, and that the stalk `J̄(s)_x̂` is contained in the
> `b`th power of the prime ideal of `B̄'` at every point `x̂` of `B̄'`. Let `B_s` be the closure of
> `c_s(B̄')` in `X_s` … Then `B_s` is an irreducible subscheme of `X_s` such that
> `B̄' = c_s⁻¹(B_s) ∩ X̂'_s`, and there exists a non-empty open subset `U_s` of `B_s`, containing
> no multiple points of `B_s`, such that (i) `U_s ⊇ c_s(B̄')` and (ii) `V_1(s), …, V_β(s)` and
> `W(s)` are all normally flat along `B_s` at every point of `U_s`. (p. 306)

The proof in the paper has two parts: the scheme-level part (the closure `B̄` of `B̄'`, the
Corollary of (AB.3), the open set `U_s` of simple points where the `V_j(s)`, `W(s)` are normally
flat, and the inclusion `U_s ⊇ c_s(B̄')` which is checked pointwise) and the ring-level part (the
frame `(T_s; z_s)` of `Ŝ_s`, "by the same argument as in the proof of Lemma (AB.5)", whence
"`P̂` is a permissible center for all the `Ĵ_j(s)`" and, by faithful flatness and Lemma 9 of
Ch. II §3, `P` is a permissible center for the `J_j(s)`).

This file proves the scheme-level part, and the final descent, from the one ring-level
statement that the paper's argument produces:

* `Frame.isIrreducible_and_isNormallyFlatAlongAt_of_isPermissibleCenter`: Lemma (AB.6) with the
  extra hypothesis that, at every point of `B̄' ∩ X̄'_s`, the ideal `B_s Ŝ_s` is a permissible
  center for `J_j(s) Ŝ_s` (`0 ≤ j ≤ β`); the call site for `Frame.isIrreducible_and_isNormallyFlatAlongAt_of_jbar_le_pow`;
* `isPermissibleCenter_of_ordElem_le`: the step "`ν_P̂(g_jk(s)) ≥ ν_jk` for all `j, k`, hence by
  (a), (b) of (2), `P̂` is a permissible center for the `Ĵ_j(s)`" (ring level, from a system of
  elements of `J` with initial forms generating `gr_M(J)`).

General facts about subschemes used on the way (`Subscheme.pts_subset_of_stalkIdeal_le`,
`Subscheme.exists_isOpen_isNormallyFlatAlongAt'`, `Subscheme.exists_isOpen_isSimpleAt`
(in `Hironaka/Compat/TransformNormalCrossingsLocalized.lean`),
`Subscheme.stalkIdeal_ofClosed_eq_of_local`, …) are stated for arbitrary schemes.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory TopologicalSpace Topology

namespace Hironaka

universe u

/-- Faithful flatness reflects containment of extended ideals. -/
theorem le_of_map_le_of_mapsRSOP {R R' : Type u} [CommRing R] [IsRegularLocalRing R]
    [CommRing R'] [IsRegularLocalRing R'] (α : R →+* R') [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) {J P : Ideal R} (h : J.map α ≤ P.map α) : J ≤ P := by
  let _ : Algebra R R' := α.toAlgebra
  have _ : IsLocalHom (algebraMap R R') := ‹IsLocalHom α›
  have _ : Module.Flat R R' := hα.flat
  have _ : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  calc J ≤ (J.map (algebraMap R R')).comap (algebraMap R R') := Ideal.le_comap_map
    _ ≤ (P.map (algebraMap R R')).comap (algebraMap R R') := Ideal.comap_mono h
    _ = P := Ideal.comap_map_eq_self_of_faithfullyFlat P

/-- A proper ideal stays proper under a ring map transforming a regular system of parameters
into one. -/
theorem map_ne_top_of_mapsRSOP {R R' : Type u} [CommRing R] [IsRegularLocalRing R]
    [CommRing R'] [IsRegularLocalRing R'] (α : R →+* R') [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) {P : Ideal R} (hP : P ≠ ⊤) : P.map α ≠ ⊤ := by
  let _ : Algebra R R' := α.toAlgebra
  have _ : IsLocalHom (algebraMap R R') := ‹IsLocalHom α›
  have _ : Module.Flat R R' := hα.flat
  have _ : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  intro h
  have h' : P.map (algebraMap R R') = ⊤ := h
  exact hP (by rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R') P, h', Ideal.comap_top])

/-- (AB.6), p. 306: "Therefore, by (1), (3), (4), `ν_P̂(g_jk(s)) ≥ ν_jk` for all `j, k`; hence by
(a), (b) of (2), `P̂` is a permissible center for all the `Ĵ_j(s)`."  Ring-level form: a system of
elements of `J` whose initial forms generate `gr_M(J, R)` and whose orders along `P` are at least
their orders at the maximal ideal `M` shows that the prime `P ⊇ J` with `R/P` regular is a
permissible center for `J` (Definition 8 (ii)*; the inequality `ν_P ≤ ν_M` holds as `P ⊆ M`).

Deviation from the paper (gap filled): the paper writes only "hence by (a), (b) of (2)"; Lean
combines (a) and (b) into the system of Definition 8 (ii)* (`ν_M(g) = ν_P(g)`, the orders
`ν_M(g_jk) = ν_jk ≤ ν_P̂(g_jk) ≤ ν_M(g_jk)` using `P̂ ⊆ M̂`) and applies the equivalence
(ii) ⇔ (ii)* of p. 226 (`isPermissibleCenter_tfae`). -/
@[blueprint "lem:IV.AB-6-permissible"
  (statement := /-- Let $R$ be a regular local ring with maximal ideal $M$, $J$ an ideal and $P$ a
    prime ideal of $R$ with $J\subseteq P$ and $R/P$ regular. Let $f_1,\dots,f_m\in J$ be such that
    the initial forms of the $f_k$ in $\operatorname{gr}_M(R)$ generate
    $\operatorname{gr}_M(J,R)$ and $\nu_M(f_k)\le\nu_P(f_k)$ for all $k$. Then $P$ is a
    permissible center for $J$ (\cref{def:III.8}). (Used on p.~306: ``hence by (a), (b) of (2),
    $\hat P$ is a permissible center for all the $\hat J_j(s)$''.) -/)
  (proof := /-- Since $P\subseteq M$ we have $\nu_P(f_k)\le\nu_M(f_k)$, so $\nu_M(f_k)=\nu_P(f_k)$,
    and $(f_k)$ is a system as in (ii)$^*$ of \cref{lem:III.8-equivalents}; this is equivalent to
    condition (ii) of \cref{def:III.8}.

    \textbf{Deviation from the paper (gap filled).} The paper writes only ``hence by (a), (b) of
    (2), $\hat P$ is a permissible center'' (p.~306). Lean combines (a) and (b) of (2) with
    $\nu_{\hat P}(g_{jk}(s))\ge\nu_{jk}$ into the system (ii)$^*$ ($\nu_M=\nu_P$ because
    $\nu_P\le\nu_M$ for $P\subseteq M$) and applies \cref{lem:III.8-equivalents}. -/)
  (proofUses := ["lem:III.8-equivalents", "def:III.8"])
  (latexEnv := "lemma")]
theorem isPermissibleCenter_of_ordElem_le {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (J P : Ideal R) [P.IsPrime] (hJP : J ≤ P) [IsRegularLocalRing (R ⧸ P)] {m : ℕ}
    (f : Fin m → R) (hfJ : ∀ k, f k ∈ J)
    (hord : ∀ k, Ideal.ordElem (maximalIdeal R) (f k) ≤ Ideal.ordElem P (f k))
    (hgen : Ideal.span (Set.range fun k => initialForm (maximalIdeal R) (f k)) =
      grIdeal (maximalIdeal R) J) :
    IsPermissibleCenter R J P := by
  have hPtop : P ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  refine Or.inr ⟨inferInstance, hJP, inferInstance, ?_⟩
  have h1 : HasInitialFormSystem J P (maximalIdeal R) := ⟨m, f, hfJ, fun k =>
    le_antisymm (hord k) (Ideal.ordElem_mono (le_maximalIdeal hPtop) _), hgen⟩
  exact ((isPermissibleCenter_tfae R J P hJP).out 1 2).mpr h1

namespace Subscheme

variable {Z : Scheme.{u}}

/-- Stalks of ideal sheaves at a generization are obtained by localizing: if `η ⤳ x` and
`V_x ≤ W_x` then `V_η ≤ W_η`. -/
theorem stalkIdeal_le_of_specializes {V W : Subscheme Z} {η x : Z} (h : η ⤳ x)
    (hle : V.stalkIdeal x ≤ W.stalkIdeal x) : V.stalkIdeal η ≤ W.stalkIdeal η := by
  obtain ⟨U, hxU⟩ := exists_affineOpen_mem x
  have hηU : η ∈ (U : Z.Opens) := h.mem_open U.1.isOpen hxU
  let φ := (Z.presheaf.stalkSpecializes h).hom
  have hgerm : ∀ a, φ (Z.presheaf.germ U x hxU a) = Z.presheaf.germ U η hηU a := fun a => by
    have := Z.presheaf.germ_stalkSpecializes hxU h
    exact congrArg (fun f => f.hom a) this
  have key : ∀ D : Subscheme Z, D.stalkIdeal η = (D.stalkIdeal x).map φ := by
    intro D
    rw [stalkIdeal_eq_map_germ_affine D U hxU, stalkIdeal_eq_map_germ_affine D U hηU,
      Ideal.map_map]
    congr 1
    ext a
    exact (hgerm a).symm
  rw [key V, key W]
  exact Ideal.map_mono hle

/-- If `W` is irreducible and `V_x ≤ W_x` at one point `x` of `W`, then `W` lies in `V`
(as sets of points): the generic point of `W` is a generization of `x`, where `V_η ≤ W_η ≠ ⊤`. -/
theorem pts_subset_of_stalkIdeal_le (V W : Subscheme Z) (hirr : _root_.IsIrreducible W.pts)
    {x : Z} (hx : x ∈ W.pts) (hle : V.stalkIdeal x ≤ W.stalkIdeal x) : W.pts ⊆ V.pts := by
  have hcl : IsClosed W.pts := W.support.isClosed
  have hη : closure {hirr.genericPoint} = W.pts := hirr.closure_genericPoint hcl
  have hηW : hirr.genericPoint ∈ W.pts := hη.le (subset_closure (Set.mem_singleton _))
  have hxη : hirr.genericPoint ⤳ x := specializes_iff_mem_closure.mpr (by rw [hη]; exact hx)
  have h1 := stalkIdeal_le_of_specializes hxη hle
  have hηV : hirr.genericPoint ∈ V.pts := by
    rw [mem_pts_iff_stalkIdeal_ne_top] at hηW ⊢
    intro htop
    rw [htop, top_le_iff] at h1
    exact hηW h1
  intro y hy
  rw [← hη] at hy
  exact closure_minimal (Set.singleton_subset_iff.mpr hηV) V.support.isClosed hy

/-- The points of `W ×_Z V = ι_V⁻¹(W)` are the points of `V` lying on `W`. -/
theorem mem_pts_totalTransform_ι_iff (V W : Subscheme Z) (z' : V.toScheme) :
    z' ∈ (totalTransform V.ι W).pts ↔ V.ι z' ∈ W.pts := by
  change z' ∈ ((W.comap V.ι).support : Set V.toScheme) ↔ _
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- Bridge from the ring-level condition to `IsNormallyFlatAlongAt'` for `W ⊄ V` (the case
`W ⊆ V` is `isNormallyFlatAlongAt'_iff`): for `z ∈ V ∩ W`, `V` is normally flat along `W` at `z`
as soon as `O_{Z,z}/V_z` is normally flat along the image of `W_z`. -/
theorem isNormallyFlatAlongAt'_of_isNormallyFlatAlongIdeal (V W : Subscheme Z) {z : Z}
    (hV : z ∈ V.pts) (hW : z ∈ W.pts)
    (h : IsNormallyFlatAlongIdeal ((W.stalkIdeal z).map (Ideal.Quotient.mk (V.stalkIdeal z)))) :
    IsNormallyFlatAlongAt' V W z := by
  have key : ∀ z' : V.toScheme,
      (totalTransform V.ι W).stalkIdeal z' =
        ((W.stalkIdeal (V.ι z')).map (Ideal.Quotient.mk (V.stalkIdeal (V.ι z')))).map
          ((Ideal.quotEquivOfEq (stalkIdeal_eq_ker_stalkMap V z')).trans
            (RingHom.quotientKerEquivOfSurjective (V.ι.stalkMap_surjective z'))
            : _ →+* V.toScheme.presheaf.stalk z') := by
    intro z'
    rw [stalkIdeal_totalTransform, Ideal.map_map]
    rfl
  obtain ⟨z', rfl⟩ := exists_ι_eq_of_mem_pts V hV
  refine ⟨z', rfl, (mem_pts_totalTransform_ι_iff V W z').mpr hW, ?_⟩
  rw [key]
  exact Hironaka.isNormallyFlatAlongIdeal_of_ringEquiv _ _ _ rfl h

/-- The locus of `W` at which `V` is normally flat along `W` is, inside `V ∩ W`, the trace of an
open subset (Cor. of Th. 1, Ch. II §1, on `V`; no containment `W ⊆ V` is needed). -/
theorem exists_isOpen_isNormallyFlatAlongAt' [IsAlgebraicScheme Z] (V W : Subscheme Z) :
    ∃ O : Set Z, IsOpen O ∧ ∀ y ∈ W.pts, y ∈ V.pts → (IsNormallyFlatAlongAt' V W y ↔ y ∈ O) := by
  have := isAlgebraicScheme_toScheme V
  obtain ⟨U₀, hU₀, hU⟩ := exists_isOpen_isNormallyFlatAlongAt (X := V.toScheme)
    (totalTransform V.ι W)
  obtain ⟨O, hO, hOU⟩ := V.ι.isEmbedding.isInducing.isOpen_iff.mp hU₀
  refine ⟨O, hO, fun y hyW hyV => ?_⟩
  obtain ⟨x', rfl⟩ := exists_ι_eq_of_mem_pts V hyV
  have hx'tt : x' ∈ (totalTransform V.ι W).pts := (mem_pts_totalTransform_ι_iff V W x').mpr hyW
  have e : V.ι x' ∈ O ↔ x' ∈ U₀ := by rw [← hOU]; rfl
  rw [e, hU x' hx'tt]
  constructor
  · rintro ⟨x'', hx'', hnf⟩
    obtain rfl : x'' = x' := V.ι.isEmbedding.injective hx''
    exact hnf
  · exact fun hnf => ⟨x', rfl, hnf⟩

/-- A closed immersion `f : Y ⟶ Z` identifies `Y` with the closed subscheme `f.ker` of `Z`. -/
theorem exists_iso_ker {Y : Scheme.{u}} (f : Y ⟶ Z) [IsClosedImmersion f] :
    ∃ e : f.ker.subscheme ≅ Y, e.hom ≫ f = f.ker.subschemeι := by
  have hker : f.ker = f.ker.subschemeι.ker := (Scheme.IdealSheafData.ker_subschemeι (I := f.ker)).symm
  have : IsIso (IsClosedImmersion.lift f f.ker.subschemeι hker.le) :=
    IsClosedImmersion.isIso_lift _ _ hker
  exact ⟨asIso (IsClosedImmersion.lift f f.ker.subschemeι hker.le),
    IsClosedImmersion.lift_fac _ _ _⟩

/-- If `W` lies in `T` and `W_x` is prime, then `(red T)_x ≤ W_x`. -/
theorem stalkIdeal_ofClosed_le_of_isPrime {W : Subscheme Z} {T : Closeds Z} (hWT : W.pts ⊆ T)
    {x : Z} (hWx : (W.stalkIdeal x).IsPrime) : (ofClosed T).stalkIdeal x ≤ W.stalkIdeal x := by
  refine Ideal.span_le.mpr ?_
  rintro a ⟨U, hx, s, hs, rfl⟩
  have h1 : ofClosed T ≤ W.radical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono hWT
  obtain ⟨n, hn⟩ := h1 U hs
  refine hWx.mem_of_pow_mem n ?_
  rw [← map_pow]
  exact Ideal.subset_span ⟨U, hx, s ^ n, hn, rfl⟩

/-- Local comparison of a reduced structure with a subscheme: if `T ⊆ K` as sets, `K ∩ O ⊆ T`
for an open `O`, and `K_y` is prime at the points of `K ∩ O`, then `K_y = (red T)_y` for
`y ∈ O`. -/
theorem stalkIdeal_ofClosed_eq_of_local (K : Subscheme Z) (T : Closeds Z) {O : Set Z}
    (hO : IsOpen O) (hTK : (T : Set Z) ⊆ K.pts) (hKT : K.pts ∩ O ⊆ T)
    (hprime : ∀ y ∈ K.pts ∩ O, (K.stalkIdeal y).IsPrime) {y : Z} (hy : y ∈ O) :
    (ofClosed T).stalkIdeal y = K.stalkIdeal y := by
  by_cases hyK : y ∈ K.pts
  · apply le_antisymm
    · let F : Closeds Z := ⟨K.pts \ O, K.support.isClosed.inter hO.isClosed_compl⟩
      let T₂ : Closeds Z := T ⊔ F
      have h1 : K.pts ⊆ T₂ := by
        intro z hz
        by_cases hzO : z ∈ O
        · exact Or.inl (hKT ⟨hz, hzO⟩)
        · exact Or.inr ⟨hz, hzO⟩
      have h2 := stalkIdeal_ofClosed_le_of_isPrime h1 (hprime y ⟨hyK, hy⟩)
      have h3 : (ofClosed T).stalkIdeal y ≤ (ofClosed T₂).stalkIdeal y := by
        obtain ⟨_, ⟨U, hUaff, rfl⟩, hyU, hUO⟩ :=
          Z.isBasis_affineOpens.exists_subset_of_mem_open hy hO
        have hUa : IsAffineOpen U := hUaff
        rw [stalkIdeal_eq_map_germ_affine _ ⟨U, hUaff⟩ hyU,
          stalkIdeal_eq_map_germ_affine _ ⟨U, hUaff⟩ hyU]
        refine Ideal.map_mono (le_of_eq ?_)
        show PrimeSpectrum.vanishingIdeal (hUa.fromSpec ⁻¹' (T : Set Z)) =
          PrimeSpectrum.vanishingIdeal (hUa.fromSpec ⁻¹' (T₂ : Set Z))
        congr 1
        ext p
        have hpU : hUa.fromSpec p ∈ (U : Set Z) := by
          have : hUa.fromSpec p ∈ Set.range hUa.fromSpec := ⟨p, rfl⟩
          rwa [hUa.range_fromSpec] at this
        simp only [T₂, Closeds.coe_sup]
        refine ⟨Or.inl, fun h => h.elim id fun h => ?_⟩
        exact absurd (hUO hpU) h.2
      exact h3.trans h2
    · have hle : T ≤ K.support := fun z hz => hTK hz
      exact stalkIdeal_mono (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp hle) y
  · have hyT : y ∉ (ofClosed T).pts := by
      rw [pts_ofClosed]; exact fun h => hyK (hTK h)
    rw [stalkIdeal_eq_top_of_notMem_pts hyT, stalkIdeal_eq_top_of_notMem_pts hyK]

end Subscheme

namespace Subscheme

variable {Z : Scheme.{u}}

/-- `O_y / K_y` is regular at every point of the kernel `K` of `Bb.ι ≫ i` over a simple point of
`Bb`, and `K.pts` is the range of `Bb.ι ≫ i`. -/
theorem exists_eq_of_mem_pts_ker_comp {W Y : Scheme.{u}} (i : W ⟶ Y) [IsClosedImmersion i]
    (Bb : Subscheme W) {y : Y} (hy : y ∈ Subscheme.pts (Bb.ι ≫ i).ker) :
    ∃ b : Bb.toScheme, i (Bb.ι b) = y := by
  obtain ⟨e, he⟩ := exists_iso_ker (Bb.ι ≫ i)
  obtain ⟨k, rfl⟩ := exists_ι_eq_of_mem_pts (Bb.ι ≫ i).ker hy
  refine ⟨e.hom k, ?_⟩
  have := congrArg (fun g => g.base k) he
  exact this

theorem apply_mem_pts_ker_comp {W Y : Scheme.{u}} (i : W ⟶ Y) [IsClosedImmersion i]
    (Bb : Subscheme W) (b : Bb.toScheme) : i (Bb.ι b) ∈ Subscheme.pts (Bb.ι ≫ i).ker := by
  have := Scheme.Hom.range_subset_ker_support (Bb.ι ≫ i)
  exact this ⟨b, rfl⟩

/-- At a point `y = i b` of the kernel `K` of `Bb.ι ≫ i` with `Bb` simple at `b`, the quotient
`O_y / K_y` is regular. -/
theorem isRegularLocalRing_quotient_stalkIdeal_ker_comp {W Y : Scheme.{u}} (i : W ⟶ Y) [IsClosedImmersion i]
    (Bb : Subscheme W) {y : Y} (hy : y ∈ Subscheme.pts (Bb.ι ≫ i).ker)
    (hs : ∀ b : Bb.toScheme, i (Bb.ι b) = y → Bb.IsSimpleAt (Bb.ι b)) :
    IsRegularLocalRing (Y.presheaf.stalk y ⧸ Subscheme.stalkIdeal (Bb.ι ≫ i).ker y) := by
  obtain ⟨e, he⟩ := exists_iso_ker (Bb.ι ≫ i)
  obtain ⟨k, rfl⟩ := exists_ι_eq_of_mem_pts (Bb.ι ≫ i).ker hy
  have hb : i (Bb.ι (e.hom k)) = Subscheme.ι (Bb.ι ≫ i).ker k := congrArg (fun g => g.base k) he
  obtain ⟨-, hreg⟩ := hs (e.hom k) hb
  obtain ⟨e1⟩ := nonempty_stalk_quot_equiv Bb (e.hom k)
  have h1 : IsRegularLocalRing (W.presheaf.stalk (Bb.ι (e.hom k)) ⧸
      Bb.stalkIdeal (Bb.ι (e.hom k))) := hreg
  have h2 : IsRegularLocalRing (Bb.toScheme.presheaf.stalk (e.hom k)) :=
    IsRegularLocalRing.of_ringEquiv e1
  have h3 : IsRegularLocalRing ((Subscheme.toScheme (Bb.ι ≫ i).ker).presheaf.stalk k) := by
    have : IsIso (e.hom.stalkMap k) := inferInstance
    exact IsRegularLocalRing.of_ringEquiv (asIso (e.hom.stalkMap k)).commRingCatIsoToRingEquiv
  obtain ⟨e2⟩ := nonempty_stalk_quot_equiv (Bb.ι ≫ i).ker k
  exact IsRegularLocalRing.of_ringEquiv e2.symm

end Subscheme

namespace Subscheme

variable {Z : Scheme.{u}}

/-- The reduced subscheme structure on the closure of a set of points (`B̄` in the proof of
(AB.6): "the closure of `B̄'` in `X̄_s`"). -/
noncomputable abbrev redClosure (S : Set Z) : Subscheme Z := ofClosed ⟨closure S, isClosed_closure⟩

theorem isSimpleAt_ι_of_isRegularLocalRing_stalk (D : Subscheme Z) (q : D.toScheme)
    (h : IsRegularLocalRing (D.toScheme.presheaf.stalk q)) : D.IsSimpleAt (D.ι q) := by
  obtain ⟨e⟩ := nonempty_stalk_quot_equiv D q
  exact ⟨mem_pts_ι D q, IsRegularLocalRing.of_ringEquiv e.symm⟩

/-- The scheme-level core of Lemma (AB.6), for an open subset `O_Y` of `Y` (= `X̂_s`): once the
reduced closure `B̄` of the image of `Bb ∩ O_W` in `Y` is the total transform of `Bs` and `c`
induces `B̄ ≅ Bs` (the Corollary of (AB.3)), the total transform of `Bs` agrees with the kernel
of `Bb → Y` over `O_Y`, and `Bs` is simple at the images of the simple points of `Bb`.  (The
version with `O_Y = c⁻¹(O_X)` for an open `O_X` of `X` is
`stalkIdeal_totalTransform_eq_ker_and_isSimpleAt`; the open subschemes `X̂*'_s` of the corrected
construction are not of that form, hence this generalization.) -/
theorem stalkIdeal_totalTransform_eq_ker_and_isSimpleAt_of_isOpen {X Y W : Scheme.{u}}
    (c : Y ⟶ X) (i : W ⟶ Y) [IsClosedImmersion i] (Bb : Subscheme W) {OY : Set Y}
    (hO : IsOpen OY) {OW : Set W} (hOW : ∀ b, b ∈ OW ↔ i b ∈ OY)
    (hns : ∀ b ∈ Bb.pts ∩ OW, Bb.IsSimpleAt b) (Bs : Subscheme X)
    (htt : totalTransform c Bs = redClosure (i '' (Bb.pts ∩ OW)))
    (e : (redClosure (i '' (Bb.pts ∩ OW))).toScheme ≅ Bs.toScheme)
    (he : e.hom ≫ Bs.ι = (redClosure (i '' (Bb.pts ∩ OW))).ι ≫ c) :
    (∀ yh ∈ OY, (totalTransform c Bs).stalkIdeal yh =
      Subscheme.stalkIdeal (Bb.ι ≫ i).ker yh) ∧
    ∀ b ∈ Bb.pts ∩ OW, Bs.IsSimpleAt (c (i b)) := by
  have hTK : ((⟨closure (i '' (Bb.pts ∩ OW)), isClosed_closure⟩ : TopologicalSpace.Closeds Y) :
      Set Y) ⊆ Subscheme.pts (Bb.ι ≫ i).ker := by
    refine closure_minimal ?_ (Bb.ι ≫ i).ker.support.isClosed
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨b₀, rfl⟩ := exists_ι_eq_of_mem_pts Bb hb.1
    exact apply_mem_pts_ker_comp i Bb b₀
  have hKT : Subscheme.pts (Bb.ι ≫ i).ker ∩ OY ⊆ closure (i '' (Bb.pts ∩ OW)) := by
    rintro y ⟨hy, hyO⟩
    obtain ⟨b₀, rfl⟩ := exists_eq_of_mem_pts_ker_comp i Bb hy
    exact subset_closure ⟨Bb.ι b₀, ⟨mem_pts_ι Bb b₀, (hOW _).mpr hyO⟩, rfl⟩
  have hreg : ∀ y ∈ Subscheme.pts (Bb.ι ≫ i).ker ∩ OY,
      IsRegularLocalRing (Y.presheaf.stalk y ⧸ Subscheme.stalkIdeal (Bb.ι ≫ i).ker y) := by
    rintro y ⟨hy, hyO⟩
    refine isRegularLocalRing_quotient_stalkIdeal_ker_comp i Bb hy fun b₀ hb₀ => ?_
    exact hns _ ⟨mem_pts_ι Bb b₀, (hOW _).mpr (by rw [hb₀]; exact hyO)⟩
  have hprime : ∀ y ∈ Subscheme.pts (Bb.ι ≫ i).ker ∩ OY,
      (Subscheme.stalkIdeal (Bb.ι ≫ i).ker y).IsPrime := by
    intro y hy
    have := hreg y hy
    have : IsDomain (Y.presheaf.stalk y ⧸ Subscheme.stalkIdeal (Bb.ι ≫ i).ker y) :=
      Transforms.isDomain_of_isRegularLocalRing _
    exact Ideal.Quotient.isDomain_iff_prime _ |>.mp this
  have hb' : ∀ y ∈ OY, (redClosure (i '' (Bb.pts ∩ OW))).stalkIdeal y =
      Subscheme.stalkIdeal (Bb.ι ≫ i).ker y := fun y hy =>
    stalkIdeal_ofClosed_eq_of_local _ ⟨closure (i '' (Bb.pts ∩ OW)), isClosed_closure⟩ hO hTK hKT
      hprime hy
  refine ⟨fun y hy => by rw [htt]; exact hb' y hy, fun b hb => ?_⟩
  have hbT : i b ∈ (redClosure (i '' (Bb.pts ∩ OW))).pts := by
    rw [pts_ofClosed]; exact subset_closure ⟨b, hb, rfl⟩
  obtain ⟨bb, hbb⟩ := exists_ι_eq_of_mem_pts _ hbT
  have hyO : (redClosure (i '' (Bb.pts ∩ OW))).ι bb ∈ OY := by
    rw [hbb]; exact (hOW b).mp hb.2
  have hKy : (redClosure (i '' (Bb.pts ∩ OW))).ι bb ∈ Subscheme.pts (Bb.ι ≫ i).ker := by
    rw [hbb]
    obtain ⟨b₀, rfl⟩ := exists_ι_eq_of_mem_pts Bb hb.1
    exact apply_mem_pts_ker_comp i Bb b₀
  have hreg1 := isRegularLocalRing_quotient_stalkIdeal_ker_comp i Bb hKy fun b₁ hb₁ =>
    hns _ ⟨mem_pts_ι Bb b₁, (hOW _).mpr (by rw [hb₁]; exact hyO)⟩
  rw [← hb' _ hyO] at hreg1
  obtain ⟨e2⟩ := nonempty_stalk_quot_equiv (redClosure (i '' (Bb.pts ∩ OW))) bb
  have h1 : IsRegularLocalRing ((redClosure (i '' (Bb.pts ∩ OW))).toScheme.presheaf.stalk bb) :=
    IsRegularLocalRing.of_ringEquiv e2
  have h2 : IsRegularLocalRing (Bs.toScheme.presheaf.stalk (e.hom bb)) := by
    have : IsIso (e.hom.stalkMap bb) := inferInstance
    exact IsRegularLocalRing.of_ringEquiv (asIso (e.hom.stalkMap bb)).commRingCatIsoToRingEquiv.symm
  have hq : Bs.ι (e.hom bb) = c ((redClosure (i '' (Bb.pts ∩ OW))).ι bb) :=
    congrArg (fun g => g.base bb) he
  rw [← hbb, ← hq]
  exact isSimpleAt_ι_of_isRegularLocalRing_stalk Bs _ h2

/-- The scheme-level core of Lemma (AB.6): once the reduced closure `B̄` of the image of
`Bb ∩ O_W` in `Y` is the total transform of `Bs` and `c` induces `B̄ ≅ Bs` (the Corollary of
(AB.3)), the total transform of `Bs` agrees with the kernel of `Bb → Y` over `c⁻¹(O_X)`, and
`Bs` is simple at the images of the simple points of `Bb`.  The case `O_Y = c⁻¹(O_X)` of
`stalkIdeal_totalTransform_eq_ker_and_isSimpleAt_of_isOpen`. -/
theorem stalkIdeal_totalTransform_eq_ker_and_isSimpleAt {X Y W : Scheme.{u}} (c : Y ⟶ X)
    (i : W ⟶ Y) [IsClosedImmersion i] (Bb : Subscheme W) {OX : Set X} (hOX : IsOpen OX)
    {OW : Set W} (hOW : ∀ b, b ∈ OW ↔ c (i b) ∈ OX)
    (hns : ∀ b ∈ Bb.pts ∩ OW, Bb.IsSimpleAt b) (Bs : Subscheme X)
    (htt : totalTransform c Bs = redClosure (i '' (Bb.pts ∩ OW)))
    (e : (redClosure (i '' (Bb.pts ∩ OW))).toScheme ≅ Bs.toScheme)
    (he : e.hom ≫ Bs.ι = (redClosure (i '' (Bb.pts ∩ OW))).ι ≫ c) :
    (∀ yh ∈ c ⁻¹' OX, (totalTransform c Bs).stalkIdeal yh =
      Subscheme.stalkIdeal (Bb.ι ≫ i).ker yh) ∧
    ∀ b ∈ Bb.pts ∩ OW, Bs.IsSimpleAt (c (i b)) :=
  stalkIdeal_totalTransform_eq_ker_and_isSimpleAt_of_isOpen c i Bb
    (hOX.preimage c.continuous) hOW hns Bs htt e he

end Subscheme

namespace AB

/-- **Lemma (AB.6)** (p. 306) for an arbitrary open family with removals `U_s`
(`Frame.RemovalFamily`), with `U_s`, `Ū_s = U_s ∩ X̄_s` in place of `X̂'_s`, `X̄'_s`, assembled
from the permissibility of `P̂ = B_s Ŝ_s` for the `J_j(s) Ŝ_s` at the points of `B̄' ∩ Ū_s`
(`hperm`).  The printed version is the instance `U_s = X̂'_s`
(`Frame.isIrreducible_and_isNormallyFlatAlongAt_of_isPermissibleCenter`); the corrected
construction of `Hironaka.Ch4.ComponentwiseConstruction` is the instance `U_s = X̂*'_s`.  The
proof is that of the printed version: of `X̂'_s` it uses only that it is open in `X̂_s`
(`Subscheme.stalkIdeal_totalTransform_eq_ker_and_isSimpleAt_of_isOpen`). -/
@[blueprint "lem:IV.AB-6-of-permissible-generic"
  (statement := /-- Notation as in \cref{lem:IV.AB-6-of-permissible}, for an arbitrary open
    family with removals $U_s\subseteq\hat X_s$ (\cref{lem:IV.3-construction-facts-generic}),
    with $U_s$ and $\bar U_s=U_s\cap\bar X_s$ in place of $\hat X_s'$ and $\bar X_s'$: the
    conclusion of \cref{lem:IV.AB-6-of-permissible} holds, with
    $\bar B'=c_s^{-1}(B_s)\cap U_s$. (Formalization note: the printed version is the instance
    $U_s=\hat X_s'$; the corrected construction of \cref{def:IV.3-construction-componentwise}
    is the instance $U_s=\hat X_s^{*\prime}$.) -/)
  (proof := /-- The proof of \cref{lem:IV.AB-6-of-permissible} verbatim: of $\hat X_s'$ it
    uses only that it is an open subset of $\hat X_s$ with $\bar X_s'=\hat X_s'\cap\bar X_s$.
 -/)
  (proofUses := ["cor:IV.AB-3", "lem:IV.AB-2", "rem:III.5-1", "lem:II.3-9", "cor:II.1-thm1",
    "lem:IV.AB-6-permissible"])
  (latexEnv := "lemma")]
theorem Frame.RemovalFamily.isIrreducible_and_isNormallyFlatAlongAt_of_isPermissibleCenter [Hironaka.HironakaCitedResults.{u}]
    {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
    {𝒮 : Frame hS} (R : 𝒮.RemovalFamily) (s : ℕ) (Bb : Subscheme (𝒮.xBar s).toScheme)
    (hns : ∀ xb ∈ Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme), Bb.IsSimpleAt xb)
    (hirr : IsIrreducible (Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme)))
    (hg : ((𝒮.xBar s).ι ≫ (𝒮.tHat.pre s).composite).base ''
      (Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme)) = {hS.xh})
    (hperm : ∀ xb ∈ Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme), ∀ j,
      IsPermissibleCenter ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb))
        ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal ((𝒮.xBar s).ι.base xb))
        ((Subscheme.totalTransform (𝒮.c s) (Subscheme.ofClosed
          ⟨closure ((𝒮.cBar s).base ''
            (Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme))), isClosed_closure⟩)).stalkIdeal
          ((𝒮.xBar s).ι.base xb))) :
    let Bs : Subscheme (T.X s) := Subscheme.ofClosed
      ⟨closure ((𝒮.cBar s).base '' (Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme))),
        isClosed_closure⟩
    Bs.IsIrreducible ∧
    (∀ xh ∈ R.U s, (Subscheme.totalTransform (𝒮.c s) Bs).stalkIdeal xh =
      Subscheme.stalkIdeal (Bb.ι ≫ (𝒮.xBar s).ι).ker xh) ∧
    ∃ Us : Set (T.X s), (∃ U₀ : Set (T.X s), IsOpen U₀ ∧ Us = U₀ ∩ Bs.pts) ∧ Us.Nonempty ∧
      (∀ x ∈ Us, Bs.IsSimpleAt x) ∧
      (𝒮.cBar s).base '' (Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme)) ⊆ Us ∧
      ∀ x ∈ Us, ∀ j, Subscheme.IsNormallyFlatAlongAt' (T.sys ℜ s j) Bs x := by
  intro Bs
  have hX : IsAlgebraicScheme (T.X s) := hS.isAlgebraicScheme_X s
  set A : Set (𝒮.xBar s).toScheme := Bb.pts ∩ (R.uBar s : Set (𝒮.xBar s).toScheme) with hA
  have hOW : ∀ b : (𝒮.xBar s).toScheme, b ∈ (R.uBar s : Set (𝒮.xBar s).toScheme) ↔
      (𝒮.xBar s).ι.base b ∈ (R.U s : Set (𝒮.tHat.X s)) := fun b => Iff.rfl
  have hBsA : (𝒮.cBar s).base '' A = (𝒮.c s).base '' ((𝒮.xBar s).ι.base '' A) := by
    rw [Set.image_image]; rfl
  -- `B̄`, the reduced closure of the image of `B̄'` in `X̂_s`
  have hclosed : IsClosed ({hS.xh} : Set (xHat0 X x₀)) :=
    ((isClosed_singleton_iff_eq_xhat0_and_c0_apply_xhat0 x₀ (hS.ambient.2.1 x₀)).1 hS.xh).mpr rfl
  have hBbarImg : (𝒮.tHat.pre s).composite.base ''
      (Subscheme.redClosure ((𝒮.xBar s).ι.base '' A)).pts = {hS.xh} := by
    rw [Subscheme.pts_ofClosed]
    have hg' : (𝒮.tHat.pre s).composite.base '' ((𝒮.xBar s).ι.base '' A) = {hS.xh} := by
      rw [Set.image_image]; exact hg
    refine Set.Subset.antisymm ?_ ?_
    · refine (image_closure_subset_closure_image (𝒮.tHat.pre s).composite.continuous).trans ?_
      rw [hg']; exact hclosed.closure_subset_iff.mpr le_rfl
    · rw [← hg']
      exact Set.image_mono subset_closure
  obtain ⟨B, ⟨hBred, himg, hBbar⟩, -, e, he⟩ :=
    (Completion.bijective_quotientMap_and_exists_unique_reduced_totalTransform hS
      𝒮.toCompletion s).2 (Subscheme.redClosure ((𝒮.xBar s).ι.base '' A))
      (Subscheme.ofClosed_isReduced _) hBbarImg
  have hsurj : Function.Surjective e.hom.base := e.hom.homeomorph.surjective
  have hrR : Set.range (Subscheme.redClosure ((𝒮.xBar s).ι.base '' A)).ι.base =
      closure ((𝒮.xBar s).ι.base '' A) := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact Subscheme.pts_ofClosed _
  have hBpts : B.pts = (𝒮.c s).base '' closure ((𝒮.xBar s).ι.base '' A) := by
    have h1 : B.pts = Set.range B.ι.base :=
      (Scheme.IdealSheafData.range_subschemeι (I := B)).symm
    have h2 : Set.range B.ι.base = Set.range (e.hom ≫ B.ι).base := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]
    rw [h1, h2, he, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrR]
  have hBsets : B.pts = closure ((𝒮.cBar s).base '' A) := by
    refine Set.Subset.antisymm ?_ ?_
    · rw [hBpts, hBsA]
      exact image_closure_subset_closure_image (𝒮.c s).continuous
    · refine closure_minimal ?_ B.support.isClosed
      rw [hBsA, hBpts]
      exact Set.image_mono subset_closure
  have hBeq : B = Bs := by
    rw [Subscheme.eq_ofClosed_support B hBred]
    congr 1
    exact TopologicalSpace.Closeds.ext hBsets
  subst hBeq
  obtain ⟨hb, hsimp⟩ := Subscheme.stalkIdeal_totalTransform_eq_ker_and_isSimpleAt_of_isOpen
    (𝒮.c s) (𝒮.xBar s).ι Bb (OY := (R.U s : Set (𝒮.tHat.X s))) (R.U s).isOpen hOW hns Bs
    hBbar.symm e he
  -- irreducibility
  have hIrrA : IsIrreducible ((𝒮.cBar s).base '' A) := hirr.image _ (𝒮.cBar s).continuous.continuousOn
  have hptsBs : Bs.pts = closure ((𝒮.cBar s).base '' A) := Subscheme.pts_ofClosed _
  have hIrrBs : IsIrreducible Bs.pts := by rw [hptsBs]; exact hIrrA.closure
  refine ⟨Subscheme.isIrreducible_of_pts Bs hIrrBs, fun xh hxh => hb xh hxh, ?_⟩
  -- the open set `U_s`
  obtain ⟨Os, hOs, hOsS⟩ := Subscheme.exists_isOpen_isSimpleAt Bs
  choose Oj hOj hOjN using fun j => Subscheme.exists_isOpen_isNormallyFlatAlongAt' (T.sys ℜ s j) Bs
  have hpt : ∀ xb ∈ A, ∀ j, (T.sys ℜ s j).stalkIdeal ((𝒮.cBar s).base xb) ≤
        Bs.stalkIdeal ((𝒮.cBar s).base xb) ∧
      IsNormallyFlatAlongIdeal ((Bs.stalkIdeal ((𝒮.cBar s).base xb)).map
        (Ideal.Quotient.mk ((T.sys ℜ s j).stalkIdeal ((𝒮.cBar s).base xb)))) := by
    intro xb hxb j
    have hxh : (𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base xb) = hS.xh := by
      have : (𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base xb) ∈
          ((𝒮.xBar s).ι ≫ (𝒮.tHat.pre s).composite).base '' A := ⟨xb, hxb, rfl⟩
      rw [hg] at this; exact this
    obtain ⟨hreg, hmaps, -⟩ := 𝒮.toCompletion.isRegularLocalRing_and_mapsRSOP_stalkMap
      (hS.ambient.2.1 x₀) hS.isNonsingular_X hS.isNonsingular_B s _ hxh
    have hR : IsRegularLocalRing ((T.X s).presheaf.stalk
        ((𝒮.c s).base ((𝒮.xBar s).ι.base xb))) := hS.isNonsingular_X s _
    have hP : (Bs.stalkIdeal ((𝒮.cBar s).base xb)).IsPrime := by
      have h1 : IsRegularLocalRing ((T.X s).presheaf.stalk ((𝒮.cBar s).base xb) ⧸
          Bs.stalkIdeal ((𝒮.cBar s).base xb)) := (hsimp xb hxb).2
      have : IsDomain ((T.X s).presheaf.stalk ((𝒮.cBar s).base xb) ⧸
          Bs.stalkIdeal ((𝒮.cBar s).base xb)) := Transforms.isDomain_of_isRegularLocalRing _
      exact (Ideal.Quotient.isDomain_iff_prime _).mp this
    have hPtop : Bs.stalkIdeal ((𝒮.cBar s).base xb) ≠ ⊤ := hP.ne_top
    have _ : (Bs.stalkIdeal ((𝒮.c s).base ((𝒮.xBar s).ι.base xb))).IsPrime := hP
    have _ : (Bs.stalkIdeal ((𝒮.cBar s) xb)).IsPrime := hP
    have hperm' := hperm xb hxb j
    rw [stalkIdeal_totalTransform, stalkIdeal_totalTransform] at hperm'
    let α := ((𝒮.c s).stalkMap ((𝒮.xBar s).ι.base xb)).hom
    have hJP : (T.sys ℜ s j).stalkIdeal ((𝒮.cBar s).base xb) ≤
        Bs.stalkIdeal ((𝒮.cBar s).base xb) := by
      rcases hperm' with h | ⟨-, h, -, -⟩
      · exact absurd h (map_ne_top_of_mapsRSOP α hmaps hPtop)
      · exact le_of_map_le_of_mapsRSOP α hmaps h
    refine ⟨hJP, ?_⟩
    have := ((@isPermissibleCenter_map_iff _ _ _ _ _ _ α _ hmaps _ _ hP hJP).2.2.2).mpr hperm'
    rcases this with h | ⟨-, -, -, h⟩
    · exact absurd h hPtop
    · exact h
  have hmem : ∀ xb ∈ A, (𝒮.cBar s).base xb ∈ Bs.pts := fun xb hxb => by
    rw [hptsBs]; exact subset_closure ⟨xb, hxb, rfl⟩
  have hVpts : ∀ xb ∈ A, ∀ j, (𝒮.cBar s).base xb ∈ (T.sys ℜ s j).pts := fun xb hxb j => by
    rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top]
    intro htop
    have h1 := (hpt xb hxb j).1
    rw [htop, top_le_iff] at h1
    exact (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp (hmem xb hxb)) h1
  have hxO : ∀ xb ∈ A, (𝒮.cBar s).base xb ∈ Os ∩ ⋂ j, Oj j := fun xb hxb => by
    refine ⟨(hOsS _ (hmem xb hxb)).mp (hsimp xb hxb), Set.mem_iInter.mpr fun j => ?_⟩
    have hV := hVpts xb hxb j
    refine (hOjN j _ (hmem xb hxb) hV).mp ?_
    refine Subscheme.isNormallyFlatAlongAt'_of_isNormallyFlatAlongIdeal _ _ hV (hmem xb hxb) ?_
    exact (hpt xb hxb j).2
  have hVall : ∀ j, Bs.pts ⊆ (T.sys ℜ s j).pts := fun j => by
    obtain ⟨xb, hxb⟩ := hirr.nonempty
    exact Subscheme.pts_subset_of_stalkIdeal_le (T.sys ℜ s j) Bs hIrrBs (hmem xb hxb)
      (hpt xb hxb j).1
  refine ⟨(Os ∩ ⋂ j, Oj j) ∩ Bs.pts, ⟨Os ∩ ⋂ j, Oj j, hOs.inter (isOpen_iInter_of_finite hOj), rfl⟩,
    ?_, ?_, ?_, ?_⟩
  · obtain ⟨xb, hxb⟩ := hirr.nonempty
    exact ⟨(𝒮.cBar s).base xb, hxO xb hxb, hmem xb hxb⟩
  · rintro x ⟨⟨hxO, -⟩, hxB⟩
    exact (hOsS x hxB).mpr hxO
  · rintro _ ⟨xb, hxb, rfl⟩
    exact hxO xb hxb |> fun h => ⟨h, hmem xb hxb⟩
  · rintro x ⟨⟨-, hxO⟩, hxB⟩ j
    exact (hOjN j x hxB (hVall j hxB)).mpr (Set.mem_iInter.mp hxO j)

/-- **Lemma (AB.6)** (p. 306), assembled from the permissibility of `P̂ = B_s Ŝ_s` for the
`J_j(s) Ŝ_s` at the points of `B̄' ∩ X̄'_s` (`hperm`; this is the output of the paper's frame
argument "by the same argument as in the proof of Lemma (AB.5)", see
`isPermissibleCenter_of_ordElem_le`).  The conclusion is that of
`Frame.isIrreducible_and_isNormallyFlatAlongAt_of_jbar_le_pow`.

In Lean: the instance `U_s = X̂'_s` (`Frame.removalFamily`) of
`Frame.RemovalFamily.isIrreducible_and_isNormallyFlatAlongAt_of_isPermissibleCenter`
(`lem:IV.AB-6-of-permissible-generic`), which is proved by the argument described below.

The proof follows the paper: `B̄` is the reduced closure of `B̄'` in `X̂_s`; the Corollary of
(AB.3) gives the unique reduced `B_s` with `B̄ = c_s⁻¹(B_s)` and `B̄ ≅ B_s`; `B_s` is the closure of
`c_s(B̄')`; `U_s` is the set of simple points of `B_s` at which all the `V_j(s)`, `W(s)` are
normally flat; `c_s(B̄') ⊆ U_s` is checked at a point `x' = c_s(x̂')`, where `P̂ = P Ŝ_s` is a
permissible center for the `Ĵ_j(s) = J_j(s) Ŝ_s` and so `P` is one for `J_j(s)` (Remark 1, §5,
which rests on Lemma 9 of Ch. II §3).

Deviation from the paper (gap filled):
* the paper's "`B_s` is the closure of `c_s(B̄')`" and "`B̄' = c_s⁻¹(B_s) ∩ X̂'_s`" are proved:
  `B_s` is identified with the reduced closure via the isomorphism `B̄ ≅ B_s` and the closedness of
  its image; the comparison of `c_s⁻¹(B_s)` with the subscheme `Bb` of `X̄_s` is made stalkwise on
  `X̂'_s` (the ideal of `Bb` in `X̂_s` has a regular, hence prime, quotient at the points of
  `X̂'_s`, so it is the ideal of the reduced closure there);
* "Let `U_s` be the open subset of `B_s` consisting of those simple points … at which all the
  `V_j(s)` and `W(s)` are normally flat along `B_s`": openness of both conditions is taken from
  Cor. of Th. 1, Ch. II §1 (applied on `V_j(s)`) and p. 161 (iii); since `B_s ⊆ V_j(s)` is not
  assumed in the definition of `IsNormallyFlatAlongAt'`, Lean first proves it at the points of
  `B_s` from `J_j(s) ⊆ P` at one point (the generic point of the irreducible `B_s` is a
  generization of it, where the stalk of `V_j(s)` is proper);
* non-emptiness of `U_s` (not stated in the proof) follows from `U_s ⊇ c_s(B̄')`, and that `B_s` is
  simple at `c_s(x̂')` from the regularity of `B̄'` at `x̂'` through the isomorphism `B̄ ≅ B_s`. -/
@[blueprint "lem:IV.AB-6-of-permissible"
  (statement := /-- Notation as in \cref{lem:IV.AB-6}. Suppose that for every point $\hat x'$ of
    $\bar B'$ and every $0\le j\le\beta$ the ideal $P\hat S_s$ (with $P$ the ideal of $B_s$ at
    $x'=c_s(\hat x')$ and $\hat S_s$ the local ring of $\hat X_s$ at $\hat x'$) is a permissible
    center for $J_j(s)\hat S_s$. Then the conclusion of \cref{lem:IV.AB-6} holds: $B_s$ is
    irreducible, $\bar B'=c_s^{-1}(B_s)\cap\hat X_s'$, and there is a non-empty open subset $U_s$
    of $B_s$ consisting of simple points, containing $c_s(\bar B')$, along which all the $V_j(s)$
    and $W(s)$ are normally flat. -/)
  (proof := /-- Let $\bar B$ be the closure of $\bar B'$ in $\hat X_s$, a reduced subscheme with
    $\hat g_s(\bar B)=\hat x_0$. By the Corollary of (AB.3) (\cref{cor:IV.AB-3}) there is a
    unique reduced $B_s\subseteq X_s$ with $\bar B=c_s^{-1}(B_s)$ and $c_s$ induces an
    isomorphism $\bar B\to B_s$; $B_s$ is the closure of $c_s(\bar B')$. At the points of
    $\hat X_s'$ the ideal of $\bar B$ is that of $\bar B'$, so $\bar B'=c_s^{-1}(B_s)\cap
    \hat X_s'$, and $B_s$ is simple at $c_s(\hat x')$ for $\hat x'\in\bar B'$ since $\bar B'$ is
    regular there. Let $\hat x'\in\bar B'$, $x'=c_s(\hat x')$. By hypothesis $\hat P=P\hat S_s$
    is a permissible center for $\hat J_j(s)=J_j(s)\hat S_s$; since $S_s\to\hat S_s$ transforms a
    regular system of parameters into one (\cref{lem:IV.AB-2}), $P$ is a permissible center for
    $J_j(s)$ (\cref{rem:III.5-1}, i.e.\ Lemma~9, \S3, Ch.~II, \cref{lem:II.3-9}), that is
    $V_j(s)$ and $W(s)$ are normally flat along $B_s$ at $x'$. The simple points of $B_s$ at which
    all $V_j(s)$, $W(s)$ are normally flat form an open subset of $B_s$
    (\cref{cor:II.1-thm1}) which therefore contains $c_s(\bar B')$. \textsc{q.e.d.}

    \textbf{Deviation from the paper (gap filled).} The paper's ``$B_s$ is the closure of
    $c_s(\bar B')$'' and ``$\bar B'=c_s^{-1}(B_s)\cap\hat X_s'$'' are proved in Lean (via the
    isomorphism $\bar B\cong B_s$ and a stalkwise comparison of the ideals on $\hat X_s'$); the
    openness of the set $U_s$ is proved from \cref{cor:II.1-thm1} and the openness of the simple
    locus, after showing $B_s\subseteq V_j(s)$ on points from $J_j(s)\subseteq P$ at one point
    (generic point of the irreducible $B_s$); non-emptiness of $U_s$ is deduced from
    $U_s\supseteq c_s(\bar B')$. The step ``by the same argument as in the proof of Lemma (AB.5),
    we can find a regular frame $(T_s;z_s)$\dots'' is not part of this node: it is the hypothesis
    on $\hat P$.

    (Formalization note: in Lean this is the instance $U_s=\hat X_s'$ of
    \cref{lem:IV.AB-6-of-permissible-generic}, the lemma for an arbitrary open family with
    removals.) -/)
  (proofUses := ["cor:IV.AB-3", "lem:IV.AB-2", "rem:III.5-1", "lem:II.3-9", "cor:II.1-thm1",
    "lem:IV.AB-6-permissible", "lem:IV.AB-6-of-permissible-generic"])
  (latexEnv := "lemma")]
theorem Frame.isIrreducible_and_isNormallyFlatAlongAt_of_isPermissibleCenter [Hironaka.HironakaCitedResults.{u}] {N n : ℕ}
    {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
    (𝒮 : Frame hS) (s : ℕ) (Bb : Subscheme (𝒮.xBar s).toScheme)
    (hns : ∀ xb ∈ Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme), Bb.IsSimpleAt xb)
    (hirr : IsIrreducible (Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme)))
    (hg : ((𝒮.xBar s).ι ≫ (𝒮.tHat.pre s).composite).base ''
      (Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme)) = {hS.xh})
    (hperm : ∀ xb ∈ Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme), ∀ j,
      IsPermissibleCenter ((𝒮.tHat.X s).presheaf.stalk ((𝒮.xBar s).ι.base xb))
        ((Subscheme.totalTransform (𝒮.c s) (T.sys ℜ s j)).stalkIdeal ((𝒮.xBar s).ι.base xb))
        ((Subscheme.totalTransform (𝒮.c s) (Subscheme.ofClosed
          ⟨closure ((𝒮.cBar s).base ''
            (Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme))), isClosed_closure⟩)).stalkIdeal
          ((𝒮.xBar s).ι.base xb))) :
    let Bs : Subscheme (T.X s) := Subscheme.ofClosed
      ⟨closure ((𝒮.cBar s).base '' (Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme))),
        isClosed_closure⟩
    Bs.IsIrreducible ∧
    (∀ xh ∈ 𝒮.xHatPrime s, (Subscheme.totalTransform (𝒮.c s) Bs).stalkIdeal xh =
      Subscheme.stalkIdeal (Bb.ι ≫ (𝒮.xBar s).ι).ker xh) ∧
    ∃ Us : Set (T.X s), (∃ U₀ : Set (T.X s), IsOpen U₀ ∧ Us = U₀ ∩ Bs.pts) ∧ Us.Nonempty ∧
      (∀ x ∈ Us, Bs.IsSimpleAt x) ∧
      (𝒮.cBar s).base '' (Bb.pts ∩ (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme)) ⊆ Us ∧
      ∀ x ∈ Us, ∀ j, Subscheme.IsNormallyFlatAlongAt' (T.sys ℜ s j) Bs x :=
  𝒮.removalFamily.isIrreducible_and_isNormallyFlatAlongAt_of_isPermissibleCenter s Bb hns hirr
    hg hperm
