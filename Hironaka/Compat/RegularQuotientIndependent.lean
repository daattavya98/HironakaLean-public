/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Compat.RegularQuotient

/-!
# Compatibility layer: elements independent modulo `𝔫²`, derivations, and regular quotients

A step in the proof of property (c) of the class 𝔅 (p. 161), the
"elementary lemma" behind footnote 30's "jacobian criterion for simplicity": in a regular local
ring `(L, 𝔫)`,

* `IsIndepModSq f`: the images of `f₁,…,f_h ∈ 𝔫` in `𝔫/𝔫²` are linearly independent over the
  residue field (`Σ cᵢ fᵢ ∈ 𝔫²` forces all `cᵢ ∈ 𝔫`);
* `isIndepModSq_of_isUnit_det`: if there are derivations `D₁,…,D_h` of `L` with `det(D_j f_i)` a
  unit, then the `f_i` are independent modulo `𝔫²` (apply `D_j` to a relation; `D_j(𝔫²) ⊆ 𝔫`);
* `isRegularLocalRing_quotient_span_of_isIndepModSq`: if `L` is regular and `f` is independent
  modulo `𝔫²`, then `L/(f₁,…,f_h)` is regular (the one-element lemma
  `quotient_span_singleton_regular` applied `h` times).
-/

@[expose] public section

open IsLocalRing Matrix

namespace Hironaka

universe u

section Independent

variable {L : Type u} [CommRing L] [IsLocalRing L]

/-- Elements `f₁,…,f_h` of a local ring `L` are *independent modulo `𝔫²`* (`𝔫` the maximal ideal)
if `Σ cᵢ fᵢ ∈ 𝔫²` implies `cᵢ ∈ 𝔫` for all `i`: their images in `𝔫/𝔫²` (for `fᵢ ∈ 𝔫`) are
linearly independent over the residue field.  For a regular local ring this says that the `f_i`
are part of a regular system of parameters. -/
def IsIndepModSq {ι : Type*} [Fintype ι] (f : ι → L) : Prop :=
  ∀ c : ι → L, ∑ i, c i * f i ∈ maximalIdeal L ^ 2 → ∀ i, c i ∈ maximalIdeal L

/-- A derivation maps `𝔫²` into `𝔫`. -/
theorem derivation_mem_maximalIdeal_of_mem_sq {k : Type*} [CommRing k] [Algebra k L]
    (D : Derivation k L L) {z : L} (hz : z ∈ maximalIdeal L ^ 2) : D z ∈ maximalIdeal L := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_right _ _ hb)
  · rw [map_add]
    exact add_mem hx hy

/-- **The elementary lemma** behind the jacobian criterion: if `D₁,…,D_h` are derivations of a
local ring `L` and `f₁,…,f_h ∈ 𝔫` are such that `det(D_j f_i)` is a unit, then the `f_i` are
independent modulo `𝔫²`.  (Apply `D_j` to a relation `Σ cᵢ fᵢ ∈ 𝔫²`; since `D_j(𝔫²) ⊆ 𝔫` and
`fᵢ ∈ 𝔫`, one gets `Σ cᵢ D_j fᵢ ∈ 𝔫` for all `j`, and the matrix `(D_j fᵢ)` is invertible modulo
`𝔫`.) -/
@[blueprint "lem:indep-mod-sq-of-unit-det"
  (statement := /-- Let $(L,\mathfrak n)$ be a local ring, $D_1,\dots,D_h$ derivations of $L$ and
    $f_1,\dots,f_h\in\mathfrak n$ such that $\det(D_jf_i)$ is a unit of $L$. Then
    $f_1,\dots,f_h$ are linearly independent modulo $\mathfrak n^2$: $\sum c_if_i\in\mathfrak
    n^2$ implies all $c_i\in\mathfrak n$. -/)
  (proof := /-- Apply $D_j$ to a relation $\sum_ic_if_i\in\mathfrak n^2$. Since
    $D_j(\mathfrak n^2)\subseteq\mathfrak n$ and $f_i\in\mathfrak n$, one gets
    $\sum_ic_iD_jf_i\in\mathfrak n$ for all $j$; the matrix $(D_jf_i)$ is invertible modulo
    $\mathfrak n$, so all $c_i\in\mathfrak n$. \textbf{Deviation from the paper (gap filled).}
    Footnote~30 (p.~161) says only ``For this case, will suffice the jacobian criterion for
    simplicity''; this lemma is the elementary half used for the completion, see
    \cref{lem:class-A-c-complete}. -/)
  (latexEnv := "lemma")]
theorem isIndepModSq_of_isUnit_det {k : Type*} [CommRing k] [Algebra k L] {h : ℕ}
    (D : Fin h → Derivation k L L) (f : Fin h → L) (hf : ∀ i, f i ∈ maximalIdeal L)
    (hdet : IsUnit (Matrix.of fun i j => D j (f i)).det) : IsIndepModSq f := by
  intro c hc i
  have hj : ∀ j, ∑ i, c i * D j (f i) ∈ maximalIdeal L := by
    intro j
    have h1 := derivation_mem_maximalIdeal_of_mem_sq (D j) hc
    rw [map_sum] at h1
    simp only [Derivation.leibniz, smul_eq_mul] at h1
    rw [Finset.sum_add_distrib] at h1
    have h2 : ∑ i, f i * D j (c i) ∈ maximalIdeal L :=
      Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hf i)
    exact (Ideal.add_mem_iff_left _ h2).mp h1
  let M : Matrix (Fin h) (Fin h) (ResidueField L) :=
    (Matrix.of fun i j => D j (f i)).map (residue L)
  have hM : M.det ≠ 0 := by
    show ((residue L).mapMatrix (Matrix.of fun i j => D j (f i))).det ≠ 0
    rw [← RingHom.map_det]
    exact (hdet.map (residue L)).ne_zero
  have hv : (fun i => residue L (c i)) ᵥ* M = 0 := by
    ext j
    simp only [Matrix.vecMul, dotProduct, M, Matrix.map_apply, Matrix.of_apply, Pi.zero_apply]
    simp only [← map_mul, ← map_sum]
    exact (residue_eq_zero_iff _).mpr (hj j)
  have := Matrix.eq_zero_of_vecMul_eq_zero hM hv
  exact (residue_eq_zero_iff _).mp (congrFun this i)

end Independent

section Quotient

/-- A quotient of a regular local ring by `(f₁,…,f_h)`, `f` independent modulo `𝔫²` (that is, part
of a regular system of parameters), is a regular local ring (the one-element lemma
`quotient_span_singleton_regular` applied `h` times). -/
@[blueprint "lem:regular-quotient-indep-mod-sq"
  (statement := /-- Let $L$ be a regular local ring and $f_1,\dots,f_h\in\mathfrak n$
    linearly independent modulo $\mathfrak n^2$. Then $L/(f_1,\dots,f_h)$ is a regular local
    ring. -/)
  (proof := /-- Induction on $h$: $f_1\notin\mathfrak n^2$, so $L/(f_1)$ is regular
    (\cref{lem:regular-quotient-hyperplane}); the images of $f_2,\dots,f_h$ are independent
    modulo the square of the maximal ideal of $L/(f_1)$ (a relation lifts to one in $L$ with an
    extra term $-bf_1$), and $L/(f_1,\dots,f_h)\cong(L/(f_1))/(f_2,\dots,f_h)$.
    \textbf{Deviation from the paper (gap filled).} Used tacitly with the jacobian criterion
    (footnote~30, p.~161). -/)
  (proofUses := ["lem:regular-quotient-hyperplane"])
  (latexEnv := "lemma")]
theorem isRegularLocalRing_quotient_span_of_isIndepModSq :
    ∀ (h : ℕ) (L : Type u) [CommRing L] [IsRegularLocalRing L] (f : Fin h → L),
      (∀ i, f i ∈ maximalIdeal L) → IsIndepModSq f →
      IsRegularLocalRing (L ⧸ Ideal.span (Set.range f)) := by
  intro h
  induction h with
  | zero =>
    intro L _ _ f _ _
    have hbot : Ideal.span (Set.range f) = ⊥ := by
      rw [Set.range_eq_empty, Ideal.span_empty]
    rw [hbot]
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot L).symm
  | succ h ih =>
    intro L _ _ f hf hind
    classical
    set x := f 0 with hxdef
    have hx : x ∈ maximalIdeal L := hf 0
    have hx2 : x ∉ maximalIdeal L ^ 2 := by
      intro hx2
      have hsum : ∑ i, (Pi.single 0 1 : Fin (h + 1) → L) i * f i = x := by
        rw [Fintype.sum_eq_single 0 (fun i hi => by simp [hi])]
        simp [hxdef]
      have := hind (Pi.single 0 1) (by rw [hsum]; exact hx2) 0
      simp at this
    have : IsLocalRing (L ⧸ Ideal.span {x}) :=
      isLocalRing_quotient_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hx)
    obtain ⟨hreg, -⟩ := quotient_span_singleton_regular hx hx2
    -- the family in the quotient
    set mk := Ideal.Quotient.mk (Ideal.span {x}) with hmk
    let f' : Fin h → L ⧸ Ideal.span {x} := fun i => mk (f i.succ)
    have hmax : maximalIdeal (L ⧸ Ideal.span {x}) = (maximalIdeal L).map mk :=
      (map_maximalIdeal_of_surjective mk Ideal.Quotient.mk_surjective).symm
    have hf' : ∀ i, f' i ∈ maximalIdeal (L ⧸ Ideal.span {x}) := fun i => by
      rw [hmax]
      exact Ideal.mem_map_of_mem _ (hf i.succ)
    have hind' : IsIndepModSq f' := by
      intro c' hc' i
      obtain ⟨c, hc⟩ : ∃ c : Fin h → L, ∀ i, mk (c i) = c' i :=
        ⟨fun i => (Ideal.Quotient.mk_surjective (c' i)).choose,
          fun i => (Ideal.Quotient.mk_surjective (c' i)).choose_spec⟩
      have h1 : mk (∑ i, c i * f i.succ) ∈ (maximalIdeal L ^ 2).map mk := by
        rw [Ideal.map_pow, ← hmax]
        convert hc' using 1
        simp [f', hc, map_sum]
      obtain ⟨q, hq, hqeq⟩ :=
        (Ideal.mem_map_iff_of_surjective mk Ideal.Quotient.mk_surjective).mp h1
      have h2 : ∑ i, c i * f i.succ - q ∈ Ideal.span {x} := by
        rw [← Ideal.Quotient.eq]
        exact hqeq.symm
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp h2
      have h3 : ∑ j : Fin (h + 1), (Fin.cons (-b) c : Fin (h + 1) → L) j * f j ∈
          maximalIdeal L ^ 2 := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have : -b * f 0 + ∑ i, c i * f i.succ = q := by
          rw [← hxdef] at *
          linear_combination (-1 : L) * hb
        rw [this]
        exact hq
      have h4 := hind _ h3 i.succ
      simp only [Fin.cons_succ] at h4
      rw [hmax, ← hc i]
      exact Ideal.mem_map_of_mem _ h4
    have ih' := ih (L ⧸ Ideal.span {x}) f' hf' hind'
    -- identify the two quotients
    have hrange : Set.range f = insert x (Set.range fun i : Fin h => f i.succ) := by
      ext y
      simp only [Set.mem_range, Set.mem_insert_iff]
      constructor
      · rintro ⟨i, rfl⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · left; rfl
        · right; exact ⟨j, rfl⟩
      · rintro (rfl | ⟨j, rfl⟩)
        · exact ⟨0, rfl⟩
        · exact ⟨j.succ, rfl⟩
    have hspan : Ideal.span (Set.range f) =
        Ideal.span {x} ⊔ Ideal.span (Set.range fun i : Fin h => f i.succ) := by
      rw [hrange, Set.insert_eq, Ideal.span_union]
    have hmap : (Ideal.span (Set.range fun i : Fin h => f i.succ)).map mk =
        Ideal.span (Set.range f') := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    let e₁ := DoubleQuot.quotQuotEquivQuotSup (Ideal.span {x})
      (Ideal.span (Set.range fun i : Fin h => f i.succ))
    let e₂ := Ideal.quotEquivOfEq hspan.symm
    let e₃ := Ideal.quotEquivOfEq hmap
    exact IsRegularLocalRing.of_ringEquiv ((e₃.symm.trans e₁).trans e₂)

/-- `isRegularLocalRing_quotient_span_of_isIndepModSq` with implicit arguments. -/
theorem IsIndepModSq.isRegularLocalRing_quotient {L : Type u} [CommRing L]
    [IsRegularLocalRing L] {h : ℕ} {f : Fin h → L} (hf : ∀ i, f i ∈ maximalIdeal L)
    (hind : IsIndepModSq f) : IsRegularLocalRing (L ⧸ Ideal.span (Set.range f)) :=
  isRegularLocalRing_quotient_span_of_isIndepModSq h L f hf hind

/-- **Regularity of the quotient from a unit jacobian determinant.**  If `L` is a regular local
ring, `f₁,…,f_h ∈ 𝔫` and `D₁,…,D_h` are derivations of `L` with `det(D_j f_i)` a unit, then
`L/(f₁,…,f_h)` is regular. -/
theorem isRegularLocalRing_quotient_span_of_isUnit_det {L : Type u} [CommRing L]
    [IsRegularLocalRing L] {k : Type*} [CommRing k] [Algebra k L] {h : ℕ}
    (D : Fin h → Derivation k L L) (f : Fin h → L) (hf : ∀ i, f i ∈ maximalIdeal L)
    (hdet : IsUnit (Matrix.of fun i j => D j (f i)).det) :
    IsRegularLocalRing (L ⧸ Ideal.span (Set.range f)) :=
  (isIndepModSq_of_isUnit_det D f hf hdet).isRegularLocalRing_quotient hf

end Quotient

section MinimalGenerators

open IsLocalRing

/-- **Part of a minimal system of generators of the maximal ideal is independent modulo `𝔫²`.**
If `S` generates `𝔫` and has `spanFinrank 𝔫` elements, then any `T ⊆ S` is independent modulo `𝔫²`:
a relation `Σ c_x x ∈ 𝔫²` with a unit coefficient would let one drop a generator (Nakayama,
`span_erase_eq_of_mem`). -/
theorem isIndepModSq_of_subset_minimalGenerators {L : Type u} [CommRing L] [IsLocalRing L]
    [IsNoetherianRing L] (S : Finset L) (hS : Ideal.span (S : Set L) = maximalIdeal L)
    (hcard : S.card = (maximalIdeal L).spanFinrank) (T : Finset L) (hTS : T ⊆ S) :
    IsIndepModSq (fun x : T => (x : L)) := by
  classical
  intro c hc x
  by_contra hx
  have hunit : IsUnit (c x) := notMem_maximalIdeal.mp hx
  -- `c x * x ∈ span (S.erase x) ⊔ 𝔫²`
  have hsplit : ∑ y : T, c y * (y : L) =
      c x * (x : L) + ∑ y ∈ Finset.univ.erase x, c y * (y : L) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ x)).symm
  have hrest : ∑ y ∈ Finset.univ.erase x, c y * (y : L) ∈
      Ideal.span ((S.erase (x : L) : Finset L) : Set L) := by
    refine Ideal.sum_mem _ fun y hy => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
    refine ⟨hTS y.2, fun h => ?_⟩
    exact (Finset.mem_erase.mp hy).1 (Subtype.ext h)
  have hmem : c x * (x : L) ∈
      Ideal.span ((S.erase (x : L) : Finset L) : Set L) ⊔ maximalIdeal L ^ 2 := by
    have : c x * (x : L) = (∑ y : T, c y * (y : L)) - ∑ y ∈ Finset.univ.erase x, c y * (y : L) := by
      rw [hsplit]; ring
    rw [this]
    exact sub_mem (Ideal.mem_sup_right hc) (Ideal.mem_sup_left hrest)
  have hxmem : (x : L) ∈
      Ideal.span ((S.erase (x : L) : Finset L) : Set L) ⊔ maximalIdeal L ^ 2 :=
    (Ideal.unit_mul_mem_iff_mem _ hunit).mp hmem
  have hspan := span_erase_eq_of_mem hS (hTS x.2) hxmem
  have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := L)
    (S.erase (x : L)).finite_toSet
  rw [Set.ncard_coe_finset] at hle
  rw [show Submodule.span L ((S.erase (x : L) : Finset L) : Set L) = maximalIdeal L from hspan]
    at hle
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨x, hTS x.2⟩
  have := Finset.card_erase_of_mem (hTS x.2)
  omega

end MinimalGenerators

end Hironaka
