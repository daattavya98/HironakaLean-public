/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Nakayama
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Architect
public import Hironaka.Compat.RegularLocalRing
public import Hironaka.Compat.RegularQuotient

/-!
# Compatibility layer: generators of primes with regular quotient; footnotes 39 and 41 of Ch. II

> 39. Let A be a regular local ring, M the maximal ideal of A, and N a prime ideal in A such that
> A/N is regular. Then a system of elements of N generates N if and only if their images in M/M²
> span the A/M-submodule (N + M²)/M².  (footnote 39, p. 183, attached to "Since K = Ō/m̄ and Ō are
> both regular, (x̄₁, …, x̄_r) can be extended to a regular system of parameters of Ō")

> Let us choose a regular system of parameters (z₁, …, z_r, y₁, …, y_s, x₁, …, x_t) of R such that
> P = (z₁, …, z_r)R and Q = (z₁, …, z_r, y₁, …, y_s)R, where t = dim R/Q, s + t = dim R/P, and
> r + s + t = dim R.⁴¹    ⁴¹ cf. footnote 39 of this chapter.  (Lemma 7, p. 191)

The paper states the criterion of footnote 39 without proof or citation, and obtains the system
of footnote 41 from it.  This file proves both, in the paper's order:

* classes `cotangentClass a ∈ M/M²` and the `A/M`-submodule `cotangentImage N = (N + M²)/M²`;
* footnote 39 (`span_range_eq_iff_span_range_cotangentClass_eq`);
* the system `(z, y, x)` of footnote 41 (`exists_isRegularSystemOfParameters_span_eq_of_le`),
  with the dimension count `t = dim R/Q`, `s + t = dim R/P`
  (`ringKrullDim_quotient_span_eq_card_sdiff`).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

/-! ### Classes in the cotangent space `M/M²` and the criterion of footnote 39 (p. 183) -/

section CotangentClass

variable {A : Type u} [CommRing A] [IsLocalRing A]

open Classical in
/-- The class in `M/M²` of an element of `A` (zero outside `M`). -/
noncomputable def cotangentClass (a : A) : CotangentSpace A :=
  if h : a ∈ maximalIdeal A then (maximalIdeal A).toCotangent ⟨a, h⟩ else 0

theorem cotangentClass_of_mem {a : A} (h : a ∈ maximalIdeal A) :
    cotangentClass a = (maximalIdeal A).toCotangent ⟨a, h⟩ := by
  unfold cotangentClass
  simp [h]

theorem cotangentClass_add {a b : A} (ha : a ∈ maximalIdeal A) (hb : b ∈ maximalIdeal A) :
    cotangentClass (a + b) = cotangentClass a + cotangentClass b := by
  rw [cotangentClass_of_mem ha, cotangentClass_of_mem hb, cotangentClass_of_mem (add_mem ha hb),
    ← map_add]
  rfl

theorem cotangentClass_sub {a b : A} (ha : a ∈ maximalIdeal A) (hb : b ∈ maximalIdeal A) :
    cotangentClass (a - b) = cotangentClass a - cotangentClass b := by
  rw [cotangentClass_of_mem ha, cotangentClass_of_mem hb, cotangentClass_of_mem (sub_mem ha hb),
    ← map_sub]
  rfl

theorem cotangentClass_mul (r : A) {a : A} (ha : a ∈ maximalIdeal A) :
    cotangentClass (r * a) = (IsLocalRing.residue A r) • cotangentClass a := by
  rw [cotangentClass_of_mem ha, cotangentClass_of_mem (Ideal.mul_mem_left _ r ha),
    ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul, ← map_smul]
  rfl

theorem cotangentClass_eq_zero_iff {a : A} (ha : a ∈ maximalIdeal A) :
    cotangentClass a = 0 ↔ a ∈ maximalIdeal A ^ 2 := by
  rw [cotangentClass_of_mem ha, Ideal.toCotangent_eq_zero]

theorem cotangentClass_zero : cotangentClass (0 : A) = 0 := by
  rw [cotangentClass_eq_zero_iff (zero_mem _)]
  exact zero_mem _

/-- The class of a combination `Σ fᵢ gᵢ` of elements `gᵢ ∈ M` is the combination of the classes of
the `gᵢ` with the coefficients reduced modulo `M`. -/
theorem cotangentClass_sum {ι : Type*} {T : Finset ι} (g f : ι → A)
    (hg : ∀ i ∈ T, g i ∈ maximalIdeal A) :
    cotangentClass (∑ i ∈ T, f i * g i) =
      ∑ i ∈ T, (IsLocalRing.residue A (f i)) • cotangentClass (g i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [cotangentClass_zero]
  | insert j T hj ih =>
    have hj' := hg j (Finset.mem_insert_self j T)
    have hT' : ∀ i ∈ T, g i ∈ maximalIdeal A := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      cotangentClass_add (Ideal.mul_mem_left _ _ hj')
        (sum_mem fun i hi => Ideal.mul_mem_left _ _ (hT' i hi)),
      cotangentClass_mul _ hj', ih hT']

theorem cotangentClass_mem_span_of_mem_span {s : Set A} (hs : s ⊆ maximalIdeal A) {a : A}
    (ha : a ∈ Ideal.span s) :
    cotangentClass a ∈ Submodule.span (ResidueField A) (cotangentClass '' s) := by
  have hle : Ideal.span s ≤ maximalIdeal A := Ideal.span_le.mpr hs
  induction ha using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [cotangentClass_zero]; exact zero_mem _
  | add x y hx hy ihx ihy =>
    rw [cotangentClass_add (hle hx) (hle hy)]
    exact add_mem ihx ihy
  | smul r x hx ihx =>
    rw [smul_eq_mul, cotangentClass_mul r (hle hx)]
    exact Submodule.smul_mem _ _ ihx

/-- The `A/M`-submodule `(N + M²)/M²` of `M/M²`, for an ideal `N ⊆ M`: spanned by the classes of
the elements of `N`; its elements are exactly the classes of elements of `N`
(`mem_cotangentImage_iff`). -/
noncomputable def cotangentImage (N : Ideal A) : Submodule (ResidueField A) (CotangentSpace A) :=
  Submodule.span (ResidueField A) (cotangentClass '' (N : Set A))

theorem mem_cotangentImage_iff {N : Ideal A} (hN : N ≤ maximalIdeal A) {c : CotangentSpace A} :
    c ∈ cotangentImage N ↔ ∃ n ∈ N, cotangentClass n = c := by
  constructor
  · intro hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, hn, rfl⟩ := hx
      exact ⟨n, hn, rfl⟩
    | zero => exact ⟨0, zero_mem _, cotangentClass_zero⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨n₁, hn₁, rfl⟩ := ihx
      obtain ⟨n₂, hn₂, rfl⟩ := ihy
      exact ⟨n₁ + n₂, add_mem hn₁ hn₂, cotangentClass_add (hN hn₁) (hN hn₂)⟩
    | smul c x _ ihx =>
      obtain ⟨n, hn, rfl⟩ := ihx
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
      exact ⟨r * n, Ideal.mul_mem_left _ r hn, cotangentClass_mul r (hN hn)⟩
  · rintro ⟨n, hn, rfl⟩
    exact Submodule.subset_span ⟨n, hn, rfl⟩

theorem exists_sub_mem_sq_of_cotangentClass_mem_span {g : Set A} (hg : g ⊆ maximalIdeal A)
    {a : A} (ha : a ∈ maximalIdeal A)
    (h : cotangentClass a ∈ Submodule.span (ResidueField A) (cotangentClass '' g)) :
    ∃ b ∈ Ideal.span g, a - b ∈ maximalIdeal A ^ 2 := by
  have hle : Ideal.span g ≤ maximalIdeal A := Ideal.span_le.mpr hg
  have key : ∀ v ∈ Submodule.span (ResidueField A) (cotangentClass '' g),
      ∃ b ∈ Ideal.span g, cotangentClass b = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, Ideal.subset_span hy, rfl⟩
    | zero => exact ⟨0, zero_mem _, cotangentClass_zero⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨b₁, hb₁, rfl⟩ := ihx
      obtain ⟨b₂, hb₂, rfl⟩ := ihy
      exact ⟨b₁ + b₂, add_mem hb₁ hb₂, cotangentClass_add (hle hb₁) (hle hb₂)⟩
    | smul c x _ ihx =>
      obtain ⟨b, hb, rfl⟩ := ihx
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
      exact ⟨r * b, Ideal.mul_mem_left _ r hb, cotangentClass_mul r (hle hb)⟩
  obtain ⟨b, hb, hbv⟩ := key _ h
  refine ⟨b, hb, (cotangentClass_eq_zero_iff (sub_mem ha (hle hb))).mp ?_⟩
  rw [cotangentClass_sub ha (hle hb), hbv, sub_self]

/-- Nakayama's lemma in the form used for the criterion of footnote 39: if the classes of the
elements of `g ⊆ N` span the classes of all elements of `N` in `M/M²`, and `N ∩ M² ⊆ M N`, then
`g` generates `N`. -/
theorem le_span_of_cotangentClass [IsNoetherianRing A] (N : Ideal A) (hN : N ≤ maximalIdeal A)
    {g : Set A} (hgN : g ⊆ N)
    (h1 : ∀ a ∈ N, cotangentClass a ∈ Submodule.span (ResidueField A) (cotangentClass '' g))
    (h2 : ∀ e ∈ N, e ∈ maximalIdeal A ^ 2 → e ∈ maximalIdeal A * N) :
    N ≤ Ideal.span g := by
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian N)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_
  intro a ha
  obtain ⟨b, hb, hab⟩ := exists_sub_mem_sq_of_cotangentClass_mem_span (hgN.trans hN) (hN ha)
    (h1 a ha)
  have hbN : b ∈ N := Ideal.span_le.mpr hgN hb
  have : a - b ∈ maximalIdeal A • N := h2 _ (sub_mem ha hbN) hab
  rw [show a = b + (a - b) by ring]
  exact Submodule.add_mem_sup hb this

section Minimal

variable [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- The classes in `M/M²` of the elements of a minimal system `S` of generators of `M`
span `M/M²`. -/
theorem span_cotangentClass_eq_top_of_minimal {S : Finset A}
    (hS : Ideal.span (S : Set A) = maximalIdeal A) :
    Submodule.span (ResidueField A) (cotangentClass '' (S : Set A)) = ⊤ := by
  have hSM : (S : Set A) ⊆ maximalIdeal A := hS ▸ Ideal.subset_span
  refine eq_top_iff.mpr fun v _ => ?_
  obtain ⟨⟨a, ha⟩, rfl⟩ := (maximalIdeal A).toCotangent_surjective v
  rw [← cotangentClass_of_mem ha]
  refine cotangentClass_mem_span_of_mem_span hSM ?_
  rw [hS]
  exact ha

/-- The classes in `M/M²` of the elements of a minimal system `S` of generators of `M`
(`#S = dim_k M/M²`) are linearly independent over `k = A/M`. -/
theorem linearIndepOn_cotangentClass_of_minimal {S : Finset A}
    (hS : Ideal.span (S : Set A) = maximalIdeal A)
    (hScard : S.card = (maximalIdeal A).spanFinrank) :
    LinearIndepOn (ResidueField A) cotangentClass (S : Set A) := by
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
  · rw [← Set.image_eq_range, span_cotangentClass_eq_top_of_minimal hS]
  · rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    simpa using hScard

/-- If `T` is part of a minimal system `S` of generators of `M`, then `(T) ∩ M² ⊆ M (T)`: a
combination `Σ fᵢ tᵢ ∈ M²` of the `tᵢ ∈ T` has all `fᵢ ∈ M`, since the classes of the `tᵢ` in `M/M²`
are linearly independent. -/
theorem mem_maximalIdeal_mul_span_of_mem_sq_of_minimal {S T : Finset A}
    (hS : Ideal.span (S : Set A) = maximalIdeal A)
    (hScard : S.card = (maximalIdeal A).spanFinrank) (hTS : T ⊆ S) {e : A}
    (he : e ∈ Ideal.span (T : Set A)) (he2 : e ∈ maximalIdeal A ^ 2) :
    e ∈ maximalIdeal A * Ideal.span (T : Set A) := by
  classical
  obtain ⟨f, -, rfl⟩ := Submodule.mem_span_finset.mp he
  have hTm : ∀ i ∈ T, i ∈ maximalIdeal A := fun i hi => hS ▸ Ideal.subset_span (hTS hi)
  have hind : LinearIndepOn (ResidueField A) cotangentClass (T : Set A) :=
    (linearIndepOn_cotangentClass_of_minimal hS hScard).mono (by exact_mod_cast hTS)
  have hsum : ∑ i ∈ T, (IsLocalRing.residue A (f i)) • cotangentClass i = 0 := by
    have := cotangentClass_sum (T := T) (fun i => i) f hTm
    simp only [smul_eq_mul] at he2 ⊢
    rw [← this, cotangentClass_eq_zero_iff (sum_mem fun i hi => Ideal.mul_mem_left _ _ (hTm i hi))]
    exact he2
  have hf := linearIndepOn_finset_iff.mp hind (fun i => IsLocalRing.residue A (f i)) hsum
  refine sum_mem fun i hi => ?_
  rw [smul_eq_mul]
  have : f i ∈ maximalIdeal A := (IsLocalRing.residue_eq_zero_iff _).mp (hf i hi)
  exact Ideal.mul_mem_mul this (Ideal.subset_span hi)

end Minimal

end CotangentClass

section Footnote39

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- **Footnote 39 (p. 183).** "Let A be a regular local ring, M the maximal ideal of A, and N a
prime ideal in A such that A/N is regular. Then a system of elements of N generates N if and only
if their images in M/M² span the A/M-submodule (N + M²)/M²."

Deviation from the paper (gap filled): the paper states this without proof or citation. The proof
of `⇐` uses that `N` is generated by part `T` of a minimal system `S` of generators of `M`
(`exists_finset_span_eq_prime`): the classes of `T` in `M/M²` are linearly independent, so
`N ∩ M² ⊆ M N`, and then Nakayama's lemma applies. -/
@[blueprint "fn:II.1-39"
  (statement := /-- (Footnote 39, p.~183.) Let $A$ be a regular local ring, $\mathfrak M$ the
    maximal ideal of $A$, and $N$ a prime ideal in $A$ such that $A/N$ is regular. Then a system
    of elements of $N$ generates $N$ if and only if their images in $\mathfrak M/\mathfrak M^2$
    span the $A/\mathfrak M$-submodule $(N+\mathfrak M^2)/\mathfrak M^2$. -/)
  (proof := /-- ($\Rightarrow$) is clear. ($\Leftarrow$) By \cref{lem:regular-quotient-rsop},
    $N=(T)$ for a subset $T$ of a minimal system $S$ of generators of $\mathfrak M$; the classes
    of the elements of $S$ form a basis of $\mathfrak M/\mathfrak M^2$, so a combination
    $\sum f_tt\in N\cap\mathfrak M^2$ ($t\in T$) has all $f_t\in\mathfrak M$, i.e.
    $N\cap\mathfrak M^2\subseteq\mathfrak MN$. If the classes of the given elements span the
    classes of $N$, then every element of $N$ is congruent modulo $\mathfrak M^2$, hence (as the
    difference lies in $N\cap\mathfrak M^2\subseteq\mathfrak MN$) modulo $\mathfrak MN$, to an
    element of the ideal they generate, and Nakayama's lemma gives that they generate $N$.
    \textbf{Gap filled}: the paper gives no proof. -/)
  (proofUses := ["lem:regular-quotient-rsop"])
  (latexEnv := "lemma")]
theorem span_range_eq_iff_span_range_cotangentClass_eq (N : Ideal A) [N.IsPrime]
    (hN : IsRegularLocalRing (A ⧸ N)) {ι : Type*} (x : ι → A) (hxN : ∀ i, x i ∈ N) :
    Ideal.span (Set.range x) = N ↔
      Submodule.span (ResidueField A) (Set.range fun i => cotangentClass (x i)) =
        cotangentImage N := by
  have hNM : N ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top'
  have hxN' : Set.range x ⊆ (N : Set A) := by
    rintro _ ⟨i, rfl⟩
    exact hxN i
  have himg : cotangentClass '' Set.range x = Set.range fun i => cotangentClass (x i) :=
    (Set.range_comp cotangentClass x).symm
  constructor
  · intro h
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨x i, hxN i, rfl⟩
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨n, hn, rfl⟩
      rw [← himg]
      exact cotangentClass_mem_span_of_mem_span (hxN'.trans hNM) (h ▸ hn)
  · intro h
    obtain ⟨S, T, hS, hScard, hTS, hT⟩ := exists_finset_span_eq_prime A N hN
    refine le_antisymm (Ideal.span_le.mpr hxN') ?_
    refine le_span_of_cotangentClass N hNM hxN' (fun a ha => ?_) (fun e he he2 => ?_)
    · rw [himg, h]
      exact Submodule.subset_span ⟨a, ha, rfl⟩
    · rw [← hT] at he ⊢
      exact mem_maximalIdeal_mul_span_of_mem_sq_of_minimal hS hScard hTS he he2

/-- Footnote 39 for a set `s ⊆ N` instead of a family. -/
theorem span_eq_iff_span_cotangentClass_image_eq (N : Ideal A) [N.IsPrime]
    (hN : IsRegularLocalRing (A ⧸ N)) {s : Set A} (hs : s ⊆ N) :
    Ideal.span s = N ↔
      Submodule.span (ResidueField A) (cotangentClass '' s) = cotangentImage N := by
  have := span_range_eq_iff_span_range_cotangentClass_eq N hN (ι := s) (fun a => (a : A))
    (fun a => hs a.2)
  rw [Subtype.range_coe] at this
  rwa [← Set.image_eq_range] at this

end Footnote39


/-! ### The regular system of parameters of footnote 41 (p. 191) -/

section Footnote41

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

open Classical in
/-- Let `T` be part of a minimal system `S` of generators of the maximal ideal of the regular local
ring `R`, with `R/(T)` regular.  Then `dim R/(T) = #(S ∖ T)`: the images of `S ∖ T` generate the
maximal ideal of `R/(T)`, and a smaller generating set would, together with `T`, give fewer than
`#S = dim R` generators of the maximal ideal of `R`. -/
theorem ringKrullDim_quotient_span_eq_card_sdiff {S T : Finset R}
    (hS : Ideal.span (S : Set R) = maximalIdeal R)
    (hScard : S.card = (maximalIdeal R).spanFinrank) (hTS : T ⊆ S)
    (hreg : IsRegularLocalRing (R ⧸ Ideal.span (T : Set R))) :
    ringKrullDim (R ⧸ Ideal.span (T : Set R)) = (((S \ T).card : ℕ) : WithBot ℕ∞) := by
  set I := Ideal.span (T : Set R) with hI
  have hSM : (S : Set R) ⊆ maximalIdeal R := hS ▸ Ideal.subset_span
  have hTM : (T : Set R) ⊆ maximalIdeal R := (by exact_mod_cast hTS : (T : Set R) ⊆ S).trans hSM
  set mk := Ideal.Quotient.mk I with hmk
  have hMbar : (maximalIdeal R).map mk = maximalIdeal (R ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective mk Ideal.Quotient.mk_surjective
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ I)]
  norm_cast
  -- the images of `S \ T` generate the maximal ideal of `R/I`
  have hgen : Ideal.span (((S \ T).image mk : Finset (R ⧸ I)) : Set (R ⧸ I)) =
      maximalIdeal (R ⧸ I) := by
    rw [← hMbar, ← hS, Ideal.map_span]
    apply le_antisymm
    · refine Ideal.span_mono ?_
      rw [Finset.coe_image]
      exact Set.image_mono (by simp)
    · rw [Ideal.span_le]
      rintro _ ⟨y, hy, rfl⟩
      by_cases hyT : y ∈ T
      · have : mk y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hyT)
        rw [this]
        exact zero_mem _
      · exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _
          (Finset.mem_sdiff.mpr ⟨hy, hyT⟩)))
  apply le_antisymm
  · rw [← hgen]
    calc _ ≤ (((S \ T).image mk : Finset (R ⧸ I)) : Set (R ⧸ I)).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)
      _ = ((S \ T).image mk).card := Set.ncard_coe_finset _
      _ ≤ (S \ T).card := Finset.card_image_le
  · -- lifting `spanFinrank` generators of the maximal ideal of `R/I`, together with `T`, gives
    -- generators of the maximal ideal of `R`
    obtain ⟨U, hUcard, hUspan⟩ :=
      (IsNoetherian.noetherian (maximalIdeal (R ⧸ I))).exists_span_finset_card_eq_spanFinrank
    have hUspan' : Ideal.span (U : Set (R ⧸ I)) = maximalIdeal (R ⧸ I) := hUspan
    set σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := I)) with hσdef
    have hσ : ∀ b, mk (σ b) = b := Function.surjInv_eq _
    have himage : (Ideal.span ((U.image σ : Finset R) : Set R)).map mk =
        Ideal.span (U : Set (R ⧸ I)) := by
      rw [Ideal.map_span, Finset.coe_image, Set.image_image]
      simp only [hσ, Set.image_id']
    have hM : maximalIdeal R ≤ Ideal.span ((T ∪ U.image σ : Finset R) : Set R) := by
      intro a ha
      have h1 : mk a ∈ (Ideal.span ((U.image σ : Finset R) : Set R)).map mk := by
        rw [himage, hUspan', ← hMbar]
        exact Ideal.mem_map_of_mem _ ha
      rw [Ideal.mem_quotient_iff_mem_sup] at h1
      refine (sup_le (Ideal.span_mono ?_) (Ideal.span_mono ?_) :
        Ideal.span ((U.image σ : Finset R) : Set R) ⊔ I ≤
          Ideal.span ((T ∪ U.image σ : Finset R) : Set R)) h1
      · rw [Finset.coe_union]
        exact Set.subset_union_right
      · rw [Finset.coe_union]
        exact Set.subset_union_left
    have hle : (maximalIdeal R).spanFinrank ≤ T.card + U.card := by
      calc (maximalIdeal R).spanFinrank
          ≤ (Ideal.span ((T ∪ U.image σ : Finset R) : Set R)).spanFinrank := by
            have hle' : Ideal.span ((T ∪ U.image σ : Finset R) : Set R) ≤ maximalIdeal R :=
              Ideal.span_le.mpr (by
                rw [Finset.coe_union]
                refine Set.union_subset hTM ?_
                intro y hy
                obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
                have : mk (σ b) ∈ (maximalIdeal R).map mk := by
                  rw [hMbar, hσ, ← hUspan']
                  exact Ideal.subset_span hb
                rw [Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr
                  (Ideal.span_le.mpr hTM)] at this
                exact this)
            rw [le_antisymm hM hle']
        _ ≤ ((T ∪ U.image σ : Finset R) : Set R).ncard :=
            Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)
        _ = (T ∪ U.image σ).card := Set.ncard_coe_finset _
        _ ≤ T.card + (U.image σ).card := Finset.card_union_le _ _
        _ ≤ T.card + U.card := Nat.add_le_add_left Finset.card_image_le _
    have hsd : (S \ T).card = S.card - T.card := Finset.card_sdiff_of_subset hTS
    have hTc : T.card ≤ S.card := Finset.card_le_card hTS
    omega

open Classical in
/-- **The system of parameters of footnote 41 (p. 191).**  "Let us choose a regular system of
parameters `(z₁, …, z_r, y₁, …, y_s, x₁, …, x_t)` of `R` such that `P = (z₁, …, z_r)R` and
`Q = (z₁, …, z_r, y₁, …, y_s)R`, where `t = dim R/Q`, `s + t = dim R/P`, and `r + s + t = dim R`"
(footnote 41: "cf. footnote 39").  For primes `P ⊆ Q` of the regular local ring `R` with `R/P` and
`R/Q` regular, there is such a system, as a disjoint union `Z ∪ Y ∪ X` of finite sets
(`r + s + t = dim R` is the cardinality of the regular system of parameters).

Proof as in the paper: choose `z` in `P` whose classes form a basis of `(P + M²)/M²`, then `y` in
`Q` such that the classes of `(z, y)` form a basis of `(Q + M²)/M²`, then `x` such that the classes
of `(z, y, x)` form a basis of `M/M²`; by Nakayama `(z, y, x)` is a regular system of
parameters, and by footnote 39 (`span_range_eq_iff_span_range_cotangentClass_eq`) `(z)` generates
`P` and `(z, y)` generates `Q`.

Deviation from the paper (gap filled): the dimension count `t = dim R/Q`, `s + t = dim R/P` is not
argued in the paper (`ringKrullDim_quotient_span_eq_card_sdiff`). -/
@[blueprint "fn:II.2-41"
  (statement := /-- (Footnote 41, p.~191, ``cf.\ footnote 39''.) Let $R$ be a regular local ring
    and $P\subseteq Q$ prime ideals such that $R/P$ and $R/Q$ are regular. Then there is a
    regular system of parameters $(z_1,\dots,z_r,y_1,\dots,y_s,x_1,\dots,x_t)$ of $R$ such that
    $P=(z_1,\dots,z_r)R$ and $Q=(z_1,\dots,z_r,y_1,\dots,y_s)R$, where $t=\dim R/Q$,
    $s+t=\dim R/P$ and $r+s+t=\dim R$. -/)
  (proof := /-- Choose $z_1,\dots,z_r\in P$ whose classes form a basis of
    $(P+\mathfrak M^2)/\mathfrak M^2$, then $y_1,\dots,y_s\in Q$ such that the classes of $(z,y)$
    form a basis of $(Q+\mathfrak M^2)/\mathfrak M^2$, then $x_1,\dots,x_t$ such that the classes
    of $(z,y,x)$ form a basis of $\mathfrak M/\mathfrak M^2$. By Nakayama's lemma $(z,y,x)$
    generates $\mathfrak M$, and $r+s+t=\dim_k\mathfrak M/\mathfrak M^2=\dim R$. By footnote~39
    (\cref{fn:II.1-39}) $(z)$ generates $P$ and $(z,y)$ generates $Q$. Finally
    $\dim R/Q=t$ and $\dim R/P=s+t$ since the images of $x$ (resp. $y,x$) generate the maximal
    ideal of the regular local ring $R/Q$ (resp. $R/P$) and fewer generators would give fewer than
    $\dim R$ generators of $\mathfrak M$. \textbf{Gap filled}: the dimension count is not
    argued in the paper. -/)
  (proofUses := ["fn:II.1-39"])
  (latexEnv := "lemma")]
theorem exists_isRegularSystemOfParameters_span_eq_of_le (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hPQ : P ≤ Q) (hP : IsRegularLocalRing (R ⧸ P)) (hQ : IsRegularLocalRing (R ⧸ Q)) :
    ∃ Z Y X : Finset R, Disjoint Z Y ∧ Disjoint (Z ∪ Y) X ∧
      IsRegularSystemOfParameters R (Z ∪ Y ∪ X) ∧
      Ideal.span (Z : Set R) = P ∧ Ideal.span ((Z ∪ Y : Finset R) : Set R) = Q ∧
      (X.card : WithBot ℕ∞) = ringKrullDim (R ⧸ Q) ∧
      ((Y ∪ X).card : WithBot ℕ∞) = ringKrullDim (R ⧸ P) := by
  have hPM : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top'
  have hQM : Q ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top'
  -- bases `B₁ ⊆ B₂ ⊆ B₃` of `(P + M²)/M² ⊆ (Q + M²)/M² ⊆ M/M²`, each extending the previous one
  obtain ⟨B₁, hB₁t, -, hB₁span, hB₁ind⟩ :=
    exists_linearIndepOn_id_extension (K := ResidueField R)
      (linearIndepOn_empty (ResidueField R) id)
      (Set.empty_subset (cotangentClass '' (P : Set R)))
  have hB₁Q : B₁ ⊆ cotangentClass '' (Q : Set R) := hB₁t.trans (Set.image_mono hPQ)
  obtain ⟨B₂, hB₂t, hB₁B₂, hB₂span, hB₂ind⟩ := exists_linearIndepOn_id_extension hB₁ind hB₁Q
  obtain ⟨B₃, -, hB₂B₃, hB₃span, hB₃ind⟩ := exists_linearIndepOn_id_extension hB₂ind
    (Set.subset_univ B₂)
  have hB₁V : Submodule.span (ResidueField R) B₁ = cotangentImage P :=
    le_antisymm (Submodule.span_le.mpr (hB₁t.trans Submodule.subset_span))
      (Submodule.span_le.mpr hB₁span)
  have hB₂V : Submodule.span (ResidueField R) B₂ = cotangentImage Q :=
    le_antisymm (Submodule.span_le.mpr (hB₂t.trans Submodule.subset_span))
      (Submodule.span_le.mpr hB₂span)
  have hB₃top : Submodule.span (ResidueField R) B₃ = ⊤ :=
    eq_top_iff.mpr fun v _ => hB₃span (Set.mem_univ v)
  have hB₃fin : B₃.Finite := by
    have := LinearIndependent.finite_of_isNoetherian hB₃ind
    exact Set.toFinite B₃
  have hB₂B₃' : B₂ ⊆ B₃ := hB₂B₃
  have hB₂fin : B₂.Finite := hB₃fin.subset hB₂B₃'
  have hB₁fin : B₁.Finite := hB₂fin.subset hB₁B₂
  -- lifts of the basis vectors, in `P` for `B₁`, in `Q` for `B₂`, in `M` for `B₃`
  have hlift₃ : ∀ b : CotangentSpace R, ∃ a, a ∈ maximalIdeal R ∧ cotangentClass a = b := by
    intro b
    obtain ⟨⟨a, ha⟩, rfl⟩ := (maximalIdeal R).toCotangent_surjective b
    exact ⟨a, ha, cotangentClass_of_mem ha⟩
  have hlift₂ : ∀ b ∈ B₂, ∃ a, a ∈ Q ∧ cotangentClass a = b := fun b hb => hB₂t hb
  have hlift₁ : ∀ b ∈ B₁, ∃ a, a ∈ P ∧ cotangentClass a = b := fun b hb => hB₁t hb
  let σ : CotangentSpace R → R := fun b =>
    if h₁ : b ∈ B₁ then (hlift₁ b h₁).choose
    else if h₂ : b ∈ B₂ then (hlift₂ b h₂).choose
    else (hlift₃ b).choose
  have hσcls : ∀ b, cotangentClass (σ b) = b := by
    intro b
    by_cases h₁ : b ∈ B₁
    · simp only [σ, h₁, ↓reduceDIte]
      exact (hlift₁ b h₁).choose_spec.2
    · by_cases h₂ : b ∈ B₂
      · simp only [σ, h₁, h₂, ↓reduceDIte]
        exact (hlift₂ b h₂).choose_spec.2
      · simp only [σ, h₁, h₂, ↓reduceDIte]
        exact (hlift₃ b).choose_spec.2
  have hσP : ∀ b ∈ B₁, σ b ∈ P := by
    intro b h₁
    simp only [σ, h₁, ↓reduceDIte]
    exact (hlift₁ b h₁).choose_spec.1
  have hσQ : ∀ b ∈ B₂, σ b ∈ Q := by
    intro b h₂
    by_cases h₁ : b ∈ B₁
    · exact hPQ (hσP b h₁)
    · simp only [σ, h₁, h₂, ↓reduceDIte]
      exact (hlift₂ b h₂).choose_spec.1
  have hσM : ∀ b, σ b ∈ maximalIdeal R := by
    intro b
    by_cases h₁ : b ∈ B₁
    · exact hPM (hσP b h₁)
    · by_cases h₂ : b ∈ B₂
      · exact hQM (hσQ b h₂)
      · simp only [σ, h₁, h₂, ↓reduceDIte]
        exact (hlift₃ b).choose_spec.1
  have hinj : Function.Injective σ := Function.LeftInverse.injective hσcls
  have himg : ∀ F : Finset (CotangentSpace R),
      cotangentClass '' ((F.image σ : Finset R) : Set R) = (F : Set (CotangentSpace R)) := by
    intro F
    rw [Finset.coe_image, Set.image_image]
    simp only [hσcls, Set.image_id']
  set F₁ := hB₁fin.toFinset with hF₁
  set F₂ := hB₂fin.toFinset with hF₂
  set F₃ := hB₃fin.toFinset with hF₃
  have hF₁B : (F₁ : Set (CotangentSpace R)) = B₁ := hB₁fin.coe_toFinset
  have hF₂B : (F₂ : Set (CotangentSpace R)) = B₂ := hB₂fin.coe_toFinset
  have hF₃B : (F₃ : Set (CotangentSpace R)) = B₃ := hB₃fin.coe_toFinset
  have hF₁₂ : F₁ ⊆ F₂ := by
    rw [← Finset.coe_subset, hF₁B, hF₂B]
    exact hB₁B₂
  have hF₂₃ : F₂ ⊆ F₃ := by
    rw [← Finset.coe_subset, hF₂B, hF₃B]
    exact hB₂B₃'
  have hZY : F₁.image σ ∪ (F₂ \ F₁).image σ = F₂.image σ := by
    rw [← Finset.image_union, Finset.union_sdiff_of_subset hF₁₂]
  have hZYX : F₂.image σ ∪ (F₃ \ F₂).image σ = F₃.image σ := by
    rw [← Finset.image_union, Finset.union_sdiff_of_subset hF₂₃]
  -- `(z, y, x)` generates `M` and has `dim R` elements: a regular system of parameters
  have hSspan : Ideal.span ((F₃.image σ : Finset R) : Set R) = maximalIdeal R := by
    refine le_antisymm (Ideal.span_le.mpr ?_) ?_
    · intro y hy
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      exact hσM b
    · refine le_span_of_cotangentClass (maximalIdeal R) le_rfl ?_ (fun a _ => ?_)
        (fun e he he2 => by rwa [← pow_two])
      · intro y hy
        obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
        exact hσM b
      · rw [himg, hF₃B, hB₃top]
        exact Submodule.mem_top
  have hScard : (F₃.image σ).card = (maximalIdeal R).spanFinrank := by
    rw [Finset.card_image_of_injective _ hinj,
      IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, ← finrank_top (ResidueField R)
        (CotangentSpace R), ← hB₃top, ← hF₃B, finrank_span_finset_eq_card (hF₃B ▸ hB₃ind)]
  -- `(z)` generates `P`, `(z, y)` generates `Q`: footnote 39
  have hZP : Ideal.span ((F₁.image σ : Finset R) : Set R) = P := by
    refine (span_eq_iff_span_cotangentClass_image_eq P hP ?_).mpr ?_
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      exact hσP b (hF₁B ▸ Finset.mem_coe.mpr hb)
    · rw [himg, hF₁B]
      exact hB₁V
  have hZYQ : Ideal.span ((F₂.image σ : Finset R) : Set R) = Q := by
    refine (span_eq_iff_span_cotangentClass_image_eq Q hQ ?_).mpr ?_
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      exact hσQ b (hF₂B ▸ Finset.mem_coe.mpr hb)
    · rw [himg, hF₂B]
      exact hB₂V
  refine ⟨F₁.image σ, (F₂ \ F₁).image σ, (F₃ \ F₂).image σ, ?_, ?_, ?_, hZP, ?_, ?_, ?_⟩
  · exact (Finset.disjoint_image hinj).mpr Finset.disjoint_sdiff
  · rw [hZY]
    exact (Finset.disjoint_image hinj).mpr Finset.disjoint_sdiff
  · rw [hZY, hZYX]
    refine ⟨hSspan, ?_⟩
    rw [hScard]
    exact IsRegularLocalRing.spanFinrank_maximalIdeal
  · rw [hZY]
    exact hZYQ
  · -- `t = dim R/Q`
    have hreg : IsRegularLocalRing (R ⧸ Ideal.span ((F₂.image σ : Finset R) : Set R)) := by
      rw [hZYQ]
      exact hQ
    have := ringKrullDim_quotient_span_eq_card_sdiff hSspan hScard
      (Finset.image_subset_image hF₂₃) hreg
    rw [hZYQ] at this
    rw [this, ← Finset.image_sdiff _ _ hinj, Finset.card_image_of_injective _ hinj]
  · -- `s + t = dim R/P`
    have hreg : IsRegularLocalRing (R ⧸ Ideal.span ((F₁.image σ : Finset R) : Set R)) := by
      rw [hZP]
      exact hP
    have := ringKrullDim_quotient_span_eq_card_sdiff hSspan hScard
      (Finset.image_subset_image (hF₁₂.trans hF₂₃)) hreg
    rw [hZP] at this
    rw [this, ← Finset.image_sdiff _ _ hinj, ← Finset.image_union,
      Finset.card_image_of_injective _ hinj, Finset.card_image_of_injective _ hinj]
    congr 2
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    have h12 := @hF₁₂ x
    have h23 := @hF₂₃ x
    tauto


open Classical in
/-- **"`(ȳ₁, …, ȳ_s, x̄₁, …, x̄_t)` is a regular system of parameters of `R̄`"** (Lemma 7, p. 192:
"If `ȳ_i` denotes the residue class of `y_i` in `R̄ = R/P` and `x̄_j` that of `x_j`, then
`(ȳ₁, …, ȳ_s, x̄₁, …, x̄_t)` is a regular system of parameters of `R̄`"): the classes in `R/P` of the
system `Y ∪ X` of footnote 41 (`P = (Z)`, `#(Y ∪ X) = dim R/P`) are distinct and form a regular
system of parameters of `R/P`.  Their number is `dim R/P` (the dimension count of footnote 41,
`exists_isRegularSystemOfParameters_span_eq_of_le`), and they generate the maximal ideal of `R/P`
because `(Z ∪ Y ∪ X)` generates that of `R` and `Z` goes to `0`.

Deviation from the paper (gap filled): the paper asserts this without argument (p. 192). -/
theorem isRegularSystemOfParameters_image_quotient {P : Ideal R} [P.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] {Z Y X : Finset R}
    (hS : IsRegularSystemOfParameters R (Z ∪ Y ∪ X)) (hZ : Ideal.span (Z : Set R) = P)
    (hcard : ((Y ∪ X).card : WithBot ℕ∞) = ringKrullDim (R ⧸ P)) :
    Set.InjOn (Ideal.Quotient.mk P) ↑(Y ∪ X) ∧
      IsRegularSystemOfParameters (R ⧸ P) ((Y ∪ X).image (Ideal.Quotient.mk P)) := by
  classical
  set mk := Ideal.Quotient.mk P with hmk
  have hMbar : (maximalIdeal R).map mk = maximalIdeal (R ⧸ P) :=
    IsLocalRing.map_maximalIdeal_of_surjective mk Ideal.Quotient.mk_surjective
  have hspan : Ideal.span (((Y ∪ X).image mk : Finset (R ⧸ P)) : Set (R ⧸ P)) =
      maximalIdeal (R ⧸ P) := by
    rw [← hMbar, ← hS.1, Ideal.map_span]
    apply le_antisymm
    · refine Ideal.span_mono ?_
      rw [Finset.coe_image]
      refine Set.image_mono ?_
      intro a ha
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha ⊢
      tauto
    · rw [Ideal.span_le]
      rintro _ ⟨a, ha, rfl⟩
      by_cases haZ : a ∈ Z
      · have : mk a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hZ ▸ Ideal.subset_span haZ)
        rw [this]
        exact zero_mem _
      · refine Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ?_))
        simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha
        simp only [Finset.mem_union]
        tauto
  have hcard' : (Y ∪ X).card = (maximalIdeal (R ⧸ P)).spanFinrank := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal] at hcard
    exact_mod_cast hcard
  have hle : (maximalIdeal (R ⧸ P)).spanFinrank ≤ ((Y ∪ X).image mk).card := by
    calc (maximalIdeal (R ⧸ P)).spanFinrank
        = (Ideal.span (((Y ∪ X).image mk : Finset (R ⧸ P)) : Set (R ⧸ P))).spanFinrank := by
          rw [hspan]
      _ ≤ (((Y ∪ X).image mk : Finset (R ⧸ P)) : Set (R ⧸ P)).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)
      _ = ((Y ∪ X).image mk).card := Set.ncard_coe_finset _
  have heq : ((Y ∪ X).image mk).card = (Y ∪ X).card :=
    le_antisymm Finset.card_image_le (hcard' ▸ hle)
  refine ⟨Finset.card_image_iff.mp heq, hspan, ?_⟩
  rw [heq, hcard']
  exact IsRegularLocalRing.spanFinrank_maximalIdeal

end Footnote41

end Hironaka
