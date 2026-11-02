/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Compat.RegularLocalRing
public import Hironaka.Compat.HironakaBaseStability
public import Hironaka.Compat.ClassBLocalization
public import Hironaka.Statements

/-!
# Ch. 0 §1 and the opening of Ch. I: the class 𝔅 of base rings, algebraic schemes, subschemes

Hironaka fixes "once for always" (Ch. I, p. 161) the class 𝔅 of local rings S such that
  (i)  S is a noetherian local ring with residue field of characteristic zero; and
  (ii) if Ŝ denotes the completion of S, then for every S-algebra of finite type A, the
       singular locus of Spec(A ⊗_S Ŝ) is the preimage of that of Spec(A).
An *algebraic scheme* is a scheme admitting a morphism of finite type to Spec(S), S ∈ 𝔅.
Subschemes are closed subschemes, identified with coherent sheaves of ideals (Ch. 0 §2, p. 129).
"Simple" is in the absolute sense of Grothendieck (footnote 29): local rings regular.

Conventions used throughout the formalization:
* `Subscheme X := X.IdealSheafData`.  Containment of subschemes is *reverse* inclusion of
  ideal sheaves; the union E ∪ F is the subscheme defined by the intersection of the ideal
  sheaves and E ∩ F by their sum (Def. 3, p. 165).
* The empty subscheme is the ideal sheaf ⊤ (= O_X); X itself is ⊥.
* Dimensions follow p. 163: `dim_x X` is the Krull dimension of `O_{X,x}` and `dim X` is the
  supremum of the `dim_x X`, in `WithBot ℕ∞`; the empty scheme has dimension ⊥, which plays
  the role of Hironaka's "dim ∅ = -1".  Codimensions likewise follow p. 163 (heights of the
  ideals of the subscheme in the local rings).

* `IsRegularLocalRing` is Mathlib's (see `Hironaka/Compat/RegularLocalRing.lean`); it bundles
  `IsLocalRing` and `IsNoetherianRing`, so e.g. `IsRegularLocalRing (O_{X,x} ⧸ I)` needs no
  separate local-ring instance on the quotient.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing

noncomputable section

universe u

namespace Hironaka

/-! ### The class 𝔅 of base rings (Ch. I, p. 161) -/




/-- (iii), p. 161: for `S ∈ 𝔅` and `A` of finite type over `S`, the singular locus of
`Spec A` is closed.  Hironaka: reduce to `S` complete by (ii) and use Nagata's jacobian
criterion (footnote 30).  Cited leaf: Nagata [14], [15] §46, and Nagata, *On the
closedness of singular loci*, Publ. IHES 2 (1959). -/
@[blueprint "prop:class-A-iii"
  (statement := /-- For $S\in\mathfrak B$ and $A$ an $S$-algebra of finite type, the singular
    locus of $\operatorname{Spec}A$ is Zariski closed. -/)
  (proof := /-- Cited: Nagata's jacobian criterion after reduction to $S$ complete.
    (Hironaka, footnote 30, p. 161.) -/)
  (latexEnv := "proposition")]
theorem IsHironakaBase.isClosed_singularLocus [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] :
    ∀ (S : Type u) [CommRing S] [IsLocalRing S]
    [IsHironakaBase S] (A : Type u) [CommRing A] [Algebra S A] [Algebra.FiniteType S A],
    IsClosed (regularLocus A)ᶜ :=
  @Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.isClosed_singularLocus _

/-- A noetherian local ring `S` with residue field of characteristic zero that is complete for
its maximal ideal belongs to 𝔅: the canonical map `S → Ŝ` is bijective, so `A ⊗_S Ŝ ≅ A` for
every `S`-algebra `A`, and condition (ii) of p. 161 holds trivially (the singular locus of
`Spec (A ⊗_S Ŝ)` is the preimage of that of `Spec A` because the canonical morphism is an
isomorphism).  This is the case "in which `S` is complete" of footnote 31 ("Reduce the proof to
the case in which S is complete, and then apply the jacobian criterion"), where, for the
properties (a) and (b), the jacobian criterion is not needed.

Deviation from the paper (gap filled): this lemma is not in the paper; it is the common core of
the proofs of (a) and (b), which p. 161 asserts ("one can prove") without proof. -/
@[blueprint "lem:class-A-complete"
  (statement := /-- Let $S$ be a noetherian local ring with residue field of characteristic
    zero which is complete for its maximal ideal. Then $S\in\mathfrak B$.
    \textbf{Deviation from the paper (gap filled).} Not stated in the paper; it is the common
    core of the proofs of (a) and (b) of p.~161. -/)
  (proof := /-- Since $S$ is $\mathfrak m_S$-adically complete, the canonical map
    $S\to\hat S$ is bijective, hence so is $A\to A\otimes_S\hat S$ for every $S$-algebra $A$
    (it is the base change of an isomorphism). A ring isomorphism identifies the regular loci
    of the two spectra (the local rings at corresponding primes are isomorphic), which is (ii).
    \textbf{Deviation from the paper (gap filled).} The paper does not state this lemma. Its
    footnote~31 reduces (a)--(c) to the case $S$ complete and then invokes the jacobian
    criterion; for (a) and (b) the reduction is the statement here and the jacobian criterion is
    not needed. -/)
  (latexEnv := "lemma")]
theorem IsHironakaBase.of_isAdicComplete (S : Type u) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [CharZero (ResidueField S)] [IsAdicComplete (maximalIdeal S) S] :
    IsHironakaBase S := by
  have hb : Function.Bijective (algebraMap S (AdicCompletion (maximalIdeal S) S)) :=
    AdicCompletion.of_bijective (maximalIdeal S) S
  exact { charZero_residueField := inferInstance
          completion_singularLocus := fun A _ _ _ q =>
            mem_regularLocus_tensor_iff_of_bijective hb q }

/-- (a) of p. 161: every field of characteristic zero belongs to 𝔅.

Deviation from the paper (gap filled): p. 161 says "Moreover, one can prove that the class 𝔅
has the following properties: (a) Every field of characteristic zero belongs to 𝔅" and gives no
proof (footnote 31, on (c): "Reduce the proof to the case in which S is complete, and then
apply the jacobian criterion").  A field `k` is complete for its maximal ideal `(0)`, so
`IsHironakaBase.of_isAdicComplete` applies; its residue field is `k` itself. -/
@[blueprint "prop:class-A-a"
  (statement := /-- Every field of characteristic zero belongs to $\mathfrak B$.
    (p.~161, (a).) -/)
  (proof := /-- The maximal ideal of a field $k$ is $(0)$, and $k$ is complete for it, so
    $k\to\hat k$ is bijective, and \cref{lem:class-A-complete} applies (the residue field is
    $k$ itself, of characteristic zero).
    \textbf{Deviation from the paper (gap filled).} The paper says ``one can prove'' (a)
    without proof. -/)
  (proofUses := ["lem:class-A-complete"])
  (latexEnv := "proposition")]
theorem IsHironakaBase.of_field (k : Type u) [Field k] [CharZero k] : IsHironakaBase k := by
  have : CharZero (ResidueField k) :=
    charZero_of_injective_ringHom (f := algebraMap k (ResidueField k)) (RingHom.injective _)
  have := isAdicComplete_maximalIdeal_of_field k
  exact IsHironakaBase.of_isAdicComplete k

/-- (b) of p. 161: the completion `Ŝ` of any `S ∈ 𝔅` belongs to 𝔅.

Deviation from the paper (gap filled): p. 161 says "one can prove" (b) ("the completion of any
S ∈ 𝔅 belongs to 𝔅") without proof.  `Ŝ` is noetherian and local with the residue field of
`S`, and is complete for its maximal ideal `m_S Ŝ` (Mathlib and
`Compat/AdicCompletionRegular`), so `IsHironakaBase.of_isAdicComplete` applies. -/
@[blueprint "prop:class-A-b"
  (statement := /-- The completion of any $S\in\mathfrak B$ belongs to $\mathfrak B$.
    (p.~161, (b).) -/)
  (proof := /-- The completion $\hat S$ is a noetherian local ring with maximal ideal
    $\mathfrak m_S\hat S$ and the same residue field as $S$ (so of characteristic zero), and it
    is complete for $\mathfrak m_{\hat S}=\mathfrak m_S\hat S$. Apply
    \cref{lem:class-A-complete}.
    \textbf{Deviation from the paper (gap filled).} The paper says ``one can prove'' (b)
    without proof. -/)
  (proofUses := ["lem:class-A-complete"])
  (latexEnv := "proposition")]
theorem IsHironakaBase.adicCompletion_maximalIdeal (S : Type u) [CommRing S] [IsLocalRing S]
    [IsHironakaBase S] : IsHironakaBase (AdicCompletion (maximalIdeal S) S) := by
  have : IsNoetherianRing (AdicCompletion (maximalIdeal S) S) :=
    isNoetherianRing_adicCompletion_of_isNoetherianRing _
  have : CharZero (ResidueField (AdicCompletion (maximalIdeal S) S)) :=
    charZero_of_injective_ringHom
      (f := ResidueField.map (algebraMap S (AdicCompletion (maximalIdeal S) S)))
      (RingHom.injective _)
  exact IsHironakaBase.of_isAdicComplete _

/-- (c) of p. 161: every local ring of a finite-type algebra `A` over `S ∈ 𝔅` belongs to 𝔅.
(Footnote 31: reduce to `S` complete and apply the jacobian criterion.)

Deviation from the paper (gap filled): p. 161 says "one can prove" and footnote 31 only sketches
the proof ("Reduce the proof to the case in which S is complete, and then apply the jacobian
criterion"; the jacobian criterion itself is cited in footnote 30, the property (c) is not).
The proof is in `Hironaka/Compat/ClassBLocalization.lean`, stated without the class: condition (i)
for `A_p` (`isNoetherianRing_localization_atPrime_of_finiteType`,
`charZero_residueField_localization_atPrime`) and condition (ii)
(`hasCompletionRegularLocus_localization_atPrime`, the reduction to the complete case by (ii) for
`S`, and `hasCompletionRegularLocus_localization_atPrime_of_isAdicComplete`, the jacobian
criterion).  Cited inputs: the jacobian criterion (`lem:jacobian-criterion`), Cohen's theorem in
the form of footnote 30 (`lem:cohen-power-series-image`), and the theory of local rings through
footnote 3 and footnote 9 (`lem:regular-descent-flat-local`, `lem:completion-flat-local`,
`lem:regular-localization-serre`). -/
@[blueprint "prop:class-A-c"
  (statement := /-- If $A$ is an algebra of finite type over $S\in\mathfrak B$, then every local
    ring of $\operatorname{Spec}A$ belongs to $\mathfrak B$. (p.~161, (c).) -/)
  (proof := /-- Condition (i) for $A_{\mathfrak p}$ is Hilbert's basis theorem and the fact that
    every nonzero integer is a unit in $S$ (the residue field has characteristic zero), hence in
    $A_{\mathfrak p}$. Condition (ii) is \cref{lem:class-A-c-reduction}. Footnote~31: ``Reduce the
    proof to the case in which S is complete, and then apply the jacobian criterion.''
    \textbf{Deviation from the paper (gap filled).} The paper says ``one can prove'' (c) and only
    sketches the proof. -/)
  (proofUses := ["lem:class-A-c-reduction"])
  (latexEnv := "proposition")]
theorem IsHironakaBase.localization_atPrime_of_finiteType [Hironaka.Cited.ExistsFlatIsLocalHomAdicCompletionOfFlat.{u}] [Hironaka.Cited.ExistsSurjectiveMvPowerSeriesOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationIffRankJacobianEqHeight.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsRegularLocalRingOfFlatOfIsRegularLocalRing.{u}] (S : Type u) [CommRing S]
    [IsLocalRing S] [IsHironakaBase S] (A : Type u) [CommRing A] [Algebra S A]
    [Algebra.FiniteType S A] (p : PrimeSpectrum A) :
    IsHironakaBase (Localization.AtPrime p.asIdeal) := by
  have : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    isNoetherianRing_localization_atPrime_of_finiteType S A p
  have : CharZero (ResidueField (Localization.AtPrime p.asIdeal)) :=
    charZero_residueField_localization_atPrime S A p
  exact { charZero_residueField := inferInstance
          completion_singularLocus :=
            hasCompletionRegularLocus_localization_atPrime S
              (fun A _ _ _ q => IsHironakaBase.completion_singularLocus A q) A p }

/-- (a), (b), (c) of p. 161: fields of characteristic zero belong to 𝔅; 𝔅 is stable under
completion; and every local ring of a finite-type algebra over `S ∈ 𝔅` is in 𝔅.
(Footnote 31: reduce to `S` complete and apply the jacobian criterion.)

Asserted by the paper without proof or citation: p. 161 says "one can prove" and footnote 31
only sketches the proof ("Reduce the proof to the case in which S is complete, and then apply
the jacobian criterion"; the jacobian criterion itself is cited in footnote 30, the properties
(a)–(c) are not).  Deviation from the paper (gap filled): split into the three
properties `IsHironakaBase.of_field` (a), `IsHironakaBase.adicCompletion_maximalIdeal` (b) and
`IsHironakaBase.localization_atPrime_of_finiteType` (c), all proved along footnote 31; the only
hypotheses are five results the paper cites (Serre, footnote 9; Cohen and the jacobian
criterion, footnote 30; flat descent of regularity and flatness of completions, the theory of
local rings of footnote 3). -/
@[blueprint "prop:class-A-abc"
  (statement := /-- (a) Every field of characteristic zero belongs to $\mathfrak B$;
    (b) the completion of any $S\in\mathfrak B$ belongs to $\mathfrak B$;
    (c) if $A$ is an algebra of finite type over $S\in\mathfrak B$, then every local ring of
    $\operatorname{Spec}A$ belongs to $\mathfrak B$. -/)
  (proof := /-- The conjunction of \cref{prop:class-A-a,prop:class-A-b,prop:class-A-c}. The
    paper says ``one can prove'' these properties and only sketches the proof in footnote~31
    (``Reduce the proof to the case in which S is complete, and then apply the jacobian
    criterion''); see the nodes (a), (b), (c) for the proofs. -/)
  (proofUses := ["prop:class-A-a", "prop:class-A-b", "prop:class-A-c"])
  (latexEnv := "proposition")]
theorem IsHironakaBase.stability [Hironaka.Cited.ExistsFlatIsLocalHomAdicCompletionOfFlat.{u}] [Hironaka.Cited.ExistsSurjectiveMvPowerSeriesOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationIffRankJacobianEqHeight.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsRegularLocalRingOfFlatOfIsRegularLocalRing.{u}] :
    (∀ (k : Type u) [Field k] [CharZero k], IsHironakaBase k) ∧
    (∀ (S : Type u) [CommRing S] [IsLocalRing S] [IsHironakaBase S],
      IsHironakaBase (AdicCompletion (maximalIdeal S) S)) ∧
    (∀ (S : Type u) [CommRing S] [IsLocalRing S] [IsHironakaBase S]
      (A : Type u) [CommRing A] [Algebra S A] [Algebra.FiniteType S A] (p : PrimeSpectrum A),
      IsHironakaBase (Localization.AtPrime p.asIdeal)) :=
  ⟨fun k _ _ => IsHironakaBase.of_field k,
    fun S _ _ _ => IsHironakaBase.adicCompletion_maximalIdeal S,
    fun S _ _ _ A _ _ _ p => IsHironakaBase.localization_atPrime_of_finiteType S A p⟩

/-! ### Algebraic schemes (Ch. I, p. 162) -/


end Hironaka

/-! ### Points, simple points, dimension

These live in the `AlgebraicGeometry.Scheme` namespace so that dot notation `X.IsNonsingular`,
`X.dim` works for `X : Scheme`. -/

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})





/-- The dimension of p. 163 is bounded below by the Krull dimension of the underlying
topological space.  (A chain of irreducible closed subsets of `X` ending at the closure of
`x` is a chain of generizations of `x`, hence of primes of `O_{X,x}`, by
`Scheme.range_fromSpecStalk`.)  Hironaka uses the two notions interchangeably. -/
@[blueprint "lem:I.0-dimension-topological"
  (statement := /-- For a scheme $X$, the Krull dimension of the underlying topological space
    of $X$ equals $\sup_x\dim\mathcal O_{X,x}$. -/)
  (proof := /-- Chains of irreducible closed subsets containing $\overline{\{x\}}$
    correspond to chains of generizations of $x$, i.e.\ to chains of prime ideals of
    $\mathcal O_{X,x}$. -/)
  (latexEnv := "lemma")]
theorem topologicalKrullDim_le_dim : topologicalKrullDim X ≤ X.dim := by
  -- Irreducible closed subsets of the sober space `X` are the points of `X` ordered by
  -- specialization (`y ≤ x ↔ x ⤳ y`), so `topologicalKrullDim X = ⨆ x, coheight x`.
  let _ : PartialOrder X := specializationOrder X
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x => le_trans ?_ (le_iSup (fun x => X.dimAt x) x)
  -- `coheight x` is the Krull dimension of the poset `Set.Ici x` of generizations of `x`.
  rw [Order.coheight_eq_krullDim_Ici]
  show Order.krullDim (Set.Ici x) ≤ Order.krullDim (PrimeSpectrum (X.presheaf.stalk x))
  rw [← Order.krullDim_orderDual (α := PrimeSpectrum (X.presheaf.stalk x))]
  -- `Spec 𝒪_{X,x} → X` is an embedding onto the generizations of `x`
  -- (`Scheme.range_fromSpecStalk`), reversing the order.
  have hrange := Scheme.range_fromSpecStalk (X := X) (x := x)
  have hmem : ∀ p : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x p ∈ Set.Ici x := by
    intro p
    have : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := Set.mem_range_self p
    rw [hrange] at this
    exact this
  refine Order.krullDim_le_of_strictComono_and_surj
    (fun p : (PrimeSpectrum (X.presheaf.stalk x))ᵒᵈ =>
      (⟨X.fromSpecStalk x (OrderDual.ofDual p), hmem _⟩ : Set.Ici x)) ?_ ?_
  · intro a b hab
    rw [Subtype.mk_lt_mk] at hab
    obtain ⟨h1, h2⟩ := hab
    change X.fromSpecStalk x (OrderDual.ofDual b) ⤳ X.fromSpecStalk x (OrderDual.ofDual a) at h1
    change ¬ X.fromSpecStalk x (OrderDual.ofDual a) ⤳ X.fromSpecStalk x (OrderDual.ofDual b) at h2
    rw [(X.fromSpecStalk x).isEmbedding.isInducing.specializes_iff] at h1 h2
    have h1' : (OrderDual.ofDual b : PrimeSpectrum (X.presheaf.stalk x)) ≤ OrderDual.ofDual a :=
      (PrimeSpectrum.le_iff_specializes _ _).mpr h1
    have h2' : ¬ (OrderDual.ofDual a : PrimeSpectrum (X.presheaf.stalk x)) ≤ OrderDual.ofDual b :=
      fun h => h2 ((PrimeSpectrum.le_iff_specializes _ _).mp h)
    exact lt_of_le_not_ge h1' h2'
  · rintro ⟨y, hy⟩
    have hy' : y ∈ Set.range (X.fromSpecStalk x) := by
      rw [hrange]
      exact hy
    obtain ⟨p, hp⟩ := hy'
    exact ⟨OrderDual.toDual p, Subtype.ext hp⟩

theorem dim_le_topologicalKrullDim : X.dim ≤ topologicalKrullDim X := by
  refine iSup_le fun x => ?_
  -- `Spec 𝒪_{X,x} → X` is an embedding (a preimmersion), so the Krull dimension of
  -- `Spec 𝒪_{X,x}`, which is `ringKrullDim 𝒪_{X,x}`, is at most that of `X`.
  have h1 : topologicalKrullDim (Spec (X.presheaf.stalk x)) ≤ topologicalKrullDim X :=
    (X.fromSpecStalk x).isEmbedding.isInducing.topologicalKrullDim_le
  have h2 : topologicalKrullDim (PrimeSpectrum (X.presheaf.stalk x)) =
      ringKrullDim (X.presheaf.stalk x) :=
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  exact h2.symm.le.trans h1

theorem dim_eq_topologicalKrullDim : X.dim = topologicalKrullDim X :=
  le_antisymm X.dim_le_topologicalKrullDim X.topologicalKrullDim_le_dim

end AlgebraicGeometry.Scheme

namespace Hironaka

/-! ### Subschemes as coherent sheaves of ideals -/


namespace Subscheme

variable {X : Scheme.{u}}






/-- Intersection of subschemes: defined by the sum ("join") of the ideal sheaves (p. 165). -/
def inter (D D' : Subscheme X) : Subscheme X := D ⊔ D'



def IsNonempty (D : Subscheme X) : Prop := D.pts.Nonempty










end Subscheme

/-! ### Noetherianity and zero-dimensional subschemes

An algebraic scheme has noetherian underlying space, and a subscheme of dimension `0` of such
a scheme is a finite set of closed points, so every subset of its point set is closed.  (Used
for the trivial case `n = 0` of Theorems I₁, I₂ of Ch. I §2.) -/

/-- An algebraic scheme (of finite type over a noetherian local ring `S ∈ 𝔅`) is a
noetherian scheme. -/
theorem IsAlgebraicScheme.isNoetherian (X : Scheme.{u}) [IsAlgebraicScheme X] :
    IsNoetherian X := by
  obtain ⟨S, _, _, _, p, hp, hq⟩ := IsAlgebraicScheme.exists_base (X := X)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact ⟨⟩

/-- The underlying space of an algebraic scheme is a noetherian topological space. -/
theorem IsAlgebraicScheme.noetherianSpace (X : Scheme.{u}) [IsAlgebraicScheme X] :
    TopologicalSpace.NoetherianSpace X :=
  haveI := IsAlgebraicScheme.isNoetherian X
  inferInstance

/-- In a `T₀` space of Krull dimension `≤ 0` every point is closed.  Indeed `closure {z}` is
irreducible and closed, hence maximal among irreducible closed sets; for `y ∈ closure {z}`
this forces `closure {z} ⊆ closure {y}`, so `y` and `z` are inseparable and `T₀` gives
`y = z`. -/
theorem isClosed_singleton_of_topologicalKrullDim_nonpos {Z : Type*} [TopologicalSpace Z]
    [T0Space Z] (hZ : topologicalKrullDim Z ≤ 0) (z : Z) : IsClosed ({z} : Set Z) := by
  have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp hZ
  suffices h : closure ({z} : Set Z) = {z} by rw [← h]; exact isClosed_closure
  refine subset_antisymm (fun y hy => ?_) subset_closure
  have h1 : z ⤳ y := specializes_iff_mem_closure.mpr hy
  have h2 : y ⤳ z := by
    have hle : (⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        TopologicalSpace.IrreducibleCloseds Z) ≤
        ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ :=
      SetLike.coe_subset_coe.mp h1.closure_subset
    exact specializes_iff_closure_subset.mpr (SetLike.coe_subset_coe.mpr (hmax _ hle))
  exact (h2.antisymm h1).eq

/-- A noetherian sober `T₀` space of Krull dimension `≤ 0` is finite: it has finitely many
irreducible components, and each of them is the closure of its generic point, i.e. a single
closed point. -/
theorem finite_of_topologicalKrullDim_nonpos {Z : Type*} [TopologicalSpace Z]
    [TopologicalSpace.NoetherianSpace Z] [QuasiSober Z] [T0Space Z]
    (hZ : topologicalKrullDim Z ≤ 0) : Finite Z := by
  have hcomp : ∀ C ∈ irreducibleComponents Z, ∃ z : Z, C = {z} := by
    intro C hC
    have hirr : IsIrreducible C := hC.1
    have hcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
    exact ⟨hirr.genericPoint, (hirr.closure_genericPoint hcl).symm.trans
      (isClosed_singleton_of_topologicalKrullDim_nonpos hZ _).closure_eq⟩
  have hfin : (Set.univ : Set Z).Finite := by
    rw [← sUnion_irreducibleComponents]
    refine Set.Finite.sUnion TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ?_
    intro C hC
    obtain ⟨z, rfl⟩ := hcomp C hC
    exact Set.finite_singleton z
  exact Set.finite_univ_iff.mp hfin

/-- On a scheme with noetherian underlying space, every subset of the point set of a
zero-dimensional subscheme `W` is closed: `W.toScheme` is a finite `T₀` sober space all of
whose points are closed (previous two lemmas), and `W.ι` is a closed embedding with image
`W.pts`, so `W.pts` is a finite set of closed points of `X`. -/
theorem Subscheme.isClosed_of_subset_pts_of_dim_nonpos {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (W : Subscheme X) (hW : W.dim ≤ 0)
    {S : Set X} (hS : S ⊆ W.pts) : IsClosed S := by
  have hι : Topology.IsClosedEmbedding W.ι := W.ι.isClosedEmbedding
  have : TopologicalSpace.NoetherianSpace W.toScheme := hι.isInducing.noetherianSpace
  have hW' : topologicalKrullDim W.toScheme ≤ 0 :=
    (W.toScheme.topologicalKrullDim_le_dim).trans hW
  have : Finite W.toScheme := finite_of_topologicalKrullDim_nonpos hW'
  have hpts : W.pts = Set.range W.ι := W.range_subschemeι.symm
  have hS' : S = ⋃ x ∈ S, ({x} : Set X) := by simp
  rw [hS']
  refine Set.Finite.isClosed_biUnion ((Set.finite_range W.ι).subset (hpts ▸ hS)) ?_
  intro x hx
  obtain ⟨z, rfl⟩ : x ∈ Set.range W.ι := hpts ▸ hS hx
  rw [← Set.image_singleton]
  exact hι.isClosedMap _ (isClosed_singleton_of_topologicalKrullDim_nonpos hW' z)

end Hironaka

end
