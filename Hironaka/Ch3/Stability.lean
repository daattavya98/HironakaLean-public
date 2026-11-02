/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact
public import Architect
public import Hironaka.Ch3.Basic
public import Hironaka.Ch3.NuStar
public import Hironaka.Ch3.TauStar
public import Hironaka.Ch0.NormalFlatness
public import Hironaka.Ch0.Blowup
public import Hironaka.Ch3.PermissibleEffects
public import Hironaka.Ch3.Transforms
public import Hironaka.Ch3.SemiContinuity
public import Hironaka.Compat.RegularGraded
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Compat.BlowupStalkPoints
public import Hironaka.Compat.StalkGeneralization

/-!
# Ch. III §6: A stability theorem of a standard base (pp. 238–244)

> REMARK. Let R → R' be a local homomorphism of regular local rings which transforms a regular
> system of parameters of R into such a system of parameters of R'. Let J be an ideal in R and
> J' = JR'. Let (f₁, …, f_m) be a system of elements of J, and (f₁', …, f_m') the image of the
> system in R'. The local homomorphism induces a canonical homomorphism of graded algebras
> gr_M(R) → gr_{M'}(R'), where M (resp. M') denotes the maximal ideal of R (resp. R'), and the
> image of gr_M(J, R) by this homomorphism generates gr_{M'}(J', R'). … we can easily show that
> (f₁, …, f_m) is a standard base
> of J if and only if (f₁', …, f_m') is such a base of J'.  (p. 238)

Contents, in the paper's order: the Remark of p. 238, Theorem 5 (pp. 238–241), and its three
Corollaries — Corollary 1 (p. 241), Corollary 2 (p. 242, scheme level) and Corollary 3
(pp. 242–244), whose three assertions (a), (b), (c) are split into three separate nodes
`cor:III.thm5-3a`, `cor:III.thm5-3b`, `cor:III.thm5-3c` sharing the hypotheses (i), (ii)
(packaged as `IsLocallyAdaptedSystem`).  Assertion (c), whose proof passes to the completion and
resolves a curve germ, is in `Hironaka/Ch3/StabilityCor3c.lean`.

## Conventions

`ν_P(f)` for an element is `Ideal.ordElem P f`, `ν_M(J)` is `Ideal.ord M J` and `ν(J)` is
`Ideal.nu J` (`Hironaka/Compat/{Graded,RegularLocalRing}.lean`); `gr_M(R)` is
`AssocGraded (maximalIdeal R)`, the initial form is `initialForm` and `gr_M(J, R)` is
`grIdeal (maximalIdeal R) J`; `ν*(J)`, `τ*(J)`, standard bases, monoidal transforms, strict
transforms and permissible centers are `nuStar`, `tauStar`, `IsStandardBase`,
`MonoidalTransform`, `strictTransformIdeal` and `IsPermissibleCenter`
(`Hironaka/Ch3/{Basic,NuStar,TauStar}.lean`).  `R_Q` is `Localization.AtPrime Q`, `JR_Q` is
`J.map (algebraMap R (Localization.AtPrime Q))`, and the completion `R̂` of `R` is
`AdicCompletion (maximalIdeal R) R`.

For a monoidal transform `t : MonoidalTransform R P`, `R₁ = t.ring` and the canonical local
homomorphism `R → R₁` is `t.toRing`.  That this homomorphism *is* local and that `R₁` *is* a
regular local ring are lemmas of §2 (pp. 209–210), which live in `Hironaka/Ch3/Transforms.lean`
(imported here): `MonoidalTransform.isLocalHom_toRing` is a global instance and, for a prime `P`
with `R/P` regular, the regularity of `R₁` is the global instance
`MonoidalTransform.instIsRegularLocalRing`; accordingly the statements of this file do not carry
`[IsLocalHom t.toRing]` or `[IsRegularLocalRing t.ring]` (except where `R/P` is not an instance
argument, as in `isLocallyAdaptedSystem_strictTransform`).  Likewise `[IsDomain R]` (a regular local
ring is a domain) is a hypothesis wherever `MonoidalTransform R P` has to be formed.

The paper's `x^{-ν} f` (for `x ∈ P` with `PR₁ = (x)R₁`, `f ∈ J`, `ν ≤ ν_P(f)`) is encoded as an
element `g` of `R₁` subject to the equation `(t.toRing x)^ν * g = t.toRing f`, exactly as in
Definition 5 (p. 213).  Because `R₁` is a domain such a `g` is unique when it exists, so this is
a faithful encoding of the division; `t.xR = t.toRing t.x` is the special case `x = t.x`.

Representation choices are flagged as "Formalization note (encoding): …".  Every place where a
Lean statement or proof departs from the paper is flagged in the docstring by a paragraph
"Deviation from the paper (<category>): …" and in the blueprint text by a paragraph
"Deviation from the paper (<category>)" / "Gap in the paper filled" / "Paper misprint".

Note on the name `t`: `Hironaka.t R J` is the integer `t(J)` of Definition 6 (p. 221); monoidal
transforms are also called `t` here (as in the rest of Ch. III), so `t(J)` is written with its
full name `Hironaka.t` in the statement of Corollary 1.
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

namespace Hironaka

universe u

/-! ### Extending a system of elements to a standard base

A system `(g₁, …, g_i)` of elements "can be extended to a standard base of `J`" if it is a
subsystem of a standard base of `J` (Definition 3, p. 208); the encoding fixed for the chapter is

  `∃ (m' : ℕ) (F : Fin m' → R), IsStandardBase R J F ∧ ∀ j, ∃ j', F j' = g j`

(`Hironaka.ExtendsToStandardBase`).  §6 contains no statement of that form — it is the hypothesis
(iv) of Lemmas 14–16 of §5 — so the definition is not repeated here; it is made once in
`Hironaka/Ch3/PermissibleEffects.lean` (§5), a duplicate in this file being a clash in the
namespace `Hironaka`. -/

/-! ### The Remark opening §6 (p. 238) -/

/-! ### Auxiliary facts for the Remark of p. 238 -/

section RemarkAux

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- A non-zero initial form which is homogeneous of degree `d` has `ν_I(a) = d`. -/
private theorem ordElem_eq_of_initialForm_mem_homogeneous {A : Type*} [CommRing A]
    (I : Ideal A) {a : A} {d : ℕ} (hd : initialForm I a ∈ AssocGraded.homogeneous I d)
    (h0 : initialForm I a ≠ 0) : Ideal.ordElem I a = d := by
  by_cases htop : Ideal.ordElem I a = ⊤
  · exact absurd (by rw [initialForm, dite_eq_left htop]) h0
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn]
  by_contra hnd
  have hnd' : n ≠ d := fun h => hnd (by rw [h])
  apply h0
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hd
  have h1 : grProj I d (initialForm I a) = y := by rw [← hy, grProj_ofGrPiece_same]
  have h2 : grProj I d (initialForm I a) = 0 := by
    rw [initialForm_eq_mk I hn.symm, grProj_mk_ne I hnd']
  rw [← hy, ← h1, h2, map_zero]

/-- A system of elements of `J` whose initial forms generate `gr_M(J, R)` contains a standard
base of `J` (with at most as many elements): sort the elements by order and discard those whose
initial form lies in the ideal generated by the initial forms of the preceding ones. -/
theorem exists_isStandardBase_comp (J : Ideal R) {n : ℕ} (f : Fin n → R)
    (hfJ : ∀ i, f i ∈ J)
    (hgen : Ideal.span (Set.range fun i => initialForm (maximalIdeal R) (f i)) =
      grIdeal (maximalIdeal R) J) :
    ∃ (m : ℕ) (σ : Fin m → Fin n), m ≤ n ∧ IsStandardBase R J (f ∘ σ) := by
  classical
  let e : Fin n → ℕ := fun i => (Ideal.ordElem (maximalIdeal R) (f i)).toNat
  let φ : Fin n → AssocGraded (maximalIdeal R) := fun i => initialForm (maximalIdeal R) (f i)
  let g' := φ ∘ Tuple.sort e
  let e' := e ∘ Tuple.sort e
  have he' : Monotone e' := Tuple.monotone_sort e
  have hspan' : grIdeal (maximalIdeal R) J = Ideal.span (Set.range g') := by
    rw [← hgen, Set.range_comp, (Tuple.sort e).surjective.range_eq, Set.image_univ]
  let S : Finset (Fin n) := Finset.univ.filter fun i =>
    g' i ∉ Ideal.span (Set.range fun j : Fin i => g' (Fin.castLE i.2.le j))
  let emb := S.orderEmbOfFin rfl
  have hS : S.card ≤ n := (Finset.card_le_univ S).trans (Fintype.card_fin n).le
  refine ⟨S.card, fun k => Tuple.sort e (emb k), hS, fun k => hfJ _,
    fun k => Ideal.subset_span ⟨_, hfJ _, rfl⟩,
    ⟨fun k => e' (emb k), fun k => ?_, he'.comp emb.monotone⟩, ?_, ?_⟩
  · show initialForm (maximalIdeal R) (f (Tuple.sort e (emb k))) ∈
      AssocGraded.homogeneous (maximalIdeal R) (e (Tuple.sort e (emb k)))
    by_cases htop : Ideal.ordElem (maximalIdeal R) (f (Tuple.sort e (emb k))) = ⊤
    · rw [initialForm, dite_eq_left htop]
      exact zero_mem _
    · rw [initialForm_eq_mk _ (ENat.natCast_toNat htop).symm]
      exact AssocGraded.mk_mem_homogeneous _ _
  · rw [hspan']
    refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
    · have key : ∀ N : ℕ, ∀ i : Fin n, (i : ℕ) < N →
          g' i ∈ Ideal.span (Set.range fun k => g' (emb k)) := by
        intro N
        induction N with
        | zero => intro i hi; omega
        | succ N ih =>
          intro i hi
          by_cases hiS : i ∈ S
          · have : i ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hiS
            obtain ⟨k, rfl⟩ := this
            exact Ideal.subset_span ⟨k, rfl⟩
          · have hmem : g' i ∈
                Ideal.span (Set.range fun j : Fin i => g' (Fin.castLE i.2.le j)) := by
              simpa [S] using hiS
            refine (Ideal.span_le.mpr ?_) hmem
            rintro _ ⟨j, rfl⟩
            exact ih _ (by simp only [Fin.val_castLE]; omega)
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact key n i i.2
    · rintro _ ⟨k, rfl⟩
      exact Ideal.subset_span ⟨_, rfl⟩
  · intro k hk
    have hkS : emb k ∈ S := S.orderEmbOfFin_mem rfl k
    rw [Finset.mem_filter] at hkS
    apply hkS.2
    refine (Ideal.span_mono ?_) hk
    rintro _ ⟨j, rfl⟩
    have hlt : emb (Fin.castLE k.2.le j) < emb k :=
      emb.strictMono (show Fin.castLE k.2.le j < k from Fin.lt_def.mpr (by simp))
    exact ⟨⟨(emb (Fin.castLE k.2.le j) : ℕ), hlt⟩, by simp [g', φ]⟩

end RemarkAux

/-! ### Flat base change of orders, initial forms and `gr_M(J, R)` -/

section FlatAux

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]

/-- For a faithfully flat `A`-algebra `B`, `ν_{IB}(a) = ν_I(a)` (`Iⁿ B ∩ A = Iⁿ`). -/
private theorem Ideal.ordElem_map_of_faithfullyFlat (I : Ideal A) (a : A) :
    Ideal.ordElem (I.map (algebraMap A B)) (algebraMap A B a) = Ideal.ordElem I a := by
  have h : ∀ ν : ℕ, algebraMap A B a ∈ I.map (algebraMap A B) ^ ν ↔ a ∈ I ^ ν := by
    intro ν
    rw [← Ideal.map_pow]
    refine ⟨fun h => ?_, Ideal.mem_map_of_mem _⟩
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (I ^ ν)]
    exact h
  simp only [Ideal.ordElem, h]

/-- For a faithfully flat `A`-algebra `B`, the canonical homomorphism
`gr_I(A) → gr_{IB}(B)` maps the initial form of `a` to that of its image. -/
private theorem AssocGraded.map_initialForm_algebraMap (I : Ideal A) (a : A) :
    AssocGraded.map (algebraMap A B) I (initialForm I a) =
      initialForm (I.map (algebraMap A B)) (algebraMap A B a) := by
  by_cases htop : Ideal.ordElem I a = ⊤
  · have htop' : Ideal.ordElem (I.map (algebraMap A B)) (algebraMap A B a) = ⊤ := by
      rw [Ideal.ordElem_map_of_faithfullyFlat, htop]
    rw [initialForm, dite_eq_left htop, map_zero, initialForm, dite_eq_left htop']
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [initialForm_eq_mk I hn.symm, AssocGraded.map_mk,
      initialForm_eq_mk _ ((Ideal.ordElem_map_of_faithfullyFlat I a).trans hn.symm)]

/-- Lemma 2 of §1 for a faithfully flat local homomorphism: if the initial forms of `g_j`
generate `gr_I(J, A)` then the initial forms of their images generate `gr_{IB}(JB, B)`. -/
private theorem grIdeal_map_eq_span_initialForm_of_faithfullyFlat [IsNoetherianRing A] [IsNoetherianRing B]
    (I J : Ideal A) (hI : I.map (algebraMap A B) ≤ Ring.jacobson B) {n : ℕ} (g : Fin n → A)
    (hg : grIdeal I J = Ideal.span (Set.range fun j => initialForm I (g j))) :
    grIdeal (I.map (algebraMap A B)) (J.map (algebraMap A B)) =
      Ideal.span (Set.range fun j =>
        initialForm (I.map (algebraMap A B)) (algebraMap A B (g j))) := by
  rw [← map_grIdeal_eq_grIdeal_map_of_flat A B I J hI, hg, Ideal.map_span, ← Set.range_comp]
  congr 2
  funext j
  exact AssocGraded.map_initialForm_algebraMap I (g j)

end FlatAux

section Remark

variable {R R' : Type u} [CommRing R] [CommRing R'] [IsRegularLocalRing R] [IsRegularLocalRing R']

/-- The Remark of p. 238: "Let `R → R'` be a local homomorphism of regular local rings which
transforms a regular system of parameters of `R` into such a system of parameters of `R'`. Let
`J` be an ideal in `R` and `J' = JR'`. Let `(f₁, …, f_m)` be a system of elements of `J`, and
`(f₁', …, f_m')` the image of the system in `R'`. The local homomorphism induces a canonical
homomorphism of graded algebras `gr_M(R) → gr_{M'}(R')`, … and the image of `gr_M(J, R)` by this
homomorphism generates `gr_{M'}(J', R')`. (See Lemma 2 and its Corollary of §1.) We know that
`gr_M(R)` and `gr_{M'}(R')` are polynomial rings over fields, and the homomorphism
`gr_M(R) → gr_{M'}(R')` is obtained by the coefficient field extension `R/M → R'/M'`. In view of
these facts, we can easily show that `(f₁, …, f_m)` is a standard base of `J` if and only if
`(f₁', …, f_m')` is such a base of `J'`."

The proof follows the printed one.  The homomorphism `σ = grMapMax : gr_M(R) → gr_{M'}(R')` maps the
initial form of `a` to that of `α(a)` (`initialForm_map_of_mapsRSOP`), the image of `gr_M(J, R)` generates
`gr_{M'}(J', R')` (Lemma 2, `grIdeal_map_eq_span_initialForm_of_faithfullyFlat`), and "in view of these
facts" `σ` is the coefficient field extension of the polynomial rings `k[X] → k'[X]`, hence faithfully flat:
`σ x ∈ 𝔞 · gr_{M'}(R')` implies `x ∈ 𝔞` (`mem_of_map_mem_map_grMapMax`, "non-membership descends").
Thus `(f_j)` satisfies (iii) of Lemma 1 (Definition 3) iff `(α(f_j))` does (the initial form of `α(f_i)` is
`σ` of that of `f_i`), the initial forms of the `α(f_j)` generate `gr_{M'}(J', R')` iff those of the
`f_j` generate `gr_M(J, R)`, and the degrees are preserved (`ν_{M'}(α a) = ν_M(a)`).

Deviation from the paper (statement modified): the hypothesis that the `f_j` lie in `J` is not
assumed; `IsStandardBase` contains membership, so the direction `⇐` proves `f_j ∈ J` (from
`JR' ∩ R = J`, faithful flatness) and the Lean statement is slightly stronger than the paper's.
The literal form, with `f_j ∈ J` as a hypothesis, is `isStandardBase_iff_isStandardBase_map_of_mem`. -/
@[blueprint "rem:III.6-standard-base-ascent"
  (statement := /-- Let $\alpha\colon R\to R'$ be a local homomorphism of regular local rings
    which transforms a regular system of parameters of $R$ into such a system of parameters of
    $R'$ (\cref{def:III.rsop-map}). Let $J$ be an ideal in $R$ and $J'=JR'$. Let
    $(f_1,\dots,f_m)$ be a system of elements of $J$, and $(f_1',\dots,f_m')$ the image of the
    system in $R'$. Then $(f_1,\dots,f_m)$ is a standard base of $J$ (\cref{def:III.3}) if and
    only if $(f_1',\dots,f_m')$ is such a base of $J'$. (Remark, p.~238.)

    \textbf{Deviation from the paper (statement modified).} The Lean statement does not assume
    that the $f_j$ lie in $J$: the direction ``$\Leftarrow$'' proves $f_j\in J$ (as $JR'\cap R=J$
    by faithful flatness), so it is slightly stronger than the Remark; the literal form is
    \cref{rem:III.6-standard-base-ascent-printed}. -/)
  (proof := /-- The local homomorphism induces a canonical homomorphism of graded algebras
    $\operatorname{gr}_M(R)\to\operatorname{gr}_{M'}(R')$ (\cref{def:III.1-graded-map}), where
    $M$ (resp.\ $M'$) denotes the maximal ideal of $R$ (resp.\ $R'$), and the image of
    $\operatorname{gr}_M(J,R)$ by this homomorphism generates $\operatorname{gr}_{M'}(J',R')$.
    (See Lemma~2 and its Corollary of \S1: \cref{lem:III.2}, \cref{cor:III.lem2}.) We know that
    $\operatorname{gr}_M(R)$ and $\operatorname{gr}_{M'}(R')$ are polynomial rings over fields,
    and the homomorphism $\operatorname{gr}_M(R)\to\operatorname{gr}_{M'}(R')$ is obtained by
    the coefficient field extension $R/M\to R'/M'$. In view of these facts, we can easily show
    that $(f_1,\dots,f_m)$ is a standard base of $J$ if and only if $(f_1',\dots,f_m')$ is such
    a base of $J'$.

    \textbf{Formal proof.} The Lean proof follows this one. The homomorphism
    $\sigma\colon\operatorname{gr}_M(R)\to\operatorname{gr}_{M'}(R')$ maps the initial form of $a$
    to that of $\alpha(a)$; by \cref{lem:III.2} it maps the generators of
    $\operatorname{gr}_M(J,R)$ to generators of $\operatorname{gr}_{M'}(J',R')$; and
    ``in view of these facts'' $\sigma$ is the coefficient extension $k[X]\to k'[X]$ of polynomial
    rings (the polynomial pictures given by corresponding regular systems of parameters), hence
    faithfully flat, so that non-membership descends: $\sigma(x)\in\mathfrak a\cdot
    \operatorname{gr}_{M'}(R')$ implies $x\in\mathfrak a$. This gives property (iii) and the
    generation of $\operatorname{gr}_M(J,R)$ by the initial forms of the $f_j$ in the direction
    ``$\Leftarrow$''; the orders are preserved, $\nu_{M'}(\alpha(a))=\nu_M(a)$. -/)
  (latexEnv := "remark")]
theorem isStandardBase_iff_isStandardBase_map (α : R →+* R') [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (J : Ideal R) {m : ℕ} (f : Fin m → R) :
    IsStandardBase R J f ↔ IsStandardBase R' (J.map α) fun j => α (f j) := by
  classical
  let _ : Algebra R R' := α.toAlgebra
  have _ : IsLocalHom (algebraMap R R') := ‹IsLocalHom α›
  have _ : Module.Flat R R' := hα.flat
  have _ : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hM : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R' := by
    obtain ⟨s, hs, hs', -⟩ := hα
    rw [← hs.1, Ideal.map_span, ← hs'.1, Finset.coe_image]
    rfl
  have hjac : (maximalIdeal R).map (algebraMap R R') ≤ Ring.jacobson R' := by
    rw [hM, ← Ideal.jacobson_bot]
    exact maximalIdeal_le_jacobson _
  -- `ν_{M'}(α(a)) = ν_M(a)`
  have hord : ∀ a : R,
      Ideal.ordElem (maximalIdeal R') (α a) = Ideal.ordElem (maximalIdeal R) a :=
    ordElem_map_of_mapsRSOP α hα
  -- "The local homomorphism induces a canonical homomorphism of graded algebras
  -- `gr_M(R) → gr_{M'}(R')`", `σ`; it maps the initial form of `a` to that of `α(a)`
  have hσinit : ∀ a : R, grMapMax α hα (initialForm (maximalIdeal R) a) =
      initialForm (maximalIdeal R') (α a) := fun a => (initialForm_map_of_mapsRSOP α hα a).symm
  -- "In view of these facts": `σ` is the coefficient field extension of polynomial rings, hence
  -- faithfully flat, so that `σ x ∈ σ(𝔞) gr_{M'}(R')` implies `x ∈ 𝔞` (non-membership descends)
  have hpure := mem_of_map_mem_map_grMapMax α hα
  -- the image under `σ` of an ideal generated by initial forms is generated by those of the images
  have hmapspan : ∀ {n : ℕ} (g : Fin n → R),
      Ideal.map (grMapMax α hα) (Ideal.span (Set.range fun j => initialForm (maximalIdeal R) (g j))) =
        Ideal.span (Set.range fun j => initialForm (maximalIdeal R') (α (g j))) := by
    intro n g
    rw [Ideal.map_span, ← Set.range_comp]
    simp only [Function.comp_def, hσinit]
  -- Lemma 2: generators of `gr_M(J, R)` by initial forms go to generators of `gr_{M'}(J', R')`
  have hgen : ∀ {n : ℕ} (g : Fin n → R), grIdeal (maximalIdeal R) J =
        Ideal.span (Set.range fun j => initialForm (maximalIdeal R) (g j)) →
      grIdeal (maximalIdeal R') (J.map α) =
        Ideal.span (Set.range fun j => initialForm (maximalIdeal R') (α (g j))) := by
    intro n g hg
    have := grIdeal_map_eq_span_initialForm_of_faithfullyFlat (B := R') (maximalIdeal R) J hjac g hg
    rw [hM] at this
    exact this
  -- the homomorphism `gr_M(R) → gr_{M'}(R')` maps `gr_M(J, R)` into `gr_{M'}(J', R')`
  have hσJ : ∀ x ∈ grIdeal (maximalIdeal R) J,
      grMapMax α hα x ∈ grIdeal (maximalIdeal R') (J.map α) := by
    intro x hx
    have : Ideal.map (grMapMax α hα) (grIdeal (maximalIdeal R) J) ≤
        grIdeal (maximalIdeal R') (J.map α) := by
      rw [grIdeal, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      rw [hσinit]
      exact Ideal.subset_span ⟨α a, Ideal.mem_map_of_mem α ha, rfl⟩
    exact this (Ideal.mem_map_of_mem _ hx)
  -- the homomorphism `gr_M(R) → gr_{M'}(R')` preserves ideal membership
  have hrefl : ∀ i : Fin m, initialForm (maximalIdeal R) (f i) ∈ Ideal.span
        (Set.range fun j : Fin i => initialForm (maximalIdeal R) (f (Fin.castLE i.2.le j))) →
      initialForm (maximalIdeal R') (α (f i)) ∈ Ideal.span (Set.range fun j : Fin i =>
        initialForm (maximalIdeal R') (α (f (Fin.castLE i.2.le j)))) := by
    intro i hi
    have h1 := Ideal.mem_map_of_mem (grMapMax α hα) hi
    rw [hmapspan, hσinit] at h1
    exact h1
  constructor
  · -- `(f_j)` a standard base of `J` ⟹ `(α(f_j))` a standard base of `J'`
    intro hf
    obtain ⟨hfJ, -, ⟨d, hd, hmono⟩, hspan, hnot⟩ := hf
    have hne : ∀ j, initialForm (maximalIdeal R) (f j) ≠ 0 := fun j h0 => hnot j (by
      dsimp only; rw [h0]; exact zero_mem _)
    have hordf : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = d j := fun j =>
      ordElem_eq_of_initialForm_mem_homogeneous _ (hd j) (hne j)
    refine ⟨fun j => Ideal.mem_map_of_mem α (hfJ j),
      fun j => Ideal.subset_span ⟨α (f j), Ideal.mem_map_of_mem α (hfJ j), rfl⟩,
      ⟨d, fun j => ?_, hmono⟩, hgen f hspan, fun i hi => hnot i ?_⟩
    · show initialForm (maximalIdeal R') (α (f j)) ∈ _
      rw [initialForm_eq_mk _ ((hord _).trans (hordf j))]
      exact AssocGraded.mk_mem_homogeneous _ _
    · -- (iii): non-membership ascends since `σ` is faithfully flat
      refine hpure _ _ ?_
      rw [hmapspan, hσinit]
      exact hi
  · -- `(α(f_j))` a standard base of `J'` ⟹ `(f_j)` a standard base of `J`
    intro hg
    have hg' := hg
    obtain ⟨hgJ, hψJ, ⟨d, hd, hmono⟩, hspan, hnot⟩ := hg
    have hne : ∀ j, initialForm (maximalIdeal R') (α (f j)) ≠ 0 := fun j h0 => hnot j (by
      dsimp only; rw [h0]; exact zero_mem _)
    have hordg : ∀ j, Ideal.ordElem (maximalIdeal R') (α (f j)) = d j := fun j =>
      ordElem_eq_of_initialForm_mem_homogeneous _ (hd j) (hne j)
    have hordf : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = d j := fun j =>
      (hord _).symm.trans (hordg j)
    -- `J R' ∩ R = J` (faithful flatness)
    have hfJ : ∀ j, f j ∈ J := fun j => by
      rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R') J]
      exact hgJ j
    have hdf : ∀ j, initialForm (maximalIdeal R) (f j) ∈
        AssocGraded.homogeneous (maximalIdeal R) (d j) := fun j => by
      rw [initialForm_eq_mk _ (hordf j)]
      exact AssocGraded.mk_mem_homogeneous _ _
    -- (iii): non-membership descends
    have hnotf : ∀ i : Fin m, initialForm (maximalIdeal R) (f i) ∉ Ideal.span
        (Set.range fun j : Fin i => initialForm (maximalIdeal R) (f (Fin.castLE i.2.le j))) :=
      fun i hi => hnot i (hrefl i hi)
    have hφJ : ∀ j, initialForm (maximalIdeal R) (f j) ∈ grIdeal (maximalIdeal R) J :=
      fun j => Ideal.subset_span ⟨f j, hfJ j, rfl⟩
    -- the initial forms of the `f_j` generate `gr_M(J, R)`: if `x ∈ gr_M(J, R)` then `σ x` lies in
    -- `gr_{M'}(J', R')`, which is generated by the initial forms of the `α(f_j)`, i.e. `σ x` lies in
    -- the extension of `(in f_j)`, whence `x ∈ (in f_j)` by faithful flatness
    refine ⟨hfJ, hφJ, ⟨d, hdf, hmono⟩, le_antisymm (fun x hx => ?_)
      (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hφJ j)), hnotf⟩
    refine hpure _ _ ?_
    rw [hmapspan]
    rw [← hspan]
    exact hσJ x hx

/-- The Remark of p. 238 in its printed form: with the hypothesis "Let `(f₁, …, f_m)` be a system of
elements of `J`" (`f_j ∈ J`) as a hypothesis.  This is `isStandardBase_iff_isStandardBase_map`, whose
statement does not assume `f_j ∈ J` (the direction `⇐` proves it) and is therefore slightly stronger. -/
@[blueprint "rem:III.6-standard-base-ascent-printed"
  (statement := /-- Let $\alpha\colon R\to R'$ be a local homomorphism of regular local rings
    which transforms a regular system of parameters of $R$ into such a system of parameters of
    $R'$ (\cref{def:III.rsop-map}). Let $J$ be an ideal in $R$ and $J'=JR'$. Let
    $(f_1,\dots,f_m)$ be a system of elements of $J$, and $(f_1',\dots,f_m')$ the image of the
    system in $R'$. Then $(f_1,\dots,f_m)$ is a standard base of $J$ (\cref{def:III.3}) if and
    only if $(f_1',\dots,f_m')$ is such a base of $J'$. (Remark, p.~238, with the hypothesis
    $f_j\in J$ as printed.) -/)
  (proof := /-- This is \cref{rem:III.6-standard-base-ascent}, which does not need the
    hypothesis $f_j\in J$. -/)
  (proofUses := ["rem:III.6-standard-base-ascent"])
  (latexEnv := "remark")]
theorem isStandardBase_iff_isStandardBase_map_of_mem (α : R →+* R') [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (J : Ideal R) {m : ℕ} (f : Fin m → R) (hfJ : ∀ j, f j ∈ J) :
    IsStandardBase R J f ↔ IsStandardBase R' (J.map α) fun j => α (f j) := by
  have _ := hfJ
  exact isStandardBase_iff_isStandardBase_map α hα J f

end Remark

/-! ### Auxiliary material for the proof of Theorem 5

The coordinates of `Hironaka/Ch3/PermissibleEffects.lean` (`TransformCoord`) are used to carry out the
computation of pp. 239–241: the description of the strict transform as a localization
(`TransformCoord.exists_isUnit_mul_eq_of_mem_strictTransformIdeal`), the expansion of `f` with
`f' ∈ P^{ν+μ₁+1}` (`TransformCoord.exists_pAdicExpansion`) and its consequences
(`TransformCoord.eval_notMem_pow_succ_of_coeff_notMem`, `TransformCoord.toRing_eval_notMem_pow_succ_of_coeff_notMem`),
the element `h` with the properties (1)–(4) (`TransformCoord.exists_mem_ideal_sub_mem_pow_succ`), the descent
(`TransformCoord.mk_mem_span_initialForm`), the residually rational case
(`isStandardBase_strictTransformIdeal_of_isResiduallyRational`) and the reduction to it
(`isStandardBase_and_nuStar_eq_strictTransformIdeal`). -/

section PE5Theorem5Aux

open MvPolynomial

section PolyHelpers

variable {k : Type*} [CommRing k] {σ : Type*}

/-- `hc_n(q · p) = hc_{n-d}(q) · p` for `p` homogeneous of degree `d ≤ n`. -/
theorem _root_.MvPolynomial.homogeneousComponent_mul_of_isHomogeneous (q p : MvPolynomial σ k) {d : ℕ} (hp : p.IsHomogeneous d)
    (n : ℕ) : homogeneousComponent n (q * p) =
      if d ≤ n then homogeneousComponent (n - d) q * p else 0 := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent q, Finset.sum_mul, map_sum]
  have hterm : ∀ e ∈ Finset.range (q.totalDegree + 1),
      homogeneousComponent n (homogeneousComponent e q * p) =
        if e + d = n then homogeneousComponent e q * p else 0 := by
    intro e _
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr
      ((homogeneousComponent_isHomogeneous e q).mul hp))]
    split_ifs with h1 h2 h2 <;> first | rfl | omega
  rw [Finset.sum_congr rfl hterm]
  split_ifs with hdn
  · by_cases hmem : n - d ∈ Finset.range (q.totalDegree + 1)
    · rw [Finset.sum_eq_single (n - d)]
      · simp only [show n - d + d = n by omega, ↓reduceIte]
      · intro e _ he
        have : e + d ≠ n := by omega
        simp only [this, ↓reduceIte]
      · intro h; exact absurd hmem h
    · rw [Finset.mem_range, not_lt] at hmem
      rw [homogeneousComponent_eq_zero _ _ (by omega), zero_mul]
      refine Finset.sum_eq_zero fun e he => ?_
      rw [Finset.mem_range] at he
      have : e + d ≠ n := by omega
      simp only [this, ↓reduceIte]
  · refine Finset.sum_eq_zero fun e _ => ?_
    have : e + d ≠ n := by omega
    simp only [this, ↓reduceIte]

theorem _root_.MvPolynomial.filterSupport_add (pr : (σ →₀ ℕ) → Prop) [DecidablePred pr] (F G : MvPolynomial σ k) :
    restrictSupport pr (F + G) = restrictSupport pr F + restrictSupport pr G := by
  ext β
  simp only [coeff_restrictSupport, MvPolynomial.coeff_add]
  split_ifs <;> simp

theorem _root_.MvPolynomial.filterSupport_sum (pr : (σ →₀ ℕ) → Prop) [DecidablePred pr] {ι : Type*} (s : Finset ι)
    (F : ι → MvPolynomial σ k) :
    restrictSupport pr (∑ i ∈ s, F i) = ∑ i ∈ s, restrictSupport pr (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext β; simp [coeff_restrictSupport]
  | insert j s hj ih => rw [Finset.sum_insert hj, MvPolynomial.filterSupport_add, ih, Finset.sum_insert hj]

/-- Restriction to a set of monomials which is invariant under multiplication by the monomials of
`q` commutes with multiplication by `q`. -/
theorem _root_.MvPolynomial.filterSupport_mul_of_forall_support_add_iff [DecidableEq σ] (pr : (σ →₀ ℕ) → Prop) [DecidablePred pr]
    (c q : MvPolynomial σ k) (hq : ∀ β ∈ q.support, ∀ δ, pr (δ + β) ↔ pr δ) :
    restrictSupport pr (c * q) = restrictSupport pr c * q := by
  ext γ
  rw [coeff_restrictSupport, coeff_mul, coeff_mul]
  split_ifs with hγ
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hx := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    by_cases hx2 : x.2 ∈ q.support
    · rw [← hx, hq x.2 hx2] at hγ
      simp [coeff_restrictSupport, hγ]
    · rw [notMem_support_iff.mp hx2]; simp
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    by_cases hx2 : x.2 ∈ q.support
    · rw [← hx, hq x.2 hx2] at hγ
      simp [coeff_restrictSupport, hγ]
    · rw [notMem_support_iff.mp hx2]; simp

theorem _root_.MvPolynomial.filterSupport_eq_self_of_forall_mem_support (pr : (σ →₀ ℕ) → Prop) [DecidablePred pr] (F : MvPolynomial σ k)
    (hF : ∀ β ∈ F.support, pr β) : restrictSupport pr F = F := by
  ext β
  rw [coeff_restrictSupport]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hF β (mem_support_iff.mpr (Ne.symm hne)))

theorem _root_.MvPolynomial.IsHomogeneous.filterSupport (pr : (σ →₀ ℕ) → Prop) [DecidablePred pr]
    {F : MvPolynomial σ k} {n : ℕ} (hF : F.IsHomogeneous n) :
    (restrictSupport pr F).IsHomogeneous n := by
  intro β hβ
  rw [coeff_restrictSupport] at hβ
  split_ifs at hβ
  · exact hF hβ
  · exact absurd rfl hβ

end PolyHelpers

section Thm5Helpers

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {σ : Type*}

/-- Coefficientwise lift of a polynomial over `k = R/M` to `R`. -/
noncomputable def _root_.MvPolynomial.liftResidue (c : MvPolynomial σ (R ⧸ maximalIdeal R)) : MvPolynomial σ R :=
  ∑ δ ∈ c.support, monomial δ (TransformCoord.lift (c.coeff δ))

theorem _root_.MvPolynomial.coeff_liftResidue (c : MvPolynomial σ (R ⧸ maximalIdeal R)) (δ : σ →₀ ℕ) :
    (MvPolynomial.liftResidue c).coeff δ = TransformCoord.lift (c.coeff δ) := by
  classical
  rw [MvPolynomial.liftResidue, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, TransformCoord.lift_zero]

theorem _root_.MvPolynomial.support_liftResidue (c : MvPolynomial σ (R ⧸ maximalIdeal R)) :
    (MvPolynomial.liftResidue c).support = c.support := by
  ext δ
  rw [mem_support_iff, mem_support_iff, MvPolynomial.coeff_liftResidue]
  constructor
  · intro h h0; exact h (by rw [h0, TransformCoord.lift_zero])
  · intro h h0; exact h (by rw [← TransformCoord.mk_lift (c.coeff δ), h0, map_zero])

theorem _root_.MvPolynomial.map_mk_liftResidue (c : MvPolynomial σ (R ⧸ maximalIdeal R)) :
    (MvPolynomial.liftResidue c).map (Ideal.Quotient.mk _) = c := by
  ext δ
  rw [coeff_map, MvPolynomial.coeff_liftResidue, TransformCoord.mk_lift]

theorem _root_.MvPolynomial.IsHomogeneous.liftResidue {c : MvPolynomial σ (R ⧸ maximalIdeal R)} {n : ℕ}
    (hc : c.IsHomogeneous n) : (MvPolynomial.liftResidue c).IsHomogeneous n := by
  intro δ hδ
  apply hc
  rw [← mem_support_iff, ← MvPolynomial.support_liftResidue]
  exact mem_support_iff.mpr hδ

/-- The weight `0` on `x₀` and `1` on the other variables. -/
def weightNeNone {r s : ℕ} : CoordIndex r s → ℕ
  | none => 0
  | _ => 1

theorem weight_weightNeNone_add_apply_none {r s : ℕ} (δ : CoordIndex r s →₀ ℕ) :
    Finsupp.weight weightNeNone δ + δ none = δ.degree := by
  induction δ using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [map_add, map_add, Finsupp.add_apply, Finsupp.degree_single]
    have hw : Finsupp.weight weightNeNone (Finsupp.single a b) = b * weightNeNone a := by
      simp [Finsupp.weight_apply, Finsupp.sum_single_index]
    rw [hw]
    rcases a with _ | (i | j)
    · simp [weightNeNone]; omega
    · simp [weightNeNone]; omega
    · simp [weightNeNone]; omega

/-- The "outer part" (exponents of `x₀` and of the `y_j`) of a monomial. -/
def outerExponents {r s : ℕ} (δ : CoordIndex r s →₀ ℕ) : ℕ × (Fin s → ℕ) :=
  (δ none, fun j => δ (some (Sum.inr j)))

theorem outerExponents_add_of_isPure {r s : ℕ} (δ β : CoordIndex r s →₀ ℕ) (hβ : IsPure β) :
    outerExponents (δ + β) = outerExponents δ := by
  simp only [outerExponents, Finsupp.add_apply, hβ.1, hβ.2, add_zero]

/-- The numerical invariants of a monomial: `deg = P-deg + y-deg`, `P-deg = e₀ + x-deg`. -/
theorem degree_eq_pDeg_add_sum_and_pDeg_eq_none_add_xDeg {r s : ℕ} (δ : CoordIndex r s →₀ ℕ) :
    δ.degree = pDeg δ + ∑ j : Fin s, δ (some (Sum.inr j)) ∧
      pDeg δ = δ none + xDeg δ := by
  refine ⟨degree_eq_pDeg_add_sum δ, ?_⟩
  have := exponentShift_none_eq_pDeg δ
  rw [exponentShift, Finsupp.add_apply, Finsupp.single_eq_same] at this
  exact this.symm

end Thm5Helpers

section EHom

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

namespace TransformCoord

variable {T : MonoidalTransform R P} (C : TransformCoord T)

/-- `e` is graded: if `e(q)` is homogeneous of degree `d`, so is `q`. -/
theorem isHomogeneous_of_e_mem {q : MvPolynomial (CoordIndex C.r C.s) (R ⧸ maximalIdeal R)} {d : ℕ}
    (hq : C.e q ∈ AssocGraded.homogeneous (maximalIdeal R) d) : q.IsHomogeneous d := by
  classical
  have hhom : ∀ e', C.e (homogeneousComponent e' q) ∈ AssocGraded.homogeneous (maximalIdeal R) e' :=
    fun e' => AssocGraded.aeval_mem_homogeneous _ C.z C.z_mem (homogeneousComponent_isHomogeneous e' q)
  have hcomp : ∀ d', AssocGraded.proj _ d' (C.e q) = C.e (homogeneousComponent d' q) := by
    intro d'
    conv_lhs => rw [← sum_homogeneousComponent q, map_sum, map_sum]
    have hterm : ∀ e' ∈ Finset.range (q.totalDegree + 1),
        AssocGraded.proj _ d' (C.e (homogeneousComponent e' q)) =
          if e' = d' then C.e (homogeneousComponent d' q) else 0 := by
      intro e' _
      split_ifs with h
      · subst h; exact AssocGraded.proj_of_mem_homogeneous _ (hhom e')
      · exact AssocGraded.proj_of_mem_homogeneous_of_ne _ (hhom e') h
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    split_ifs with hd'
    · rfl
    · rw [Finset.mem_range, not_lt] at hd'
      rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]
  intro β hβ
  by_contra hne
  have hne' : β.degree ≠ d := by
    intro h; apply hne; rw [Finsupp.degree_eq_weight_one] at h; exact h
  have h0 : homogeneousComponent β.degree q = 0 := by
    apply C.e_bijective.1
    rw [← hcomp, map_zero]
    exact AssocGraded.proj_of_mem_homogeneous_of_ne _ hq (Ne.symm hne')
  have := congrArg (fun p : MvPolynomial _ _ => p.coeff β) h0
  simp only [coeff_homogeneousComponent, ↓reduceIte] at this
  exact hβ (by simpa using this)

end TransformCoord

end EHom

section Thm5Expansion

open MvPolynomial

/-- The exponent vector of the monomial `x₀^β x₁^{a₁}⋯x_r^{a_r} y₁^{γ₁}⋯y_s^{γ_s}`, where `(β, a)` is
encoded by `m : Option (Fin r) →₀ ℕ` (`m none = β`, `m (some i) = aᵢ`). -/
noncomputable def coordExponents {r s : ℕ} (m : Option (Fin r) →₀ ℕ) (γ : Fin s →₀ ℕ) : CoordIndex r s →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v =>
    match v with
    | none => m none
    | some (Sum.inl i) => m (some i)
    | some (Sum.inr j) => γ j

variable {r s : ℕ}

@[simp] theorem coordExponents_none (m : Option (Fin r) →₀ ℕ) (γ : Fin s →₀ ℕ) :
    coordExponents m γ none = m none := rfl

@[simp] theorem coordExponents_inl (m : Option (Fin r) →₀ ℕ) (γ : Fin s →₀ ℕ) (i : Fin r) :
    coordExponents m γ (some (Sum.inl i)) = m (some i) := rfl

@[simp] theorem coordExponents_inr (m : Option (Fin r) →₀ ℕ) (γ : Fin s →₀ ℕ) (j : Fin s) :
    coordExponents m γ (some (Sum.inr j)) = γ j := rfl

theorem coordExponents_injective {m m' : Option (Fin r) →₀ ℕ} {γ γ' : Fin s →₀ ℕ}
    (h : coordExponents m γ = coordExponents m' γ') : m = m' ∧ γ = γ' := by
  refine ⟨Finsupp.ext fun o => ?_, Finsupp.ext fun j => ?_⟩
  · rcases o with _ | i
    · simpa using congrArg (fun δ : CoordIndex r s →₀ ℕ => δ none) h
    · simpa using congrArg (fun δ : CoordIndex r s →₀ ℕ => δ (some (Sum.inl i))) h
  · simpa using congrArg (fun δ : CoordIndex r s →₀ ℕ => δ (some (Sum.inr j))) h

theorem coordExponents_eq_iff {m m' : Option (Fin r) →₀ ℕ} {γ γ' : Fin s →₀ ℕ} :
    coordExponents m γ = coordExponents m' γ' ↔ m = m' ∧ γ = γ' :=
  ⟨coordExponents_injective, fun h => by rw [h.1, h.2]⟩

theorem pDeg_coordExponents (m : Option (Fin r) →₀ ℕ) (γ : Fin s →₀ ℕ) :
    pDeg (coordExponents m γ) = m.degree := by
  simp [pDeg, Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option, Fintype.sum_sum_type,
    pWeight, Finsupp.degree_eq_sum]

theorem xDeg_coordExponents (m : Option (Fin r) →₀ ℕ) (γ : Fin s →₀ ℕ) :
    xDeg (coordExponents m γ) = ∑ i : Fin r, m (some i) := by
  simp [xDeg, Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option, Fintype.sum_sum_type,
    xWeight]

theorem degree_coordExponents (m : Option (Fin r) →₀ ℕ) (γ : Fin s →₀ ℕ) :
    (coordExponents m γ).degree = m.degree + γ.degree := by
  simp [Finsupp.degree_eq_sum, Fintype.sum_option, Fintype.sum_sum_type]
  ring

theorem monomialVal_coordExponents {B : Type*} [CommMonoid B] (z : CoordIndex r s → B)
    (m : Option (Fin r) →₀ ℕ) (γ : Fin s →₀ ℕ) :
    monomialVal z (coordExponents m γ) =
      (z none ^ m none * ∏ i : Fin r, z (some (Sum.inl i)) ^ m (some i)) *
        ∏ j : Fin s, z (some (Sum.inr j)) ^ γ j := by
  rw [monomialVal, Finsupp.prod_fintype _ _ (fun v => pow_zero _)]
  simp [Fintype.prod_option, Fintype.prod_sum_type, mul_assoc]

end Thm5Expansion

section Thm5Core

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

namespace TransformCoord

variable {T : MonoidalTransform R P} (C : TransformCoord T) [IsRegularLocalRing T.ring]

omit [IsRegularLocalRing T.ring] in
include C in
/-- The center `P = (x₀, x₁, …, x_r)R` of a coordinate system lies in the maximal ideal. -/
theorem center_le_maximalIdeal : P ≤ maximalIdeal R := by
  rw [C.hP, Ideal.span_le]
  rintro _ (h | ⟨i, rfl⟩)
  · rw [Set.mem_singleton_iff.mp h]
    simpa [TransformCoord.z, coordFamily] using C.z_mem none
  · simpa [TransformCoord.z, coordFamily] using C.z_mem (some (Sum.inl i))

omit [IsRegularLocalRing T.ring] in
/-- The coefficients of the expansion of `f` on p. 240: "where `c_{(a)β} ∈ (y₁, …, y_s)^{t_{(a)β}} R`
with `t_{(a)β} = ν_M(c_{(a)β})`".  The paper does not say why such coefficients exist.  Here: every class
`q` of `R/P` has a representative `c = K(y₁, …, y_s)`, with `K` a form of some degree `t` in
`y₁, …, y_s` having a coefficient outside `M` (so that `c ∈ (y₁, …, y_s)^t R` and `ν_M(c) = t`), and
`K = 0` for `q = 0`.  Proof: `q ≠ 0` lies in `M̄^t ∖ M̄^{t+1}` for some `t` (Krull's intersection
theorem in `R/P`), and `M̄^t` is the image of `(y₁, …, y_s)^t R`, because `M = (y₁, …, y_s)R + P`. -/
theorem exists_isHomogeneous_eval_eq_mk (q : R ⧸ P) :
    ∃ (t : ℕ) (K : MvPolynomial (Fin C.s) R), K.IsHomogeneous t ∧
      (K ≠ 0 → ∃ γ, K.coeff γ ∉ maximalIdeal R) ∧ (q = 0 → K = 0) ∧
      Ideal.Quotient.mk P (eval C.y K) = q := by
  classical
  by_cases hq : q = 0
  · exact ⟨0, 0, isHomogeneous_zero _ _ _, fun h => absurd rfl h, fun _ => rfl, by simp [hq]⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hrP : r ∉ P := fun h => hq (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  set Iy : Ideal R := Ideal.span (Set.range C.y) with hIy
  have hPM : P ≤ maximalIdeal R := C.center_le_maximalIdeal
  have hPne : P ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hPM
  -- Krull's intersection theorem: `r ∉ P ⊔ Mⁿ` for some `n`
  have hex : ∃ n : ℕ, r ∉ P ⊔ maximalIdeal R ^ n := by
    by_contra h
    push Not at h
    refine hrP ?_
    have : IsLocalRing (R ⧸ P) := isLocalRing_quotient_of_le hPM
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (R ⧸ P))
      (Ideal.IsPrime.ne_top inferInstance)
    have hmem : Ideal.Quotient.mk P r ∈ ⨅ n : ℕ, maximalIdeal (R ⧸ P) ^ n := by
      rw [Ideal.mem_iInf]
      intro n
      rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk P)
        Ideal.Quotient.mk_surjective, ← Ideal.map_pow, Ideal.mem_quotient_iff_mem_sup]
      simpa [sup_comm] using h n
    rw [hbot, Ideal.mem_bot] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmem
  let n₀ := Nat.find hex
  have hn₀ : r ∉ P ⊔ maximalIdeal R ^ n₀ := Nat.find_spec hex
  have hn₀pos : n₀ ≠ 0 := fun h => hn₀ (by rw [h]; simp)
  obtain ⟨t, ht⟩ : ∃ t, n₀ = t + 1 := Nat.exists_eq_succ_of_ne_zero hn₀pos
  have hrt : r ∈ P ⊔ maximalIdeal R ^ t := by
    by_contra h
    exact Nat.find_min hex (show t < n₀ by omega) h
  -- `M = (y) + P` and `Mᵗ ⊆ (y)ᵗ + P`
  have hM : maximalIdeal R ≤ Iy ⊔ P := by
    rw [← C.span_z, Ideal.span_le]
    rintro _ ⟨v, rfl⟩
    rcases v with _ | (i | j)
    · exact Ideal.mem_sup_right (by simpa [TransformCoord.z, coordFamily] using C.x₀_mem)
    · exact Ideal.mem_sup_right (by simpa [TransformCoord.z, coordFamily] using C.x_mem i)
    · exact Ideal.mem_sup_left (Ideal.subset_span ⟨j, by simp [TransformCoord.z, coordFamily]⟩)
  have hpow : ∀ n : ℕ, maximalIdeal R ^ n ≤ Iy ^ n ⊔ P := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      refine (Ideal.mul_mono ih hM).trans (Ideal.mul_le.mpr fun a ha b hb => ?_)
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hb
      have h1 : a₁ * b₁ ∈ Iy ^ (n + 1) := by rw [pow_succ]; exact Ideal.mul_mem_mul ha₁ hb₁
      have h2 : a₁ * b₂ + a₂ * b₁ + a₂ * b₂ ∈ P :=
        add_mem (add_mem (Ideal.mul_mem_left _ _ hb₂) (Ideal.mul_mem_right _ _ ha₂))
          (Ideal.mul_mem_left _ _ hb₂)
      have : (a₁ + a₂) * (b₁ + b₂) = a₁ * b₁ + (a₁ * b₂ + a₂ * b₁ + a₂ * b₂) := by ring
      rw [this]
      exact add_mem (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
  obtain ⟨p₁, hp₁, m, hm, hrpm⟩ := Submodule.mem_sup.mp hrt
  obtain ⟨c, hc, p₂, hp₂, hmcp⟩ := Submodule.mem_sup.mp (hpow t hm)
  obtain ⟨K, hK, hKc⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous C.y c).mp hc
  have hunit : ∃ γ, K.coeff γ ∉ maximalIdeal R := by
    by_contra h
    push Not at h
    have h1 := eval_mem_mul_span_pow_of_coeff_mem (y := C.y) hK h
    rw [hKc] at h1
    have h2 : c ∈ maximalIdeal R ^ (t + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mono_right (by
        exact Ideal.pow_right_mono (by
          rw [Ideal.span_le]
          rintro _ ⟨j, rfl⟩
          exact C.hM ▸ Ideal.subset_span ⟨some (Sum.inr j), by simp [coordFamily]⟩) t)
        h1
    refine hn₀ ?_
    rw [ht]
    refine Submodule.mem_sup.mpr ⟨p₁ + p₂, add_mem hp₁ hp₂, c, h2, ?_⟩
    rw [← hrpm, ← hmcp]; ring
  refine ⟨t, K, hK, fun _ => hunit, fun h => absurd h hq, ?_⟩
  rw [hKc, Ideal.Quotient.eq]
  have : r - c = p₁ + p₂ := by rw [← hrpm, ← hmcp]; ring
  rw [← neg_sub, this]
  exact neg_mem (add_mem hp₁ hp₂)

omit [IsRegularLocalRing T.ring] in
/-- **The expansion of `f` on p. 240**: "In fact, we write `f` in the form
`f = (∑_{(a),β} c_{(a)β} x^β x₁^{a₁}⋯x_r^{a_r}) + f'`, where `c_{(a)β} ∈ (y₁, …, y_s)^{t_{(a)β}} R` with
`t_{(a)β} = ν_M(c_{(a)β})` and `f' ∈ P^{ν+μ₁+1}`", for `f ∈ P^ν`; "The assumption `ν_P(f) ≥ ν` implies
that `β + a₁ + ⋯ + a_r ≥ ν` for all `((a), β)`." (The latter holds for any expansion whose coefficients
`c_{(a)β}` are nonzero modulo `P`, because `gr_P(R)` is a polynomial ring over `R/P`; here the
expansion is constructed starting from `f ∈ P^ν`, so that it holds by construction, and the existence
of the expansion, not argued in the paper, is part of the statement.)

Encoding: the expansion is a polynomial `G` in all the coordinates `x₀, x₁, …, x_r, y₁, …, y_s`; the
coefficient `c_{(a)β}` is the value at `y` of a form `K` of degree `t_{(a)β}` in `y₁, …, y_s` (so
`c_{(a)β} ∈ (y)^{t_{(a)β}} R`), the monomials of `c_{(a)β} x^β x^a` being those of `G` with the exponents
`(β, a)` on `x₀, x₁, …, x_r`; `ν_M(c_{(a)β}) = t_{(a)β}` says that some coefficient of `K` is not in `M`.
The statement gives `n` in place of `ν + μ₁ + 1`; the three properties are
`f - G(x₀, x, y) ∈ Pⁿ`, "`β + a₁ + ⋯ + a_r ≥ ν`" (the `P`-degree `pDeg`), and `ν_M(c_{(a)β}) = t_{(a)β}`
(each monomial of `G` has, in its block `(β, a)`, a monomial of the same degree and weight whose
coefficient is outside `M`). -/
theorem exists_pAdicExpansion (F : R) (N n : ℕ) (hF : F ∈ P ^ N) (hNn : N ≤ n) :
    ∃ G : MvPolynomial (CoordIndex C.r C.s) R,
      F - eval C.z G ∈ P ^ n ∧ (∀ δ ∈ G.support, N ≤ pDeg δ) ∧
        ∀ δ ∈ G.support, ∃ δ' ∈ G.support, G.coeff δ' ∉ maximalIdeal R ∧
          δ'.degree = δ.degree ∧ C.wt δ' = C.wt δ := by
  classical
  choose t K hK using C.exists_isHomogeneous_eval_eq_mk
  let liftP : R ⧸ P → R := fun q => eval C.y (K q)
  have hlift : ∀ q, Ideal.Quotient.mk P (liftP q) = q := fun q => (hK q).2.2.2
  have hlift0 : liftP 0 = 0 := by
    show eval C.y (K 0) = 0
    rw [(hK 0).2.2.1 rfl, map_zero]
  let z' : Option (Fin C.r) → R := fun o => o.elim C.x₀ C.x
  have hz' : Ideal.span (Set.range z') = P := by
    have hr : Set.range z' = {C.x₀} ∪ Set.range C.x := by
      ext w
      simp [z', Set.mem_range, Option.exists, eq_comm]
    rw [hr]
    exact C.hP.symm
  obtain ⟨E, hEc, hEs, hEr⟩ := exists_eval_sub_mem_pow P z' hz' liftP hlift hlift0 F N hF n hNn
  -- the forms `K_m` representing the coefficients of `E`
  let Km : (Option (Fin C.r) →₀ ℕ) → MvPolynomial (Fin C.s) R :=
    fun m => K (Ideal.Quotient.mk P (E.coeff m))
  have hEK : ∀ m, E.coeff m = eval C.y (Km m) := by
    intro m
    obtain ⟨q, hq⟩ := hEc m
    have : Ideal.Quotient.mk P (E.coeff m) = q := by rw [← hq]; exact hlift q
    show E.coeff m = eval C.y (K (Ideal.Quotient.mk P (E.coeff m)))
    rw [this, ← hq]
  have hKm : ∀ m, (Km m).IsHomogeneous (t (Ideal.Quotient.mk P (E.coeff m))) := fun m => (hK _).1
  let G : MvPolynomial (CoordIndex C.r C.s) R :=
    ∑ m ∈ E.support, ∑ γ ∈ (Km m).support, monomial (coordExponents m γ) ((Km m).coeff γ)
  have hGcoeff : ∀ m ∈ E.support, ∀ γ, G.coeff (coordExponents m γ) = (Km m).coeff γ := by
    intro m hm γ
    simp only [G, coeff_sum, coeff_monomial, coordExponents_eq_iff]
    rw [Finset.sum_eq_single m]
    · rw [Finset.sum_eq_single γ]
      · simp
      · intro γ' _ hγ'
        simp [hγ']
      · intro hγ
        simp [notMem_support_iff.mp hγ]
    · intro m' _ hm'
      refine Finset.sum_eq_zero fun γ' _ => ?_
      simp [hm']
    · intro h; exact absurd hm h
  have hGsupp : ∀ δ ∈ G.support, ∃ m ∈ E.support, ∃ γ ∈ (Km m).support, δ = coordExponents m γ := by
    intro δ hδ
    have h0 : G.coeff δ ≠ 0 := mem_support_iff.mp hδ
    simp only [G, coeff_sum, coeff_monomial] at h0
    obtain ⟨m, hm, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    obtain ⟨γ, hγ, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    refine ⟨m, hm, γ, hγ, ?_⟩
    by_contra hne
    exact h2 (by simp [Ne.symm hne])
  -- (P1) `G(x₀, x, y) = E(x₀, x)`
  have hGeval : eval C.z G = eval z' E := by
    have h1 : ∀ m, ∑ γ ∈ (Km m).support, (Km m).coeff γ * monomialVal C.z (coordExponents m γ) =
        (C.x₀ ^ m none * ∏ i : Fin C.r, C.x i ^ m (some i)) * E.coeff m := by
      intro m
      rw [hEK m, eval_eq' C.y (Km m), Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [monomialVal_coordExponents]
      simp only [TransformCoord.z, coordFamily]
      ring
    simp only [G, map_sum, eval_monomial_eq_mul_monomialVal]
    rw [Finset.sum_congr rfl fun m _ => h1 m, eval_eq' z' E]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [z', Fintype.prod_option, Option.elim]
    ring
  have hKunit : ∀ m ∈ E.support, ∃ γ ∈ (Km m).support, (Km m).coeff γ ∉ maximalIdeal R := by
    intro m hm
    have hne : Km m ≠ 0 := by
      intro h0
      apply mem_support_iff.mp hm
      rw [hEK m, h0, map_zero]
    obtain ⟨γ, hγ⟩ := (hK _).2.1 hne
    exact ⟨γ, mem_support_iff.mpr fun h0 => hγ (h0 ▸ zero_mem _), hγ⟩
  refine ⟨G, by rw [hGeval]; exact hEr, fun δ hδ => ?_, fun δ hδ => ?_⟩
  · obtain ⟨m, hm, γ, -, rfl⟩ := hGsupp δ hδ
    rw [pDeg_coordExponents]
    exact (hEs m hm).1
  · obtain ⟨m, hm, γ, hγ, rfl⟩ := hGsupp δ hδ
    obtain ⟨γ', hγ', hγ'M⟩ := hKunit m hm
    have hdeg : γ'.degree = γ.degree := by
      rw [degree_eq_of_isHomogeneous_of_coeff_ne_zero (hKm m) (mem_support_iff.mp hγ'),
        degree_eq_of_isHomogeneous_of_coeff_ne_zero (hKm m) (mem_support_iff.mp hγ)]
    have hcoef : G.coeff (coordExponents m γ') = (Km m).coeff γ' := hGcoeff m hm γ'
    refine ⟨coordExponents m γ', mem_support_iff.mpr (by rw [hcoef]; exact mem_support_iff.mp hγ'), by
      rw [hcoef]; exact hγ'M, by rw [degree_coordExponents, degree_coordExponents, hdeg], ?_⟩
    simp only [TransformCoord.wt, degree_exponentShift, xDeg_coordExponents, degree_coordExponents, hdeg]

omit [IsRegularLocalRing T.ring] in
/-- p. 240: "Then we have `t_{(a)β} + β + a₁ + ⋯ + a_r ≥ μ` for all `((a), β)` and, since
`f' ∈ M^{ν+μ₁+1} ⊆ M^{μ+1}`, the initial form `φ` is the sum of those `c̄_{(a)β} X^β X₁^{a₁}⋯X_r^{a_r}`
such that `t_{(a)β} + β + a₁ + ⋯ + a_r = μ`".  In the encoding by a polynomial `G` in all the
coordinates (see `exists_pAdicExpansion`): if the lowest-degree monomials of `G` have degree `W` and one
of them has a coefficient outside `M`, then `G(x₀, x, y) ∉ M^{W+1}` (the class of `G(x₀, x, y)` in degree
`W` is the reduction of the part of `G` of degree `W`, and `gr_M(R)` is the polynomial ring `k[X, X₁, …, X_r, Y]`). -/
theorem eval_notMem_pow_succ_of_coeff_notMem (G : MvPolynomial (CoordIndex C.r C.s) R) (W : ℕ)
    (hG : ∀ δ ∈ G.support, W ≤ δ.degree) (δ₀ : CoordIndex C.r C.s →₀ ℕ) (hδ₀ : δ₀.degree = W)
    (hunit : G.coeff δ₀ ∉ maximalIdeal R) : eval C.z G ∉ maximalIdeal R ^ (W + 1) := by
  intro hmem
  have h := mk_eval_eq_aeval C.z C.z_mem C.span_z G W hG
  have h0 := (AssocGraded.mk_eq_zero_iff (maximalIdeal R)
    (eval_mem_pow_of_le_degree _ C.z C.span_z G W hG)).mpr hmem
  rw [h] at h0
  have h2 : C.e ((homogeneousComponent W G).map (Ideal.Quotient.mk _)) = C.e 0 :=
    h0.trans (map_zero C.e).symm
  have h3 := congrArg (fun p : MvPolynomial _ _ => p.coeff δ₀) (C.e_bijective.1 h2)
  simp only [coeff_map, coeff_homogeneousComponent, hδ₀, ↓reduceIte] at h3
  exact hunit (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h3))

/-- p. 240: "If we write `β'` for `β + a₁ + ⋯ + a_r - ν` for each `((a), β)`, then
`g = (∑ c_{(a)β} x^{β'} (x₁/x)^{a₁}⋯(x_r/x)^{a_r}) + x^{-ν} f'`.  Since `x^{-ν} f' ∈ M₁^{μ₁+1}`, the
assumption `μ₁ = ν_{M₁}(g)` implies that `t_{(a)β} + β' + a₁ + ⋯ + a_r ≥ μ₁` for all `((a), β)`, i.e. `(*)`".
The same computation as `eval_notMem_pow_succ_of_coeff_notMem`, in `R₁` with the coordinates
`(x, x₁/x, …, x_r/x, y)`: the monomial `x₀^β x^a y^γ` becomes `x₀^{β+|a|} (x/x₀)^a y^γ`, of weight
`β + 2|a| + |γ|` (`x₀, y_j` of weight `1`, `x_i` of weight `2`).  If every monomial of `G` has weight at least `W`
and one monomial of weight `W` has a coefficient outside `M`, then `G(x₀, x, y) ∉ M₁^{W+1}` in `R₁`. -/
theorem toRing_eval_notMem_pow_succ_of_coeff_notMem (G : MvPolynomial (CoordIndex C.r C.s) R) (W : ℕ)
    (hG : ∀ δ ∈ G.support, W ≤ C.wt δ) (δ₀ : CoordIndex C.r C.s →₀ ℕ) (hδ₀ : C.wt δ₀ = W)
    (hunit : G.coeff δ₀ ∉ maximalIdeal R) :
    T.toRing (eval C.z G) ∉ maximalIdeal T.ring ^ (W + 1) := by
  intro hmem
  have hmk := C.mk_toRing_of_expansion (eval C.z G) G W (by simp) W le_rfl hG
  have h0 := (AssocGraded.mk_eq_zero_iff (maximalIdeal T.ring)
    (C.toRing_mem_pow_of_expansion (eval C.z G) G W (by simp) W (by omega) hG)).mpr hmem
  rw [hmk] at h0
  have h2 : C.e₁ ((homogeneousComponent W (C.Φ G)).map (Ideal.Quotient.mk _)) = C.e₁ 0 :=
    h0.trans (map_zero C.e₁).symm
  have h3 := congrArg (fun p : MvPolynomial _ _ => p.coeff (exponentShift δ₀)) (C.e₁_bijective.1 h2)
  simp only [coeff_map, coeff_homogeneousComponent, TransformCoord.wt] at h3 hδ₀
  rw [hδ₀] at h3
  simp only [↓reduceIte] at h3
  rw [coeff_transformPoly_exponentShift] at h3
  have h4 : T.toRing (G.coeff δ₀) ∈ maximalIdeal T.ring :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h3)
  exact hunit ((IsLocalHom.map_mem_maximalIdeal_iff T.toRing _).mp h4)

/-- p. 239: "this process cannot be repeated infinitely, for the number `ν_M(f)` will be then made
arbitrarily big while it should be bounded by `ν_{M₁}(g) + ν = μ₁ + ν`" (also used on p. 240 for
"`f' ∈ M^{ν+μ₁+1} ⊆ M^{μ+1}`").  If `x₀ᴺ a = f` in `R₁` and `ν_M(f) ≥ N + μ₁ + 1`, then
`ν_{M₁}(a) ≥ μ₁ + 1`: `ν_M(f) ≤ ν_{M₁}(f) = N + ν_{M₁}(a)`. -/
theorem mem_pow_succ_of_le_ordElem (N μ₁ : ℕ) (F : R) (a : T.ring) (hFa : C.x₁ ^ N * a = T.toRing F)
    (hbig : ((N + μ₁ + 1 : ℕ) : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) F) :
    a ∈ maximalIdeal T.ring ^ (μ₁ + 1) := by
  have hF : F ∈ maximalIdeal R ^ (N + μ₁ + 1) := Ideal.mem_pow_of_le_ordElem hbig
  have hF₁ : T.toRing F ∈ maximalIdeal T.ring ^ (N + μ₁ + 1) := by
    have := Ideal.mem_map_of_mem T.toRing hF
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono (map_maximalIdeal_le T.toRing) _ this
  have h1 := Ideal.le_ordElem hF₁
  rw [← hFa, ordElem_mul_maximalIdeal, C.ordElem_x₁_pow] at h1
  refine Ideal.mem_pow_of_le_ordElem ?_
  by_cases htop : Ideal.ordElem (maximalIdeal T.ring) a = ⊤
  · rw [htop]; exact le_top
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hk] at h1 ⊢
    have : N + μ₁ + 1 ≤ N + k := by exact_mod_cast h1
    exact_mod_cast (by omega : μ₁ + 1 ≤ k)

/-- **The element `h` of the proof of Theorem 5** (pp. 239--241): "We shall prove the existence of an
element `h ∈ J` with the properties (1)--(4) for a given element `f ∈ J` such that `ν_P(f) ≥ ν > 0`":
(1) `ν_P(h) ≥ ν`, (2) `ν_M(f - h) > μ`, (3) `ν_{M₁}(g - x^{-ν}h) ≥ μ₁`, and (4) the initial form of
`x^{-ν}h` in `gr_{M₁}(R₁)` is in `I` if `ν_{M₁}(x^{-ν}h) = μ₁`; here `F = f` is in `J` with `ν_P(F) ≥ N`
(`N` is the printed `ν`), `μ = ν_M(F)`, `a = g = x₀^{-N} F` with `μ₁ = ν_{M₁}(a)`, and `h`, `a' = x₀^{-N} h` are
as printed.  (3) and (4) are stated as: `a' ∈ M₁^{μ₁}` (so that `ν_{M₁}(g - a') ≥ μ₁`), and the class of `a'` in
degree `μ₁` lies in `I = (ψ₁, …, ψ_m)`.

The proof follows the printed one:
* the expansion `f = Σ c_{(a)β} x^β x^a + f'` with `f' ∈ P^{ν+μ₁+1}` (`exists_pAdicExpansion`), where
  `ν_M(f) ≤ ν_{M₁}(f) = ν + μ₁`, so `f' ∈ M^{ν+μ₁+1} ⊆ M^{μ+1}` (`mem_pow_succ_of_le_ordElem`);
* "`t_{(a)β} + β + a₁ + ⋯ + a_r ≥ μ`" and "the initial form `φ` is the sum of those `c̄_{(a)β} X^β X^a`
  such that `t_{(a)β} + β + a₁ + ⋯ + a_r = μ`" (`eval_notMem_pow_succ_of_coeff_notMem`);
* "`β + a₁ + ⋯ + a_r ≥ ν`" (by construction) and `(*)` (`toRing_eval_notMem_pow_succ_of_coeff_notMem`), which
  give the claimed inequalities on the monomials `X^β T_α(Y) X^a` of `φ` (`hpPD`: `P`-degree `≥ ν` and
  weight `≥ ν + μ₁`);
* "`φ` belongs to `gr_M(J, R) = (φ₁, …, φ_m) gr_M(R)`, and the `φ_i` are forms only in `X₁, …, X_r`.
  Therefore we can write `ξ_{αβ} = Σ_i ξ_{αβi} φ_i`": the comparison of the coefficients of `X^β T_α(Y)`
  is done for all `(α, β)` at once, by restricting `φ = Σ_i c'_i φ_i` to the monomials with the outer
  parts `(β, T_α)` occurring in `φ` (`restrictSupport`) and taking the homogeneous component of degree
  `μ - ν_i`; the `h_{αβi}` are lifts of the `ξ_{αβi}` with coefficients in the fixed set of representatives
  of `k` (`H_i`), and `h = Σ_i H_i f_i` is the printed `h` grouped by `i`;
* (1) from `ν_P(f_i) ≥ ν_i` (hypothesis (ii)) and the inequality `P`-degree `≥ ν`, (2) from "`h` has the same
  initial form as `f`", and (3), (4) from the expression `x^{-ν}h = Σ h'_{αβi} g_i x^{β''} T_α(y)`
  (`A_i`) and `(*)`. -/
theorem exists_mem_ideal_sub_mem_pow_succ (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing)
    (J : Ideal R) {m : ℕ} (f : Fin m → R) (hf : IsStandardBase R J f) (ν : Fin m → ℕ)
    (hfM : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = ν j)
    (hfP : ∀ j, (ν j : ℕ∞) ≤ Ideal.ordElem P (f j)) (g : Fin m → T.ring)
    (hg : ∀ j, C.x₁ ^ ν j * g j = T.toRing (f j))
    (hgM : ∀ j, Ideal.ordElem (maximalIdeal T.ring) (g j) = ν j) (N μ₁ : ℕ)
    (F : R) (hFJ : F ∈ J) (hFP : (N : ℕ∞) ≤ Ideal.ordElem P F) (a : T.ring)
    (hFa : C.x₁ ^ N * a = T.toRing F) (ha : Ideal.ordElem (maximalIdeal T.ring) a = μ₁) (μ : ℕ)
    (hμ : Ideal.ordElem (maximalIdeal R) F = μ) :
    ∃ (h : R) (a' : T.ring), h ∈ J ∧ (N : ℕ∞) ≤ Ideal.ordElem P h ∧
      F - h ∈ maximalIdeal R ^ (μ + 1) ∧ C.x₁ ^ N * a' = T.toRing h ∧
      ∃ ha' : a' ∈ maximalIdeal T.ring ^ μ₁,
        AssocGraded.mk (maximalIdeal T.ring) μ₁ a' ha' ∈
          Ideal.span (Set.range fun j => initialForm (maximalIdeal T.ring) (g j)) := by
  classical
  set I₁ := Ideal.span (Set.range fun j => initialForm (maximalIdeal T.ring) (g j)) with hI₁
  have hFμ : F ∈ maximalIdeal R ^ μ := Ideal.mem_pow_of_ordElem hμ
  have haμ₁ : a ∈ maximalIdeal T.ring ^ μ₁ := Ideal.mem_pow_of_ordElem ha
  have hx₁M : C.x₁ ∈ maximalIdeal T.ring := by simpa [z₁_none] using C.z₁_mem none
  -- "`ν_M(f)` is bounded by `ν_{M₁}(g) + ν = μ₁ + ν`", so that `M^{ν+μ₁+1} ⊆ M^{μ+1}`
  have hμle : μ ≤ N + μ₁ := by
    by_contra hlt
    have h1 := Ideal.le_ordElem (C.mem_pow_succ_of_le_ordElem N μ₁ F a hFa (by
      rw [hμ]; exact_mod_cast (by omega : N + μ₁ + 1 ≤ μ)))
    rw [ha] at h1
    have : μ₁ + 1 ≤ μ₁ := by exact_mod_cast h1
    omega
  -- the expansion of `f` (p. 240) with `n = ν + μ₁ + 1`
  obtain ⟨G, hGr, hGP, hGu⟩ := C.exists_pAdicExpansion F N (N + μ₁ + 1)
    (Ideal.mem_pow_of_le_ordElem hFP) (by omega)
  have hGrM : F - eval C.z G ∈ maximalIdeal R ^ (μ + 1) :=
    Ideal.pow_le_pow_right (by omega)
      (Ideal.pow_right_mono C.center_le_maximalIdeal _ hGr)
  have hGM : eval C.z G ∈ maximalIdeal R ^ μ := by
    have : eval C.z G = F - (F - eval C.z G) := by ring
    rw [this]
    exact sub_mem hFμ (Ideal.pow_le_pow_right (by omega) hGrM)
  -- "`t_{(a)β} + β + a₁ + ⋯ + a_r ≥ μ` for all `((a), β)`"
  have hGdeg : ∀ δ ∈ G.support, μ ≤ δ.degree := by
    by_contra hcon
    push Not at hcon
    obtain ⟨δ₁, hδ₁, hlt⟩ := hcon
    obtain ⟨δ₀, hδ₀, hmin⟩ := G.support.exists_min_image (fun δ => δ.degree) ⟨δ₁, hδ₁⟩
    obtain ⟨δ', -, hunit, hdeg, -⟩ := hGu δ₀ hδ₀
    exact C.eval_notMem_pow_succ_of_coeff_notMem G δ₀.degree hmin δ' hdeg hunit
      (Ideal.pow_le_pow_right (by have := hmin δ₁ hδ₁; omega) hGM)
  set p := (homogeneousComponent μ G).map (Ideal.Quotient.mk (maximalIdeal R)) with hpdef
  have hinit : initialForm (maximalIdeal R) F = C.e p :=
    (initialForm_eq_mk _ hμ).trans (C.mk_eq_e_of_expansion F μ hFμ G μ le_rfl hGdeg hGrM)
  have hp_supp : ∀ γ ∈ p.support, γ ∈ G.support ∧ γ.degree = μ := by
    intro γ hγ
    rw [mem_support_iff] at hγ
    simp only [p, coeff_map, coeff_homogeneousComponent] at hγ
    split_ifs at hγ with hd
    · exact ⟨mem_support_iff.mpr fun h0 => hγ (by rw [h0, map_zero]), hd⟩
    · exact absurd (map_zero _) hγ
  have hphom : p.IsHomogeneous μ := (homogeneousComponent_isHomogeneous μ G).map _
  -- "`T(F) ∈ M₁^{N+μ₁}`": `T(f') ∈ (x₀)^{ν+μ₁+1}`
  have hTG : T.toRing (eval C.z G) ∈ maximalIdeal T.ring ^ (N + μ₁) := by
    have h1 : T.toRing F ∈ maximalIdeal T.ring ^ (N + μ₁) := by
      rw [← hFa, pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hx₁M N) haμ₁
    have h2 : T.toRing (F - eval C.z G) ∈ maximalIdeal T.ring ^ (N + μ₁) := by
      obtain ⟨a'', ha''⟩ := C.exists_pow_mul_eq_of_mem_pow hGr
      rw [← ha'']
      exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow hx₁M _))
    have : T.toRing (eval C.z G) = T.toRing F - T.toRing (F - eval C.z G) := by
      rw [map_sub]; ring
    rw [this]
    exact sub_mem h1 h2
  -- "(*) `2(a₁ + ⋯ + a_r) + β + t_{(a)β} ≥ ν + μ₁` for all `((a), β)`"
  have hGwt : ∀ δ ∈ G.support, N + μ₁ ≤ C.wt δ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨δ₁, hδ₁, hlt⟩ := hcon
    obtain ⟨δ₀, hδ₀, hmin⟩ := G.support.exists_min_image C.wt ⟨δ₁, hδ₁⟩
    obtain ⟨δ', -, hunit, -, hwt⟩ := hGu δ₀ hδ₀
    exact C.toRing_eval_notMem_pow_succ_of_coeff_notMem G (C.wt δ₀) hmin δ' hwt hunit
      (Ideal.pow_le_pow_right (by have := hmin δ₁ hδ₁; omega) hTG)
  -- the inequalities `P-deg ≥ N` and `weight ≥ N + μ₁` for the monomials of `φ`
  have hpPD : ∀ γ ∈ p.support, N ≤ pDeg γ ∧ N + μ₁ ≤ C.wt γ := fun γ hγ =>
    ⟨hGP γ (hp_supp γ hγ).1, hGwt γ (hp_supp γ hγ).1⟩
  -- the pure forms `p_j` of the initial forms of the `f_j`
  have hpj : ∀ j, ∃ pj, C.e pj = initialForm (maximalIdeal R) (f j) ∧
      ∀ β ∈ pj.support, IsPure β := fun j =>
    ((C.ordElem_le_and_rho_initialForm_eq hrat (f j) (ν j) (hfM j) (g j) (hg j)).2 (hgM j)).1
  choose pj hpje hpjpure using hpj
  have hpjhom : ∀ j, (pj j).IsHomogeneous (ν j) := by
    intro j
    apply C.isHomogeneous_of_e_mem
    rw [hpje, initialForm_eq_mk _ (hfM j)]
    exact AssocGraded.mk_mem_homogeneous _ _
  -- `p ∈ (p_j)`
  set eE := RingEquiv.ofBijective C.e C.e_bijective with heE
  have hpspan : p ∈ Ideal.span (Set.range pj) := by
    have h1 : initialForm (maximalIdeal R) F ∈ grIdeal (maximalIdeal R) J :=
      Ideal.subset_span ⟨F, hFJ, rfl⟩
    rw [hf.2.2.2.1, hinit] at h1
    have h2 := Ideal.mem_map_of_mem eE.symm.toRingHom h1
    rw [Ideal.map_span] at h2
    have h3 : eE.symm.toRingHom (C.e p) = p := eE.symm_apply_apply p
    rw [h3] at h2
    refine (Ideal.span_mono ?_) h2
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    refine ⟨j, ?_⟩
    show pj j = eE.symm (initialForm (maximalIdeal R) (f j))
    rw [← hpje j]
    exact (eE.symm_apply_apply (pj j)).symm
  obtain ⟨c', hc'⟩ := Ideal.mem_span_range_iff_exists_fun.mp hpspan
  -- restrict to the outer parts of `p` and take homogeneous components
  set pr : (CoordIndex C.r C.s →₀ ℕ) → Prop := fun δ => ∃ γ ∈ p.support, outerExponents γ = outerExponents δ
    with hprdef
  have hprpure : ∀ j, ∀ β ∈ (pj j).support, ∀ δ, pr (δ + β) ↔ pr δ := by
    intro j β hβ δ
    simp only [pr, outerExponents_add_of_isPure δ β (hpjpure j β hβ)]
  let c : Fin m → MvPolynomial (CoordIndex C.r C.s) (R ⧸ maximalIdeal R) := fun j =>
    if ν j ≤ μ then homogeneousComponent (μ - ν j) (restrictSupport pr (c' j)) else 0
  have hcsum : ∑ j, c j * pj j = p := by
    have h1 : restrictSupport pr p = p := MvPolynomial.filterSupport_eq_self_of_forall_mem_support pr p fun γ hγ => ⟨γ, hγ, rfl⟩
    have h2' : restrictSupport pr (∑ j, c' j * pj j) = ∑ j, restrictSupport pr (c' j) * pj j := by
      rw [MvPolynomial.filterSupport_sum]
      exact Finset.sum_congr rfl fun j _ => MvPolynomial.filterSupport_mul_of_forall_support_add_iff pr _ _ (hprpure j)
    have h2 : p = ∑ j, restrictSupport pr (c' j) * pj j := by
      rw [hc'] at h2'
      exact h1.symm.trans h2'
    have h3 : p = homogeneousComponent μ p := by
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hphom)]
      simp
    rw [h3, h2, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.homogeneousComponent_mul_of_isHomogeneous _ _ (hpjhom j)]
    simp only [c]
    split_ifs <;> simp
  have hchom : ∀ j, (c j).IsHomogeneous (μ - ν j) := by
    intro j
    simp only [c]
    split_ifs
    · exact homogeneousComponent_isHomogeneous _ _
    · exact isHomogeneous_zero _ _ _
  -- the numerical properties of the monomials of the `c_j`
  have hcsupp : ∀ j, ∀ δ ∈ (c j).support, ν j ≤ μ ∧ δ.degree = μ - ν j ∧
      N ≤ pDeg δ + ν j ∧ N + μ₁ ≤ δ.degree + xDeg δ + 2 * ν j := by
    intro j δ hδ
    have hνμ : ν j ≤ μ := by
      by_contra hlt
      simp only [c, hlt, ↓reduceIte, support_zero, Finset.notMem_empty] at hδ
    have hδc : δ ∈ (restrictSupport pr (c' j)).support := by
      have := hδ
      simp only [c, hνμ, ↓reduceIte, mem_support_iff, coeff_homogeneousComponent] at this
      split_ifs at this
      · exact mem_support_iff.mpr this
      · exact absurd rfl this
    obtain ⟨-, γ, hγp, hγδ⟩ := mem_support_restrictSupport.mp hδc
    have hdeg := degree_eq_of_isHomogeneous_of_coeff_ne_zero (hchom j) (mem_support_iff.mp hδ)
    obtain ⟨hγN, hγw⟩ := hpPD γ hγp
    have hγd := (hp_supp γ hγp).2
    obtain ⟨hγ1, hγ2⟩ := degree_eq_pDeg_add_sum_and_pDeg_eq_none_add_xDeg γ
    obtain ⟨hδ1, hδ2⟩ := degree_eq_pDeg_add_sum_and_pDeg_eq_none_add_xDeg δ
    have hout : γ none = δ none ∧
        ∑ j : Fin C.s, γ (some (Sum.inr j)) = ∑ j : Fin C.s, δ (some (Sum.inr j)) := by
      simp only [outerExponents, Prod.mk.injEq] at hγδ
      exact ⟨hγδ.1, by rw [hγδ.2]⟩
    simp only [wt, degree_exponentShift] at hγw
    refine ⟨hνμ, hdeg, ?_, ?_⟩ <;> omega
  -- the lifted elements `H_j` and `h = ∑ H_j f_j`
  let H : Fin m → R := fun j => eval C.z (MvPolynomial.liftResidue (c j))
  have hHM : ∀ j, H j ∈ maximalIdeal R ^ (μ - ν j) := fun j =>
    eval_mem_pow_of_isHomogeneous (maximalIdeal R) C.z C.z_mem
      (MvPolynomial.IsHomogeneous.liftResidue (hchom j))
  have hHmk : ∀ j, AssocGraded.mk _ (μ - ν j) (H j) (hHM j) = C.e (c j) := by
    intro j
    have := aeval_mk_map_of_isHomogeneous (maximalIdeal R) C.z C.z_mem
      (MvPolynomial.IsHomogeneous.liftResidue (hchom j))
    rw [MvPolynomial.map_mk_liftResidue] at this
    exact this.symm
  have hH0 : ∀ j, ¬ ν j ≤ μ → H j = 0 := by
    intro j hj
    have hc0 : c j = 0 := by simp only [c, hj, ↓reduceIte]
    simp only [H, hc0, MvPolynomial.liftResidue, support_zero, Finset.sum_empty, map_zero]
  have hfjM : ∀ j, f j ∈ maximalIdeal R ^ ν j := fun j => Ideal.mem_pow_of_ordElem (hfM j)
  have hprodM : ∀ j, H j * f j ∈ maximalIdeal R ^ μ := fun j =>
    Ideal.pow_le_pow_right (show μ ≤ (μ - ν j) + ν j by omega)
      (by rw [pow_add]; exact Ideal.mul_mem_mul (hHM j) (hfjM j))
  have hprodmk : ∀ j, AssocGraded.mk (maximalIdeal R) μ (H j * f j) (hprodM j) =
      C.e (c j) * C.e (pj j) := by
    intro j
    by_cases hj : ν j ≤ μ
    · rw [← hHmk j, hpje j, initialForm_eq_mk _ (hfM j), AssocGraded.mk_mul_mk]
      congr 1 <;> omega
    · have hc0 : c j = 0 := by simp only [c, hj, ↓reduceIte]
      rw [hc0, map_zero, zero_mul, AssocGraded.mk_eq_zero_iff, hH0 j hj, zero_mul]
      exact zero_mem _
  -- the element `a' = x₀^{-N} h` of `R₁`
  set z₁' : CoordIndex C.r C.s → T.ring := coordFamilyOfOne C.x' fun j => T.toRing (C.y j) with hz₁'
  let A : Fin m → T.ring := fun j => ∑ δ ∈ (c j).support,
    T.toRing (lift ((c j).coeff δ)) * C.x₁ ^ (pDeg δ + ν j - N) * monomialVal z₁' δ
  have hHtoRing : ∀ j, T.toRing (H j) * C.x₁ ^ ν j = C.x₁ ^ N * A j := by
    intro j
    simp only [H, A, C.eval_z_eq_sum, MvPolynomial.support_liftResidue, MvPolynomial.coeff_liftResidue, map_sum,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    rw [map_mul, C.toRing_monomialVal_eq_pow_pDeg_mul]
    have hN := (hcsupp j δ hδ).2.2.1
    have : C.x₁ ^ pDeg δ * C.x₁ ^ ν j = C.x₁ ^ N * C.x₁ ^ (pDeg δ + ν j - N) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    calc T.toRing (lift ((c j).coeff δ)) * (C.x₁ ^ pDeg δ * monomialVal z₁' δ) * C.x₁ ^ ν j
        = T.toRing (lift ((c j).coeff δ)) * (C.x₁ ^ pDeg δ * C.x₁ ^ ν j) *
          monomialVal z₁' δ := by ring
      _ = _ := by rw [this]; ring
  have hz₁'M : ∀ v, z₁' v ∈ maximalIdeal T.ring ^ weightNeNone v := by
    intro v
    rcases v with _ | (i | j)
    · simp [z₁', coordFamilyOfOne, coordFamily, weightNeNone]
    · simpa [z₁', coordFamilyOfOne, coordFamily, weightNeNone, z₁] using C.z₁_mem (some (Sum.inl i))
    · simpa [z₁', coordFamilyOfOne, coordFamily, weightNeNone, z₁] using C.z₁_mem (some (Sum.inr j))
  have hx₁M : C.x₁ ∈ maximalIdeal T.ring := by simpa [z₁_none] using C.z₁_mem none
  have hAM : ∀ j, A j ∈ maximalIdeal T.ring ^ (μ₁ - ν j) := by
    intro j
    refine sum_mem fun δ hδ => ?_
    obtain ⟨-, hdeg, hN, hw⟩ := hcsupp j δ hδ
    have h1 := monomialVal_mem_pow_weight _ weightNeNone z₁' hz₁'M δ
    have h2 : C.x₁ ^ (pDeg δ + ν j - N) ∈ maximalIdeal T.ring ^ (pDeg δ + ν j - N) :=
      Ideal.pow_mem_pow hx₁M _
    have h3 := Ideal.mul_mem_mul h2 h1
    rw [← pow_add] at h3
    have hw1 := weight_weightNeNone_add_apply_none δ
    obtain ⟨-, hP⟩ := degree_eq_pDeg_add_sum_and_pDeg_eq_none_add_xDeg δ
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) h3)
  have hgjM : ∀ j, g j ∈ maximalIdeal T.ring ^ ν j := fun j => Ideal.mem_pow_of_ordElem (hgM j)
  have hAgM : ∀ j, A j * g j ∈ maximalIdeal T.ring ^ μ₁ := fun j =>
    Ideal.pow_le_pow_right (show μ₁ ≤ (μ₁ - ν j) + ν j by omega)
      (by rw [pow_add]; exact Ideal.mul_mem_mul (hAM j) (hgjM j))
  -- (1) "`ν_P(h) ≥ Min(μ - t_α - β - ν_i + ν_i + β) = Min(μ - t_α) ≥ ν`", since `ν_P(f_i) ≥ ν_i`
  have hHfP : ∀ j, H j * f j ∈ P ^ N := by
    intro j
    simp only [H, C.eval_z_eq_sum, MvPolynomial.support_liftResidue,
      MvPolynomial.coeff_liftResidue, Finset.sum_mul]
    refine sum_mem fun δ hδ => ?_
    have h1 := C.monomialVal_z_mem_pow_pDeg δ
    have h2 : f j ∈ P ^ ν j := Ideal.mem_pow_of_le_ordElem (hfP j)
    have h3 : monomialVal C.z δ * f j ∈ P ^ (pDeg δ + ν j) := by
      rw [pow_add]; exact Ideal.mul_mem_mul h1 h2
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (hcsupp j δ hδ).2.2.1 h3)
  refine ⟨∑ j, H j * f j, ∑ j, A j * g j, sum_mem fun j _ => J.mul_mem_left _ (hf.1 j),
    Ideal.le_ordElem (sum_mem fun j _ => hHfP j), ?_, ?_, sum_mem fun j _ => hAgM j, ?_⟩
  · -- (2) `ν_M(f - h) > μ`
    rw [← AssocGraded.mk_eq_zero_iff _ (sub_mem hFμ (sum_mem fun j _ => hprodM j)),
      AssocGraded.mk_sub _ _ _ _ hFμ (sum_mem fun j _ => hprodM j), AssocGraded.mk_sum _ _ _ _ hprodM,
      ← initialForm_eq_mk _ hμ, hinit]
    simp only [hprodmk, ← map_mul, ← map_sum, hcsum, sub_self]
  · -- `h = x₀^N a'`
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← hg j, ← mul_assoc (T.toRing (H j)), hHtoRing j]
    ring
  · -- the class of `a'` lies in `(ψ₁, …, ψ_m)`
    rw [AssocGraded.mk_sum _ _ _ _ hAgM]
    refine sum_mem fun j _ => ?_
    by_cases hj : ν j ≤ μ₁
    · have hmk : AssocGraded.mk (maximalIdeal T.ring) μ₁ (A j * g j) (hAgM j) =
          AssocGraded.mk _ (μ₁ - ν j) (A j) (hAM j) *
            initialForm (maximalIdeal T.ring) (g j) := by
        rw [initialForm_eq_mk _ (hgM j), AssocGraded.mk_mul_mk]
        congr 1 <;> omega
      rw [hmk]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    · rw [(AssocGraded.mk_eq_zero_iff _ _).mpr]
      · exact zero_mem _
      · exact Ideal.pow_le_pow_right (show μ₁ + 1 ≤ (μ₁ - ν j) + ν j by omega)
          (by rw [pow_add]; exact Ideal.mul_mem_mul (hAM j) (hgjM j))

theorem mk_eq_zero_of_le_ordElem (N μ₁ : ℕ) (F : R) (a : T.ring) (hFa : C.x₁ ^ N * a = T.toRing F)
    (ha : a ∈ maximalIdeal T.ring ^ μ₁)
    (hbig : ((N + μ₁ + 1 : ℕ) : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) F) :
    AssocGraded.mk (maximalIdeal T.ring) μ₁ a ha = 0 :=
  (AssocGraded.mk_eq_zero_iff _ ha).mpr (C.mem_pow_succ_of_le_ordElem N μ₁ F a hFa hbig)

/-- **The descent of Theorem 5** (pp. 239--240): "Suppose this is proved.  If `ν_{M₁}(g - x^{-ν}h) > μ₁`,
then `g` and `x^{-ν}h` should have the same initial form in `gr_{M₁}(R₁)`, and hence the initial form
of `g` in `gr_{M₁}(R₁)` must be in `I` by (4).  If `ν_{M₁}(g - x^{-ν}h) = μ₁`, then we replace `f` by
`f - h` (and `g` by `g - x^{-ν}h`) and apply the same result.  As long as `ν_{M₁}(g - x^{-ν}h)` remains
to be `μ₁`, we repeat this process.  But this process cannot be repeated infinitely, for the number
`ν_M(f)` will be then made arbitrarily big while it should be bounded by `ν_{M₁}(g) + ν = μ₁ + ν`."
Here `f ∈ J` has `ν_P(f) ≥ N` (`N` is the printed `ν`), `g = a = x₀^{-N} f`, and the repetition is an
induction on `N + μ₁ + 1 - ν_M(f)` (the number of steps left before `ν_M(f)` exceeds `N + μ₁`, the
printed bound for `ν_M(f)`), the class of `g` in degree `μ₁` being in `I`. -/
theorem mk_mem_span_initialForm (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing)
    (J : Ideal R) {m : ℕ} (f : Fin m → R) (hf : IsStandardBase R J f) (ν : Fin m → ℕ)
    (hfM : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = ν j)
    (hfP : ∀ j, (ν j : ℕ∞) ≤ Ideal.ordElem P (f j)) (g : Fin m → T.ring)
    (hg : ∀ j, C.x₁ ^ ν j * g j = T.toRing (f j))
    (hgM : ∀ j, Ideal.ordElem (maximalIdeal T.ring) (g j) = ν j) (N μ₁ : ℕ) :
    ∀ (n : ℕ) (F : R) (a : T.ring), F ∈ J → (N : ℕ∞) ≤ Ideal.ordElem P F →
      C.x₁ ^ N * a = T.toRing F → ∀ ha : a ∈ maximalIdeal T.ring ^ μ₁,
      ((N + μ₁ + 1 : ℕ) : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) F + n →
      AssocGraded.mk (maximalIdeal T.ring) μ₁ a ha ∈
        Ideal.span (Set.range fun j => initialForm (maximalIdeal T.ring) (g j)) := by
  intro n
  induction n with
  | zero =>
    intro F a _ _ hFa ha hbound
    rw [Nat.cast_zero, add_zero] at hbound
    rw [C.mk_eq_zero_of_le_ordElem N μ₁ F a hFa ha hbound]
    exact zero_mem _
  | succ n ih =>
    intro F a hFJ hFP hFa ha hbound
    by_cases hbig : ((N + μ₁ + 1 : ℕ) : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) F
    · rw [C.mk_eq_zero_of_le_ordElem N μ₁ F a hFa ha hbig]
      exact zero_mem _
    · have htop : Ideal.ordElem (maximalIdeal R) F ≠ ⊤ := fun h => hbig (by rw [h]; exact le_top)
      obtain ⟨μ, hμ⟩ := ENat.ne_top_iff_exists.mp htop
      by_cases hex : a ∈ maximalIdeal T.ring ^ (μ₁ + 1)
      · rw [(AssocGraded.mk_eq_zero_iff _ ha).mpr hex]
        exact zero_mem _
      · -- `ν_{M₁}(g) = μ₁`
        have hord : Ideal.ordElem (maximalIdeal T.ring) a = μ₁ :=
          le_antisymm (Ideal.ordElem_le_of_notMem hex) (Ideal.le_ordElem ha)
        obtain ⟨h, a', hhJ, hhP, hFh, ha'x, ha', ha'mk⟩ :=
          C.exists_mem_ideal_sub_mem_pow_succ hrat J f hf ν hfM hfP g hg hgM N μ₁ F hFJ hFP a hFa
            hord μ hμ.symm
        have ha'' : a - a' ∈ maximalIdeal T.ring ^ μ₁ := sub_mem ha ha'
        by_cases hgt : a - a' ∈ maximalIdeal T.ring ^ (μ₁ + 1)
        · -- `ν_{M₁}(g - x^{-ν}h) > μ₁`: `g` and `x^{-ν}h` have the same initial form, which is in `I`
          rw [AssocGraded.mk_eq_mk_of_sub_mem_pow_succ _ _ ha ha' hgt]
          exact ha'mk
        · -- `ν_{M₁}(g - x^{-ν}h) = μ₁`: replace `f` by `f - h` and `g` by `g - x^{-ν}h`
          have hIH := ih (F - h) (a - a') (sub_mem hFJ hhJ)
            (Ideal.le_ordElem (sub_mem (Ideal.mem_pow_of_le_ordElem hFP)
              (Ideal.mem_pow_of_le_ordElem hhP)))
            (by rw [mul_sub, hFa, ha'x, map_sub]) ha'' (by
              have h1 := Ideal.le_ordElem hFh
              rw [← hμ] at hbound
              have h2 : N + μ₁ + 1 ≤ μ + (n + 1) := by exact_mod_cast hbound
              calc ((N + μ₁ + 1 : ℕ) : ℕ∞) ≤ ((μ + 1 : ℕ) : ℕ∞) + (n : ℕ∞) := by
                    exact_mod_cast (by omega : N + μ₁ + 1 ≤ μ + 1 + n)
                _ ≤ Ideal.ordElem (maximalIdeal R) (F - h) + n := add_le_add_left h1 _)
          have : AssocGraded.mk (maximalIdeal T.ring) μ₁ a ha =
              AssocGraded.mk _ μ₁ (a - a') ha'' + AssocGraded.mk _ μ₁ a' ha' := by
            rw [← AssocGraded.mk_add]
            exact AssocGraded.mk_congr _ _ (by ring)
          rw [this]
          exact add_mem hIH ha'mk

omit [IsRegularLocalRing T.ring] in
/-- p. 239: "Since `J₁` is obtained by localization from the ideal `⋃_{ν=1}^∞ x^{-ν}(J ∩ P^ν)` in the
ring `A₁ = R[x₁/x, …, x_r/x]` with respect to the prime ideal `A₁ ∩ M₁`".  What is used of this
(not argued in the paper): every element `z` of the strict transform is, up to a unit `u` of `R₁`,
of the form `x₀^{-N} F` with `F ∈ J` and `ν_P(F) ≥ N`, i.e. `u z = a` with `x₀ᴺ a = F`. -/
theorem exists_isUnit_mul_eq_of_mem_strictTransformIdeal (J : Ideal R) {z : T.ring} (hz : z ∈ strictTransformIdeal T J) :
    ∃ (u : T.ring) (N : ℕ) (F : R) (a : T.ring), IsUnit u ∧ F ∈ J ∧ (N : ℕ∞) ≤ Ideal.ordElem P F ∧
      C.x₁ ^ N * a = T.toRing F ∧ u * z = a := by
  classical
  -- elements of `R[x⁻¹P]` are fractions `c / x^K` with `c ∈ P^K`
  have hfrac : ∀ b : blowupAlgebra R P T.x, ∃ (K : ℕ) (c : R), c ∈ P ^ K ∧
      T.xR ^ K * algebraMap (blowupAlgebra R P T.x) T.ring b = T.toRing c := by
    intro b
    have hx' : algebraMap R (FractionRing R) T.x ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R _)).mpr T.x_ne_zero
    have hb : ∃ (K : ℕ) (c : R), c ∈ P ^ K ∧ algebraMap R (FractionRing R) T.x ^ K *
        (b : FractionRing R) = algebraMap R (FractionRing R) c := by
      obtain ⟨b, hb⟩ := b
      simp only
      induction hb using Algebra.adjoin_induction with
      | mem y hy =>
        obtain ⟨p, hp, rfl⟩ := hy
        exact ⟨1, p, by rwa [pow_one], by rw [pow_one, mul_div_cancel₀ _ hx']⟩
      | algebraMap r => exact ⟨0, r, by simp, by rw [pow_zero, one_mul]⟩
      | add y z _ _ hy hz =>
        obtain ⟨N₁, f₁, hf₁, h₁⟩ := hy
        obtain ⟨N₂, f₂, hf₂, h₂⟩ := hz
        refine ⟨N₁ + N₂, T.x ^ N₂ * f₁ + T.x ^ N₁ * f₂, add_mem ?_ ?_, ?_⟩
        · rw [add_comm N₁ N₂, pow_add]
          exact Ideal.mul_mem_mul (Ideal.pow_mem_pow T.x_mem N₂) hf₁
        · rw [pow_add]
          exact Ideal.mul_mem_mul (Ideal.pow_mem_pow T.x_mem N₁) hf₂
        · rw [map_add, map_mul, map_mul, map_pow, map_pow, ← h₁, ← h₂]
          ring
      | mul y z _ _ hy hz =>
        obtain ⟨N₁, f₁, hf₁, h₁⟩ := hy
        obtain ⟨N₂, f₂, hf₂, h₂⟩ := hz
        refine ⟨N₁ + N₂, f₁ * f₂, ?_, ?_⟩
        · rw [pow_add]; exact Ideal.mul_mem_mul hf₁ hf₂
        · rw [map_mul, ← h₁, ← h₂]
          ring
    obtain ⟨K, c, hcK, hKc⟩ := hb
    refine ⟨K, c, hcK, ?_⟩
    have hB : algebraMap R (blowupAlgebra R P T.x) T.x ^ K * b =
        algebraMap R (blowupAlgebra R P T.x) c := Subtype.ext (by simpa using hKc)
    have := congrArg (algebraMap (blowupAlgebra R P T.x) T.ring) hB
    rw [map_mul, map_pow] at this
    exact this
  -- the invariant, with `T.xR` and a denominator `s ∉ M'`
  have key : ∀ z ∈ strictTransformIdeal T J, ∃ s ∈ T.M'.primeCompl, ∃ (K : ℕ) (F : R),
      F ∈ J ∧ F ∈ P ^ K ∧
        T.xR ^ K * (algebraMap (blowupAlgebra R P T.x) T.ring s * z) = T.toRing F := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x', hx', f, hfJ, ν, hνf, hy⟩ := hy
      have hxR : T.xR ∈ Ideal.span {x'} := by
        rw [hx', ← T.span_xR_eq_map]; exact Ideal.subset_span rfl
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hxR
      obtain ⟨⟨b, s'⟩, hbs⟩ := IsLocalization.mk'_surjective T.M'.primeCompl w
      have hws : w * algebraMap _ T.ring (s' : blowupAlgebra R P T.x) =
          algebraMap _ T.ring b := by rw [← hbs]; exact IsLocalization.mk'_spec _ _ _
      obtain ⟨K, c, hcK, hKc⟩ := hfrac b
      refine ⟨s' ^ ν, pow_mem s'.2 ν, ν + K * ν, c ^ ν * f, J.mul_mem_left _ hfJ, ?_, ?_⟩
      · have h1 : c ^ ν ∈ P ^ (K * ν) := by
          rw [pow_mul]; exact Ideal.pow_mem_pow hcK ν
        have h2 : f ∈ P ^ ν := Ideal.mem_pow_of_le_ordElem hνf
        rw [add_comm, pow_add]
        exact Ideal.mul_mem_mul h1 h2
      calc T.xR ^ (ν + K * ν) * (algebraMap _ T.ring ((s' : blowupAlgebra R P T.x) ^ ν) * y)
          = (T.xR ^ K * (w * algebraMap _ T.ring (s' : blowupAlgebra R P T.x))) ^ ν *
            (x' ^ ν * y) := by rw [← hw, map_pow]; ring
        _ = T.toRing (c ^ ν * f) := by rw [hws, hKc, hy, map_mul, map_pow]
    | zero => exact ⟨1, T.M'.primeCompl.one_mem, 0, 0, zero_mem _, by simp, by simp⟩
    | add z₁ z₂ _ _ h₁ h₂ =>
      obtain ⟨s₁, hs₁, N₁, F₁, hF₁, hP₁, e₁⟩ := h₁
      obtain ⟨s₂, hs₂, N₂, F₂, hF₂, hP₂, e₂⟩ := h₂
      obtain ⟨K₁, c₁, hcK₁, hc₁⟩ := hfrac s₁
      obtain ⟨K₂, c₂, hcK₂, hc₂⟩ := hfrac s₂
      refine ⟨s₁ * s₂, T.M'.primeCompl.mul_mem hs₁ hs₂, N₁ + N₂ + K₁ + K₂,
        c₂ * T.x ^ (N₂ + K₁) * F₁ + c₁ * T.x ^ (N₁ + K₂) * F₂,
        add_mem (J.mul_mem_left _ hF₁) (J.mul_mem_left _ hF₂), add_mem ?_ ?_, ?_⟩
      · have : N₁ + N₂ + K₁ + K₂ = K₂ + (N₂ + K₁) + N₁ := by ring
        rw [this, pow_add, pow_add]
        exact Ideal.mul_mem_mul (Ideal.mul_mem_mul hcK₂ (Ideal.pow_mem_pow T.x_mem _)) hP₁
      · have : N₁ + N₂ + K₁ + K₂ = K₁ + (N₁ + K₂) + N₂ := by ring
        rw [this, pow_add, pow_add]
        exact Ideal.mul_mem_mul (Ideal.mul_mem_mul hcK₁ (Ideal.pow_mem_pow T.x_mem _)) hP₂
      have hxR : T.xR = T.toRing T.x := rfl
      calc T.xR ^ (N₁ + N₂ + K₁ + K₂) * (algebraMap _ T.ring (s₁ * s₂) * (z₁ + z₂))
          = (T.xR ^ K₂ * algebraMap _ T.ring s₂) * T.xR ^ (N₂ + K₁) *
              (T.xR ^ N₁ * (algebraMap _ T.ring s₁ * z₁)) +
            (T.xR ^ K₁ * algebraMap _ T.ring s₁) * T.xR ^ (N₁ + K₂) *
              (T.xR ^ N₂ * (algebraMap _ T.ring s₂ * z₂)) := by rw [map_mul]; ring
        _ = _ := by rw [e₁, e₂, hc₁, hc₂, hxR]; simp only [map_add, map_mul, map_pow]
    | smul r z _ h =>
      obtain ⟨s, hs, N, F, hF, hPF, e⟩ := h
      obtain ⟨⟨b, s'⟩, hbs⟩ := IsLocalization.mk'_surjective T.M'.primeCompl r
      have hrs : r * algebraMap _ T.ring (s' : blowupAlgebra R P T.x) = algebraMap _ T.ring b := by
        rw [← hbs]; exact IsLocalization.mk'_spec _ _ _
      obtain ⟨K, c, hcK, hKc⟩ := hfrac b
      refine ⟨s' * s, T.M'.primeCompl.mul_mem s'.2 hs, N + K, c * F, J.mul_mem_left _ hF, ?_, ?_⟩
      · rw [add_comm, pow_add]; exact Ideal.mul_mem_mul hcK hPF
      calc T.xR ^ (N + K) * (algebraMap _ T.ring ((s' : blowupAlgebra R P T.x) * s) * (r • z))
          = (T.xR ^ K * (r * algebraMap _ T.ring (s' : blowupAlgebra R P T.x))) *
            (T.xR ^ N * (algebraMap _ T.ring s * z)) := by rw [map_mul, smul_eq_mul]; ring
        _ = T.toRing (c * F) := by rw [hrs, hKc, e, map_mul]
  obtain ⟨s, hs, K, F, hFJ, hFP, hKF⟩ := key z hz
  -- replace `T.xR` by `x₀`
  have hassoc : Associated C.x₁ T.xR :=
    Ideal.span_singleton_eq_span_singleton.mp (C.span_x₁.trans T.span_xR_eq_map.symm)
  obtain ⟨v, hv⟩ := hassoc
  refine ⟨(v : T.ring) ^ K * algebraMap _ T.ring s, K, F,
    (v : T.ring) ^ K * algebraMap _ T.ring s * z,
    ((Units.isUnit v).pow K).mul (IsLocalization.map_units T.ring (⟨s, hs⟩ : T.M'.primeCompl)),
    hFJ, Ideal.le_ordElem hFP, ?_, rfl⟩
  rw [← hKF, ← hv]
  ring

/-- The initial forms of the elements of `J₁` lie in the ideal generated by the `ψ_j`: "it is
sufficient to show that for every `f ∈ J` with `ν_P(f) ≥ ν > 0`, the initial form of `x^{-ν} f` in
`gr_{M₁}(R₁)` belongs to the ideal `I = (ψ₁, …, ψ_m) gr_{M₁}(R₁)`" (p. 239), the initial form of a
unit multiple of an element being a unit multiple of the initial form. -/
theorem grIdeal_strictTransformIdeal_le_span_initialForm (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing)
    (J : Ideal R) {m : ℕ} (f : Fin m → R) (hf : IsStandardBase R J f) (ν : Fin m → ℕ)
    (hfM : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = ν j)
    (hfP : ∀ j, (ν j : ℕ∞) ≤ Ideal.ordElem P (f j)) (g : Fin m → T.ring)
    (hg : ∀ j, C.x₁ ^ ν j * g j = T.toRing (f j))
    (hgM : ∀ j, Ideal.ordElem (maximalIdeal T.ring) (g j) = ν j) :
    grIdeal (maximalIdeal T.ring) (strictTransformIdeal T J) ≤
      Ideal.span (Set.range fun j => initialForm (maximalIdeal T.ring) (g j)) := by
  rw [grIdeal, Ideal.span_le]
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨u, N, F, a, hu, hFJ, hFP, hFa, hua⟩ :=
    C.exists_isUnit_mul_eq_of_mem_strictTransformIdeal J hz
  have hinit : initialForm (maximalIdeal T.ring) z =
      (initialForm_eq_algebraMap_of_isUnit hu).2.unit⁻¹ * initialForm (maximalIdeal T.ring) a := by
    rw [← hua, initialForm_mul_maximalIdeal, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  rw [SetLike.mem_coe, hinit]
  refine Ideal.mul_mem_left _ _ ?_
  by_cases htop : Ideal.ordElem (maximalIdeal T.ring) a = ⊤
  · rw [initialForm, dite_eq_left htop]; exact zero_mem _
  · obtain ⟨μ₁, hμ₁⟩ := ENat.ne_top_iff_exists.mp htop
    rw [initialForm_eq_mk _ hμ₁.symm]
    exact C.mk_mem_span_initialForm hrat J f hf ν hfM hfP g hg hgM N μ₁ (N + μ₁ + 1) F a hFJ hFP
      hFa _ (le_add_self)

/-- **Theorem 5 in the residually rational case** (pp. 239–241). -/
theorem isStandardBase_strictTransformIdeal_of_isResiduallyRational (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing)
    (J : Ideal R) {m : ℕ} (f : Fin m → R) (hf : IsStandardBase R J f) (ν : Fin m → ℕ)
    (hfM : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = ν j)
    (hfP : ∀ j, (ν j : ℕ∞) ≤ Ideal.ordElem P (f j)) (g : Fin m → T.ring)
    (hg : ∀ j, C.x₁ ^ ν j * g j = T.toRing (f j))
    (hgM : ∀ j, Ideal.ordElem (maximalIdeal T.ring) (g j) = ν j) :
    IsStandardBase T.ring (strictTransformIdeal T J) g := by
  have hgJ : ∀ j, g j ∈ strictTransformIdeal T J := fun j =>
    C.mem_strictTransformIdeal_of_pow_mul_eq (hf.1 j) (hfP j) (hg j)
  obtain ⟨d, hd, hmono⟩ := hf.2.2.1
  have hνmono : Monotone ν := by
    intro a b hab
    have ha := (ordElem_eq_of_isStandardBase_of_initialForm_mem_homogeneous J f hf d hd a).symm.trans (hfM a)
    have hb := (ordElem_eq_of_isStandardBase_of_initialForm_mem_homogeneous J f hf d hd b).symm.trans (hfM b)
    have ha' : d a = ν a := by exact_mod_cast ha
    have hb' : d b = ν b := by exact_mod_cast hb
    rw [← ha', ← hb']
    exact hmono hab
  have hρ : ∀ j, C.ρ hrat (initialForm (maximalIdeal T.ring) (g j)) =
      initialForm (maximalIdeal R) (f j) := fun j =>
    ((C.ordElem_le_and_rho_initialForm_eq hrat (f j) (ν j) (hfM j) (g j) (hg j)).2 (hgM j)).2
  refine ⟨hgJ, fun j => Ideal.subset_span ⟨_, hgJ j, rfl⟩, ⟨ν, fun j => ?_, hνmono⟩,
    le_antisymm (C.grIdeal_strictTransformIdeal_le_span_initialForm hrat J f hf ν hfM hfP g hg hgM)
      (Ideal.span_le.mpr ?_), fun j hj => ?_⟩
  · dsimp only; rw [initialForm_eq_mk _ (hgM j)]; exact AssocGraded.mk_mem_homogeneous _ _
  · rintro _ ⟨j, rfl⟩; exact Ideal.subset_span ⟨_, hgJ j, rfl⟩
  · apply hf.2.2.2.2 j
    have := Ideal.mem_map_of_mem (C.ρ hrat) hj
    rw [Ideal.map_span, hρ] at this
    refine (Ideal.span_mono ?_) this
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, (hρ _).symm⟩

end TransformCoord

end Thm5Core

section Thm5General

/-- Multiplying the members of a standard base by units gives a standard base. -/
theorem IsStandardBase.mul_isUnit {S : Type u} [CommRing S] [IsRegularLocalRing S]
    (J : Ideal S) {m : ℕ} (G : Fin m → S) (U : Fin m → S) (hU : ∀ t, IsUnit (U t))
    (hG : IsStandardBase S J G) : IsStandardBase S J (fun t => U t * G t) := by
  classical
  obtain ⟨hGJ, -, ⟨d, hd, hmono⟩, hspan, hirr⟩ := hG
  let c : Fin m → AssocGraded (maximalIdeal S) := fun t => initialForm (maximalIdeal S) (U t)
  have hc : ∀ t, IsUnit (c t) := fun t => (initialForm_eq_algebraMap_of_isUnit (hU t)).2
  have hc0 : ∀ t, c t ∈ AssocGraded.homogeneous (maximalIdeal S) 0 := fun t => by
    simp only [c, (initialForm_eq_algebraMap_of_isUnit (hU t)).1]
    rw [← AssocGraded.mk_zero_eq_algebraMap _ _ (by simp)]
    exact AssocGraded.mk_mem_homogeneous _ _
  have hφ' : ∀ t, initialForm (maximalIdeal S) (U t * G t) =
      c t * initialForm (maximalIdeal S) (G t) := fun t => initialForm_mul_maximalIdeal _ _
  have hspan_eq : ∀ {ι : Type} (emb : ι → Fin m),
      Ideal.span (Set.range fun t => initialForm (maximalIdeal S) (U (emb t) * G (emb t))) =
        Ideal.span (Set.range fun t => initialForm (maximalIdeal S) (G (emb t))) := by
    intro ι emb
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨t, rfl⟩
      dsimp only
      rw [hφ']
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨t, rfl⟩)
    · rintro _ ⟨t, rfl⟩
      dsimp only
      have : initialForm (maximalIdeal S) (G (emb t)) =
          (hc (emb t)).unit⁻¹ * initialForm (maximalIdeal S) (U (emb t) * G (emb t)) := by
        rw [hφ', ← mul_assoc, IsUnit.val_inv_mul, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨t, rfl⟩)
  refine ⟨fun t => J.mul_mem_left _ (hGJ t),
    fun t => Ideal.subset_span ⟨_, J.mul_mem_left _ (hGJ t), rfl⟩,
    ⟨d, fun t => ?_, hmono⟩, ?_, fun t => ?_⟩
  · dsimp only
    rw [hφ']
    simpa using AssocGraded.mul_mem_homogeneous _ (hc0 t) (hd t)
  · rw [hspan]
    exact (hspan_eq id).symm
  · dsimp only
    rw [hspan_eq (Fin.castLE t.2.le), hφ']
    intro hmem
    apply hirr t
    dsimp only
    have : initialForm (maximalIdeal S) (G t) =
        (hc t).unit⁻¹ * (c t * initialForm (maximalIdeal S) (G t)) := by
      rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ hmem

/-- For a faithfully flat `A`-algebra `B`, `ν_{IB}(a) = ν_I(a)`. -/
theorem Ideal.ordElem_map_algebraMap_of_faithfullyFlat {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (I : Ideal A) (a : A) :
    Ideal.ordElem (I.map (algebraMap A B)) (algebraMap A B a) = Ideal.ordElem I a := by
  have h : ∀ ν : ℕ, algebraMap A B a ∈ I.map (algebraMap A B) ^ ν ↔ a ∈ I ^ ν := by
    intro ν
    rw [← Ideal.map_pow]
    refine ⟨fun h => ?_, Ideal.mem_map_of_mem _⟩
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (I ^ ν)]
    exact h
  simp only [Ideal.ordElem, h]

/-- Theorem 5 in the residually rational case, for an arbitrary generator `x` of `PR₁`. -/
theorem isStandardBase_strictTransformIdeal_of_isResiduallyRational {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (J P : Ideal R) [P.IsPrime] [IsRegularLocalRing (R ⧸ P)]
    (t : MonoidalTransform R P)
    (hrat : RingHom.IsResiduallyRational (R := R) (R' := t.ring) t.toRing)
    (x : R) (hx : P.map t.toRing = Ideal.span {t.toRing x})
    {m : ℕ} (f : Fin m → R) (ν : Fin m → ℕ)
    (g : Fin m → t.ring) (hν : ∀ j, (ν j : ℕ∞) = Ideal.ordElem (maximalIdeal R) (f j))
    (hg : ∀ j, t.toRing x ^ ν j * g j = t.toRing (f j))
    (hi : IsStandardBase R J f)
    (hii : ∀ j, Ideal.ordElem P (f j) = Ideal.ordElem (maximalIdeal R) (f j))
    (hiii : ∀ j, Ideal.ordElem (maximalIdeal t.ring) (g j) = (ν j : ℕ∞)) :
    IsStandardBase t.ring (strictTransformIdeal t J) g := by
  obtain ⟨C⟩ := TransformCoord.nonempty t hrat
  have hassoc : Associated C.x₁ (t.toRing x) :=
    Ideal.span_singleton_eq_span_singleton.mp (C.span_x₁.trans hx)
  obtain ⟨v, hv⟩ := hassoc
  have hsb := C.isStandardBase_strictTransformIdeal_of_isResiduallyRational hrat J f hi ν (fun j => (hν j).symm)
    (fun j => by rw [hii, ← hν]) (fun j => (v : t.ring) ^ ν j * g j)
    (fun j => by rw [← hg, ← hv, mul_pow]; ring)
    (fun j => by rw [ordElem_mul_maximalIdeal, Ideal.ordElem_eq_zero_of_isUnit ((Units.isUnit v).pow _),
      zero_add, hiii])
  have := IsStandardBase.mul_isUnit _ _ (fun j => ((v⁻¹ : (t.ring)ˣ) : t.ring) ^ ν j)
    (fun j => (Units.isUnit _).pow _) hsb
  convert this using 1
  funext j
  rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]

/-- Theorem 5 (pp. 238–241). -/
theorem isStandardBase_and_nuStar_eq_strictTransformIdeal [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (J P : Ideal R) [P.IsPrime] [IsRegularLocalRing (R ⧸ P)]
    (hJP : J ≤ P) (t : MonoidalTransform R P)
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := t.ring) t.toRing)
    (x : R) (hxP : x ∈ P) (hx : P.map t.toRing = Ideal.span {t.toRing x})
    {m : ℕ} (f : Fin m → R) (ν : Fin m → ℕ)
    (g : Fin m → t.ring) (hν : ∀ j, (ν j : ℕ∞) = Ideal.ordElem (maximalIdeal R) (f j))
    (hg : ∀ j, t.toRing x ^ ν j * g j = t.toRing (f j))
    (hi : IsStandardBase R J f)
    (hii : ∀ j, Ideal.ordElem P (f j) = Ideal.ordElem (maximalIdeal R) (f j))
    (hiii : ∀ j, Ideal.ordElem (maximalIdeal t.ring) (g j) = (ν j : ℕ∞)) :
    IsStandardBase t.ring (strictTransformIdeal t J) g ∧
      nuStar t.ring (strictTransformIdeal t J) = nuStar R J := by
  classical
  have _ := hJP
  have _ := hxP
  have hP : P.IsPrime := inferInstance
  have hS : IsRegularLocalRing (R ⧸ P) := inferInstance
  have hP0 : P ≠ ⊥ := fun h => t.x_ne_zero (Ideal.mem_bot.mp (h ▸ t.x_mem))
  -- a local extension `R → R'` with separably closed residue field (proof of Theorem 3)
  obtain ⟨R', _, _, α, _, hα, hsepα, hsc⟩ := exists_maximal_local_extension R
  have _ : IsDomain R' := Transforms.isDomain_of_isRegularLocalRing R'
  obtain ⟨⟨hP', hS'⟩, -, h2, h3⟩ := RingHom.MapsRSOP.canonicalLift_properties α hα hP hS
  have _ : (P.map α).IsPrime := hP'
  have _ : IsRegularLocalRing (R' ⧸ P.map α) := hS'
  obtain ⟨T', β, hcan⟩ := t.exists_isCanonicalLift_of_isRegular α hα hP hS
  have _ : IsLocalHom β := hcan.isLocalHom
  have hP'0 : P.map α ≠ ⊥ := fun h => T'.x_ne_zero (Ideal.mem_bot.mp (h.le T'.x_mem))
  have _ : IsRegularLocalRing T'.ring := (MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map T' hP' hP'0 hS').1
  have hsepT' : RingHom.IsResiduallySeparableAlgebraic (R := R') (R' := T'.ring) T'.toRing :=
    isResiduallySeparableAlgebraic_of_closure_eq_top t.toRing α β T'.toRing hcan.comm.symm hsep
      (by rw [Set.union_comm]; exact (h2 t T' β hcan).2.2.2.2)
  have hrat' : RingHom.IsResiduallyRational (R := R') (R' := T'.ring) T'.toRing := by
    let _ : Algebra (ResidueField R') (ResidueField T'.ring) :=
      (ResidueField.map T'.toRing).toAlgebra
    have _ : Algebra.IsSeparable (ResidueField R') (ResidueField T'.ring) := hsepT'
    exact IsSepClosed.algebraMap_surjective (ResidueField R') (ResidueField T'.ring)
  -- `R₁ → R₁'` transforms a regular system of parameters into one (Lemma 4)
  have hβrsop : RingHom.MapsRSOP β := by
    obtain ⟨-, s, hs⟩ := (isRegularLocalRing_iff_exists_rsop t.ring).mp inferInstance
    exact ⟨s, hs, (h3 t T' β hcan).2 hsepα s hs, (h2 t T' β hcan).2.2.2.1.injOn⟩
  -- faithful flatness of `α` and `β`
  let _ : Algebra R R' := α.toAlgebra
  have _ : IsLocalHom (algebraMap R R') := ‹IsLocalHom α›
  have _ : Module.Flat R R' := hα.flat
  have _ : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hMα : (maximalIdeal R).map α = maximalIdeal R' := by
    obtain ⟨s, hs, hs', -⟩ := hα
    rw [← hs.1, Ideal.map_span, ← hs'.1, Finset.coe_image]
  have hordα : ∀ (I : Ideal R) (a : R), Ideal.ordElem (I.map α) (α a) = Ideal.ordElem I a :=
    fun I a => Ideal.ordElem_map_algebraMap_of_faithfullyFlat (B := R') I a
  let _ : Algebra t.ring T'.ring := β.toAlgebra
  have _ : IsLocalHom (algebraMap t.ring T'.ring) := ‹IsLocalHom β›
  have _ : Module.Flat t.ring T'.ring := hβrsop.flat
  have _ : Module.FaithfullyFlat t.ring T'.ring := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hMβ : (maximalIdeal t.ring).map β = maximalIdeal T'.ring := by
    obtain ⟨s, hs, hs', -⟩ := hβrsop
    rw [← hs.1, Ideal.map_span, ← hs'.1, Finset.coe_image]
  have hordβ : ∀ a : t.ring,
      Ideal.ordElem (maximalIdeal T'.ring) (β a) = Ideal.ordElem (maximalIdeal t.ring) a := by
    intro a
    have := Ideal.ordElem_map_algebraMap_of_faithfullyFlat (B := T'.ring) (maximalIdeal t.ring) a
    rw [← hMβ]
    exact this
  -- the transformed data over `R'`
  have hx' : (P.map α).map T'.toRing = Ideal.span {T'.toRing (α x)} := by
    have := congrArg (Ideal.map β) hx
    rw [Ideal.map_map, hcan.comm, ← Ideal.map_map, Ideal.map_span, Set.image_singleton] at this
    rw [this]
    congr 2
    exact RingHom.congr_fun hcan.comm x
  have hsb' : IsStandardBase T'.ring (strictTransformIdeal T' (J.map α)) fun j => β (g j) := by
    refine isStandardBase_strictTransformIdeal_of_isResiduallyRational (J.map α) (P.map α) T' hrat' (α x) hx' (fun j => α (f j)) ν _
      (fun j => ?_) (fun j => ?_) ((isStandardBase_iff_isStandardBase_map α hα J f).mp hi)
      (fun j => ?_) (fun j => ?_)
    · rw [← hMα, hordα, hν]
    · have hc : T'.toRing (α x) = β (t.toRing x) := by
        first
          | exact RingHom.congr_fun hcan.comm x
          | exact (RingHom.congr_fun hcan.comm x).symm
      rw [← map_pow, ← RingHom.comp_apply, ← hcan.comm, RingHom.comp_apply, ← hg j, map_mul,
        map_pow, map_pow, hc]
    · rw [hordα, ← hMα, hordα, hii]
    · rw [hordβ, hiii]
  have hJ₁ : strictTransformIdeal T' (J.map α) = (strictTransformIdeal t J).map β :=
    (strictTransform_map_of_mapsRSOP α hα J P hJP t T' β hcan.comm).1
  rw [hJ₁] at hsb'
  have hsb : IsStandardBase t.ring (strictTransformIdeal t J) g :=
    (isStandardBase_iff_isStandardBase_map β hβrsop _ g).mpr hsb'
  refine ⟨hsb, ?_⟩
  -- `ν*(J₁) = ν*(J)`: both are `(ν₁, …, ν_m, ∞, …)`
  simp only [nuStar]
  congr 1
  funext i
  by_cases hi' : (i : ℕ) ≤ m
  · have hi1 : (i : ℕ) - 1 < m := by have := i.pos; omega
    have h1 := ordElem_eq_nuI_of_isStandardBase _ g hsb ⟨(i : ℕ) - 1, hi1⟩
    have h2 := ordElem_eq_nuI_of_isStandardBase _ f hi ⟨(i : ℕ) - 1, hi1⟩
    have h3 : (((⟨(i : ℕ) - 1, hi1⟩ : Fin m) : ℕ)).succPNat = i := by
      apply PNat.eq; simp; have := i.pos; omega
    rw [h3] at h1 h2
    rw [← h1, ← h2, hiii, hν]
  · rw [(nuI_eq_of_hasLemma1Properties _ _ _ hsb.2).2 i (by omega),
      (nuI_eq_of_hasLemma1Properties _ _ _ hi.2).2 i (by omega)]

end Thm5General

end PE5Theorem5Aux

/-! ### Theorem 5 (pp. 238–241) -/

section Theorem5

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- Theorem 5, pp. 238–239: "Let `R` be a regular local ring, `J` an ideal in `R`, and `P` a
prime ideal in `R` such that `R/P` is regular and `P ⊇ J`. Let `R₁` be a monoidal transform of
`R` with center `P` which is residually separable algebraic over `R`, and `J₁` the strict
transform of `J` in `R₁`. Let `M` (resp. `M₁`) be the maximal ideal of `R` (resp. `R₁`). Let `x`
be an element of `P` such that `PR₁ = (x)R₁`. Suppose we have a system of elements
`(f₁, …, f_m)` of `J` such that the following conditions are satisfied: (i) `(f₁, …, f_m)` is a
standard base of `J`, (ii) `ν_P(f_j) = ν_M(f_j)` for `1 ≤ j ≤ m`, and
(iii) `ν_{M₁}(x^{-ν_j} f_j) = ν_M(f_j)` for `1 ≤ j ≤ m`, where `ν_j = ν_M(f_j) = ν^{(j)}(J)`.
Let `g_j = x^{-ν_j} f_j` for `1 ≤ j ≤ m`. Then `(g₁, …, g_m)` is a standard base of `J₁`. In
particular, `ν*(J₁) = ν*(J)`."

Formalization notes (encoding).
* `[IsLocalHom t.toRing]` and `[IsRegularLocalRing t.ring]` are lemmas of §2 (pp. 209–210), global
  instances (see the module docstring); they are not hypotheses.
* The paper writes `ν_j = ν_M(f_j) = ν^{(j)}(J)`; the second equality is an automatic
  consequence of (i) by Lemma 1 (p. 205), so only `ν_j = ν_M(f_j)` is taken as a hypothesis
  (`hν`).  Adding `ν_j = ν^{(j)}(J)` as a further hypothesis would weaken the statement.
* `g_j = x^{-ν_j} f_j` is the element `g j` of `R₁` with `(t.toRing x)^{ν_j} * g j = t.toRing
  (f j)`; `R₁` is a domain and `t.toRing x ≠ 0`, so `g j` is unique.

The proof follows the printed one (pp. 238--241): the reduction to the case in which `R₁` is residually
rational over `R` is the paper's (the proof of Theorem 3, with the Remark on both sides); in that case
(`TransformCoord.isStandardBase_strictTransformIdeal_of_isResiduallyRational`), for `f ∈ J` with
`ν_P(f) ≥ ν > 0` the expansion `f = Σ c_{(a)β} x^β x^a + f'` with `f' ∈ P^{ν+μ₁+1}`
(`exists_pAdicExpansion`), the inequalities "`β + a₁ + ⋯ + a_r ≥ ν`" and `(*)`, the element `h` with the
properties (1)--(4) (`exists_mem_ideal_sub_mem_pow_succ`) and the repetition of the replacement of `f` by
`f - h` (`mk_mem_span_initialForm`: an induction on `ν + μ₁ + 1 - ν_M(f)` with the printed case
distinction on `ν_{M₁}(g - x^{-ν}h)`) are those of the paper.  The expansion is encoded as a polynomial in
all the coordinates (see `exists_pAdicExpansion`), and the comparison of the coefficients of
`X^β T_α(Y)` in `ξ_{αβ} = Σ_i ξ_{αβi} φ_i` is done for all `(α, β)` at once, by `restrictSupport`
(see `exists_mem_ideal_sub_mem_pow_succ`).  The hypothesis `hxP : x ∈ P` is not used.

Deviation from the paper (gap filled): the paper stops at "the proof of Theorem 5 will follow if
we can show `gr_{M₁}(J₁, R₁) = (ψ₁, …, ψ_m)`"; Lean also proves the non-redundancy of the `ψ_j`
via the homomorphism `ρ : gr_{M₁}(R₁) → gr_M(R)` of the proof of Lemma 15 (`ρ(ψ_j) = φ_j`).  The
following printed steps are asserted without argument and are proved:
* "`J₁` is obtained by localization from the ideal `⋃ x^{-ν}(J ∩ P^ν)` in the ring `A₁`": every element
  of `J₁` is a unit times some `x^{-ν} f`, `f ∈ J`, `ν_P(f) ≥ ν`
  (`TransformCoord.exists_isUnit_mul_eq_of_mem_strictTransformIdeal`);
* the existence of the expansion `f = Σ c_{(a)β} x^β x^a + f'` with `c_{(a)β} ∈ (y)^{t_{(a)β}} R`,
  `t_{(a)β} = ν_M(c_{(a)β})`, and the claims "`β + a₁ + ⋯ + a_r ≥ ν`", "`t_{(a)β} + β + a₁ + ⋯ + a_r ≥ μ`"
  and `(*)` (`exists_pAdicExpansion`; the claim `β + |a| ≥ ν` needs an expansion chosen starting from
  `f ∈ P^ν`);
* `ν_M(f) ≤ ν_{M₁}(g) + ν`, whence `f' ∈ M^{ν+μ₁+1} ⊆ M^{μ+1}`;
* that the `φ_j` are forms only in `X₁, …, X_r` (from (iii) and `x^{ν_j} g_j = f_j`). -/
@[blueprint "thm:III.5"
  (statement := /-- Let $R$ be a regular local ring, $J$ an ideal in $R$, and $P$ a prime ideal
    in $R$ such that $R/P$ is regular and $P\supseteq J$. Let $R_1$ be a monoidal transform of
    $R$ with center $P$ (\cref{def:III.2-monoidal-transform}) which is residually separable
    algebraic over $R$ (\cref{def:III.2-residually}), and $J_1$ the strict transform of $J$ in
    $R_1$ (\cref{def:III.5-strict}). Let $M$ (resp.\ $M_1$) be the maximal ideal of $R$
    (resp.\ $R_1$). Let $x$ be an element of $P$ such that $PR_1=(x)R_1$. Suppose we have a
    system of elements $(f_1,\dots,f_m)$ of $J$ such that the following conditions are
    satisfied:
    (i) $(f_1,\dots,f_m)$ is a standard base of $J$ (\cref{def:III.3});
    (ii) $\nu_P(f_j)=\nu_M(f_j)$ for $1\le j\le m$; and
    (iii) $\nu_{M_1}(x^{-\nu_j}f_j)=\nu_M(f_j)$ for $1\le j\le m$, where
    $\nu_j=\nu_M(f_j)=\nu^{(j)}(J)$.
    Let $g_j=x^{-\nu_j}f_j$ for $1\le j\le m$. Then $(g_1,\dots,g_m)$ is a standard base of
    $J_1$. In particular, $\nu^*(J_1)=\nu^*(J)$. (Theorem 5, pp.~238--239.)
    (Formalization note (encoding): the equality $\nu_j=\nu^{(j)}(J)$ of the paper's display is a
    consequence of (i) and Lemma~1 (\cref{lem:III.1}), so only $\nu_j=\nu_M(f_j)$ is assumed;
    that $R\to R_1$ is a local homomorphism and that $R_1$ is a regular local ring are the
    lemmas of \S2, assumed here as hypotheses.) -/)
  (proof := /-- In view of the above remark (\cref{rem:III.6-standard-base-ascent}), the same
    argument as in the proof of Theorem~3 (\cref{thm:III.3}) can be used to reduce the problem
    to the case in which $R_1$ is residually rational over $R$. We shall assume this. We have a
    regular system of parameters $(x,x_1,\dots,x_r,y_1,\dots,y_s)$ of $R$ such that
    $P=(x,x_1,\dots,x_r)R$, and $(x,x_1/x,\dots,x_r/x,y_1,\dots,y_s)$ is a regular system of
    parameters of $R_1$. As in the proof of Lemma~14 of \S5 (\cref{lem:III.14}), we make the
    following identifications:
    $$\operatorname{gr}_M(R)=k[X,X_1,\dots,X_r,Y_1,\dots,Y_s],\qquad
      \operatorname{gr}_{M_1}(R_1)=k[X,\bar X_1,\dots,\bar X_r,Y_1,\dots,Y_s],$$
    where $k=R/M=R_1/M_1$. Let $\varphi_j$ (resp.\ $\psi_j$) be the initial form of $f_j$
    (resp.\ $g_j$) in $\operatorname{gr}_M(R)$ (resp.\ $\operatorname{gr}_{M_1}(R_1)$) for
    $1\le j\le m$. By the assumptions (ii) and (iii), the $\varphi_j$ are all forms only in
    $X_1,\dots,X_r$, and the forms $\psi_j$ can be written as
    $\psi_j=\varphi_j(\bar X_1,\dots,\bar X_r)+\lambda_j$, where $\lambda_j$ is a form of degree
    $\nu_j$ and is contained in the ideal $(X,Y_1,\dots,Y_s)\operatorname{gr}_{M_1}(R_1)$.
    Therefore, the proof of Theorem~5 will follow if we can show that
    $\operatorname{gr}_{M_1}(J_1,R_1)=(\psi_1,\dots,\psi_m)\operatorname{gr}_{M_1}(R_1)$.
    Since $J_1$ is obtained by localization from the ideal
    $\bigcup_{\nu=1}^{\infty}x^{-\nu}(J\cap P^\nu)$
    in the ring $A_1=R[x_1/x,\dots,x_r/x]$ with respect to the prime ideal $A_1\cap M_1$, it is
    sufficient to show that for every $f\in J$ with $\nu_P(f)\ge\nu>0$, the initial form of
    $x^{-\nu}f$ in $\operatorname{gr}_{M_1}(R_1)$ belongs to the ideal
    $I=(\psi_1,\dots,\psi_m)\operatorname{gr}_{M_1}(R_1)$.

    Now, take an arbitrary element $f\in J$ such that $\nu_P(f)\ge\nu>0$. Let
    $\nu_M(f)=\mu$. Let $g=x^{-\nu}f$ and $\mu_1=\nu_{M_1}(g)$. We shall prove that we have
    then an element $h\in J$ such that
    (1) $\nu_P(h)\ge\nu$;
    (2) $\nu_M(f-h)>\mu$;
    (3) $\nu_{M_1}(g-x^{-\nu}h)\ge\mu_1$; and
    (4) the initial form of $x^{-\nu}h$ in $\operatorname{gr}_{M_1}(R_1)$ is in $I$ if
    $\nu_{M_1}(x^{-\nu}h)=\mu_1$.
    Suppose this is proved. If $\nu_{M_1}(g-x^{-\nu}h)>\mu_1$, then $g$ and $x^{-\nu}h$ should
    have the same initial form in $\operatorname{gr}_{M_1}(R_1)$, and hence the initial form of
    $g$ in $\operatorname{gr}_{M_1}(R_1)$ must be in $I$ by (4). If
    $\nu_{M_1}(g-x^{-\nu}h)=\mu_1$, then we replace $f$ by $f-h$ (and $g$ by $g-x^{-\nu}h$) and
    apply the same result. As long as $\nu_{M_1}(g-x^{-\nu}h)$ remains to be $\mu_1$, we repeat
    this process. But this process cannot be repeated infinitely, for the number $\nu_M(f)$ will
    be then made arbitrarily big while it should be bounded by $\nu_{M_1}(g)+\nu=\mu_1+\nu$.
    Thus it follows that the initial form of $g$ in $\operatorname{gr}_{M_1}(R_1)$ is in the
    ideal $I$.

    We shall prove the existence of an element $h\in J$ with the properties (1)--(4) for a given
    element $f\in J$ such that $\nu_P(f)\ge\nu>0$. Let $\varphi$ be the initial form of $f$ in
    $\operatorname{gr}_M(R)$. Then it can be written in the form
    $\varphi=\sum_\alpha\xi_\alpha T_\alpha(Y)$, where the $T_\alpha(Y)$ are distinct monomials
    in $Y_1,\dots,Y_s$ of degree $t_\alpha\ (\le\mu)$, and the $\xi_\alpha$ are forms of degree
    $\mu-t_\alpha$ only in $X,X_1,\dots,X_r$. Since $\nu_P(f)\ge\nu$, we have
    $\mu-t_\alpha\ge\nu$ for all $\alpha$. We write each $\xi_\alpha$ in the form
    $\xi_\alpha=\sum_\beta\xi_{\alpha\beta}X^\beta$, where the $\xi_{\alpha\beta}$ are forms
    of degree $\mu-t_\alpha-\beta\ (\ge0)$ only in $X_1,\dots,X_r$ for all $\alpha$ and $\beta$.
    Then we claim the following inequalities:
    $$2(\mu-t_\alpha-\beta)+\beta+t_\alpha\ \ge\ \nu+\mu_1\qquad\text{for all }\alpha,\beta.$$
    In fact, we write $f$ in the form
    $f=\big(\sum_{(a),\beta}c_{(a)\beta}x^\beta x_1^{a_1}\cdots x_r^{a_r}\big)+f'$, where
    $c_{(a)\beta}\in(y_1,\dots,y_s)^{t_{(a)\beta}}R$ with
    $t_{(a)\beta}=\nu_M(c_{(a)\beta})$ and $f'\in P^{\nu+\mu_1+1}$. Then we have
    $t_{(a)\beta}+\beta+a_1+\dots+a_r\ge\mu$ for all $((a),\beta)$ and, since
    $f'\in M^{\nu+\mu_1+1}\subseteq M^{\mu+1}$, the initial form $\varphi$ is the sum of those
    $\bar c_{(a)\beta}X^\beta X_1^{a_1}\cdots X_r^{a_r}$ such that
    $t_{(a)\beta}+\beta+a_1+\dots+a_r=\mu$, where $\bar c_{(a)\beta}$ is the initial
    form of $c_{(a)\beta}$ in $\operatorname{gr}_M(R)$, which is obviously a form only in
    $Y_1,\dots,Y_s$. The assumption $\nu_P(f)\ge\nu$ implies that $\beta+a_1+\dots+a_r\ge\nu$
    for all $((a),\beta)$. If we write $\beta'$ for $\beta+a_1+\dots+a_r-\nu$ for each
    $((a),\beta)$, then
    $$g=\Big(\sum_{(a),\beta}c_{(a)\beta}\,x^{\beta'}(x_1/x)^{a_1}\cdots(x_r/x)^{a_r}\Big)
      +x^{-\nu}f'.$$
    Since $x^{-\nu}f'\in M_1^{\mu_1+1}$, the assumption $\mu_1=\nu_{M_1}(g)$ implies that
    $t_{(a)\beta}+\beta'+a_1+\dots+a_r\ge\mu_1$ for all $((a),\beta)$, i.e.
    $$(*)\qquad 2(a_1+\dots+a_r)+\beta+t_{(a)\beta}\ \ge\ \nu+\mu_1
      \qquad\text{for all }((a),\beta).$$
    Comparing the expression
    $\varphi=\sum_{(a),\beta}\bar c_{(a)\beta}X^\beta X_1^{a_1}\cdots X_r^{a_r}$ obtained above
    with the
    expression $\varphi=\sum_{\alpha,\beta}\xi_{\alpha\beta}X^\beta T_\alpha(Y)$ previously
    given, we get from $(*)$ the claimed inequalities
    $2(\mu-t_\alpha-\beta)+\beta+t_\alpha\ge\nu+\mu_1$ for all $\alpha$ and $\beta$.

    Now, $\varphi$ belongs to
    $\operatorname{gr}_M(J,R)=(\varphi_1,\dots,\varphi_m)\operatorname{gr}_M(R)$, and the
    $\varphi_i$ are forms only in $X_1,\dots,X_r$. Therefore we can write
    $\xi_{\alpha\beta}=\sum_i\xi_{\alpha\beta i}\varphi_i$, where the $\xi_{\alpha\beta i}$
    are forms in $X_1,\dots,X_r$ of degree $\mu-t_\alpha-\beta-\nu_i\ (\ge0)$. Let us choose,
    for each $\xi_{\alpha\beta i}\ne0$, an element
    $h_{\alpha\beta i}\in(x_1,\dots,x_r)^{\mu-t_\alpha-\beta-\nu_i}R$ whose initial form in
    $\operatorname{gr}_M(R)$ is equal to $\xi_{\alpha\beta i}$. Let
    $$h=\sum_{\alpha,\beta,i}h_{\alpha\beta i}f_ix^\beta T_\alpha(y),$$
    where $T_\alpha(y)$ denotes the monomial in $y_1,\dots,y_s$ obtained from $T_\alpha(Y)$ by
    replacing $Y_j$ by $y_j$ $(1\le j\le s)$. Then
    $\nu_M(h)\ge(\mu-t_\alpha-\beta-\nu_i)+\nu_i+\beta+t_\alpha=\mu$, and $h$ has the same
    initial form as $f$. Therefore we have (2).
    $\nu_P(h)\ge\operatorname{Min}(\mu-t_\alpha-\beta-\nu_i+\nu_i+\beta)
    =\operatorname{Min}(\mu-t_\alpha)\ge\nu$, hence we have (1). We can express $x^{-\nu}h$ in
    the form
    $$x^{-\nu}h=\sum_{\alpha,\beta,i}h'_{\alpha\beta i}g_ix^{\beta''}T_\alpha(y),$$
    where $h'_{\alpha\beta i}=h_{\alpha\beta i}/x^{\mu-t_\alpha-\beta-\nu_i}$ and
    $\beta''=(\mu-t_\alpha-\beta-\nu_i)+\nu_i+\beta-\nu=(\mu-t_\alpha-\beta)+\beta-\nu$. Hence
    $\nu_{M_1}(x^{-\nu}h)\ge\operatorname{Min}(\mu-t_\alpha-\beta-\nu_i+\nu_i+\beta''+t_\alpha)
    =\operatorname{Min}(2(\mu-t_\alpha-\beta)+\beta+t_\alpha-\nu)\ge\mu_1$. Hence (3).
    Moreover, the above expression of $x^{-\nu}h$ tells us that, if
    $\nu_{M_1}(x^{-\nu}h)=\mu_1$, then the initial form of $x^{-\nu}h$ in
    $\operatorname{gr}_{M_1}(R_1)$ belongs to the ideal $I$ generated by the initial forms of
    the $g_i$. Thus (4). \qed

    \textbf{Lean.} The Lean proof follows this argument step by step: the expansion of $f$ is encoded as a
    polynomial in all the coordinates $x,x_1,\dots,x_r,y_1,\dots,y_s$ (the coefficient $c_{(a)\beta}$
    being the value at $y$ of a form of degree $t_{(a)\beta}$ with a coefficient outside $M$), and the
    comparison of the coefficients of $X^\beta T_\alpha(Y)$ in
    $\xi_{\alpha\beta}=\sum_i\xi_{\alpha\beta i}\varphi_i$ is made for all $(\alpha,\beta)$ at once.
    The hypothesis $x\in P$ is not used.

    \textbf{Gap in the paper filled.} ``The proof of Theorem~5 will follow if we can show
    $\operatorname{gr}_{M_1}(J_1,R_1)=(\psi_1,\dots,\psi_m)\operatorname{gr}_{M_1}(R_1)$'': Lean
    also proves that no $\psi_i$ lies in $(\psi_1,\dots,\psi_{i-1})$, using the homomorphism
    $\rho\colon\operatorname{gr}_{M_1}(R_1)\to\operatorname{gr}_M(R)$ ($X,Y_j\mapsto0$,
    $\bar X_i\mapsto X_i$) of the proof of Lemma~15, with $\rho(\psi_j)=\varphi_j$. Lean proves the
    following printed assertions, made without argument: that every element of $J_1$ is a unit times some
    $x^{-\nu}f$ with $f\in J$ and $\nu_P(f)\ge\nu$ (``$J_1$ is obtained by localization from
    $\bigcup x^{-\nu}(J\cap P^\nu)$''); that the expansion $f=\sum c_{(a)\beta}x^\beta x_1^{a_1}\cdots
    x_r^{a_r}+f'$ exists, with $c_{(a)\beta}\in(y)^{t_{(a)\beta}}R$, $t_{(a)\beta}=\nu_M(c_{(a)\beta})$,
    and that it has the properties ``$\beta+a_1+\dots+a_r\ge\nu$'' (which needs an expansion chosen
    starting from $f\in P^\nu$), ``$t_{(a)\beta}+\beta+a_1+\dots+a_r\ge\mu$'' and $(*)$; that
    $\nu_M(f)\le\nu_{M_1}(g)+\nu$, whence $f'\in M^{\nu+\mu_1+1}\subseteq M^{\mu+1}$; and that the
    $\varphi_j$ are forms only in $X_1,\dots,X_r$. -/)
  (latexEnv := "theorem")]
theorem isStandardBase_strictTransform [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (J P : Ideal R) [P.IsPrime] [IsRegularLocalRing (R ⧸ P)]
    (hJP : J ≤ P) (t : MonoidalTransform R P)
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := t.ring) t.toRing)
    (x : R) (hxP : x ∈ P) (hx : P.map t.toRing = Ideal.span {t.toRing x})
    {m : ℕ} (f : Fin m → R) (ν : Fin m → ℕ)
    (g : Fin m → t.ring) (hν : ∀ j, (ν j : ℕ∞) = Ideal.ordElem (maximalIdeal R) (f j))
    (hg : ∀ j, t.toRing x ^ ν j * g j = t.toRing (f j))
    (hi : IsStandardBase R J f)
    (hii : ∀ j, Ideal.ordElem P (f j) = Ideal.ordElem (maximalIdeal R) (f j))
    (hiii : ∀ j, Ideal.ordElem (maximalIdeal t.ring) (g j) = (ν j : ℕ∞)) :
    IsStandardBase t.ring (strictTransformIdeal t J) g ∧
      nuStar t.ring (strictTransformIdeal t J) = nuStar R J := by
  exact isStandardBase_and_nuStar_eq_strictTransformIdeal J P hJP t hsep x hxP hx f ν g hν hg hi hii hiii

end Theorem5

/-! ### Corollary 1 of Theorem 5 (p. 241) -/

/-! ### Auxiliary facts for Corollaries 1 and 3 -/

section Corollary1Aux

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- `ν_I(f) ≤ ν_{I'}(f)` for `I ⊆ I'`. -/
theorem Ideal.ordElem_mono {A : Type*} [CommRing A] {I I' : Ideal A} (h : I ≤ I') (f : A) :
    Ideal.ordElem I f ≤ Ideal.ordElem I' f :=
  Ideal.ordElem_le fun _ hν => Ideal.le_ordElem (Ideal.pow_right_mono h _ hν)

/-- `ν_I(f) ≤ ν_{IB}(φ(f))` for a ring homomorphism `φ : A → B`. -/
private theorem Ideal.ordElem_le_ordElem_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (I : Ideal A) (f : A) : Ideal.ordElem I f ≤ Ideal.ordElem (I.map φ) (φ f) :=
  Ideal.ordElem_le fun _ hν => Ideal.le_ordElem (by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem φ hν)

/-- `ν_I(J)` of a principal ideal is the order of its generator. -/
private theorem Ideal.ord_span_singleton {A : Type*} [CommRing A] (I : Ideal A) (x : A) :
    Ideal.ord I (Ideal.span {x}) = Ideal.ordElem I x := by
  simp only [Ideal.ord, Ideal.ordElem, Ideal.span_singleton_le_iff_mem]

/-- If `R/P` is regular then `ν_{PR_P}(f) = ν_P(f)` (the powers of `P` are `P`-primary). -/
theorem ordElem_localization_eq_of_isRegularLocalRing_quotient (P : Ideal R) [P.IsPrime]
    (hP : IsRegularLocalRing (R ⧸ P)) (f : R) :
    Ideal.ordElem (P.map (algebraMap R (Localization.AtPrime P)))
      (algebraMap R (Localization.AtPrime P) f) = Ideal.ordElem P f := by
  have hsymb := ((order_facts R ⊤ P top_ne_bot).2.2 hP).1
  refine le_antisymm (Ideal.ordElem_le fun ν hν => Ideal.le_ordElem ?_)
    (Ideal.ordElem_le_ordElem_map _ P f)
  rw [← Ideal.map_pow] at hν
  rw [← hsymb ν]
  exact hν

/-- A regular local ring localized at a prime `P` with `R/P` regular is regular: `P` is generated
by part `T` of a regular system of parameters, a regular sequence, so `dim R_P ≥ #T`. -/
theorem isRegularLocalRing_localization_of_isRegularLocalRing_quotient (P : Ideal R) [P.IsPrime]
    (hP : IsRegularLocalRing (R ⧸ P)) : IsRegularLocalRing (Localization.AtPrime P) := by
  classical
  obtain ⟨S, T, hS, hScard, hTS, hT⟩ := exists_finset_span_eq_prime R P hP
  let z : Fin T.card → R := fun i => (T.equivFin.symm i : R)
  have hinj : Function.Injective z := Subtype.val_injective.comp T.equivFin.symm.injective
  have hrange : Set.range z = (T : Set R) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (T.equivFin.symm i).2
    · intro hy
      exact ⟨T.equivFin ⟨y, hy⟩, by simp [z]⟩
  have hreg := isRegular_ofFn_of_minimal hS hScard hinj (fun i => hTS (T.equivFin.symm i).2)
  have hmem : ∀ r ∈ List.ofFn z, r ∈ P := by
    intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    rw [← hT]
    exact Ideal.subset_span (T.equivFin.symm i).2
  have hregP := hreg.1.isRegular_of_isLocalization_of_mem (Localization.AtPrime P) P hmem
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hregP
  have hne : Ideal.ofList (List.map (algebraMap R (Localization.AtPrime P))
      (List.ofFn z)) ≠ ⊤ := by
    intro h
    apply hregP.2
    rw [h, smul_eq_mul, Ideal.top_mul]
  have _ := Ideal.Quotient.nontrivial_iff.mpr hne
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := Localization.AtPrime P ⧸
    Ideal.ofList (List.map (algebraMap R (Localization.AtPrime P)) (List.ofFn z)))
  rw [List.length_map, List.length_ofFn] at hdim
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hspan : (maximalIdeal (Localization.AtPrime P)).spanFinrank ≤ T.card := by
    have e : Ideal.map (algebraMap R (Localization.AtPrime P)) (Ideal.span (T : Set R)) =
        Ideal.span (algebraMap R (Localization.AtPrime P) '' T) := Ideal.map_span _ _
    rw [hT] at e
    rw [← Localization.AtPrime.map_eq_maximalIdeal, e]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (T.finite_toSet.image _)).trans ?_
    exact (Set.ncard_image_le T.finite_toSet).trans (Set.ncard_coe_finset T).le
  calc ((maximalIdeal (Localization.AtPrime P)).spanFinrank : WithBot ℕ∞)
      ≤ (T.card : WithBot ℕ∞) := by exact_mod_cast hspan
    _ ≤ ringKrullDim (Localization.AtPrime P) := by
      rw [← hdim]
      have : (0 : WithBot ℕ∞) + (T.card : WithBot ℕ∞) ≤ _ + (T.card : WithBot ℕ∞) :=
        add_le_add_left h0 _
      simpa using this

/-- Theorem 1 of §3 (Zariski–Nagata) applied to `R_P` (regular, `R/P` being regular), together
with `ν_{PR_P} = ν_P`: for primes `Q ⊆ P`, `ν_{QR_Q}(f) ≤ ν_P(f)`. -/
theorem ordElem_localization_le_ordElem_of_le [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (Q P : Ideal R) [Q.IsPrime] [P.IsPrime] (hQP : Q ≤ P)
    (hP : IsRegularLocalRing (R ⧸ P)) (f : R) :
    Ideal.ordElem (Q.map (algebraMap R (Localization.AtPrime Q)))
      (algebraMap R (Localization.AtPrime Q) f) ≤ Ideal.ordElem P f := by
  classical
  have _ : IsDomain R := Transforms.isDomain_of_isRegularLocalRing R
  by_cases hf : f = 0
  · rw [hf, Ideal.ordElem_eq_top_iff.mpr fun ν => zero_mem (P ^ ν)]
    exact le_top
  have _ : IsRegularLocalRing (Localization.AtPrime P) := isRegularLocalRing_localization_of_isRegularLocalRing_quotient P hP
  have hdisj : Disjoint (P.primeCompl : Set R) (Q : Set R) :=
    Set.disjoint_left.mpr fun a ha haQ => ha (hQP haQ)
  have _ : (Q.map (algebraMap R (Localization.AtPrime P))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl _ Q inferInstance hdisj
  have hpQ : (Q.map (algebraMap R (Localization.AtPrime P))).comap
      (algebraMap R (Localization.AtPrime P)) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint P.primeCompl _ inferInstance hdisj
  -- the canonical homomorphism `R_Q → (R_P)_{QR_P}`
  let p := Q.map (algebraMap R (Localization.AtPrime P))
  let g : R →+* Localization.AtPrime p :=
    (algebraMap (Localization.AtPrime P) (Localization.AtPrime p)).comp
      (algebraMap R (Localization.AtPrime P))
  have hg : ∀ y : Q.primeCompl, IsUnit (g y) := by
    intro y
    refine (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p _).mpr ?_
    intro hy
    have hy' : (y : R) ∈ p.comap (algebraMap R (Localization.AtPrime P)) := hy
    exact y.2 (hpQ.le hy')
  let φ : Localization.AtPrime Q →+* Localization.AtPrime p :=
    IsLocalization.lift (M := Q.primeCompl) hg
  have hmap : (Q.map (algebraMap R (Localization.AtPrime Q))).map φ =
      maximalIdeal (Localization.AtPrime p) := by
    rw [Ideal.map_map, IsLocalization.lift_comp, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_map]
  have hx0 : algebraMap R (Localization.AtPrime P) f ≠ 0 := by
    intro h
    apply hf
    exact IsLocalization.injective (Localization.AtPrime P)
      (Ideal.primeCompl_le_nonZeroDivisors P) (h.trans (map_zero _).symm)
  have h1 := nu_localization_le (Localization.AtPrime P)
    (Ideal.span {algebraMap R (Localization.AtPrime P) f})
    (by rwa [ne_eq, Ideal.span_singleton_eq_bot]) p
  simp only [Ideal.nu, Ideal.map_span, Set.image_singleton, Ideal.ord_span_singleton] at h1
  calc _ ≤ Ideal.ordElem ((Q.map (algebraMap R (Localization.AtPrime Q))).map φ)
        (φ (algebraMap R (Localization.AtPrime Q) f)) := Ideal.ordElem_le_ordElem_map φ _ _
    _ = Ideal.ordElem (maximalIdeal (Localization.AtPrime p))
        (algebraMap (Localization.AtPrime P) (Localization.AtPrime p)
          (algebraMap R (Localization.AtPrime P) f)) := by
      rw [hmap, IsLocalization.lift_eq]
      rfl
    _ ≤ Ideal.ordElem (maximalIdeal (Localization.AtPrime P))
        (algebraMap R (Localization.AtPrime P) f) := h1
    _ = Ideal.ordElem P f := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact ordElem_localization_eq_of_isRegularLocalRing_quotient P hP f

/-- Multiplying by a unit does not change the order. -/
private theorem Ideal.ordElem_unit_mul {A : Type*} [CommRing A] (I : Ideal A) {u : A}
    (hu : IsUnit u) (a : A) : Ideal.ordElem I (u * a) = Ideal.ordElem I a := by
  obtain ⟨v, rfl⟩ := hu
  refine le_antisymm (Ideal.ordElem_le fun n hn => Ideal.le_ordElem ?_)
    (Ideal.ordElem_le fun n hn => Ideal.le_ordElem (Ideal.mul_mem_left _ _ hn))
  have := Ideal.mul_mem_left _ ((↑v⁻¹ : Aˣ) : A) hn
  rwa [← mul_assoc, Units.inv_mul, one_mul] at this

/-- Elements of `R[x⁻¹P]` are fractions `f / xᴺ`, with `N` as large as wanted. -/
theorem exists_forall_pow_mul_eq_of_mem_blowupAlgebra {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] {P : Ideal R} {x : R} (hx : x ≠ 0) {y : FractionRing R}
    (hy : y ∈ blowupAlgebra R P x) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ f : R,
      algebraMap R (FractionRing R) x ^ n * y = algebraMap R (FractionRing R) f := by
  have hx' : algebraMap R (FractionRing R) x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).mpr hx
  suffices h : ∃ (N : ℕ) (f : R),
      algebraMap R (FractionRing R) x ^ N * y = algebraMap R (FractionRing R) f by
    obtain ⟨N, f, hf⟩ := h
    refine ⟨N, fun n hn => ⟨x ^ (n - N) * f, ?_⟩⟩
    rw [map_mul, map_pow, ← hf, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨p, -, rfl⟩ := hy
    exact ⟨1, p, by rw [pow_one, mul_div_cancel₀ _ hx']⟩
  | algebraMap r => exact ⟨0, r, by rw [pow_zero, one_mul]⟩
  | add y z _ _ hy hz =>
    obtain ⟨N₁, f₁, h₁⟩ := hy
    obtain ⟨N₂, f₂, h₂⟩ := hz
    refine ⟨N₁ + N₂, x ^ N₂ * f₁ + x ^ N₁ * f₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← h₁, ← h₂]
    ring
  | mul y z _ _ hy hz =>
    obtain ⟨N₁, f₁, h₁⟩ := hy
    obtain ⟨N₂, f₂, h₂⟩ := hz
    refine ⟨N₁ + N₂, f₁ * f₂, ?_⟩
    rw [map_mul, ← h₁, ← h₂]
    ring

/-- `ν_I` is invariant under a ring isomorphism. -/
private theorem ordElem_map_equiv_eq {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (I : Ideal A) (a : A) : Ideal.ordElem (I.map (e : A →+* B)) (e a) = Ideal.ordElem I a := by
  refine le_antisymm ?_ (Ideal.ordElem_le_ordElem_map (e : A →+* B) I a)
  have h := Ideal.ordElem_le_ordElem_map (e.symm : B →+* A) (I.map (e : A →+* B)) (e a)
  have hI : (I.map (e : A →+* B)).map (e.symm : B →+* A) = I := by
    rw [Ideal.map_map]
    convert Ideal.map_id I
    exact RingHom.ext fun y => e.symm_apply_apply y
  rwa [hI, show (e.symm : B →+* A) (e a) = a from e.symm_apply_apply a] at h

/-- Corollary 1, p. 241: "Since we have `Q₁` such that `Q₁ ∩ R = Q ⊊ P`, we have `x ∈ P − Q` such
that `(x)R₁ = PR₁`": if `(x)R₁ = PR₁` and `Q₁ ∩ R = Q ≠ P`, then the image of `x` is not in `Q₁`
(equivalently `x ∉ Q`), for otherwise `PR₁ = (x)R₁ ⊆ Q₁` and `P ⊆ Q₁ ∩ R = Q`. -/
private theorem notMem_of_span_eq_map_of_comap_eq [IsDomain R] {P Q : Ideal R} (hQP : Q ≤ P)
    (hPneQ : P ≠ Q)
    (t : MonoidalTransform R P) {Q₁ : Ideal t.ring} (hQ₁ : Q₁.comap t.toRing = Q) {x : R}
    (hx : P.map t.toRing = Ideal.span {t.toRing x}) : t.toRing x ∉ Q₁ := by
  intro hxQ₁
  apply hPneQ
  refine le_antisymm (fun p hp => ?_) hQP
  rw [← hQ₁, Ideal.mem_comap]
  have hp' : t.toRing p ∈ P.map t.toRing := Ideal.mem_map_of_mem _ hp
  rw [hx, Ideal.mem_span_singleton] at hp'
  obtain ⟨c, hc⟩ := hp'
  rw [hc]
  exact Ideal.mul_mem_right _ _ hxQ₁

/-- Corollary 1, p. 241: "It follows that `R_Q = (R₁)_{Q₁}`".  Let `R₁ = R[x⁻¹P]_{M'}` be a
monoidal transform of `R` with center `P` and `Q₁` a prime of `R₁` with `Q₁ ∩ R = Q ⊊ P`.  Then
the canonical homomorphism `R_Q → (R₁)_{Q₁}` is an isomorphism, because `x ∉ Q` (so
`R[x⁻¹P] ⊆ R_x ⊆ R_Q`): every element of `R₁` is a fraction `f / d` with `f, d ∈ R`
(`exists_forall_pow_mul_eq_of_mem_blowupAlgebra`), and `d ∉ Q` if the fraction is a denominator
outside `Q₁`. -/
theorem MonoidalTransform.exists_ringEquiv_localization_of_comap_eq [IsDomain R] (P Q : Ideal R)
    [Q.IsPrime] (hQP : Q ≤ P) (hPneQ : P ≠ Q) (t : MonoidalTransform R P) (Q₁ : Ideal t.ring)
    [Q₁.IsPrime] (hQ₁ : Q₁.comap t.toRing = Q) :
    ∃ e : Localization.AtPrime Q ≃+* Localization.AtPrime Q₁, ∀ a : R,
      e (algebraMap R (Localization.AtPrime Q) a) =
        algebraMap t.ring (Localization.AtPrime Q₁) (t.toRing a) := by
  classical
  have hinj := MonoidalTransform.toRing_injective t
  have hxQ₁ : t.toRing t.x ∉ Q₁ :=
    notMem_of_span_eq_map_of_comap_eq hQP hPneQ t hQ₁ t.span_xR_eq_map.symm
  -- `X^n u ∉ Q₁` for a unit `u`
  have hnotmem : ∀ (n : ℕ) (u : t.ring), IsUnit u → t.toRing t.x ^ n * u ∉ Q₁ := by
    intro n u hu hmem
    rcases (inferInstance : Q₁.IsPrime).mem_or_mem hmem with h | h
    · exact hxQ₁ ((inferInstance : Q₁.IsPrime).mem_of_pow_mem n h)
    · exact (inferInstance : Q₁.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  -- every element of `R₁` is a fraction `r / d` with `r, d ∈ R`, `d = xⁿ u`, `u` a unit of `R₁`
  have hfrac : ∀ a : t.ring, ∃ (n : ℕ) (r d : R) (u : t.ring), IsUnit u ∧
      t.toRing d = t.toRing t.x ^ n * u ∧ a * t.toRing d = t.toRing r := by
    intro a
    obtain ⟨⟨b, c⟩, rfl⟩ := IsLocalization.mk'_surjective t.M'.primeCompl a
    obtain ⟨N₁, h₁⟩ := exists_forall_pow_mul_eq_of_mem_blowupAlgebra t.x_ne_zero b.2
    obtain ⟨N₂, h₂⟩ := exists_forall_pow_mul_eq_of_mem_blowupAlgebra t.x_ne_zero
      (c : blowupAlgebra R P t.x).2
    obtain ⟨r, hr⟩ := h₁ (max N₁ N₂) (le_max_left _ _)
    obtain ⟨d, hd⟩ := h₂ (max N₁ N₂) (le_max_right _ _)
    have hB : ∀ (y : blowupAlgebra R P t.x) (f : R),
        algebraMap R (FractionRing R) t.x ^ (max N₁ N₂) * (y : FractionRing R) =
          algebraMap R (FractionRing R) f →
        algebraMap R (blowupAlgebra R P t.x) t.x ^ (max N₁ N₂) * y =
          algebraMap R (blowupAlgebra R P t.x) f := fun y f h =>
      Subtype.ext (by simpa using h)
    have hr' : t.toRing t.x ^ (max N₁ N₂) * algebraMap (blowupAlgebra R P t.x) t.ring b =
        t.toRing r := by
      have := congrArg (algebraMap (blowupAlgebra R P t.x) t.ring) (hB b r hr)
      simpa [MonoidalTransform.toRing] using this
    have hd' : t.toRing d = t.toRing t.x ^ (max N₁ N₂) *
        algebraMap (blowupAlgebra R P t.x) t.ring (c : blowupAlgebra R P t.x) := by
      have := congrArg (algebraMap (blowupAlgebra R P t.x) t.ring) (hB c d hd)
      simpa [MonoidalTransform.toRing] using this.symm
    refine ⟨max N₁ N₂, r, d, algebraMap (blowupAlgebra R P t.x) t.ring (c : blowupAlgebra R P t.x),
      IsLocalization.map_units t.ring c, hd', ?_⟩
    rw [hd', ← hr']
    have hspec := IsLocalization.mk'_spec t.ring b c
    calc IsLocalization.mk' t.ring b c * (t.toRing t.x ^ (max N₁ N₂) *
          algebraMap (blowupAlgebra R P t.x) t.ring (c : blowupAlgebra R P t.x))
        = t.toRing t.x ^ (max N₁ N₂) * (IsLocalization.mk' t.ring b c *
          algebraMap (blowupAlgebra R P t.x) t.ring (c : blowupAlgebra R P t.x)) := by ring
      _ = _ := by rw [hspec]
  -- `(R₁)_{Q₁}` is a localization of `R` at `Q`
  let g : R →+* Localization.AtPrime Q₁ :=
    (algebraMap t.ring (Localization.AtPrime Q₁)).comp t.toRing
  let _ : Algebra R (Localization.AtPrime Q₁) := g.toAlgebra
  have hloc : IsLocalization Q.primeCompl (Localization.AtPrime Q₁) := by
    refine ⟨fun y => ?_, fun z => ?_, fun {a b} hab => ?_⟩
    · exact (IsLocalization.AtPrime.isUnit_to_map_iff _ Q₁ _).mpr fun hy => y.2 (by
        have hy' : (y : R) ∈ Q₁.comap t.toRing := hy
        exact hQ₁.le hy')
    · obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q₁.primeCompl z
      obtain ⟨n₁, r₁, d₁, u₁, hu₁, hd₁, har₁⟩ := hfrac a
      obtain ⟨n₂, r₂, d₂, u₂, hu₂, hd₂, hsr₂⟩ := hfrac (s : t.ring)
      have hd₁Q : d₁ ∉ Q := fun h => hnotmem n₁ u₁ hu₁ (hd₁ ▸ by rw [← Ideal.mem_comap, hQ₁]; exact h)
      have hr₂Q : r₂ ∉ Q := fun h => by
        have h' : t.toRing r₂ ∈ Q₁ := by rw [← Ideal.mem_comap, hQ₁]; exact h
        rw [← hsr₂] at h'
        rcases (inferInstance : Q₁.IsPrime).mem_or_mem h' with h'' | h''
        · exact s.2 h''
        · exact hnotmem n₂ u₂ hu₂ (hd₂ ▸ h'')
      refine ⟨(r₁ * d₂, ⟨d₁ * r₂, fun h => ?_⟩), ?_⟩
      · rcases (inferInstance : Q.IsPrime).mem_or_mem h with h' | h'
        · exact hd₁Q h'
        · exact hr₂Q h'
      · show IsLocalization.mk' (Localization.AtPrime Q₁) a s *
          algebraMap t.ring (Localization.AtPrime Q₁) (t.toRing (d₁ * r₂)) =
            algebraMap t.ring (Localization.AtPrime Q₁) (t.toRing (r₁ * d₂))
        have hms := IsLocalization.mk'_spec (Localization.AtPrime Q₁) a s
        rw [map_mul t.toRing d₁ r₂, ← hsr₂, map_mul t.toRing r₁ d₂, ← har₁]
        simp only [map_mul]
        linear_combination
          (algebraMap t.ring (Localization.AtPrime Q₁) (t.toRing d₁) *
            algebraMap t.ring (Localization.AtPrime Q₁) (t.toRing d₂)) * hms
    · -- `algebraMap a = algebraMap b` gives `a = b` in `R` since `R → R₁` is injective
      have hab' : algebraMap t.ring (Localization.AtPrime Q₁) (t.toRing a) =
          algebraMap t.ring (Localization.AtPrime Q₁) (t.toRing b) := hab
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists Q₁.primeCompl _).mp hab'
      have hc0 : (c : t.ring) ≠ 0 := fun h0 => c.2 (h0 ▸ Q₁.zero_mem)
      have := mul_left_cancel₀ hc0 hc
      exact ⟨1, by rw [hinj this]⟩
  let e := IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) (Localization.AtPrime Q₁)
  exact ⟨e.toRingEquiv, fun a => e.commutes a⟩

/-- Corollary 1, p. 241: "`ν_{Q₁(R₁)_{Q₁}}(g_j) = ν_{QR_Q}(g_j) = ν_{QR_Q}(f_j)`" (and, in the proof of
Corollary 3 (b), p. 243, "since `x` is a unit in `(R₁)_{Q₁}` and `R_Q = (R₁)_{Q₁}`, `ν_{QR_Q}(g_j) =
ν_{Q₁(R₁)_{Q₁}}(h_j)`"): if `x^ν h = f` with `(x)R₁ = PR₁`, `Q₁ ∩ R = Q ⊊ P`, then
`ν_{Q₁(R₁)_{Q₁}}(h) = ν_{QR_Q}(f)`.  The identification `R_Q = (R₁)_{Q₁}` is
`MonoidalTransform.exists_ringEquiv_localization_of_comap_eq`; it carries `QR_Q` to `Q₁(R₁)_{Q₁}`
(the maximal ideals) and `f` to `xᵛ h`, `x` being a unit of `(R₁)_{Q₁}`. -/
theorem ordElem_localization_eq_of_strictTransform [IsDomain R] (Q P : Ideal R) [Q.IsPrime]
    (hQP : Q ≤ P) (hPneQ : P ≠ Q) (t : MonoidalTransform R P) (Q₁ : Ideal t.ring) [Q₁.IsPrime]
    (hQ₁ : Q₁.comap t.toRing = Q) (x : R) (hx : P.map t.toRing = Ideal.span {t.toRing x})
    (f : R) (ν : ℕ) (h : t.ring) (hh : t.toRing x ^ ν * h = t.toRing f) :
    Ideal.ordElem (Q₁.map (algebraMap t.ring (Localization.AtPrime Q₁)))
        (algebraMap t.ring (Localization.AtPrime Q₁) h) =
      Ideal.ordElem (Q.map (algebraMap R (Localization.AtPrime Q)))
        (algebraMap R (Localization.AtPrime Q) f) := by
  obtain ⟨e, he⟩ := MonoidalTransform.exists_ringEquiv_localization_of_comap_eq P Q hQP hPneQ t Q₁
    hQ₁
  have hxQ₁ := notMem_of_span_eq_map_of_comap_eq hQP hPneQ t hQ₁ hx
  have hunit : IsUnit (algebraMap t.ring (Localization.AtPrime Q₁) (t.toRing x ^ ν)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff _ Q₁ _).mpr fun hmem =>
      hxQ₁ ((inferInstance : Q₁.IsPrime).mem_of_pow_mem ν hmem)
  have hmap : (Q.map (algebraMap R (Localization.AtPrime Q))).map (e : _ →+* _) =
      Q₁.map (algebraMap t.ring (Localization.AtPrime Q₁)) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.map_ringEquiv_maximalIdeal e
  have hef : e (algebraMap R (Localization.AtPrime Q) f) =
      algebraMap t.ring (Localization.AtPrime Q₁) (t.toRing x ^ ν) *
        algebraMap t.ring (Localization.AtPrime Q₁) h := by
    rw [he, ← hh, map_mul]
  rw [← hmap, ← ordElem_map_equiv_eq e (Q.map (algebraMap R (Localization.AtPrime Q))), hef,
    Ideal.ordElem_unit_mul _ hunit]

/-- Lemma 8 of §3 (p. 217), as used in the proofs of Corollary 1 (p. 241, the bound left implicit in
"Therefore `ν_{M₁}(g_j) = ν_M(f_j)`") and of Corollary 3 (b) (p. 243, "the equality `ν_M(g_j) =
ν_{M₁}(h_j)` is easily obtained by means of Lemma 8 and Theorem 1, §3"): if `ν = ν_P(f)`,
`ν_M(f) = ν_P(f)` and `x^ν h = f` with `(x)R₁ = PR₁`, then `(h)` is the weak transform of `(f)` and
`ν_{M₁}(h) ≤ ν_M(f)`. -/
private theorem ordElem_maximalIdeal_le_of_weakTransform [IsDomain R] (P : Ideal R) [P.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] (t : MonoidalTransform R P)
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := t.ring) t.toRing) (x : R)
    (hx : P.map t.toRing = Ideal.span {t.toRing x}) (hx0 : t.toRing x ≠ 0) (f : R) (ν : ℕ)
    (hν : (ν : ℕ∞) = Ideal.ordElem P f)
    (hMP : Ideal.ordElem (maximalIdeal R) f = Ideal.ordElem P f) (h : t.ring)
    (hh : t.toRing x ^ ν * h = t.toRing f) :
    Ideal.ordElem (maximalIdeal t.ring) h ≤ Ideal.ordElem (maximalIdeal R) f := by
  classical
  have hf0 : f ≠ 0 := fun h0 => by
    rw [h0, Ideal.ordElem_eq_top_iff.mpr fun n => zero_mem (P ^ n)] at hν
    exact ENat.natCast_ne_top _ hν
  have hJ0 : Ideal.span {f} ≠ ⊥ := by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact hf0
  have hPJ : Ideal.ord P (Ideal.span {f}) = Ideal.nu (Ideal.span {f}) := by
    simp only [Ideal.nu, Ideal.ord_span_singleton, hMP]
  have halg : RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing := by
    let _ : Algebra (ResidueField R) (ResidueField t.ring) :=
      (ResidueField.map t.toRing).toAlgebra
    have _ : Algebra.IsSeparable (ResidueField R) (ResidueField t.ring) := hsep
    exact Algebra.IsSeparable.isAlgebraic _ _
  have h8 := nu_weakTransform_le R (Ideal.span {f}) hJ0 P hPJ t halg
  obtain ⟨-, -, -, -, h5⟩ := t.divIdeal_monotone_and_strictTransformIdeal_eq_iSup inferInstance
    inferInstance (Ideal.span {f}) (t.toRing x) hx.symm
  obtain ⟨ν', hν', -, hweak⟩ := h5 hJ0 (Ideal.IsPrime.ne_top inferInstance)
  have hνν' : ν' = ν := by
    have : (ν' : ℕ∞) = ν := by rw [← hν', Ideal.ord_span_singleton, hν]
    exact_mod_cast this
  have hdiv : t.divIdeal (t.toRing x) ν' (Ideal.span {f}) = Ideal.span {h} := by
    rw [hνν']
    apply le_antisymm
    · rw [MonoidalTransform.divIdeal, Ideal.span_le]
      rintro y ⟨f', hf', hy⟩
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hf'
      rw [SetLike.mem_coe, Ideal.mem_span_singleton']
      refine ⟨t.toRing r, mul_left_cancel₀ (pow_ne_zero ν hx0) ?_⟩
      rw [hy, map_mul, ← hh]
      ring
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span ⟨f, Ideal.mem_span_singleton_self _, hh⟩
  rw [hweak, hdiv] at h8
  simpa only [Ideal.nu, Ideal.ord_span_singleton] using h8

/-- The orders in the proof of Corollary 3 (b), p. 243 (the printed route): "`x` is a unit in
`(R₁)_{Q₁}` and `R_Q = (R₁)_{Q₁}`, so that `ν_{QR_Q}(g_j) = ν_{Q₁(R₁)_{Q₁}}(h_j)`.  Now, the equality
`ν_M(g_j) = ν_{M₁}(h_j)` is easily obtained by means of Lemma 8 and Theorem 1, §3."  With
`x^ν h = f`, `ν_M(f) = ν_P(f)` and `ν_M(f) = ν_{QR_Q}(f)`:
`ν_M(f) ≥ ν_{M₁}(h)` (Lemma 8, `ordElem_maximalIdeal_le_of_weakTransform`), and
`ν_M(f) = ν_{QR_Q}(f) = ν_{Q₁(R₁)_{Q₁}}(h)` (`ordElem_localization_eq_of_strictTransform`, from
`R_Q = (R₁)_{Q₁}`) `≤ ν_{M₁}(h)` (Theorem 1 of §3 in `R₁`).  Hence
`ν_{M₁}(h) = ν_M(f) = ν_{Q₁(R₁)_{Q₁}}(h)`. -/
theorem ordElem_eq_and_ordElem_localization_eq_of_strictTransform [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsDomain R] (Q P : Ideal R) [Q.IsPrime]
    [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] (hQP : Q ≤ P) (hPneQ : P ≠ Q)
    (t : MonoidalTransform R P)
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := t.ring) t.toRing)
    (Q₁ : Ideal t.ring) [Q₁.IsPrime] (hQ₁ : Q₁.comap t.toRing = Q) (x : R)
    (hx : P.map t.toRing = Ideal.span {t.toRing x}) (f : R) (ν : ℕ)
    (hν : (ν : ℕ∞) = Ideal.ordElem P f) (h : t.ring) (hh : t.toRing x ^ ν * h = t.toRing f)
    (hMP : Ideal.ordElem (maximalIdeal R) f = Ideal.ordElem P f)
    (hMQ : Ideal.ordElem (maximalIdeal R) f = Ideal.ordElem
      (Q.map (algebraMap R (Localization.AtPrime Q))) (algebraMap R (Localization.AtPrime Q) f)) :
    Ideal.ordElem (maximalIdeal t.ring) h = Ideal.ordElem (maximalIdeal R) f ∧
      Ideal.ordElem (maximalIdeal (Localization.AtPrime Q₁))
        (algebraMap t.ring (Localization.AtPrime Q₁) h) =
          Ideal.ordElem (maximalIdeal t.ring) h := by
  classical
  have hinj := MonoidalTransform.toRing_injective t
  have hf0 : f ≠ 0 := fun h0 => by
    rw [h0, Ideal.ordElem_eq_top_iff.mpr fun n => zero_mem (P ^ n)] at hν
    exact ENat.natCast_ne_top _ hν
  have hxQ₁ : t.toRing x ∉ Q₁ := notMem_of_span_eq_map_of_comap_eq hQP hPneQ t hQ₁ hx
  have hx0 : t.toRing x ≠ 0 := fun h' => hxQ₁ (h' ▸ Q₁.zero_mem)
  have hh0 : h ≠ 0 := fun h0 => hf0 (hinj (by rw [← hh, h0, mul_zero, map_zero]))
  have hmaxA₁ : Q₁.map (algebraMap t.ring (Localization.AtPrime Q₁)) =
      maximalIdeal (Localization.AtPrime Q₁) := Localization.AtPrime.map_eq_maximalIdeal
  -- (1) Lemma 8 of §3: `ν_{M₁}(h) ≤ ν_M(f)`, the weak transform of `(f)` being `(h)`
  have hL8 : Ideal.ordElem (maximalIdeal t.ring) h ≤ Ideal.ordElem (maximalIdeal R) f :=
    ordElem_maximalIdeal_le_of_weakTransform P t hsep x hx hx0 f ν hν hMP h hh
  -- (2) `x` is a unit in `(R₁)_{Q₁}` and `R_Q = (R₁)_{Q₁}`: `ν_{Q₁(R₁)_{Q₁}}(h) = ν_{QR_Q}(f)`
  have hQeq : Ideal.ordElem (maximalIdeal (Localization.AtPrime Q₁))
      (algebraMap t.ring (Localization.AtPrime Q₁) h) =
        Ideal.ordElem (Q.map (algebraMap R (Localization.AtPrime Q)))
          (algebraMap R (Localization.AtPrime Q) f) := by
    rw [← hmaxA₁]
    exact ordElem_localization_eq_of_strictTransform Q P hQP hPneQ t Q₁ hQ₁ x hx f ν h hh
  -- (3) Theorem 1 of §3 in `R₁`: `ν_{Q₁(R₁)_{Q₁}}(h) ≤ ν_{M₁}(h)`
  have hT1 : Ideal.ordElem (maximalIdeal (Localization.AtPrime Q₁))
      (algebraMap t.ring (Localization.AtPrime Q₁) h) ≤
        Ideal.ordElem (maximalIdeal t.ring) h := by
    have h1 := nu_localization_le t.ring (Ideal.span {h})
      (by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact hh0) Q₁
    simpa only [Ideal.nu, Ideal.map_span, Set.image_singleton, Ideal.ord_span_singleton] using h1
  -- the chain closes: `ν_M(f) = ν_{QR_Q}(f) = ν_{Q₁(R₁)_{Q₁}}(h) ≤ ν_{M₁}(h) ≤ ν_M(f)`
  have hlow : Ideal.ordElem (maximalIdeal R) f ≤
      Ideal.ordElem (maximalIdeal (Localization.AtPrime Q₁))
        (algebraMap t.ring (Localization.AtPrime Q₁) h) := by
    rw [hQeq, ← hMQ]
  exact ⟨le_antisymm hL8 (hlow.trans hT1), le_antisymm hT1 (hL8.trans hlow)⟩

/-- If `ρ : B = R[x⁻¹P] → B̄` is surjective with kernel `Q₁ ∩ B` and `R̄₁ = B̄_{ρ(M')}` is a
regular monoidal transform, then `R₁/Q₁ ≅ R̄₁` is regular. -/
private theorem isRegularLocalRing_quotient_of_surjective_blowupAlgebra {P : Ideal R}
    [IsDomain R] (t : MonoidalTransform R P) (Q₁ : Ideal t.ring) [Q₁.IsPrime] {Rb : Type u}
    [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {Pb : Ideal Rb}
    (Tb : MonoidalTransform Rb Pb)
    [IsRegularLocalRing Tb.ring] (ρ : blowupAlgebra R P t.x →+* blowupAlgebra Rb Pb Tb.x)
    (hsurj : Function.Surjective ρ)
    (hker : RingHom.ker ρ = Q₁.comap (algebraMap (blowupAlgebra R P t.x) t.ring))
    (hM : Tb.M' = t.M'.map ρ) : IsRegularLocalRing (t.ring ⧸ Q₁) := by
  have hqM : Q₁.comap (algebraMap (blowupAlgebra R P t.x) t.ring) ≤ t.M' := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal t.ring t.M']
    exact Ideal.comap_mono (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
  have hcomapM : (t.M'.map ρ).comap ρ = t.M' := by
    rw [Ideal.comap_map_of_surjective _ hsurj, sup_eq_left]
    exact (Ideal.comap_mono bot_le).trans (by rw [← RingHom.ker_eq_comap_bot, hker]; exact hqM)
  let iso₁ := (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have hiso₁ : ∀ s, iso₁ (Ideal.Quotient.mk _ s) = ρ s := fun s => by
    simp only [iso₁, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hQ₁eq : (Q₁.comap (algebraMap (blowupAlgebra R P t.x) t.ring)).map
      (algebraMap (blowupAlgebra R P t.x) t.ring) = Q₁ :=
    IsLocalization.map_under t.M'.primeCompl t.ring Q₁
  let φb : blowupAlgebra Rb Pb Tb.x →+* t.ring ⧸ Q₁ :=
    (Ideal.quotientMap Q₁ (algebraMap (blowupAlgebra R P t.x) t.ring) le_rfl).comp
      iso₁.symm.toRingHom
  let _ : Algebra (blowupAlgebra Rb Pb Tb.x) (t.ring ⧸ Q₁) := φb.toAlgebra
  have hH : (Ideal.Quotient.mk Q₁).comp (algebraMap (blowupAlgebra R P t.x) t.ring) =
      (algebraMap _ (t.ring ⧸ Q₁)).comp ρ := by
    refine RingHom.ext fun b => ?_
    show _ = φb (ρ b)
    simp only [φb, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← hiso₁, RingEquiv.symm_apply_apply, Ideal.quotientMap_mk]
  have hloc := IsLocalization.of_surjective t.M'.primeCompl t.ring ρ hsurj
    (Ideal.Quotient.mk Q₁) Ideal.Quotient.mk_surjective hH
    (by rw [Ideal.mk_ker, hker, hQ₁eq])
  have hsub : t.M'.primeCompl.map ρ = Tb.M'.primeCompl := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩ hy
      apply hs
      have h' : s ∈ (t.M'.map ρ).comap ρ := by rw [← hM]; exact hy
      rwa [hcomapM] at h'
    · intro hy
      obtain ⟨s, rfl⟩ := hsurj y
      exact ⟨s, fun h => hy (by rw [hM]; exact Ideal.mem_map_of_mem ρ h), rfl⟩
  rw [hsub] at hloc
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv Tb.M'.primeCompl Tb.ring (t.ring ⧸ Q₁)).toRingEquiv

/-- `R₁/Q₁` is a monoidal transform of `R/Q` with center `P/Q` (p. 241), hence regular. -/
private theorem MonoidalTransform.isRegularLocalRing_quotient_of_comap_eq [IsDomain R] (P Q : Ideal R) [P.IsPrime]
    [Q.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)] (hQP : Q ≤ P)
    (hQneP : Q ≠ P) (t : MonoidalTransform R P) (Q₁ : Ideal t.ring) [Q₁.IsPrime]
    (hQ₁ : Q₁.comap t.toRing = Q) : IsRegularLocalRing (t.ring ⧸ Q₁) := by
  classical
  set K := FractionRing R
  set x := t.x
  -- `x ∉ Q`
  have hxQ : x ∉ Q := by
    intro hxQ
    apply hQneP
    refine le_antisymm hQP fun p hp => ?_
    rw [← hQ₁, Ideal.mem_comap]
    have : t.toRing p ∈ P.map t.toRing := Ideal.mem_map_of_mem _ hp
    rw [← t.span_xR_eq_map, Ideal.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    rw [hc]
    refine Ideal.mul_mem_right _ _ ?_
    show t.toRing x ∈ Q₁
    rw [← Ideal.mem_comap, hQ₁]
    exact hxQ
  -- the localization `R_x` inside `K`
  have hxK : IsUnit (algebraMap R K x) :=
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr t.x_ne_zero)
  let ι : Localization.Away x →+* K := IsLocalization.Away.lift x hxK
  have hι : Function.Injective ι := by
    refine (IsLocalization.lift_injective_iff (M := Submonoid.powers x) _).mpr fun a b => ?_
    refine ⟨fun h => ?_, fun h => by rw [(IsFractionRing.injective R K) h]⟩
    have := congrArg ι h
    simpa only [ι, IsLocalization.Away.lift_eq] using this
  -- `R̄ = R/Q`, `P̄ = P/Q`, `x̄`
  have hxb : Ideal.Quotient.mk Q x ≠ 0 := by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hxQ
  have hxbK : IsUnit (((algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q))).comp
      (Ideal.Quotient.mk Q)) x) :=
    isUnit_iff_ne_zero.mpr (by
      rw [RingHom.comp_apply]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (R ⧸ Q) _)).mpr hxb)
  let θ : Localization.Away x →+* FractionRing (R ⧸ Q) := IsLocalization.Away.lift x hxbK
  let e := RingEquiv.ofLeftInverse (Function.leftInverse_invFun hι)
  -- `B = R[x⁻¹P] ⊆ R_x`
  have hinv : ι (IsLocalization.Away.invSelf x) = (algebraMap R K x)⁻¹ := by
    have h1 : ι (algebraMap R (Localization.Away x) x) = algebraMap R K x :=
      IsLocalization.Away.lift_eq x hxK x
    have h2 : algebraMap R K x * ι (IsLocalization.Away.invSelf x) = 1 := by
      rw [← h1, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    exact eq_inv_of_mul_eq_one_right h2
  have hBle : ∀ b ∈ blowupAlgebra R P x, b ∈ ι.range := by
    intro b hb
    induction hb using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨p, -, rfl⟩ := hy
      refine ⟨algebraMap R (Localization.Away x) p * IsLocalization.Away.invSelf x, ?_⟩
      rw [map_mul, hinv, IsLocalization.Away.lift_eq]
      exact (div_eq_mul_inv _ _).symm
    | algebraMap r => exact ⟨algebraMap R _ r, IsLocalization.Away.lift_eq x hxK r⟩
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
  let incl : blowupAlgebra R P x →+* ι.range :=
    ((blowupAlgebra R P x).val.toRingHom).codRestrict ι.range fun b => hBle b b.2
  let ρ₀ : blowupAlgebra R P x →+* FractionRing (R ⧸ Q) :=
    θ.comp (e.symm.toRingHom.comp incl)
  have hρ₀ : ∀ r, ρ₀ (algebraMap R (blowupAlgebra R P x) r) =
      algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q)) (Ideal.Quotient.mk Q r) := by
    intro r
    have h1 : incl (algebraMap R (blowupAlgebra R P x) r) = e (algebraMap R _ r) :=
      Subtype.ext (IsLocalization.Away.lift_eq x hxK r).symm
    show θ (e.symm (incl _)) = _
    rw [h1, e.symm_apply_apply, IsLocalization.Away.lift_eq]
    rfl
  have hxKb : algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q)) (Ideal.Quotient.mk Q x) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hxb
  -- `xᴺ b = f` gives `x̄ᴺ ρ₀(b) = f̄`
  have hρrep : ∀ (b : blowupAlgebra R P x) (N : ℕ) (f : R),
      algebraMap R K x ^ N * (b : K) = algebraMap R K f →
      algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q)) (Ideal.Quotient.mk Q x) ^ N * ρ₀ b =
        algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q)) (Ideal.Quotient.mk Q f) := by
    intro b N f h
    have hB : algebraMap R (blowupAlgebra R P x) x ^ N * b =
        algebraMap R (blowupAlgebra R P x) f := Subtype.ext h
    have := congrArg ρ₀ hB
    rwa [map_mul, map_pow, hρ₀, hρ₀] at this
  have hgen : ∀ (p : R) (hp : p ∈ P),
      ρ₀ ⟨algebraMap R K p / algebraMap R K x, Algebra.subset_adjoin ⟨p, hp, rfl⟩⟩ =
        algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q)) (Ideal.Quotient.mk Q p) /
          algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q)) (Ideal.Quotient.mk Q x) := by
    intro p hp
    have hrep := hρrep ⟨_, Algebra.subset_adjoin ⟨p, hp, rfl⟩⟩ 1 p
      (by rw [pow_one]; exact mul_div_cancel₀ _ hxK.ne_zero)
    rw [pow_one] at hrep
    rw [eq_div_iff hxKb, mul_comm]
    exact hrep
  -- `ρ₀` maps `B` into `B̄ = (R/Q)[x̄⁻¹P̄]`
  have hρB : ∀ b : blowupAlgebra R P x, ρ₀ b ∈
      blowupAlgebra (R ⧸ Q) (P.map (Ideal.Quotient.mk Q)) (Ideal.Quotient.mk Q x) := by
    rintro ⟨b, hb⟩
    induction hb using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      rw [hgen p hp]
      exact Algebra.subset_adjoin ⟨Ideal.Quotient.mk Q p, Ideal.mem_map_of_mem _ hp, rfl⟩
    | algebraMap r =>
      have h := hρ₀ r
      rw [show algebraMap R (blowupAlgebra R P x) r = ⟨algebraMap R K r, _⟩ from rfl] at h
      rw [h]
      exact Subalgebra.algebraMap_mem _ _
    | add y z hy hz ihy ihz =>
      rw [show (⟨y + z, add_mem hy hz⟩ : blowupAlgebra R P x) = ⟨y, hy⟩ + ⟨z, hz⟩ from rfl,
        map_add]
      exact add_mem ihy ihz
    | mul y z hy hz ihy ihz =>
      rw [show (⟨y * z, mul_mem hy hz⟩ : blowupAlgebra R P x) = ⟨y, hy⟩ * ⟨z, hz⟩ from rfl,
        map_mul]
      exact mul_mem ihy ihz
  let ρ : blowupAlgebra R P x →+*
      blowupAlgebra (R ⧸ Q) (P.map (Ideal.Quotient.mk Q)) (Ideal.Quotient.mk Q x) :=
    ρ₀.codRestrict _ hρB
  have hsurj : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨pb, hpb, rfl⟩ := hy
      obtain ⟨p, hp, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hpb
      exact ⟨⟨_, Algebra.subset_adjoin ⟨p, hp, rfl⟩⟩, Subtype.ext (hgen p hp)⟩
    | algebraMap rb =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective rb
      exact ⟨algebraMap R _ r, Subtype.ext (hρ₀ r)⟩
    | add y z hy hz ihy ihz =>
      obtain ⟨u, hu⟩ := ihy
      obtain ⟨v, hv⟩ := ihz
      exact ⟨u + v, by rw [map_add, hu, hv]; rfl⟩
    | mul y z hy hz ihy ihz =>
      obtain ⟨u, hu⟩ := ihy
      obtain ⟨v, hv⟩ := ihz
      exact ⟨u * v, by rw [map_mul, hu, hv]; rfl⟩
  have hxQ₁ : t.toRing x ∉ Q₁ := fun h => hxQ (by rw [← hQ₁]; exact h)
  -- `ker ρ = Q₁ ∩ B`
  have hker : RingHom.ker ρ = Q₁.comap (algebraMap (blowupAlgebra R P x) t.ring) := by
    ext b
    obtain ⟨N, hN⟩ := exists_forall_pow_mul_eq_of_mem_blowupAlgebra t.x_ne_zero b.2
    obtain ⟨f, hf⟩ := hN N le_rfl
    have h1 := hρrep b N f hf
    have hB : algebraMap R (blowupAlgebra R P x) x ^ N * b =
        algebraMap R (blowupAlgebra R P x) f := Subtype.ext hf
    have h2 : t.toRing x ^ N * algebraMap (blowupAlgebra R P x) t.ring b = t.toRing f := by
      have := congrArg (algebraMap (blowupAlgebra R P x) t.ring) hB
      rwa [map_mul, map_pow] at this
    rw [RingHom.mem_ker, Ideal.mem_comap]
    constructor
    · intro h0
      have h0' : ρ₀ b = 0 := congrArg Subtype.val h0
      rw [h0', mul_zero, eq_comm, map_eq_zero_iff _ (IsFractionRing.injective _ _),
        Ideal.Quotient.eq_zero_iff_mem] at h1
      have hfQ₁ : t.toRing f ∈ Q₁ := by
        rw [← Ideal.mem_comap, hQ₁]
        exact h1
      rw [← h2] at hfQ₁
      exact ((inferInstance : Q₁.IsPrime).mem_or_mem hfQ₁).resolve_left fun h =>
        hxQ₁ ((inferInstance : Q₁.IsPrime).mem_of_pow_mem N h)
    · intro hb
      have hfQ : f ∈ Q := by
        rw [← hQ₁, Ideal.mem_comap, ← h2]
        exact Ideal.mul_mem_left _ _ hb
      apply Subtype.ext
      show ρ₀ b = 0
      rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hfQ, map_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hxKb)
  have hρval : ∀ b, ((ρ b : blowupAlgebra (R ⧸ Q) (P.map (Ideal.Quotient.mk Q))
      (Ideal.Quotient.mk Q x)) : FractionRing (R ⧸ Q)) = ρ₀ b := fun b => rfl
  clear_value ρ ρ₀ incl e θ ι
  -- `Q₁ ∩ B ⊆ M'`
  have hqM : Q₁.comap (algebraMap (blowupAlgebra R P x) t.ring) ≤ t.M' := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal t.ring t.M']
    exact Ideal.comap_mono (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
  have hkerM : RingHom.ker ρ ≤ t.M' := hker.le.trans hqM
  have hMb : (t.M'.map ρ).IsPrime := Ideal.map_isPrime_of_surjective hsurj hkerM
  have hcomapM : (t.M'.map ρ).comap ρ = t.M' := by
    rw [Ideal.comap_map_of_surjective _ hsurj, sup_eq_left]
    exact (Ideal.comap_mono bot_le).trans (by rw [← RingHom.ker_eq_comap_bot]; exact hkerM)
  -- the monoidal transform `R̄₁` of `R̄ = R/Q` with center `P̄ = P/Q`
  have hPb : (P.map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hQP)
  have hxPb : Ideal.Quotient.mk Q x ∈ P.map (Ideal.Quotient.mk Q) :=
    Ideal.mem_map_of_mem _ t.x_mem
  have hcomp : (algebraMap (R ⧸ Q) (blowupAlgebra (R ⧸ Q) (P.map (Ideal.Quotient.mk Q))
      (Ideal.Quotient.mk Q x))).comp (Ideal.Quotient.mk Q) =
        ρ.comp (algebraMap R (blowupAlgebra R P x)) :=
    RingHom.ext fun r => Subtype.ext (by
      simp only [RingHom.comp_apply]
      rw [hρval, hρ₀]
      rfl)
  have hleb : (maximalIdeal (R ⧸ Q)).map (algebraMap (R ⧸ Q) (blowupAlgebra (R ⧸ Q)
      (P.map (Ideal.Quotient.mk Q)) (Ideal.Quotient.mk Q x))) ≤ t.M'.map ρ := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective,
      Ideal.map_map, hcomp, ← Ideal.map_map]
    exact Ideal.map_mono t.le
  let Tb : MonoidalTransform (R ⧸ Q) (P.map (Ideal.Quotient.mk Q)) :=
    ⟨Ideal.Quotient.mk Q x, hxPb, hxb, t.M'.map ρ, hMb, hleb⟩
  have hPb0 : P.map (Ideal.Quotient.mk Q) ≠ ⊥ := fun h => hxb (Ideal.mem_bot.mp (h.le hxPb))
  have hSb : IsRegularLocalRing ((R ⧸ Q) ⧸ P.map (Ideal.Quotient.mk Q)) :=
    IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hQP).symm
  have hregb : IsRegularLocalRing Tb.ring := (MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map Tb hPb hPb0 hSb).1
  exact isRegularLocalRing_quotient_of_surjective_blowupAlgebra t Q₁ Tb ρ hsurj hker rfl

end Corollary1Aux

section Corollary1

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- Corollary 1, p. 241: "Let `R` be a regular local ring, `J` an ideal in `R`, and `P` a prime
ideal in `R` such that `R/P` is regular. Let `Q` be a prime ideal in `R`. We assume that
`P ⊇ Q ⊇ J`, that `Q ≠ P`, and that `Q` is a permissible center for `J`. Let `R₁` be a monoidal
transform of `R` with center `P` which is residually separable algebraic over `R`, and `J₁` the
strict transform of `J` in `R₁`. We assume that there exists a prime ideal `Q₁` in `R₁` such
that `Q = Q₁ ∩ R`. Then `Q₁` is a permissible center for `J₁`. Moreover, `ν*(J) = ν*(J₁)`, and
`τ*(J) = τ(J₁)`."  (sic: `τ(J₁)` is a misprint for `τ*(J₁)`, which is what the proof proves.)

Formalization notes (encoding).
* `Q = Q₁ ∩ R` is `Q₁.comap t.toRing = Q`.
* `τ*(J) = τ*(J₁)` is the pair of assertions `t(J) = t(J₁)` and `τ^{(i)}(J) = τ^{(i)}(J₁)` for
  `1 ≤ i ≤ t(J)`: the two sequences `tauStar R J : Fin (t R J) → ℕ` and
  `tauStar R₁ J₁ : Fin (t R₁ J₁) → ℕ` have different types, so their equality is stated
  componentwise, exactly as in Lemma 13 (`tauStar_map`, `Hironaka/Ch3/TauStar.lean`).
* `[IsLocalHom t.toRing]`, `[IsRegularLocalRing t.ring]` are lemmas of §2, global instances (see the
  module docstring); `Hironaka.t` is `t(J)` of Definition 6 (the local `t` is the monoidal transform).

Deviation from the paper (paper misprint): the printed conclusion "`τ*(J) = τ(J₁)`" is stated as
`τ*(J) = τ*(J₁)` (componentwise), as at the end of the paper's proof.

The proof follows the printed one (p. 241), step by step.
* "Since we have `Q₁` such that `Q₁ ∩ R = Q ⊊ P`, we have `x ∈ P − Q` such that `(x)R₁ = PR₁`."
  (`notMem_of_span_eq_map_of_comap_eq`.)
* "It follows that `R_Q = (R₁)_{Q₁}` and that `R₁/Q₁` is a monoidal transform of `R/Q` with center
  `P/Q`.  Hence (i)* `R₁/Q₁` is regular."
  (`MonoidalTransform.exists_ringEquiv_localization_of_comap_eq`,
  `MonoidalTransform.isRegularLocalRing_quotient_of_comap_eq`.)
* "Moreover, if `g_j = f_j/x^{ν_j}` with `ν_j = ν^{(j)}(J) = ν_M(f_j)`, then
  `ν_{Q₁}(g_j) = ν_{Q₁(R₁)_{Q₁}}(g_j) = ν_{QR_Q}(g_j) = ν_{QR_Q}(f_j) = ν_j`": the first equality is
  (i)* (`ordElem_localization_eq_of_isRegularLocalRing_quotient` for `R₁/Q₁`), the second and third
  are `R_Q = (R₁)_{Q₁}` with `x` a unit (`ordElem_localization_eq_of_strictTransform`), the last is
  (ii) with `R/Q` regular.
* "Therefore `ν_{M₁}(g_j) = ν_M(f_j)`": `≥` because `Q₁ ⊆ M₁` (`ν_{M₁}(g_j) ≥ ν_{Q₁}(g_j) = ν_j`), and
  `≤` is Lemma 8 of §3 (`ordElem_maximalIdeal_le_of_weakTransform`), the bound that the paper
  leaves implicit.  Theorem 1 of §3 is not used.
* "By Theorem 5, `(g₁, …, g_m)` is a standard base of `J₁` and (ii)* `ν_{M₁}(g_j) = ν_{Q₁}(g_j)`.  By
  (i)* and (ii)*, `Q₁` is a permissible center for `J₁`.  … we get `ν*(J) = ν*(J₁)`.  In view of
  Proposition 1, §5, it follows that `τ*(J) = τ*(J₁)`."

Deviation from the paper (gap filled): the printed "It follows that `R_Q = (R₁)_{Q₁}` and that `R₁/Q₁` is
a monoidal transform of `R/Q` with center `P/Q`" is proved (`MonoidalTransform.exists_ringEquiv_localization_of_comap_eq`,
`MonoidalTransform.isRegularLocalRing_quotient_of_comap_eq`); so are the lower bound `ν_{M₁}(g_j) ≥ ν_{Q₁}(g_j)`
(from `Q₁ ⊆ M₁`) and the upper bound `ν_{M₁}(g_j) ≤ ν_M(f_j)` (Lemma 8) behind "Therefore", hypothesis (ii) of
Theorem 5 (`ν_P(f_j) = ν_M(f_j)`), `J₁ ⊆ Q₁`, and hypothesis (iii) of Proposition 1 of §5 ("`P` is a
permissible center for `J`", not checked in the paper). -/
@[blueprint "cor:III.thm5-1"
  (statement := /-- Let $R$ be a regular local ring, $J$ an ideal in $R$, and $P$ a prime ideal
    in $R$ such that $R/P$ is regular. Let $Q$ be a prime ideal in $R$. We assume that
    $P\supseteq Q\supseteq J$, that $Q\ne P$, and that $Q$ is a permissible center for $J$
    (\cref{def:III.8}). Let $R_1$ be a monoidal transform of $R$ with center $P$ which is
    residually separable algebraic over $R$, and $J_1$ the strict transform of $J$ in $R_1$. We
    assume that there exists a prime ideal $Q_1$ in $R_1$ such that $Q=Q_1\cap R$. Then $Q_1$ is
    a permissible center for $J_1$. Moreover, $\nu^*(J)=\nu^*(J_1)$, and $\tau^*(J)=\tau^*(J_1)$
    (\cref{def:III.2}, \cref{def:III.6-tau-star}). (Corollary 1, p.~241.)
    (Formalization note (encoding): $\tau^*(J)=\tau^*(J_1)$ is stated componentwise, as
    $t(J)=t(J_1)$ together with $\tau^{(i)}(J)=\tau^{(i)}(J_1)$ for $1\le i\le t(J)$, the two
    sequences having different index types.)

    \textbf{Paper misprint.} The paper prints ``$\tau^*(J)=\tau(J_1)$''; what is meant (and
    proved at the end of the proof) is $\tau^*(J)=\tau^*(J_1)$. -/)
  (proof := /-- Let $M$ (resp.\ $M_1$) be the maximal ideal of $R$ (resp.\ $R_1$). The
    assumption that $Q$ is a permissible center for $J$ means that (i) $R/Q$ is regular, and
    (ii) there exists a standard base $(f_1,\dots,f_m)$ of $J$ such that $\nu_M(f_j)=\nu_Q(f_j)$
    for $1\le j\le m$. Since we have $Q_1$ such that $Q_1\cap R=Q\subsetneq P$, we have
    $x\in P-Q$ such
    that $(x)R_1=PR_1$. It follows that $R_Q=(R_1)_{Q_1}$ and that $R_1/Q_1$ is a monoidal
    transform of $R/Q$ with center $P/Q$. Hence
    (i)$^*$ $R_1/Q_1$ is regular.
    Moreover, if $g_j=f_j/x^{\nu_j}$ with $\nu_j=\nu^{(j)}(J)=\nu_M(f_j)$, then
    $\nu_{Q_1}(g_j)=\nu_{Q_1(R_1)_{Q_1}}(g_j)=\nu_{QR_Q}(g_j)=\nu_{QR_Q}(f_j)=\nu_j$. Therefore
    $\nu_{M_1}(g_j)=\nu_M(f_j)$ for $1\le j\le m$. By Theorem~5 (\cref{thm:III.5}),
    $(g_1,\dots,g_m)$ is a standard base of $J_1$ and
    (ii)$^*$ $\nu_{M_1}(g_j)=\nu_{Q_1}(g_j)\ (=\nu_j)$ for $1\le j\le m$.
    By (i)$^*$ and (ii)$^*$, $Q_1$ is a permissible [center] for $J_1$. Moreover we have
    $\nu^{(j)}(J)=\nu_{M_1}(g_j)\ (=\nu_j)$ for all $j$, $1\le j\le m$. Since $(g_1,\dots,g_m)$
    is a standard base of $J_1$, we get $\nu^*(J)=\nu^*(J_1)$. In view of Proposition~1, \S5
    (\cref{prop:III.5-1}), it follows that $\tau^*(J)=\tau^*(J_1)$. \qed

    \textbf{Gap in the paper filled.} Lean follows the printed proof step by step (Theorem~1 of
    \S3 is not used) and proves the steps the paper leaves unargued: that $R_Q=(R_1)_{Q_1}$
    (every element of $R_1$ is a fraction $f/d$ with $f,d\in R$, and $d\notin Q$ if $d$ is a
    denominator outside $Q_1$, because $x\notin Q$); that $R_1/Q_1$ is isomorphic to a monoidal
    transform of $R/Q$ with center $P/Q$; the lower bound $\nu_{M_1}(g_j)\ge\nu_{Q_1}(g_j)$ (from
    $Q_1\subseteq M_1$) and the upper bound $\nu_{M_1}(g_j)\le\nu_M(f_j)$ (Lemma~8,
    \cref{lem:III.8}) behind the printed ``Therefore''; that $\nu_P(f_j)=\nu_M(f_j)$ (hypothesis
    (ii) of Theorem~5); that $J_1\subseteq Q_1$; and that $P$ is a permissible center for $J$,
    which is hypothesis (iii) of Proposition~1 and is not checked in the paper. -/)
  (latexEnv := "corollary")]
theorem isPermissibleCenter_strictTransform [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (J P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] (hQP : Q ≤ P) (hJQ : J ≤ Q) (hQneP : Q ≠ P)
    (hQperm : IsPermissibleCenter R J Q) (t : MonoidalTransform R P)
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := t.ring) t.toRing)
    (Q₁ : Ideal t.ring) [Q₁.IsPrime] (hQ₁ : Q₁.comap t.toRing = Q) :
    IsPermissibleCenter t.ring (strictTransformIdeal t J) Q₁ ∧
      nuStar R J = nuStar t.ring (strictTransformIdeal t J) ∧
      Hironaka.t R J = Hironaka.t t.ring (strictTransformIdeal t J) ∧
      ∀ i, 1 ≤ i → i ≤ Hironaka.t R J →
        tau R J i = tau t.ring (strictTransformIdeal t J) i := by
  classical
  obtain ⟨-, -, hQreg, hNF⟩ := hQperm.resolve_left (Ideal.IsPrime.ne_top inferInstance)
  have _ : IsRegularLocalRing (R ⧸ Q) := hQreg
  have hJP : J ≤ P := hJQ.trans hQP
  -- (ii)** for `Q`: a standard base `(f_j)` with `ν_Q(f_j) = ν^{(j)}(J) = ν_M(f_j)`
  have h13 : IsNormallyFlatAlongIdeal (Q.map (Ideal.Quotient.mk J)) ↔
      ∃ (m : ℕ) (f : Fin m → R), IsStandardBase R J f ∧
        ∀ j : Fin m, Ideal.ordElem Q (f j) = nuI R J ((j : ℕ).succPNat) :=
    (isPermissibleCenter_tfae R J Q hJQ).out 1 3
  obtain ⟨m, f, hf, hfQ⟩ := h13.mp hNF
  obtain ⟨⟨d, -, hνd⟩, -⟩ := nuI_eq_of_hasLemma1Properties R J _ hf.2
  have hMf : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = d j := fun j =>
    (ordElem_eq_nuI_of_isStandardBase J f hf j).trans (hνd j)
  have hQf : ∀ j, Ideal.ordElem Q (f j) = d j := fun j => (hfQ j).trans (hνd j)
  have hPf : ∀ j, Ideal.ordElem P (f j) = d j := fun j =>
    le_antisymm ((Ideal.ordElem_mono (le_maximalIdeal_of_isPrime P) _).trans (hMf j).le)
      ((hQf j).symm.le.trans (Ideal.ordElem_mono hQP _))
  -- `PR₁ = (x)R₁` and `g_j = x^{-ν_j} f_j`
  have hx : P.map t.toRing = Ideal.span {t.toRing t.x} := t.span_xR_eq_map.symm
  have hg : ∀ j, ∃ g : t.ring, t.toRing t.x ^ d j * g = t.toRing (f j) := by
    intro j
    have hfP : f j ∈ P ^ d j := Ideal.mem_pow_of_ordElem (hPf j)
    have hmem : t.toRing (f j) ∈ (P ^ d j).map t.toRing := Ideal.mem_map_of_mem _ hfP
    rw [Ideal.map_pow, hx, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  choose g hg using hg
  -- "It follows that `R_Q = (R₁)_{Q₁}` and that `R₁/Q₁` is a monoidal transform of `R/Q` with center
  -- `P/Q`.  Hence (i)* `R₁/Q₁` is regular."
  have hxQ₁ : t.toRing t.x ∉ Q₁ := notMem_of_span_eq_map_of_comap_eq hQP hQneP.symm t hQ₁ hx
  have hx0 : t.toRing t.x ≠ 0 := fun h' => hxQ₁ (h' ▸ Q₁.zero_mem)
  have hQ₁reg := MonoidalTransform.isRegularLocalRing_quotient_of_comap_eq P Q hQP hQneP t Q₁ hQ₁
  -- "Moreover, if `g_j = f_j/x^{ν_j}` with `ν_j = ν^{(j)}(J) = ν_M(f_j)`, then
  -- `ν_{Q₁}(g_j) = ν_{Q₁(R₁)_{Q₁}}(g_j) = ν_{QR_Q}(g_j) = ν_{QR_Q}(f_j) = ν_j`":
  -- `ν_{Q₁} = ν_{Q₁(R₁)_{Q₁}}` by (i)*, `R_Q = (R₁)_{Q₁}` with `x` a unit
  -- (`ordElem_localization_eq_of_strictTransform`), and `ν_{QR_Q}(f_j) = ν_Q(f_j) = ν_j`
  -- since `R/Q` is regular
  have hQ₁g : ∀ j, Ideal.ordElem Q₁ (g j) = d j := fun j => by
    rw [← ordElem_localization_eq_of_isRegularLocalRing_quotient Q₁ hQ₁reg (g j),
      ordElem_localization_eq_of_strictTransform Q P hQP hQneP.symm t Q₁ hQ₁ t.x hx (f j) (d j)
        (g j) (hg j),
      ordElem_localization_eq_of_isRegularLocalRing_quotient Q hQreg, hQf j]
  -- "Therefore `ν_{M₁}(g_j) = ν_M(f_j)`": `≥` because `Q₁ ⊆ M₁`, and `≤` is Lemma 8 of §3,
  -- the bound that the paper leaves implicit
  have hM₁g : ∀ j, Ideal.ordElem (maximalIdeal t.ring) (g j) =
      Ideal.ordElem (maximalIdeal R) (f j) := fun j =>
    le_antisymm
      (ordElem_maximalIdeal_le_of_weakTransform P t hsep t.x hx hx0 (f j) (d j) (hPf j).symm
        ((hMf j).trans (hPf j).symm) (g j) (hg j))
      (((hMf j).trans (hQ₁g j).symm).le.trans (Ideal.ordElem_mono (le_maximalIdeal_of_isPrime Q₁) _))
  -- Theorem 5: `(g_j)` is a standard base of `J₁` and `ν*(J₁) = ν*(J)`
  have h5 := isStandardBase_strictTransform J P hJP t hsep t.x t.x_mem hx f d g
    (fun j => (hMf j).symm) hg hf (fun j => (hPf j).trans (hMf j).symm)
    (fun j => (hM₁g j).trans (hMf j))
  -- `J₁ ⊆ Q₁`
  have hPQ₁ : ¬ P.map t.toRing ≤ Q₁ := fun h => hQneP (le_antisymm hQP (by
    rw [← hQ₁, ← Ideal.map_le_iff_le_comap]
    exact h))
  have hJ₁Q₁ : strictTransformIdeal t J ≤ Q₁ := by
    rw [strictTransformIdeal, Ideal.span_le]
    rintro y ⟨z, hz, f₀, hf₀J, n, -, hy⟩
    have hzQ₁ : z ∉ Q₁ := by
      intro h
      apply hPQ₁
      rw [← hz, Ideal.span_le, Set.singleton_subset_iff]
      exact h
    have hf₀Q₁ : t.toRing f₀ ∈ Q₁ := by
      rw [← Ideal.mem_comap, hQ₁]
      exact hJQ hf₀J
    rw [← hy] at hf₀Q₁
    exact ((inferInstance : Q₁.IsPrime).mem_or_mem hf₀Q₁).resolve_left fun h =>
      hzQ₁ ((inferInstance : Q₁.IsPrime).mem_of_pow_mem n h)
  -- `Q₁` is a permissible center for `J₁`: (ii)* with `ν_{M₁}(g_j) = ν_{Q₁}(g_j)`
  have hperm₁ : IsPermissibleCenter t.ring (strictTransformIdeal t J) Q₁ := by
    refine Or.inr ⟨inferInstance, hJ₁Q₁, hQ₁reg, ?_⟩
    have h12 : IsNormallyFlatAlongIdeal (Q₁.map (Ideal.Quotient.mk (strictTransformIdeal t J))) ↔
        HasInitialFormSystem (strictTransformIdeal t J) Q₁ (maximalIdeal t.ring) :=
      (isPermissibleCenter_tfae t.ring (strictTransformIdeal t J) Q₁ hJ₁Q₁).out 1 2
    refine h12.mpr ⟨m, g, h5.1.1, fun j => ?_, h5.1.2.2.2.1.symm⟩
    exact (hM₁g j).trans ((hMf j).trans (hQ₁g j).symm)
  -- `P` is a permissible center for `J` (condition (ii)* with the system `(f_j)`)
  have hPperm : IsPermissibleCenter R J P := by
    refine Or.inr ⟨inferInstance, hJP, inferInstance, ?_⟩
    have h12 : IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)) ↔
        HasInitialFormSystem J P (maximalIdeal R) := (isPermissibleCenter_tfae R J P hJP).out 1 2
    exact h12.mpr ⟨m, f, hf.1, fun j => (hMf j).trans (hPf j).symm, hf.2.2.2.1.symm⟩
  -- `τ*(J₁) = τ*(J)`: Proposition 1 of §5
  have hprop1 := tauStar_strictTransform_eq R P Q J hQP hJQ hQneP.symm hPperm t hsep Q₁ hQ₁
    h5.2 hperm₁
  exact ⟨hperm₁, h5.2.symm, hprop1.1.symm, fun i hi hit => (hprop1.2 i hi hit).symm⟩

/-- Stalk-level core of Corollary 2 (p. 242): the application of Corollary 1 to `R`, `J`, `P`, `Q`,
`R₁`, `J₁`, `Q₁` in the proof of Corollary 2, in the form consumed by the scheme-level argument
(`isNormallyFlatAlongAt'_strictTransform`): if `Q ⊇ J` is a prime of the regular local ring `R`
with `R/Q` regular and `R` normally flat along `Q` modulo `J`, then for every monoidal transform
`R₁` of `R` with center `P ⊇ Q`, `P ≠ Q`, residually separable algebraic over `R`, and every prime
`Q₁` of `R₁` lying over `Q`, the strict transform `J₁` of `J` is contained in `Q₁` and `R₁/J₁` is
normally flat along `Q₁`. -/
theorem isNormallyFlatAlongIdeal_strictTransform_of_comap [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (J P Q : Ideal R) [P.IsPrime]
    [Q.IsPrime] [IsRegularLocalRing (R ⧸ P)] (hQP : Q ≤ P) (hJQ : J ≤ Q) (hQneP : Q ≠ P)
    (hQreg : IsRegularLocalRing (R ⧸ Q))
    (hNF : IsNormallyFlatAlongIdeal (Q.map (Ideal.Quotient.mk J)))
    (t : MonoidalTransform R P)
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := t.ring) t.toRing)
    (Q₁ : Ideal t.ring) [Q₁.IsPrime] (hQ₁ : Q₁.comap t.toRing = Q) :
    strictTransformIdeal t J ≤ Q₁ ∧
      IsNormallyFlatAlongIdeal (Q₁.map (Ideal.Quotient.mk (strictTransformIdeal t J))) := by
  have hperm : IsPermissibleCenter R J Q := Or.inr ⟨inferInstance, hJQ, hQreg, hNF⟩
  have h := (isPermissibleCenter_strictTransform J P Q hQP hJQ hQneP hperm t hsep Q₁ hQ₁).1
  rcases h with h | ⟨-, hle, -, hflat⟩
  · exact absurd h (Ideal.IsPrime.ne_top inferInstance)
  · exact ⟨hle, hflat⟩

end Corollary1

/-! #### Auxiliary results for Corollary 2: the ring-level argument

The proof of Corollary 2 is reduced to a statement about one monoidal transform `R'` of a regular
local ring `R` (`isNormallyFlatAlongIdeal_strictTransform_of_strictTransformIdeal_ne_top`): enlarge the prime `M'` of
`R[x⁻¹P]` to a maximal ideal (a closed point of the fibre, which is residually algebraic, hence
separable in characteristic zero), apply Corollary 1 there with `Q₁` the strict transform of `Q`
(a prime lying over `Q`), and return to `R'` by flat localization. -/

section Cor2Aux

open TensorProduct

/-- The residue field of every local ring of an algebraic scheme has characteristic zero: the
base `S ∈ 𝔅` has a residue field of characteristic zero, so every positive integer is a unit of `S`,
hence of every `S`-algebra. -/
theorem charZero_residueField_stalk (X : Scheme.{u}) [IsAlgebraicScheme X] (x : X) :
    CharZero (ResidueField (X.presheaf.stalk x)) := by
  obtain ⟨S, _, _, hS, p, -, -⟩ := IsAlgebraicScheme.exists_base (X := X)
  have := hS.charZero_residueField
  let φ : S →+* ResidueField (X.presheaf.stalk x) :=
    (residue (X.presheaf.stalk x)).comp ((X.presheaf.germ ⊤ x trivial).hom.comp
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom))
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra hn0
  have hunit : IsUnit (n : S) := by
    by_contra hnu
    have h1 : (n : S) ∈ maximalIdeal S := hnu
    have h2 := (residue_eq_zero_iff (n : S)).mpr h1
    rw [map_natCast] at h2
    exact hn0 (Nat.cast_eq_zero.mp h2)
  have h3 := (hunit.map φ).ne_zero
  rw [map_natCast] at h3
  exact h3 hn

section Cor2Flat

/-- For an `A`-linear map `f : M → M'` into an `A'`-module and `JA' ⊆ J'`, `f(JM) ⊆ J'M'`. -/
private theorem map_mem_smul_top_of_map_le {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] {M : Type u} [AddCommGroup M] [Module A M] {M' : Type u} [AddCommGroup M']
    [Module A' M'] [Module A M'] [IsScalarTower A A' M'] (f : M →ₗ[A] M') {J : Ideal A}
    {J' : Ideal A'} (hJ : J.map (algebraMap A A') ≤ J') {x : M}
    (hx : x ∈ J • (⊤ : Submodule A M)) : f x ∈ J' • (⊤ : Submodule A' M') := by
  refine Submodule.smul_induction_on hx (fun a ha m _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, ← algebraMap_smul A' a]
    exact Submodule.smul_mem_smul (hJ (Ideal.mem_map_of_mem _ ha)) Submodule.mem_top
  · rw [map_add]; exact add_mem hx hy

/-- The restriction `JM → J'M'` of an `A`-linear map `f : M → M'` (the map `λ` of the proof of
Lemma 9 when `M' = M ⊗_A A'` and `J' = JA'`). -/
private def smulTopRestrict {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
    {M : Type u} [AddCommGroup M] [Module A M] {M' : Type u} [AddCommGroup M'] [Module A' M']
    [Module A M'] [IsScalarTower A A' M'] (f : M →ₗ[A] M') (J : Ideal A) (J' : Ideal A')
    (hJ : J.map (algebraMap A A') ≤ J') :
    ↥(J • (⊤ : Submodule A M)) →ₗ[A] ↥(J' • (⊤ : Submodule A' M')) where
  toFun x := ⟨f x, map_mem_smul_top_of_map_le f hJ x.2⟩
  map_add' _ _ := Subtype.ext (map_add f _ _)
  map_smul' _ _ := Subtype.ext (map_smul f _ _)

/-- Proof of Lemma 9, first step: if `A'` is flat over `A` and `M'` is the base change of `M`,
then `J'M'` (`J' = JA'`) is the base change of `JM`, i.e. `λ : (JM) ⊗_A A' → J'M'` is
bijective. -/
private theorem isBaseChange_smulTopRestrict {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] [Module.Flat A A'] {M : Type u} [AddCommGroup M] [Module A M] {M' : Type u}
    [AddCommGroup M'] [Module A' M'] [Module A M'] [IsScalarTower A A' M'] {f : M →ₗ[A] M'}
    (hf : IsBaseChange A' f) (J : Ideal A) (J' : Ideal A')
    (hJ : J.map (algebraMap A A') = J') :
    IsBaseChange A' (smulTopRestrict f J J' hJ.le) := by
  let g : A' ⊗[A] ↥(J • (⊤ : Submodule A M)) →ₗ[A'] M' :=
    hf.equiv.toLinearMap ∘ₗ (J • (⊤ : Submodule A M)).subtype.baseChange A'
  have hg : ∀ (a : A') (x : ↥(J • (⊤ : Submodule A M))), g (a ⊗ₜ x) = a • f x := fun a x => by
    simp [g, IsBaseChange.equiv_tmul]
  -- `(JM) ⊗_A A' → M ⊗_A A'` is injective since `A'` is flat over `A`.
  have hinj : Function.Injective g := by
    refine hf.equiv.injective.comp ?_
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  -- Its image is `J'M'`.
  have hrange : LinearMap.range g = J' • (⊤ : Submodule A' M') := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      induction y using TensorProduct.inductionOn with
      | tmul a x =>
        rw [hg]
        exact Submodule.smul_mem _ a (map_mem_smul_top_of_map_le f hJ.le x.2)
      | add y z hy hz => rw [map_add]; exact add_mem hy hz
    · rw [Submodule.smul_le]
      intro r hr n _
      rw [← hJ] at hr
      have hr' : r ∈ Submodule.span A' (algebraMap A A' '' J) := hr
      clear hr
      induction hr' using Submodule.span_induction with
      | mem r hmem =>
        obtain ⟨a, ha, rfl⟩ := hmem
        induction n using hf.inductionOn with
        | tmul m =>
          rw [algebraMap_smul, ← map_smul]
          exact ⟨1 ⊗ₜ ⟨a • m, Submodule.smul_mem_smul ha Submodule.mem_top⟩, by
            rw [hg, one_smul]⟩
        | smul s n hn => rw [smul_comm]; exact Submodule.smul_mem _ s (hn trivial)
        | add x y hx hy => rw [smul_add]; exact add_mem (hx trivial) (hy trivial)
      | zero => simp
      | add r s _ _ hr hs => rw [add_smul]; exact add_mem hr hs
      | smul c r _ hr => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ c hr
  refine IsBaseChange.of_equiv ((LinearEquiv.ofInjective g hinj).trans
    (LinearEquiv.ofEq _ _ hrange)) fun x => Subtype.ext ?_
  simp [hg]
  rfl

/-- A module `N` killed by `I` is its own base change to `R ⧸ I`. -/
private theorem isBaseChange_quotient_id {R : Type u} [CommRing R] (I : Ideal R) (N : Type u)
    [AddCommGroup N] [Module R N] [Module (R ⧸ I) N] [IsScalarTower R (R ⧸ I) N] :
    IsBaseChange (R ⧸ I) (LinearMap.id : N →ₗ[R] N) := by
  have hbot : I • (⊤ : Submodule R N) = ⊥ := by
    rw [eq_bot_iff, Submodule.smul_le]
    intro r hr x _
    rw [Submodule.mem_bot, ← algebraMap_smul (R ⧸ I) r x, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]
  refine IsBaseChange.of_equiv
    ((TensorProduct.quotTensorEquivQuotSMul N I ≪≫ₗ
      Submodule.quotEquivOfEqBot _ hbot).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective) fun x => ?_
  simp

/-- Proof of Lemma 9, second step: if `A'` is flat over `A` and `M'` is the base change of `M`
(e.g. `M' = M ⊗_A A'`), then `ε_n : grⁿ_I(M) ⊗_A A' → grⁿ_{I'}(M')` is bijective, which gives
an `A'/I'`-linear isomorphism `grⁿ_I(M) ⊗_{A/I} A'/I' ≅ grⁿ_{I'}(M')` (`I' = IA'`). -/
private theorem nonempty_grModPiece_baseChange_equiv {A A' : Type u} [CommRing A]
    [CommRing A'] [Algebra A A'] [Module.Flat A A'] {M : Type u} [AddCommGroup M] [Module A M]
    {M' : Type u} [AddCommGroup M'] [Module A' M'] [Module A M'] [IsScalarTower A A' M']
    {f : M →ₗ[A] M'} (hf : IsBaseChange A' f) (I : Ideal A) (n : ℕ) :
    Nonempty ((A' ⧸ I.map (algebraMap A A')) ⊗[A ⧸ I] GrModPiece I M n ≃ₗ[A' ⧸ I.map
      (algebraMap A A')] GrModPiece (I.map (algebraMap A A')) M' n) := by
  have hpow : ∀ k, (I ^ k).map (algebraMap A A') = I.map (algebraMap A A') ^ k :=
    fun k => Ideal.map_pow _ _ _
  have hle : I ^ (n + 1) • (⊤ : Submodule A M) ≤ I ^ n • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right n.le_succ)
  have hle' : I.map (algebraMap A A') ^ (n + 1) • (⊤ : Submodule A' M') ≤
      I.map (algebraMap A A') ^ n • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right n.le_succ)
  let K := Submodule.comap (I ^ n • ⊤ : Submodule A M).subtype (I ^ (n + 1) • ⊤)
  let K' := Submodule.comap (I.map (algebraMap A A') ^ n • ⊤ : Submodule A' M').subtype
    (I.map (algebraMap A A') ^ (n + 1) • ⊤)
  -- The maps `λ_{n+1}`, `λ_n` and `ε_n` of the paper's diagram.
  let l₀ := smulTopRestrict f (I ^ (n + 1)) (I.map (algebraMap A A') ^ (n + 1)) (hpow _).le
  let l₁ := smulTopRestrict f (I ^ n) (I.map (algebraMap A A') ^ n) (hpow _).le
  let ε : GrModPiece I M n →ₗ[A] GrModPiece (I.map (algebraMap A A')) M' n :=
    K.liftQ ((K'.mkQ.restrictScalars A) ∘ₗ l₁) (by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact map_mem_smul_top_of_map_le f (hpow _).le hx)
  -- `λ_{n+1}`, `λ_n` are bijective (flatness), hence so is `ε_n` (right exactness of `⊗`).
  have hε : IsBaseChange A' ε := by
    refine IsBaseChange.of_right_exact A' l₀ l₁ ε (f := Submodule.inclusion hle) (g := K.mkQ)
      (f' := Submodule.inclusion hle') (g' := K'.mkQ) ?_ ?_
      (isBaseChange_smulTopRestrict hf _ _ (hpow _))
      (isBaseChange_smulTopRestrict hf _ _ (hpow _))
      ?_ (Submodule.mkQ_surjective _) ?_ (Submodule.mkQ_surjective _)
    · ext x; rfl
    · ext x; rfl
    · rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_inclusion]
    · rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_inclusion]
  -- `grⁿ_{I'}(M') ≅ grⁿ_I(M) ⊗_A A' = grⁿ_I(M) ⊗_A A'/I' = grⁿ_I(M) ⊗_{A/I} A'/I'`.
  have hT := hε.comp (isBaseChange_quotient_id (I.map (algebraMap A A'))
    (GrModPiece (I.map (algebraMap A A')) M' n))
  exact ⟨LinearEquiv.baseChange (A ⧸ I) (A' ⧸ I.map (algebraMap A A')) _ _
      (isBaseChange_quotient_id I (GrModPiece I M n)).equiv.symm ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A' ⧸ I.map (algebraMap A A'))
      (A' ⧸ I.map (algebraMap A A')) (GrModPiece I M n) ≪≫ₗ hT.equiv⟩

/-- `Pⁿ/Pⁿ⁺¹ = PⁿO/Pⁿ⁺¹O` (`GrPiece` versus `GrModPiece` for the module `O`). -/
private theorem nonempty_grPiece_equiv_grModPiece {R : Type u} [CommRing R] (P : Ideal R)
    (n : ℕ) : Nonempty (GrPiece P n ≃ₗ[R ⧸ P] GrModPiece P R n) := by
  have h : ∀ k : ℕ, (P ^ k : Submodule R R) = P ^ k • (⊤ : Submodule R R) := fun k => by
    rw [smul_eq_mul, Ideal.mul_top]
  have key : ∀ a b c d : Submodule R R, a = c → b = d →
      Nonempty ((↥a ⧸ Submodule.comap a.subtype b) ≃ₗ[R] (↥c ⧸ Submodule.comap c.subtype d)) := by
    rintro a b c d rfl rfl
    exact ⟨LinearEquiv.refl _ _⟩
  obtain ⟨e⟩ := key _ _ _ _ (h n) (h (n + 1))
  exact ⟨e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective⟩

/-- Normal flatness is preserved by flat base change (Lemma 9's isomorphism
`grⁿ_{IA'}(A') ≅ grⁿ_I(A) ⊗_{A/I} A'/IA'`). -/
private theorem isNormallyFlatAlongIdeal_map_of_flat {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] [Module.Flat A A'] (I : Ideal A) (h : IsNormallyFlatAlongIdeal I) :
    IsNormallyFlatAlongIdeal (I.map (algebraMap A A')) := fun n => by
  obtain ⟨e₁⟩ := nonempty_grPiece_equiv_grModPiece I n
  obtain ⟨e₂⟩ := nonempty_grPiece_equiv_grModPiece (I.map (algebraMap A A')) n
  obtain ⟨e⟩ := nonempty_grModPiece_baseChange_equiv (IsBaseChange.linearMap A A') I n
  have := h n
  have : Module.Free (A ⧸ I) (GrModPiece I A n) := Module.Free.of_equiv e₁
  exact Module.Free.of_equiv (e ≪≫ₗ e₂.symm)

/-- Flatness of `S ⧸ J → S' ⧸ JS'` for a flat `S → S'`. -/
private
theorem Ideal.flat_quotientMap_of_flat {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S']
    [Module.Flat S S'] (J : Ideal S) :
    (Ideal.quotientMap (J.map (algebraMap S S')) (algebraMap S S') Ideal.le_comap_map).Flat := by
  let : Algebra (S ⧸ J) (S' ⧸ J.map (algebraMap S S')) :=
    (Ideal.quotientMap (J.map (algebraMap S S')) (algebraMap S S') Ideal.le_comap_map).toAlgebra
  have : IsScalarTower S (S ⧸ J) (S' ⧸ J.map (algebraMap S S')) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show _ = Ideal.quotientMap _ _ _ (Ideal.Quotient.mk J a)
      rfl
  have : Algebra.IsPushout S S' (S ⧸ J) (S' ⧸ J.map (algebraMap S S')) := by
    refine ⟨?_⟩
    refine IsBaseChange.of_equiv (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S' J).symm.toLinearEquiv ?_
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [AlgEquiv.toLinearEquiv_symm, AlgEquiv.coe_symm_toLinearEquiv]
    rw [AlgEquiv.symm_apply_eq]
    show _ = Algebra.TensorProduct.quotIdealMapEquivTensorQuot S' J
      (Ideal.Quotient.mk _ (algebraMap S S' a))
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    congr 1
    simp [Algebra.smul_def]
  have h1 : (algebraMap S S').Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  exact RingHom.Flat.isStableUnderBaseChange S S' (S ⧸ J) (S' ⧸ J.map (algebraMap S S')) h1

/-- Normal flatness of `I` modulo `J` passes to a flat extension. -/
theorem isNormallyFlatAlongIdeal_mod_map_of_flat {S S' : Type u} [CommRing S] [CommRing S']
    [Algebra S S'] [Module.Flat S S'] (I J : Ideal S)
    (h : IsNormallyFlatAlongIdeal (I.map (Ideal.Quotient.mk J))) :
    IsNormallyFlatAlongIdeal
      ((I.map (algebraMap S S')).map (Ideal.Quotient.mk (J.map (algebraMap S S')))) := by
  let φ : S ⧸ J →+* S' ⧸ J.map (algebraMap S S') :=
    Ideal.quotientMap (J.map (algebraMap S S')) (algebraMap S S') Ideal.le_comap_map
  let _ : Algebra (S ⧸ J) (S' ⧸ J.map (algebraMap S S')) := φ.toAlgebra
  have hfl : Module.Flat (S ⧸ J) (S' ⧸ J.map (algebraMap S S')) :=
    RingHom.flat_algebraMap_iff.mp (Ideal.flat_quotientMap_of_flat J)
  have := isNormallyFlatAlongIdeal_map_of_flat (A := S ⧸ J) (A' := S' ⧸ J.map (algebraMap S S'))
    _ h
  rw [Ideal.map_map] at this ⊢
  exact this

end Cor2Flat

namespace MonoidalTransform

section Cor2Loc

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

/-- The monoidal transform with the same `x` as `t` and the (larger) prime `N ⊇ M'` of
`R[x⁻¹P]` (used in the proof of Corollary 2 of Theorem 5 to pass to a closed point of the fibre,
where `R'` is residually algebraic). -/
abbrev withPrime (t : MonoidalTransform R P) (N : Ideal (blowupAlgebra R P t.x))
    [hN : N.IsPrime] (h : t.M' ≤ N) : MonoidalTransform R P :=
  ⟨t.x, t.x_mem, t.x_ne_zero, N, hN, t.le.trans h⟩

set_option warn.classDefReducibility false in
/-- The `R[x⁻¹P]`-algebra structure of `withPrime` (as for any monoidal transform; the
elaborator cannot find it by itself, since `(cor2WithPrime t N h).x` is not syntactically `t.x`). -/
noncomputable def algebraWithPrime (t : MonoidalTransform R P) (N : Ideal (blowupAlgebra R P t.x))
    [hN : N.IsPrime] (h : t.M' ≤ N) :
    Algebra (blowupAlgebra R P t.x) (t.withPrime N h).ring :=
  MonoidalTransform.instAlgebraSubtypeFractionRingMemSubalgebraBlowupAlgebraXRing
    (t.withPrime N h)

theorem isLocalization_withPrime (t : MonoidalTransform R P) (N : Ideal (blowupAlgebra R P t.x))
    [hN : N.IsPrime] (h : t.M' ≤ N) :
    @IsLocalization _ _ N.primeCompl (t.withPrime N h).ring _ (algebraWithPrime t N h) :=
  MonoidalTransform.instAtPrimeSubtypeFractionRingMemSubalgebraBlowupAlgebraXRingM'
    (t.withPrime N h)

/-- The canonical map `R[x⁻¹P]_N → R[x⁻¹P]_{M'}` for `M' ⊆ N` (a localization). -/
noncomputable def liftWithPrime (t : MonoidalTransform R P) (N : Ideal (blowupAlgebra R P t.x))
    [hN : N.IsPrime] (h : t.M' ≤ N) : (t.withPrime N h).ring →+* t.ring :=
  letI := algebraWithPrime t N h
  haveI := isLocalization_withPrime t N h
  IsLocalization.lift (M := N.primeCompl) (S := (t.withPrime N h).ring)
    (g := algebraMap (blowupAlgebra R P t.x) t.ring)
    (fun y => IsLocalization.map_units t.ring (⟨y, fun hy => y.2 (h hy)⟩ : t.M'.primeCompl))

theorem liftWithPrime_toRing (t : MonoidalTransform R P) (N : Ideal (blowupAlgebra R P t.x))
    [hN : N.IsPrime] (h : t.M' ≤ N) (r : R) :
    t.liftWithPrime N h ((t.withPrime N h).toRing r) = t.toRing r := by
  let := algebraWithPrime t N h
  have := isLocalization_withPrime t N h
  exact IsLocalization.lift_eq (M := N.primeCompl) _ (algebraMap R (blowupAlgebra R P t.x) r)

theorem liftWithPrime_xR (t : MonoidalTransform R P) (N : Ideal (blowupAlgebra R P t.x))
    [hN : N.IsPrime] (h : t.M' ≤ N) :
    t.liftWithPrime N h (t.withPrime N h).xR = t.xR := liftWithPrime_toRing t N h t.x

/-- `R[x⁻¹P]_{M'}` is flat over `R[x⁻¹P]_N` (it is a localization). -/
theorem flat_liftWithPrime (t : MonoidalTransform R P) (N : Ideal (blowupAlgebra R P t.x))
    [hN : N.IsPrime] (h : t.M' ≤ N) : (t.liftWithPrime N h).Flat := by
  let := algebraWithPrime t N h
  have := isLocalization_withPrime t N h
  let _ : Algebra (t.withPrime N h).ring t.ring := (t.liftWithPrime N h).toAlgebra
  have : IsScalarTower (blowupAlgebra R P t.x) (t.withPrime N h).ring t.ring :=
    IsScalarTower.of_algebraMap_eq fun b => (IsLocalization.lift_eq (M := N.primeCompl) _ b).symm
  have hle : N.primeCompl ≤ t.M'.primeCompl := fun y hy hy' => hy (h hy')
  have : IsLocalization (t.M'.primeCompl.map (algebraMap (blowupAlgebra R P t.x)
      (t.withPrime N h).ring)) t.ring :=
    IsLocalization.isLocalization_of_submonoid_le (t.withPrime N h).ring t.ring
      N.primeCompl t.M'.primeCompl hle
  have : Module.Flat (t.withPrime N h).ring t.ring :=
    IsLocalization.flat t.ring (t.M'.primeCompl.map (algebraMap (blowupAlgebra R P t.x)
      (t.withPrime N h).ring))
  exact RingHom.flat_algebraMap_iff.mpr this

/-- The strict transform in `R[x⁻¹P]_{M'}` is the extension of the strict transform in
`R[x⁻¹P]_N` (`M' ⊆ N`). -/
theorem strictTransformIdeal_liftWithPrime (t : MonoidalTransform R P)
    (N : Ideal (blowupAlgebra R P t.x)) [hN : N.IsPrime] (h : t.M' ≤ N) (I : Ideal R) :
    strictTransformIdeal t I =
      (strictTransformIdeal (t.withPrime N h) I).map (t.liftWithPrime N h) := by
  set t₁ := t.withPrime N h with ht₁
  have hx0 : t.xR ≠ 0 := fun h0 => t.x_ne_zero (t.toRing_injective (h0.trans (map_zero _).symm))
  rw [t.strictTransformIdeal_eq_iSup I t.span_xR_eq_map,
    t₁.strictTransformIdeal_eq_iSup I t₁.span_xR_eq_map, Ideal.map_iSup]
  refine iSup_congr fun ν => le_antisymm ?_ ?_
  · rw [MonoidalTransform.divIdeal, Ideal.span_le]
    rintro z ⟨f, hf, hz⟩
    have hmem : t₁.toRing f ∈ (P ^ ν).map t₁.toRing := Ideal.mem_map_of_mem _ hf.2
    rw [Ideal.map_pow, ← t₁.span_xR_eq_map, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton'] at hmem
    obtain ⟨z₁, hz₁⟩ := hmem
    have hρ : t.liftWithPrime N h z₁ = z := by
      have h1 := congrArg (t.liftWithPrime N h) hz₁
      rw [map_mul, map_pow, liftWithPrime_xR, liftWithPrime_toRing] at h1
      refine mul_left_cancel₀ (pow_ne_zero ν hx0) ?_
      rw [hz, ← h1]
      ring
    rw [← hρ]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨f, hf, by rw [mul_comm]; exact hz₁⟩)
  · rw [Ideal.map_le_iff_le_comap, MonoidalTransform.divIdeal, Ideal.span_le]
    rintro z₁ ⟨f, hf, hz₁⟩
    refine Ideal.subset_span ⟨f, hf, ?_⟩
    have h1 := congrArg (t.liftWithPrime N h) hz₁
    rwa [map_mul, map_pow, liftWithPrime_xR, liftWithPrime_toRing] at h1

end Cor2Loc

end MonoidalTransform

section Cor2Prime

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

/-- `R → R[x⁻¹P]` is injective (both sit inside the field of quotients of `R`). -/
private theorem algebraMap_blowupAlgebra_injective (x : R) :
    Function.Injective (algebraMap R (blowupAlgebra R P x)) := fun _ _ h =>
  IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h)

/-- The ideal `{b ∈ R[x⁻¹P] | xⁿ b ∈ Q for some n}` of `R[x⁻¹P]`: the contraction to `R[x⁻¹P]` of
the extension of `Q` to `R_x`.  When `x ∉ Q` it is a prime ideal lying over `Q`; the strict
transform of `Q` is its extension to `R[x⁻¹P]_{M'}`. -/
def MonoidalTransform.satIdeal (t : MonoidalTransform R P) (Q : Ideal R) : Ideal (blowupAlgebra R P t.x) where
  carrier := {b | ∃ (n : ℕ) (f : R), f ∈ Q ∧
    algebraMap R (blowupAlgebra R P t.x) t.x ^ n * b = algebraMap R (blowupAlgebra R P t.x) f}
  zero_mem' := ⟨0, 0, Q.zero_mem, by simp⟩
  add_mem' := by
    rintro b b' ⟨n, f, hf, h⟩ ⟨n', f', hf', h'⟩
    refine ⟨n + n', t.x ^ n' * f + t.x ^ n * f',
      Q.add_mem (Q.mul_mem_left _ hf) (Q.mul_mem_left _ hf'), ?_⟩
    simp only [map_add, map_mul, map_pow]
    rw [pow_add]
    linear_combination (algebraMap R (blowupAlgebra R P t.x) t.x ^ n') * h +
      (algebraMap R (blowupAlgebra R P t.x) t.x ^ n) * h'
  smul_mem' := by
    rintro c b ⟨n, f, hf, h⟩
    obtain ⟨N, hN⟩ := exists_forall_pow_mul_eq_of_mem_blowupAlgebra t.x_ne_zero c.2
    obtain ⟨g, hg⟩ := hN N le_rfl
    have hg' : algebraMap R (blowupAlgebra R P t.x) t.x ^ N * c =
        algebraMap R (blowupAlgebra R P t.x) g := Subtype.ext (by simpa using hg)
    refine ⟨N + n, g * f, Q.mul_mem_left _ hf, ?_⟩
    simp only [smul_eq_mul, map_mul, pow_add]
    linear_combination (algebraMap R (blowupAlgebra R P t.x) t.x ^ n * b) * hg' +
      (algebraMap R (blowupAlgebra R P t.x) g) * h

theorem MonoidalTransform.comap_satIdeal (t : MonoidalTransform R P) (Q : Ideal R) [hQ : Q.IsPrime] (hxQ : t.x ∉ Q) :
    (MonoidalTransform.satIdeal t Q).comap (algebraMap R (blowupAlgebra R P t.x)) = Q := by
  ext r
  constructor
  · rintro ⟨n, f, hf, h⟩
    have h2 : t.x ^ n * r = f := algebraMap_blowupAlgebra_injective t.x (by simpa [map_mul, map_pow] using h)
    have hmem : t.x ^ n * r ∈ Q := h2 ▸ hf
    exact (hQ.mem_or_mem hmem).resolve_left fun hx => hxQ (hQ.mem_of_pow_mem n hx)
  · intro hr
    exact ⟨0, r, hr, by simp⟩

theorem MonoidalTransform.isPrime_satIdeal (t : MonoidalTransform R P) (Q : Ideal R) [hQ : Q.IsPrime]
    (hxQ : t.x ∉ Q) : (MonoidalTransform.satIdeal t Q).IsPrime where
  ne_top' := by
    intro h
    have h1 : (1 : blowupAlgebra R P t.x) ∈ MonoidalTransform.satIdeal t Q := h ▸ Submodule.mem_top
    obtain ⟨n, f, hf, hh⟩ := h1
    have h2 : t.x ^ n = f := algebraMap_blowupAlgebra_injective t.x (by simpa using hh)
    exact hxQ (hQ.mem_of_pow_mem n (h2 ▸ hf))
  mem_or_mem' := by
    intro b b' ⟨n, f, hf, hh⟩
    obtain ⟨N, hN⟩ := exists_forall_pow_mul_eq_of_mem_blowupAlgebra t.x_ne_zero b.2
    obtain ⟨g, hg⟩ := hN N le_rfl
    obtain ⟨N', hN'⟩ := exists_forall_pow_mul_eq_of_mem_blowupAlgebra t.x_ne_zero b'.2
    obtain ⟨g', hg'⟩ := hN' N' le_rfl
    have hgB : algebraMap R (blowupAlgebra R P t.x) t.x ^ N * b =
        algebraMap R (blowupAlgebra R P t.x) g := Subtype.ext (by simpa using hg)
    have hgB' : algebraMap R (blowupAlgebra R P t.x) t.x ^ N' * b' =
        algebraMap R (blowupAlgebra R P t.x) g' := Subtype.ext (by simpa using hg')
    have key : t.x ^ n * (g * g') = t.x ^ (N + N') * f := by
      apply algebraMap_blowupAlgebra_injective t.x
      simp only [map_mul, map_pow]
      rw [pow_add]
      linear_combination (algebraMap R (blowupAlgebra R P t.x) t.x ^ (N + N')) * hh -
        (algebraMap R (blowupAlgebra R P t.x) t.x ^ n *
          algebraMap R (blowupAlgebra R P t.x) g') * hgB -
        (algebraMap R (blowupAlgebra R P t.x) t.x ^ n *
          algebraMap R (blowupAlgebra R P t.x) t.x ^ N * b) * hgB'
    have hmem : t.x ^ n * (g * g') ∈ Q := key ▸ Q.mul_mem_left _ hf
    have hgg : g * g' ∈ Q :=
      (hQ.mem_or_mem hmem).resolve_left fun hx => hxQ (hQ.mem_of_pow_mem n hx)
    rcases hQ.mem_or_mem hgg with h1 | h1
    · exact Or.inl ⟨N, g, h1, hgB⟩
    · exact Or.inr ⟨N', g', h1, hgB'⟩

theorem MonoidalTransform.map_satIdeal_le_strictTransformIdeal (t : MonoidalTransform R P) (hP : P.IsPrime)
    (hS : IsRegularLocalRing (R ⧸ P)) (Q : Ideal R) :
    (MonoidalTransform.satIdeal t Q).map (algebraMap (blowupAlgebra R P t.x) t.ring) ≤ strictTransformIdeal t Q := by
  rw [Ideal.map_le_iff_le_comap]
  rintro b ⟨n, f, hf, h⟩
  rw [Ideal.mem_comap]
  refine t.mem_strictTransformIdeal_of_mul_pow_mem hP hS Q (n := n) ?_
  have h2 : algebraMap (blowupAlgebra R P t.x) t.ring b * t.xR ^ n = t.toRing f := by
    have := congrArg (algebraMap (blowupAlgebra R P t.x) t.ring) h
    rw [map_mul, map_pow] at this
    rw [mul_comm]
    exact this
  rw [h2]
  exact Ideal.mem_map_of_mem _ hf

theorem MonoidalTransform.strictTransformIdeal_le_map_satIdeal (t : MonoidalTransform R P) (Q : Ideal R)
    [hQ : Q.IsPrime] (hxQ : t.x ∉ Q) (hK : MonoidalTransform.satIdeal t Q ≤ t.M') :
    strictTransformIdeal t Q ≤ (MonoidalTransform.satIdeal t Q).map (algebraMap (blowupAlgebra R P t.x) t.ring) := by
  have := MonoidalTransform.isPrime_satIdeal t Q hxQ
  have hdis : Disjoint (t.M'.primeCompl : Set (blowupAlgebra R P t.x)) (MonoidalTransform.satIdeal t Q) :=
    Set.disjoint_left.mpr fun a ha haK => ha (hK haK)
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint t.M'.primeCompl t.ring (MonoidalTransform.satIdeal t Q)
    inferInstance hdis
  have hcomap : ((MonoidalTransform.satIdeal t Q).map (algebraMap (blowupAlgebra R P t.x) t.ring)).comap
      (algebraMap (blowupAlgebra R P t.x) t.ring) = MonoidalTransform.satIdeal t Q :=
    IsLocalization.under_map_of_isPrime_disjoint t.M'.primeCompl t.ring
      (I := MonoidalTransform.satIdeal t Q) inferInstance hdis
  rw [strictTransformIdeal, Ideal.span_le]
  rintro y ⟨x', hx', f, hfQ, ν, -, hy⟩
  have hfmem : t.toRing f ∈ (MonoidalTransform.satIdeal t Q).map (algebraMap (blowupAlgebra R P t.x) t.ring) :=
    Ideal.mem_map_of_mem _ (⟨0, f, hfQ, by simp⟩ : algebraMap R (blowupAlgebra R P t.x) f ∈
      MonoidalTransform.satIdeal t Q)
  have hx'notin : x' ∉ (MonoidalTransform.satIdeal t Q).map (algebraMap (blowupAlgebra R P t.x) t.ring) := by
    intro hx'm
    have hxR : t.xR ∈ Ideal.span {x'} := by
      rw [hx']
      exact Ideal.mem_map_of_mem _ t.x_mem
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hxR
    have h3 : t.xR ∈ (MonoidalTransform.satIdeal t Q).map (algebraMap (blowupAlgebra R P t.x) t.ring) := by
      rw [← hc]
      exact Ideal.mul_mem_left _ _ hx'm
    have h4 : algebraMap R (blowupAlgebra R P t.x) t.x ∈
        ((MonoidalTransform.satIdeal t Q).map (algebraMap (blowupAlgebra R P t.x) t.ring)).comap
          (algebraMap (blowupAlgebra R P t.x) t.ring) := h3
    rw [hcomap] at h4
    have h5 : t.x ∈ (MonoidalTransform.satIdeal t Q).comap (algebraMap R (blowupAlgebra R P t.x)) := h4
    rw [MonoidalTransform.comap_satIdeal t Q hxQ] at h5
    exact hxQ h5
  have hmul : x' ^ ν * y ∈ (MonoidalTransform.satIdeal t Q).map (algebraMap (blowupAlgebra R P t.x) t.ring) := by
    rw [hy]
    exact hfmem
  exact (hprime.mem_or_mem hmul).resolve_left fun h => hx'notin (hprime.mem_of_pow_mem ν h)

/-- If the strict transform of `Q` in `R'` is proper, then `x ∉ Q` (otherwise `1 = x⁻¹ · x`
lies in it). -/
theorem MonoidalTransform.x_notMem_of_strictTransformIdeal_ne_top (t : MonoidalTransform R P) (hP : P.IsPrime)
    (hS : IsRegularLocalRing (R ⧸ P)) (Q : Ideal R) (hne : strictTransformIdeal t Q ≠ ⊤) :
    t.x ∉ Q := by
  intro hx
  apply hne
  rw [Ideal.eq_top_iff_one]
  refine t.mem_strictTransformIdeal_of_mul_pow_mem hP hS Q (n := 1) ?_
  rw [one_mul, pow_one]
  exact Ideal.mem_map_of_mem _ hx

/-- The strict transform `Q'` of a prime `Q` is a prime of `R'` lying over `Q` as soon as it is a
proper ideal (the point `x'` lies on the strict transform of `W`). -/
theorem MonoidalTransform.isPrime_strictTransformIdeal_and_comap_eq (t : MonoidalTransform R P) (hP : P.IsPrime)
    (hS : IsRegularLocalRing (R ⧸ P)) (Q : Ideal R) [hQ : Q.IsPrime]
    (hne : strictTransformIdeal t Q ≠ ⊤) :
    (strictTransformIdeal t Q).IsPrime ∧ (strictTransformIdeal t Q).comap t.toRing = Q := by
  have hxQ : t.x ∉ Q := MonoidalTransform.x_notMem_of_strictTransformIdeal_ne_top t hP hS Q hne
  have hK : MonoidalTransform.satIdeal t Q ≤ t.M' := by
    intro b hb
    by_contra hbM
    apply hne
    have hunit := IsLocalization.map_units t.ring (⟨b, hbM⟩ : t.M'.primeCompl)
    exact Ideal.eq_top_of_isUnit_mem _
      (MonoidalTransform.map_satIdeal_le_strictTransformIdeal t hP hS Q (Ideal.mem_map_of_mem _ hb)) hunit
  have := MonoidalTransform.isPrime_satIdeal t Q hxQ
  have hdis : Disjoint (t.M'.primeCompl : Set (blowupAlgebra R P t.x)) (MonoidalTransform.satIdeal t Q) :=
    Set.disjoint_left.mpr fun a ha haK => ha (hK haK)
  have heq : strictTransformIdeal t Q =
      (MonoidalTransform.satIdeal t Q).map (algebraMap (blowupAlgebra R P t.x) t.ring) :=
    le_antisymm (MonoidalTransform.strictTransformIdeal_le_map_satIdeal t Q hxQ hK)
      (MonoidalTransform.map_satIdeal_le_strictTransformIdeal t hP hS Q)
  rw [heq]
  refine ⟨IsLocalization.isPrime_of_isPrime_disjoint t.M'.primeCompl t.ring (MonoidalTransform.satIdeal t Q)
    inferInstance hdis, ?_⟩
  have h1 : ((MonoidalTransform.satIdeal t Q).map (algebraMap (blowupAlgebra R P t.x) t.ring)).comap
      (algebraMap (blowupAlgebra R P t.x) t.ring) = MonoidalTransform.satIdeal t Q :=
    IsLocalization.under_map_of_isPrime_disjoint t.M'.primeCompl t.ring
      (I := MonoidalTransform.satIdeal t Q) inferInstance hdis
  show Ideal.comap ((algebraMap (blowupAlgebra R P t.x) t.ring).comp
    (algebraMap R (blowupAlgebra R P t.x))) _ = Q
  rw [← Ideal.comap_comap, h1, MonoidalTransform.comap_satIdeal t Q hxQ]

end Cor2Prime

section Cor2Ring

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- Ring-level variant of Corollary 2 of Theorem 5 (p. 242), for an arbitrary monoidal transform
`R'` of `R` with center `P` (not necessarily residually algebraic): if `Q ⊇ J` is a prime with
`Q ⊆ P`, `R/P`, `R/Q` regular and `R/J` normally flat along `Q`, and the strict transform of
`Q` in `R'` is proper, then `R'/J'` is normally flat along the strict transform `Q'` of `Q`
(`J'` the strict transform of `J`).  Proof as in the paper: first for a monoidal transform
`R₁ ⊇ R'` of the same kind which is residually algebraic over `R` (hence separable, by
characteristic zero), by Corollary 1; then pass to the localization `R'` of `R₁` by flatness.  (The proof of Corollary 2 itself follows the
printed route, with a point `x₁` of `X'`, Corollary 1 at `x₁` and generization, and does not use this
variant, which works with a maximal ideal `N ⊇ M'` of `R[x⁻¹P]` instead of the point `x₁`.) -/
theorem isNormallyFlatAlongIdeal_strictTransform_of_strictTransformIdeal_ne_top [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] [CharZero (ResidueField R)]
    (J P Q : Ideal R) [P.IsPrime] [Q.IsPrime] [IsRegularLocalRing (R ⧸ P)]
    (hQP : Q ≤ P) (hJQ : J ≤ Q) (hQreg : IsRegularLocalRing (R ⧸ Q))
    (hNF : IsNormallyFlatAlongIdeal (Q.map (Ideal.Quotient.mk J)))
    (t : MonoidalTransform R P) (hne : strictTransformIdeal t Q ≠ ⊤) :
    IsNormallyFlatAlongIdeal
      ((strictTransformIdeal t Q).map (Ideal.Quotient.mk (strictTransformIdeal t J))) := by
  classical
  have hxQ : t.x ∉ Q := MonoidalTransform.x_notMem_of_strictTransformIdeal_ne_top t inferInstance inferInstance Q hne
  have hQneP : Q ≠ P := fun h => hxQ (h ▸ t.x_mem)
  have hP0 : P ≠ ⊥ := fun h => hQneP (le_antisymm hQP (by rw [h]; exact bot_le))
  obtain ⟨N, hNmax, hMN⟩ := Ideal.exists_le_maximal t.M' (Ideal.IsPrime.ne_top inferInstance)
  have := hNmax.isPrime
  -- a monoidal transform `t₁` with the same `x`, residually algebraic over `R`
  have hres : RingHom.IsResiduallyAlgebraic (R := R) (R' := (t.withPrime N hMN).ring)
      (t.withPrime N hMN).toRing :=
    ((t.withPrime N hMN).isMaximal_iff_isResiduallyAlgebraic).mp hNmax
  have hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := (t.withPrime N hMN).ring)
      (t.withPrime N hMN).toRing := by
    unfold RingHom.IsResiduallySeparableAlgebraic
    let := (ResidueField.map (t.withPrime N hMN).toRing).toAlgebra
    have : Algebra.IsAlgebraic (ResidueField R) (ResidueField (t.withPrime N hMN).ring) := hres
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : IsRegularLocalRing (t.withPrime N hMN).ring :=
    (MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map (t.withPrime N hMN) inferInstance hP0 inferInstance).1
  -- the strict transform of `Q` in `t₁` is proper, prime, and lies over `Q`
  have hne₁ : strictTransformIdeal (t.withPrime N hMN) Q ≠ ⊤ := fun h =>
    hne (by rw [MonoidalTransform.strictTransformIdeal_liftWithPrime t N hMN, h, Ideal.map_top])
  obtain ⟨hprime, hcomap⟩ := MonoidalTransform.isPrime_strictTransformIdeal_and_comap_eq (t.withPrime N hMN)
    inferInstance inferInstance Q hne₁
  have := hprime
  obtain ⟨-, hflat⟩ := isNormallyFlatAlongIdeal_strictTransform_of_comap J P Q hQP hJQ hQneP
    hQreg hNF (t.withPrime N hMN) hsep (strictTransformIdeal (t.withPrime N hMN) Q)
    hcomap
  -- pass to the localization `R' = (R₁)_{M'}`
  let : Algebra (t.withPrime N hMN).ring t.ring := (t.liftWithPrime N hMN).toAlgebra
  have : Module.Flat (t.withPrime N hMN).ring t.ring :=
    RingHom.flat_algebraMap_iff.mp (MonoidalTransform.flat_liftWithPrime t N hMN)
  have := isNormallyFlatAlongIdeal_mod_map_of_flat (S' := t.ring) _ _ hflat
  rw [MonoidalTransform.strictTransformIdeal_liftWithPrime t N hMN Q,
    MonoidalTransform.strictTransformIdeal_liftWithPrime t N hMN J]
  exact this

end Cor2Ring

end Cor2Aux

/-! ### Auxiliary results for Corollary 2: the point `x₁` of `X'` and the passage to a generization

The proof of Corollary 2 (p. 242) chooses "a point `x₁` in the closure of `x'` in `X'` such that
`f(x₁) = x` and the residue field at `x₁` is algebraic (hence separable algebraic) over that at `x`",
applies Corollary 1 at `x₁`, and concludes that `V'` is normally flat along `W'` at `x'`.  The point
`x₁` is constructed from the maximal ideal `N ⊇ M'` of `R[x⁻¹P]` as the point of `X'` given by the
monoidal transform `R[x⁻¹P]_N` of `R` (`MonoidalTransformation.pointOfMonoidalTransform`, by the
universal mapping property of `f`, `Hironaka/Compat/BlowupStalkPoints.lean`). -/

section Corollary2Points

open CategoryTheory

/-- If `h ∘ g` is residually algebraic for local homomorphisms `g`, `h`, so is `g`. -/
theorem RingHom.isResiduallyAlgebraic_of_comp {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [IsLocalRing R] [IsLocalRing S] [IsLocalRing T] (g : R →+* S) (h : S →+* T)
    (φ : R →+* T) (hg : IsLocalHom g) (hh : IsLocalHom h) (hφ' : IsLocalHom φ)
    (hφ : h.comp g = φ) (hc : RingHom.IsResiduallyAlgebraic φ) :
    RingHom.IsResiduallyAlgebraic g := by
  subst hφ
  unfold RingHom.IsResiduallyAlgebraic at hc ⊢
  let _ : Algebra (ResidueField R) (ResidueField S) := (ResidueField.map g).toAlgebra
  let _ : Algebra (ResidueField R) (ResidueField T) := (ResidueField.map (h.comp g)).toAlgebra
  let _ : Algebra (ResidueField S) (ResidueField T) := (ResidueField.map h).toAlgebra
  let ι : ResidueField S →ₐ[ResidueField R] ResidueField T :=
    { ResidueField.map h with
      commutes' := fun r => by
        show ResidueField.map h (ResidueField.map g r) = ResidueField.map (h.comp g) r
        obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
        simp [IsLocalRing.ResidueField.map_residue] }
  exact Algebra.IsAlgebraic.of_injective ι (ResidueField.map h).injective

/-- Residual algebraicity depends only on the homomorphism. -/
theorem RingHom.isResiduallyAlgebraic_congr {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] {α β : R →+* S} [IsLocalHom α] [IsLocalHom β] (h : α = β)
    (hα : RingHom.IsResiduallyAlgebraic α) : RingHom.IsResiduallyAlgebraic β := by
  subst h
  exact hα

section Cor2Point

variable {X : Scheme.{u}} {B : Subscheme X} (t : MonoidalTransformation X B) {y : X}
  [IsRegularLocalRing (X.presheaf.stalk y)] [IsDomain (X.presheaf.stalk y)]
  (s : MonoidalTransform (X.presheaf.stalk y) (B.stalkIdeal y))
  (N : Ideal (blowupAlgebra (X.presheaf.stalk y) (B.stalkIdeal y) s.x)) [hN : N.IsPrime]
  (h : s.M' ≤ N)

/-- The lift of `s` is the lift of `s.withPrime N` composed with `Spec` of the localization map. -/
theorem MonoidalTransformation.liftOfMonoidalTransform_eq_comp :
    t.liftOfMonoidalTransform s = Spec.map (CommRingCat.ofHom (s.liftWithPrime N h)) ≫
      t.liftOfMonoidalTransform (s.withPrime N h) := by
  refine MonoidalTransformation.hom_ext (t := t) ?_ ?_
  · rw [t.liftOfMonoidalTransform_f s, Category.assoc, t.liftOfMonoidalTransform_f (s.withPrime N h),
      MonoidalTransform.toBase, MonoidalTransform.toBase, ← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun r => (s.liftWithPrime_toRing N h r).symm)
  · rw [t.liftOfMonoidalTransform_f s]
    exact s.isInvertibleIdeal_totalTransform_toBase

/-- The point of `s` specializes to the point of `s.withPrime N` (the closure of `x'` contains `x₁`). -/
theorem MonoidalTransformation.pointOfMonoidalTransform_specializes :
    t.pointOfMonoidalTransform s ⤳ t.pointOfMonoidalTransform (s.withPrime N h) := by
  have h1 : t.pointOfMonoidalTransform s =
      t.liftOfMonoidalTransform (s.withPrime N h)
        (Spec.map (CommRingCat.ofHom (s.liftWithPrime N h)) s.closedPt) := by
    unfold MonoidalTransformation.pointOfMonoidalTransform
    rw [t.liftOfMonoidalTransform_eq_comp s N h]
    rfl
  rw [h1]
  refine Specializes.map ?_ (t.liftOfMonoidalTransform (s.withPrime N h)).continuous
  exact IsLocalRing.specializes_closedPoint (R := (s.withPrime N h).ring) _

/-- The local homomorphism `λ : O_{X',x₁} → R₁` induced by the lift of a monoidal transform `R₁`
satisfies `λ ∘ f* = (R → R₁)`, `f* : O_{X,y} → O_{X',x₁}` the stalk map of `f`. -/
theorem MonoidalTransformation.stalkMapOf_comp_stalkClosedPointTo
    (h₁ : t.f (t.liftOfMonoidalTransform s (closedPoint (CommRingCat.of s.ring))) = y) :
    t.f.stalkMapOf h₁ ≫ Scheme.stalkClosedPointTo (t.liftOfMonoidalTransform s) =
      CommRingCat.ofHom s.toRing := by
  have hloc : IsLocalHom (CommRingCat.ofHom s.toRing).hom := inferInstanceAs (IsLocalHom s.toRing)
  have hF := t.liftOfMonoidalTransform_f s
  have e1 : (SpecToEquivOfLocalRing X (CommRingCat.of s.ring))
      (t.liftOfMonoidalTransform s ≫ t.f) = ⟨_, Scheme.stalkClosedPointTo
        (t.liftOfMonoidalTransform s ≫ t.f), inferInstance⟩ := rfl
  have e2 : (SpecToEquivOfLocalRing X (CommRingCat.of s.ring))
      (Spec.map (CommRingCat.ofHom s.toRing) ≫ X.fromSpecStalk y) =
      ⟨y, CommRingCat.ofHom s.toRing, hloc⟩ :=
    (SpecToEquivOfLocalRing X (CommRingCat.of s.ring)).apply_symm_apply
      ⟨y, CommRingCat.ofHom s.toRing, hloc⟩
  have := congrArg (SpecToEquivOfLocalRing X (CommRingCat.of s.ring)) hF
  rw [e1, MonoidalTransform.toBase, e2] at this
  obtain ⟨hy, hc⟩ := SpecToEquivOfLocalRing_eq_iff.mp this
  have hc' : t.f.stalkMap (t.liftOfMonoidalTransform s (closedPoint (CommRingCat.of s.ring))) ≫
      Scheme.stalkClosedPointTo (t.liftOfMonoidalTransform s) =
      (X.presheaf.stalkCongr (Inseparable.of_eq h₁)).hom ≫ CommRingCat.ofHom s.toRing := by
    rw [← Scheme.stalkClosedPointTo_comp]
    exact hc
  unfold Scheme.Hom.stalkMapOf
  rw [Category.assoc, hc']
  have key : ∀ {a b : X} (e₁ : Inseparable a b) (e₂ : Inseparable b a)
      (φ : X.presheaf.stalk a ⟶ CommRingCat.of s.ring),
      (X.presheaf.stalkCongr e₁).hom ≫ (X.presheaf.stalkCongr e₂).hom ≫ φ = φ := by
    intro a b e₁ e₂ φ
    have h : X.presheaf.stalkCongr e₂ = (X.presheaf.stalkCongr e₁).symm := by
      ext1
      rfl
    rw [h, Iso.symm_hom, Iso.hom_inv_id_assoc]
  exact key _ _ _

end Cor2Point

section Cor2Existence

variable {X : Scheme.{u}} {B : Subscheme X} (t : MonoidalTransformation X B)

/-- **Existence of the point `x₁`** of the proof of Corollary 2 of Theorem 5 (p. 242): "Let `x₁` be a
point in the closure of `x'` in `X'` such that `f(x₁) = x` and the residue field at `x₁` is algebraic
over that at `x`." -/
theorem MonoidalTransformation.exists_specializes_isResiduallyAlgebraic {y : X}
    [IsRegularLocalRing (X.presheaf.stalk y)] [IsDomain (X.presheaf.stalk y)] {x' : t.X'}
    (h' : t.f x' = y) :
    ∃ (x₁ : t.X') (h₁ : t.f x₁ = y), x' ⤳ x₁ ∧
      RingHom.IsResiduallyAlgebraic (t.f.stalkMapOf h₁).hom := by
  obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk_of_eq h'
  have hx' : t.pointOfMonoidalTransform s = x' := t.pointOfMonoidalTransform_eq s h' e he
  obtain ⟨N, hNmax, hMN⟩ := Ideal.exists_le_maximal s.M' (Ideal.IsPrime.ne_top inferInstance)
  have hNp := hNmax.isPrime
  refine ⟨t.pointOfMonoidalTransform (s.withPrime N hMN),
    t.f_pointOfMonoidalTransform (s.withPrime N hMN), ?_, ?_⟩
  · rw [← hx']
    exact t.pointOfMonoidalTransform_specializes s N hMN
  · have h₁ := t.f_pointOfMonoidalTransform (s.withPrime N hMN)
    have hres : RingHom.IsResiduallyAlgebraic (s.withPrime N hMN).toRing :=
      ((s.withPrime N hMN).isMaximal_iff_isResiduallyAlgebraic).mp hNmax
    have hcomp := congrArg CommRingCat.Hom.hom
      (t.stalkMapOf_comp_stalkClosedPointTo (s.withPrime N hMN) h₁)
    have hlocL : IsLocalHom (Scheme.stalkClosedPointTo
        (t.liftOfMonoidalTransform (s.withPrime N hMN))).hom :=
      Scheme.isLocalHom_stalkClosedPointTo' (R := (s.withPrime N hMN).ring) _
    exact RingHom.isResiduallyAlgebraic_of_comp (t.f.stalkMapOf h₁).hom
      (Scheme.stalkClosedPointTo (t.liftOfMonoidalTransform (s.withPrime N hMN))).hom
      (s.withPrime N hMN).toRing inferInstance hlocL inferInstance hcomp hres

end Cor2Existence

section Generization

variable {Y : Scheme.{u}}

/-- Normal flatness passes to a generization: if `V` is normally flat along `W ⊆ V` at `y` and `η ⤳ y`
lies on `W`, then `V` is normally flat along `W` at `η` (`O_η` is a localization of `O_y`, hence flat
over it, and `V_η = V_y O_η`, `W_η = W_y O_η`). -/
theorem Subscheme.isNormallyFlatAlongAt'_of_specializes (V W : Subscheme Y) (hWV : W.IsContainedIn V)
    {η y : Y} (h : η ⤳ y) (hη : η ∈ W.pts) (hy : Subscheme.IsNormallyFlatAlongAt' V W y) :
    Subscheme.IsNormallyFlatAlongAt' V W η := by
  rw [Subscheme.isNormallyFlatAlongAt'_iff V W hWV] at hy ⊢
  refine ⟨hη, ?_⟩
  let _ := (Y.presheaf.stalkSpecializes h).hom.toAlgebra
  have hloc := isLocalization_stalkSpecializes_of_specializes h
  have : Module.Flat (Y.presheaf.stalk y) (Y.presheaf.stalk η) :=
    IsLocalization.flat (Y.presheaf.stalk η) (((IsLocalRing.maximalIdeal
      (Y.presheaf.stalk η)).comap (Y.presheaf.stalkSpecializes h).hom).primeCompl)
  rw [Subscheme.stalkIdeal_eq_map_stalkSpecializes W h,
    Subscheme.stalkIdeal_eq_map_stalkSpecializes V h]
  exact isNormallyFlatAlongIdeal_mod_map_of_flat _ _ hy.2

end Generization

section Density

variable {X : Scheme.{u}}

/-- In an algebraic scheme, if `x` lies in the closure of `W − B` (`B, W` closed), then `x` is a
specialization of a point `η` of `W − B` (a generic point of an irreducible component of the closure
of `W − B`, which `W − B`, open in `W`, meets). -/
theorem Subscheme.exists_specializes_mem_diff_of_mem_closure [IsAlgebraicScheme X]
    (W B : Subscheme X) {x : X} (hx : x ∈ closure (W.pts \ B.pts)) :
    ∃ η ∈ W.pts \ B.pts, η ⤳ x := by
  have := IsAlgebraicScheme.noetherianSpace X
  set S := W.pts \ B.pts with hS
  obtain ⟨T, hTfin, hTcl, hTirr, hTeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_closure (s := S))
  have hSeq : S = ⋃ t ∈ T, S ∩ t := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    constructor
    · intro hz
      have : z ∈ ⋃₀ T := hTeq ▸ subset_closure hz
      obtain ⟨t, ht, hzt⟩ := this
      exact ⟨t, ht, hz, hzt⟩
    · rintro ⟨t, -, hz, -⟩
      exact hz
  have hxcl : x ∈ ⋃ t ∈ T, closure (S ∩ t) := by
    rw [← hTfin.closure_biUnion, ← hSeq]
    exact hx
  obtain ⟨t, htT, hxt⟩ := Set.mem_iUnion₂.mp hxcl
  have hxt' : x ∈ t := (hTcl t htT).closure_subset_iff.mpr Set.inter_subset_right hxt
  obtain ⟨z, hzS, hzt⟩ : (S ∩ t).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hxt
    exact hxt
  have htW : t ⊆ W.pts := fun w hw => by
    have : w ∈ closure S := by
      rw [hTeq]
      exact ⟨t, htT, hw⟩
    exact W.support.isClosed.closure_subset_iff.mpr Set.sdiff_subset this
  set g := (hTirr t htT).genericPoint with hg
  have hgt : closure {g} = t := (hTirr t htT).closure_genericPoint (hTcl t htT)
  have hgt' : g ∈ t := hgt ▸ subset_closure rfl
  refine ⟨g, ⟨htW hgt', fun hgB => hzS.2 ?_⟩, specializes_iff_mem_closure.mpr (hgt ▸ hxt')⟩
  exact B.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hgB) (hgt ▸ hzt)

/-- "`W − B` is dense in `W`" gives `Q ≠ P` at every point of `W`: if `W_x = B_x`, a point `η` of
`W − B` specializing to `x` has `W_η = W_x O_η = B_x O_η = B_η`, so `η ∈ B`. -/
theorem Subscheme.stalkIdeal_ne_of_subset_closure_diff [IsAlgebraicScheme X] (W B : Subscheme X)
    (hdense : W.pts ⊆ closure (W.pts \ B.pts)) {x : X} (hx : x ∈ W.pts) :
    W.stalkIdeal x ≠ B.stalkIdeal x := by
  intro heq
  obtain ⟨η, ⟨hηW, hηB⟩, hηx⟩ := Subscheme.exists_specializes_mem_diff_of_mem_closure W B (hdense hx)
  apply hηB
  rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top] at hηW ⊢
  rw [Subscheme.stalkIdeal_eq_map_stalkSpecializes B hηx, ← heq,
    ← Subscheme.stalkIdeal_eq_map_stalkSpecializes W hηx]
  exact hηW

end Density

end Corollary2Points

/-! ### Corollary 2 of Theorem 5 (p. 242) -/

section Corollary2

/-- Corollary 2 of Theorem 5 (p. 242) at the point `x₁`: the application of Corollary 1 "to `R`, `J`,
`P`, `Q`, `R₁`, `J₁` and `Q₁`" in the proof of Corollary 2.  Here `R` is the local ring of `X` at
`x = f(x₁)`, `J` the ideal of `V` in `R`, `P` the prime ideal of `B`, `Q` the ideal of `W` (a prime
which is a permissible center for `J`, since `x` is a simple point of `W` and `V` is normally flat
along `W` at `x`), `R₁` the local ring of `X'` at `x₁` (a monoidal transform of `R` with center `P`,
residually separable algebraic over `R` since its residue field is algebraic over that of `R` in
characteristic zero), `J₁` the ideal of `V'` in `R₁` (the strict transform of `J`) and `Q₁` the
prime ideal of `W'` in `R₁` (the strict transform of `Q`, a prime lying over `Q`).  The condition
`Q ≠ P` of Corollary 1 is the hypothesis `hQneP`. -/
theorem isNormallyFlatAlongAt'_strictTransform_of_isResiduallyAlgebraic [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {X : Scheme.{u}}
    [IsAlgebraicScheme X] (hX : X.IsNonsingular) (V W B : Subscheme X)
    (hWV : W.IsContainedIn V) (hBW : B.IsContainedIn W) (hB : B.IsNonsingular)
    (hBirr : B.IsIrreducible) (t : MonoidalTransformation X B) (x₁ : t.X')
    (hxB : t.f.base x₁ ∈ B.pts) (hWx : W.IsSimpleAt (t.f.base x₁))
    (hflat : Subscheme.IsNormallyFlatAlongAt' V W (t.f.base x₁))
    (hQneP : W.stalkIdeal (t.f.base x₁) ≠ B.stalkIdeal (t.f.base x₁))
    (hx₁W : x₁ ∈ (Subscheme.strictTransform t W).pts)
    (hres : RingHom.IsResiduallyAlgebraic (t.f.stalkMap x₁).hom) :
    Subscheme.IsNormallyFlatAlongAt' (Subscheme.strictTransform t V)
      (Subscheme.strictTransform t W) x₁ := by
  classical
  have hreg : IsRegularLocalRing (X.presheaf.stalk (t.f.base x₁)) := hX _
  have hdom : IsDomain (X.presheaf.stalk (t.f.base x₁)) :=
    Transforms.isDomain_of_isRegularLocalRing _
  have hchar : CharZero (ResidueField (X.presheaf.stalk (t.f.base x₁))) :=
    charZero_residueField_stalk X _
  have hBV : B.IsContainedIn V := fun U => (hWV U).trans (hBW U)
  obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk x₁
  obtain ⟨ξ, hξ⟩ := Subscheme.exists_isGenericPoint hBirr
  -- stalks of the strict transforms at `x₁`
  have hW' : (Subscheme.strictTransform t W).stalkIdeal x₁ =
      (strictTransformIdeal s (W.stalkIdeal (t.f.base x₁))).map e := by
    rw [← MonoidalTransformation.strictTransformIdealSheaf_eq_strictTransform hX hBirr hB t W hBW]
    exact (Subscheme.stalkIdeal_strictTransformIdealSheaf_eq_map hX hB t W hξ x₁ s e he).symm.symm
  have hV' : (Subscheme.strictTransform t V).stalkIdeal x₁ =
      (strictTransformIdeal s (V.stalkIdeal (t.f.base x₁))).map e := by
    rw [← MonoidalTransformation.strictTransformIdealSheaf_eq_strictTransform hX hBirr hB t V hBV]
    exact (Subscheme.stalkIdeal_strictTransformIdealSheaf_eq_map hX hB t V hξ x₁ s e he).symm.symm
  have hW'V' : (Subscheme.strictTransform t W).IsContainedIn (Subscheme.strictTransform t V) :=
    MonoidalTransformation.isContainedIn_strictTransform t hWV
  rw [Subscheme.isNormallyFlatAlongAt'_iff _ _ hW'V']
  refine ⟨hx₁W, ?_⟩
  rw [hW', hV']
  -- data at `x = f(x₁)`: `R`, `J`, `P`, `Q`
  have hP : (B.stalkIdeal (t.f.base x₁)).IsPrime :=
    Subscheme.isPrime_stalkIdeal_of_isNonsingular hB hxB
  have hPreg : IsRegularLocalRing (X.presheaf.stalk (t.f.base x₁) ⧸ B.stalkIdeal (t.f.base x₁)) :=
    Subscheme.isRegularLocalRing_quotient_of_isNonsingular hB hxB
  have hQreg : IsRegularLocalRing (X.presheaf.stalk (t.f.base x₁) ⧸ W.stalkIdeal (t.f.base x₁)) :=
    hWx.2
  have hQ : (W.stalkIdeal (t.f.base x₁)).IsPrime := by
    have := isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f.base x₁) ⧸
      W.stalkIdeal (t.f.base x₁))
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  have hQP : W.stalkIdeal (t.f.base x₁) ≤ B.stalkIdeal (t.f.base x₁) :=
    Subscheme.stalkIdeal_mono (show W ≤ B from fun U => hBW U) _
  have hJQ : V.stalkIdeal (t.f.base x₁) ≤ W.stalkIdeal (t.f.base x₁) :=
    Subscheme.stalkIdeal_mono (show V ≤ W from fun U => hWV U) _
  have hNF : IsNormallyFlatAlongIdeal
      ((W.stalkIdeal (t.f.base x₁)).map (Ideal.Quotient.mk (V.stalkIdeal (t.f.base x₁)))) :=
    ((Subscheme.isNormallyFlatAlongAt'_iff V W hWV _).mp hflat).2
  have hne : strictTransformIdeal s (W.stalkIdeal (t.f.base x₁)) ≠ ⊤ := by
    intro h
    have := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hx₁W
    rw [hW', h, Ideal.map_top] at this
    exact this rfl
  -- "`Q ≠ P`" (`x ∈ P - Q`), "`R₁` is residually separable algebraic over `R`" (`x₁` has algebraic
  -- residue field over that at `x`, hence separable algebraic in characteristic zero)
  have hP0 : B.stalkIdeal (t.f.base x₁) ≠ ⊥ := fun h =>
    hQneP (le_antisymm hQP (by rw [h]; exact bot_le))
  have hlocE : IsLocalHom e.toRingHom := ⟨fun a (ha : IsUnit (e a)) => by
    simpa using ha.map e.symm.toRingHom⟩
  have hresS : RingHom.IsResiduallyAlgebraic s.toRing :=
    RingHom.isResiduallyAlgebraic_of_comp s.toRing e.toRingHom (t.f.stalkMap x₁).hom
      inferInstance hlocE inferInstance he hres
  have hsep : RingHom.IsResiduallySeparableAlgebraic s.toRing := by
    unfold RingHom.IsResiduallySeparableAlgebraic
    let _ := (ResidueField.map s.toRing).toAlgebra
    have : Algebra.IsAlgebraic (ResidueField (X.presheaf.stalk (t.f.base x₁)))
        (ResidueField s.ring) := hresS
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  have _ : IsRegularLocalRing s.ring :=
    (MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map s hP hP0 hPreg).1
  -- "`Q₁` the prime ideal of `W'` in `R₁`": the strict transform of `Q` in `R₁`, a prime lying
  -- over `Q`
  obtain ⟨hprime, hcomap⟩ := MonoidalTransform.isPrime_strictTransformIdeal_and_comap_eq s hP hPreg
    (W.stalkIdeal (t.f.base x₁)) hne
  have _ := hprime
  -- Corollary 1 applied to `R`, `J`, `P`, `Q`, `R₁`, `J₁` and `Q₁`
  obtain ⟨-, hflat₁⟩ := isNormallyFlatAlongIdeal_strictTransform_of_comap
    (V.stalkIdeal (t.f.base x₁)) (B.stalkIdeal (t.f.base x₁)) (W.stalkIdeal (t.f.base x₁))
    hQP hJQ hQneP hQreg hNF s hsep (strictTransformIdeal s (W.stalkIdeal (t.f.base x₁))) hcomap
  -- transport along `e : R₁ ≃ O_{X', x₁}`
  refine isNormallyFlatAlongIdeal_transport
    ((Ideal.quotientEquiv (strictTransformIdeal s (V.stalkIdeal (t.f.base x₁)))
      ((strictTransformIdeal s (V.stalkIdeal (t.f.base x₁))).map e) e rfl)) _ _ ?_ hflat₁
  have hcomp : ((Ideal.quotientEquiv (strictTransformIdeal s (V.stalkIdeal (t.f.base x₁)))
      ((strictTransformIdeal s (V.stalkIdeal (t.f.base x₁))).map e) e rfl : _ ≃+* _) :
        _ →+* _).comp (Ideal.Quotient.mk (strictTransformIdeal s (V.stalkIdeal (t.f.base x₁)))) =
      (Ideal.Quotient.mk ((strictTransformIdeal s (V.stalkIdeal (t.f.base x₁))).map e)).comp
        (e : _ →+* _) := RingHom.ext fun r => rfl
  rw [Ideal.map_map, hcomp]
  exact (Ideal.map_map _ _).symm

/-- Corollary 2, p. 242: "Let `X` be an irreducible non-singular algebraic scheme, `V` a
subscheme of `X`, `W` a subscheme of `V`, and `B` a non-singular irreducible subscheme of `W`
such that `W − B` is dense in `W`. Let `f : X' → X` be the monoidal transformation of `X` with
center `B`. Let `V'` (resp. `W'`) be the strict transform of `V` (resp. `W`) on `X'` by `f`. Let
`x` be a point of `B`. If `x` is a simple point of `W` and if `V` is normally flat along `W` at
`x`, then `V'` is normally flat along `W'` at every point `x'` of `W'` with `f(x') = x`."

Formalization notes (encoding).
* "`W` is a subscheme of `V`" is `W.IsContainedIn V` and "`B` is a subscheme of `W`" is
  `B.IsContainedIn W`.
* "`W − B` is dense in `W`" is `W.pts ⊆ closure (W.pts \ B.pts)`.
* "`V` is normally flat along `W` at `x`" is `Subscheme.IsNormallyFlatAlongAt' V W x`
  (Definition 1 of Ch. 0 for the subscheme `W ∩ V` of `V`).

The proof follows the printed one, step by step.
* "Let `R` be the local ring of `X` at `x`, `J` the ideal of `V` in `R`, `P` the prime ideal of `B`
  in `R` and `Q` the ideal of `W` in `R`.  By the assumption that `x` is a simple point of `W` and `V`
  is normally flat along `W` at `x`, `Q` is a prime ideal in `R` which is a permissible center for `J`.
  By the assumption that `B` is non-singular, `R/P` is regular."  (The stalk ideals at `x`:
  `hWx`, `Subscheme.isPrime_stalkIdeal_of_isNonsingular`, `hQreg`.)
* "Let `x₁` be a point in the closure of `x'` in `X'` such that `f(x₁) = x` and the residue field at
  `x₁` is algebraic (hence separable algebraic) over that at `x`."
  (`MonoidalTransformation.exists_specializes_isResiduallyAlgebraic`; `x₁ ∈ W'` as `W'` is closed.)
* "Let `R₁` be the local ring of `X'` at `x₁`, and `Q₁` the prime ideal of `W'` in `R₁`.  `R₁` is a
  monoidal transform of `R` with center `P` and the ideal `J₁` of `V'` in `R₁` is the strict transform
  of `J` in `R₁`."  (`MonoidalTransformation.exists_monoidalTransform_stalk` and Remark 3,
  `Subscheme.stalkIdeal_strictTransformIdealSheaf_eq_map`; `Q₁` is a prime with `Q₁ ∩ R = Q`,
  `MonoidalTransform.isPrime_strictTransformIdeal_and_comap_eq`.)
* "Now, applying Corollary 1 to `R`, `J`, `P`, `Q`, `R₁`, `J₁` and `Q₁`, we see that `V'` is normally
  flat along `W'` at `x₁`."
  (`isNormallyFlatAlongAt'_strictTransform_of_isResiduallyAlgebraic`.)
* "It follows that `V'` is normally flat along `W'` at `x'`."
  (`Subscheme.isNormallyFlatAlongAt'_of_specializes`: `O_{X',x'}` is a localization of `O_{X',x₁}`,
  `V'_{x'}` and `W'_{x'}` are the extensions of `V'_{x₁}` and `W'_{x₁}`, and normal flatness passes to a
  flat extension.)

Deviation from the paper (gap filled): the existence of `x₁` is asserted without argument.  It is the
point of `X'` given (by the universal mapping property of `f`) by the monoidal transform `R[x⁻¹P]_N`
of `R`, `N` a maximal ideal of `R[x⁻¹P]` containing `M'`; `x'` specializes to it, and its residue field
is algebraic over that of `R` (Zariski's lemma, as `N` is maximal).  The condition `Q ≠ P` of Corollary 1
is not mentioned: it is where the hypothesis "`W − B` is dense in `W`" is used (a point of `W − B`
specializing to `x` has `W_η = W_x R_η = B_x R_η = B_η` if `Q = P`; `Subscheme.stalkIdeal_ne_of_subset_closure_diff`).
That `Q₁` is a prime of `R₁` lying over `Q`, that `J₁` is the ideal of `V'` in `R₁`, and the final
"It follows" (generization) are proved.  The hypothesis "`X` is irreducible" is not used. -/
@[blueprint "cor:III.thm5-2"
  (statement := /-- Let $X$ be an irreducible non-singular algebraic scheme, $V$ a subscheme of
    $X$, $W$ a subscheme of $V$, and $B$ a non-singular irreducible subscheme of $W$ such that
    $W-B$ is dense in $W$. Let $f\colon X'\to X$ be the monoidal transformation of $X$ with
    center $B$ (\cref{def:monoidal-transformation}). Let $V'$ (resp.\ $W'$) be the strict
    transform of $V$ (resp.\ $W$) on $X'$ by $f$ (\cref{def:strict-transform}). Let $x$ be a
    point of $B$. If $x$ is a simple point of $W$ and if $V$ is normally flat along $W$ at $x$
    (\cref{def:0.1-normally-flat-at}), then $V'$ is normally flat along $W'$ at every point $x'$
    of $W'$ with $f(x')=x$. (Corollary 2, p.~242.) -/)
  (proof := /-- Let $R$ be the local ring of $X$ at $x$, $J$ the ideal of $V$ in $R$, $P$ the
    prime ideal of $B$ in $R$ and $Q$ the ideal of $W$ in $R$. By the assumption that $x$ is a
    simple point of $W$ and $V$ is normally flat along $W$ at $x$, $Q$ is a prime ideal in $R$
    which is a permissible center for $J$ (\cref{def:III.8}). By the assumption that $B$ is
    non-singular, $R/P$ is regular. Let $x_1$ be a point in the closure of $x'$ in $X'$ such
    that $f(x_1)=x$ and the residue field at $x_1$ is algebraic (hence separable algebraic) over
    that at $x$. Let $R_1$ be the local ring of $X'$ at $x_1$, and $Q_1$ the prime ideal of $W'$
    in $R_1$. (Note that $x_1$ is a simple point of $W'$.) $R_1$ is a monoidal transform of $R$
    with center $P$ and the ideal $J_1$ of $V'$ in $R_1$ is the strict transform of $J$ in
    $R_1$. Now, applying Corollary~1 (\cref{cor:III.thm5-1}) to $R$, $J$, $P$, $Q$, $R_1$, $J_1$
    and $Q_1$, we see that $V'$ is normally flat along $W'$ at $x_1$. It follows that $V'$ is
    normally flat along $W'$ at $x'$. \qed

    \textbf{Formal proof.} The Lean proof follows this proof step by step. The stalk ideals of
    $V$, $W$, $B$ at $x$ give $J$, $Q$, $P$. The point $x_1$ is the point of $X'$ given, by the
    universal mapping property of $f$, by the monoidal transform $R[x^{-1}P]_N$ of $R$, where $N$
    is a maximal ideal of $R[x^{-1}P]$ containing the prime $M'$ of $R'=\mathcal O_{X',x'}$; the
    point $x'$ specializes to $x_1$, and the residue field at $x_1$ is algebraic over that of $R$
    by Zariski's lemma ($N$ is maximal); it is separable since the characteristic is zero. The
    local ring $R_1$ at $x_1$ is a monoidal transform of $R$ with center $P$ (\cref{rem:III.2-3}),
    the ideal of $V'$ (resp.\ $W'$) in $R_1$ is the strict transform $J_1$ of $J$ (resp.\ $Q_1$ of
    $Q$) in $R_1$, and $Q_1$ is a prime ideal lying over $Q$. Corollary~1 gives the normal flatness
    at $x_1$. The final sentence is the passage to a generization: $\mathcal O_{X',x'}$ is a
    localization of $\mathcal O_{X',x_1}$, hence flat over it, and the ideals of $V'$ and $W'$ at
    $x'$ are the extensions of those at $x_1$.

    \textbf{Gaps in the paper filled.} (1) The existence of $x_1$, with the properties stated,
    is asserted without argument; it is proved as above. (2) Corollary~1 requires $Q\ne P$, which
    the paper does not mention; it follows from the hypothesis that $W-B$ is dense in $W$: if
    $Q=P$, a point $\eta$ of $W-B$ specializing to $x$ (which exists by density) would have
    $W_\eta=W_xR_\eta=B_xR_\eta=B_\eta$, so $\eta\in B$. (3) That the ideal $Q_1$ of $W'$ in
    $R_1$ is a prime with $Q_1\cap R=Q$, and the generization ``It follows that $V'$ is normally
    flat along $W'$ at $x'$'' (normal flatness is preserved by the flat base change
    $R_1\to R'$, via the isomorphism
    $\operatorname{gr}^n_{IA'}(A')\cong\operatorname{gr}^n_I(A)\otimes_{A/I}A'/IA'$ as in
    Lemma~9) are proved in Lean. The hypothesis that $X$ is irreducible is not used. -/)
  (latexEnv := "corollary")]
theorem isNormallyFlatAlongAt'_strictTransform [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {X : Scheme.{u}} [IsAlgebraicScheme X]
    (hXirr : IrreducibleSpace X) (hX : X.IsNonsingular) (V W B : Subscheme X)
    (hWV : W.IsContainedIn V) (hBW : B.IsContainedIn W) (hB : B.IsNonsingular)
    (hBirr : B.IsIrreducible) (hdense : W.pts ⊆ closure (W.pts \ B.pts))
    (t : MonoidalTransformation X B) (x : X) (hxB : x ∈ B.pts) (hWx : W.IsSimpleAt x)
    (hflat : Subscheme.IsNormallyFlatAlongAt' V W x) :
    ∀ x' : t.X', x' ∈ (Subscheme.strictTransform t W).pts → t.f.base x' = x →
      Subscheme.IsNormallyFlatAlongAt' (Subscheme.strictTransform t V)
        (Subscheme.strictTransform t W) x' := by
  intro x' hx'W hfx
  have _ := hXirr
  have _ : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  have _ : IsDomain (X.presheaf.stalk x) := Transforms.isDomain_of_isRegularLocalRing _
  -- "Let `x₁` be a point in the closure of `x'` in `X'` such that `f(x₁) = x` and the residue field
  -- at `x₁` is algebraic (hence separable algebraic) over that at `x`."
  obtain ⟨x₁, h₁, hspec, hres⟩ := t.exists_specializes_isResiduallyAlgebraic hfx
  -- `x₁` lies on `W'` (a closed subscheme containing `x'`)
  have hx₁W : x₁ ∈ (Subscheme.strictTransform t W).pts :=
    (Subscheme.strictTransform t W).support.isClosed.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hx'W) (specializes_iff_mem_closure.mp hspec)
  subst h₁
  replace hres := RingHom.isResiduallyAlgebraic_congr
    (congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMapOf_rfl t.f x₁)) hres
  -- "Now, applying Corollary 1 to `R`, `J`, `P`, `Q`, `R₁`, `J₁` and `Q₁`, we see that `V'` is
  -- normally flat along `W'` at `x₁`."
  -- `Q ≠ P`, which Corollary 1 requires, is where "`W − B` is dense in `W`" is used
  have hQneP : W.stalkIdeal (t.f.base x₁) ≠ B.stalkIdeal (t.f.base x₁) :=
    Subscheme.stalkIdeal_ne_of_subset_closure_diff W B hdense (pts_subset_of_isContainedIn hBW hxB)
  have hnf₁ := isNormallyFlatAlongAt'_strictTransform_of_isResiduallyAlgebraic hX V W B hWV hBW hB
    hBirr t x₁ hxB hWx hflat hQneP hx₁W hres
  -- "It follows that `V'` is normally flat along `W'` at `x'`."
  exact Subscheme.isNormallyFlatAlongAt'_of_specializes _ _
    (MonoidalTransformation.isContainedIn_strictTransform t hWV) hspec hx'W hnf₁

end Corollary2

/-! ### Corollary 3 of Theorem 5 (pp. 242–244) -/

section Corollary3

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- The two conditions (i) and (ii) imposed on the system `(g₁, …, g_m)` of elements of `J` in
Corollary 3, p. 242: "(i) the initial forms of the `g_j` (`1 ≤ j ≤ m`) in `gr_M(R)` generate the
ideal `gr_M(J, R)`, and (ii) `ν_M(g_j) = ν_{QR_Q}(g_j)` for all `j` (`1 ≤ j ≤ m`)", together
with "we have a system of elements `(g₁, …, g_m)` of `J`" (membership in `J`).  Packaged because
assertion (b) of the Corollary concludes that the transformed system has the same two properties
"with respect to `R₁`, `M₁`, `Q₁` and `J₁`". -/
def IsLocallyAdaptedSystem (Q J : Ideal R) [Q.IsPrime] {m : ℕ} (g : Fin m → R) : Prop :=
  (∀ j, g j ∈ J) ∧
  grIdeal (maximalIdeal R) J =
    Ideal.span (Set.range fun j => initialForm (maximalIdeal R) (g j)) ∧
  ∀ j, Ideal.ordElem (maximalIdeal R) (g j) =
    Ideal.ordElem (Q.map (algebraMap R (Localization.AtPrime Q)))
      (algebraMap R (Localization.AtPrime Q) (g j))

variable {R}

/-- Corollary 3 (a), p. 242: "Let `R` be a regular local ring, and `M` the maximal ideal of `R`.
Let `Q` be a prime ideal in `R`, and `J` an ideal in `R` such that `Q ⊇ J`. Suppose we have a
system of elements `(g₁, …, g_m)` of `J` such that (i) the initial forms of the `g_j` in
`gr_M(R)` generate the ideal `gr_M(J, R)`, and (ii) `ν_M(g_j) = ν_{QR_Q}(g_j)` for all `j`. Then
we have the following facts: (a) If `P` is any prime ideal in `R` such that `P ⊇ Q` and `R/P` is
regular, then `P` is a permissible center for `J`."

Formalization note (encoding): conditions (i) and (ii) are `HasCor3Properties R Q J g`.

Deviation from the paper (gap filled, minor): the paper's argument is followed:
`ν_M(g_j) = ν_{QR_Q}(g_j) ≤ ν_{PR_P}(g_j) = ν_P(g_j) ≤ ν_M(g_j)` (Theorem 1 of §3 in `R_P`, and
`ν_{PR_P} = ν_P` for `R/P` regular); the regularity of `R_P` is proved directly from that of
`R/P` (`isRegularLocalRing_localization_of_isRegularLocalRing_quotient`), and permissibility is read off from the criterion
(ii)* of `lem:III.8-equivalents`. -/
@[blueprint "cor:III.thm5-3a"
  (statement := /-- Let $R$ be a regular local ring, and $M$ the maximal ideal of $R$. Let $Q$
    be a prime ideal in $R$, and $J$ an ideal in $R$ such that $Q\supseteq J$. Suppose we have a
    system of elements $(g_1,\dots,g_m)$ of $J$ such that
    (i) the initial forms of the $g_j$ $(1\le j\le m)$ in $\operatorname{gr}_M(R)$ generate the
    ideal $\operatorname{gr}_M(J,R)$ (\cref{def:II.2-graded-ideal}), and
    (ii) $\nu_M(g_j)=\nu_{QR_Q}(g_j)$ for all $j$ $(1\le j\le m)$.
    Then: (a) if $P$ is any prime ideal in $R$ such that $P\supseteq Q$ and $R/P$ is regular,
    then $P$ is a permissible center for $J$ (\cref{def:III.8}). (Corollary 3 (a), p.~242.) -/)
  (proof := /-- For the assertion (a), it suffices to prove that $\nu_M(g_j)=\nu_P(g_j)$ for all
    $j$. This follows Theorem~1, \S3 (\cref{thm:III.1}), by the fact that the regularity of
    $R/P$ implies $\nu_P(g_j)=\nu_{PR_P}(g_j)$. \qed

    \textbf{Gap in the paper filled.} In Lean:
    $\nu_M(g_j)=\nu_{QR_Q}(g_j)\le\nu_{PR_P}(g_j)=\nu_P(g_j)\le\nu_M(g_j)$, by (ii), Theorem~1
    applied to the regular local ring $R_P$ and its prime $QR_P$ (as $Q\subseteq P$), the
    regularity of $R/P$, and $P\subseteq M$; the regularity of $R_P$ is proved directly from that
    of $R/P$. Together with (i), $\nu_M(g_j)=\nu_P(g_j)$ is the condition (ii)$^*$ of
    \cref{lem:III.8-equivalents}, which with the regularity of $R/P$ says that $P$ is a
    permissible center for $J$. -/)
  (latexEnv := "corollary")]
theorem isPermissibleCenter_of_isLocallyAdaptedSystem [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (Q J : Ideal R) [Q.IsPrime] (hJQ : J ≤ Q)
    {m : ℕ} (g : Fin m → R) (hg : IsLocallyAdaptedSystem R Q J g) (P : Ideal R) [P.IsPrime]
    (hQP : Q ≤ P) [IsRegularLocalRing (R ⧸ P)] :
    IsPermissibleCenter R J P := by
  have hJP : J ≤ P := hJQ.trans hQP
  refine Or.inr ⟨inferInstance, hJP, inferInstance, ?_⟩
  -- condition (ii)* of Definition 8 for the system `(g_j)`: `ν_M(g_j) = ν_P(g_j)`
  have h12 : IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)) ↔
      HasInitialFormSystem J P (maximalIdeal R) := (isPermissibleCenter_tfae R J P hJP).out 1 2
  refine h12.mpr ⟨m, g, hg.1, fun j => ?_, hg.2.1.symm⟩
  refine le_antisymm ?_ (Ideal.ordElem_mono (le_maximalIdeal_of_isPrime P) _)
  rw [hg.2.2 j]
  exact ordElem_localization_le_ordElem_of_le Q P hQP inferInstance (g j)

/-- Corollary 3 (b), p. 242: "Let `P` be a permissible center for `J` such that `P ⊇ Q` and
`P ≠ Q`, `R₁` a monoidal transform of `R` with center `P` which is residually separable
algebraic over `R`, and `J₁` the strict transform of `J` in `R₁`. Suppose we have a prime ideal
`Q₁` in `R₁` such that `Q₁ ∩ R = Q`. Let `x` be an element of `P` such that `PR₁ = (x)R₁`, and
`h_j = x^{-ν_j} g_j` with `ν_j = ν_P(g_j)` for each `j` (`1 ≤ j ≤ m`). Then the system
`(h₁, …, h_m)` of elements in `J₁` has the properties (i) and (ii) with respect to `R₁`,
`M₁` (= the maximal ideal of `R₁`), `Q₁`, and `J₁`. Moreover, we have `ν*(J) = ν*(J₁)`."

Formalization notes (encoding): conditions (i), (ii) for `R, M, Q, J` and for `R₁, M₁, Q₁, J₁`
are `HasCor3Properties R Q J g` and `HasCor3Properties t.ring Q₁ J₁ h`; `h_j = x^{-ν_j} g_j` is
encoded by `(t.toRing x)^{ν_j} * h j = t.toRing (g j)`; `[IsLocalHom t.toRing]` is a global instance and
`[IsRegularLocalRing t.ring]` is a hypothesis of this statement only (see the module docstring).

The proof follows the printed one (p. 243): "To prove (b), we have only to show that `ν_M(g_j) =
ν_{M₁}(h_j)` for all `j`.  In fact, if this is done, the property (i) of `(h₁, …, h_m)` follows from
Theorem 5, for the reason that a suitably re-ordered subsystem of `(g₁, …, g_m)` is a standard base of `J`
by the property (i) of this system.  Moreover, (ii) of `(h₁, …, h_m)` also follows, because `x` is a
unit in `(R₁)_{Q₁}` and `R_Q = (R₁)_{Q₁}`, so that `ν_{QR_Q}(g_j) = ν_{Q₁(R₁)_{Q₁}}(h_j)` for all `j`.
Now, the equality `ν_M(g_j) = ν_{M₁}(h_j)` for each `j` is easily obtained by means of Lemma 8 and
Theorem 1, §3."  The last two sentences are `ordElem_eq_and_ordElem_localization_eq_of_strictTransform`:
`ν_M(g_j) = ν_{QR_Q}(g_j)` by (ii), `= ν_{Q₁(R₁)_{Q₁}}(h_j)` by `R_Q = (R₁)_{Q₁}` with `x` a unit
(`ordElem_localization_eq_of_strictTransform`), `≤ ν_{M₁}(h_j)` by Theorem 1 of §3 in `R₁`, `≤ ν_M(g_j)`
by Lemma 8 (`ordElem_maximalIdeal_le_of_weakTransform`).  The chain thus closes, giving both
`ν_M(g_j) = ν_{M₁}(h_j)` and `ν_{Q₁(R₁)_{Q₁}}(h_j) = ν_{M₁}(h_j)`.  The hypothesis `hxP : x ∈ P` is only
passed to Theorem 5, where it is unused.

Deviation from the paper (gap filled): `ν_M(g_j) = ν_P(g_j)` (hypothesis (ii) of Theorem 5) is
re-derived as in (a); `h_j ∈ J₁`; property (i) for all the `h_j` from Theorem 5 applied to the
extracted standard base; `ν*(J) = ν*(J₁)` is the second conclusion of Theorem 5. -/
@[blueprint "cor:III.thm5-3b"
  (statement := /-- Hypotheses as in \cref{cor:III.thm5-3a}. (b) Let $P$ be a permissible center
    for $J$ such that $P\supseteq Q$ and $P\ne Q$, $R_1$ a monoidal transform of $R$ with center
    $P$ which is residually separable algebraic over $R$, and $J_1$ the strict transform of $J$
    in $R_1$. Suppose we have a prime ideal $Q_1$ in $R_1$ such that $Q_1\cap R=Q$. Let $x$ be
    an element of $P$ such that $PR_1=(x)R_1$, and $h_j=x^{-\nu_j}g_j$ with $\nu_j=\nu_P(g_j)$
    for each $j$ $(1\le j\le m)$. Then the system $(h_1,\dots,h_m)$ of elements in $J_1$ has the
    properties (i) and (ii) with respect to $R_1$, $M_1$ ($=$ the maximal ideal of $R_1$),
    $Q_1$, and $J_1$. Moreover, we have $\nu^*(J)=\nu^*(J_1)$. (Corollary 3 (b), p.~242.) -/)
  (proof := /-- To prove (b), we have only to show that $\nu_M(g_j)=\nu_{M_1}(h_j)$ for all $j$.
    In fact, if this is done, the property (i) of $(h_1,\dots,h_m)$ follows from Theorem~5
    (\cref{thm:III.5}), for the reason that a suitably reordered subsystem of $(g_1,\dots,g_m)$
    is a standard base of $J$ by the property (i) of this system. Moreover, (ii) of
    $(h_1,\dots,h_m)$ also follows, because $x$ is a unit in $(R_1)_{Q_1}$ and
    $R_Q=(R_1)_{Q_1}$, so that $\nu_{QR_Q}(g_j)=\nu_{Q_1(R_1)_{Q_1}}(h_j)$ for all $j$. Now, the
    equality $\nu_M(g_j)=\nu_{M_1}(h_j)$ for each $j$ is easily obtained by means of Lemma~8
    (\cref{lem:III.8}) and Theorem~1, \S3 (\cref{thm:III.1}). \qed

    \textbf{Lean.} Lean follows this proof: $\nu_M(g_j)=\nu_{QR_Q}(g_j)$ by (ii),
    $\nu_{QR_Q}(g_j)=\nu_{Q_1(R_1)_{Q_1}}(h_j)$ because $x$ is a unit in $(R_1)_{Q_1}$ and
    $R_Q=(R_1)_{Q_1}$ (proved, see \cref{cor:III.thm5-1}), then
    $\nu_{Q_1(R_1)_{Q_1}}(h_j)\le\nu_{M_1}(h_j)$ by Theorem~1, \S3, in $R_1$, and
    $\nu_{M_1}(h_j)\le\nu_M(g_j)$ by Lemma~8; so the chain closes.

    \textbf{Gap in the paper filled.} Theorem~5 also needs $\nu_P(g_j)=\nu_M(g_j)$, which Lean
    derives as in (a); Lean also checks $h_j\in J_1$, derives (i) for all the $h_j$ from Theorem~5
    applied to the extracted standard base, and obtains $\nu^*(J)=\nu^*(J_1)$ as the second
    conclusion of Theorem~5. -/)
  (latexEnv := "corollary")]
theorem isLocallyAdaptedSystem_strictTransform [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] [IsDomain R] (Q J : Ideal R) [Q.IsPrime] (hJQ : J ≤ Q)
    {m : ℕ} (g : Fin m → R) (hg : IsLocallyAdaptedSystem R Q J g) (P : Ideal R) [P.IsPrime]
    (hPperm : IsPermissibleCenter R J P) (hQP : Q ≤ P) (hPneQ : P ≠ Q)
    (t : MonoidalTransform R P) [IsRegularLocalRing t.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := t.ring) t.toRing)
    (Q₁ : Ideal t.ring) [Q₁.IsPrime] (hQ₁ : Q₁.comap t.toRing = Q) (x : R) (hxP : x ∈ P)
    (hx : P.map t.toRing = Ideal.span {t.toRing x}) (ν : Fin m → ℕ)
    (hν : ∀ j, (ν j : ℕ∞) = Ideal.ordElem P (g j)) (h : Fin m → t.ring)
    (hh : ∀ j, t.toRing x ^ ν j * h j = t.toRing (g j)) :
    IsLocallyAdaptedSystem t.ring Q₁ (strictTransformIdeal t J) h ∧
      nuStar R J = nuStar t.ring (strictTransformIdeal t J) := by
  classical
  obtain ⟨-, -, hPreg, -⟩ := hPperm.resolve_left (Ideal.IsPrime.ne_top inferInstance)
  have _ : IsRegularLocalRing (R ⧸ P) := hPreg
  -- `ν_M(g_j) = ν_P(g_j)` (as in (a))
  have hMP : ∀ j, Ideal.ordElem (maximalIdeal R) (g j) = Ideal.ordElem P (g j) := fun j =>
    le_antisymm (by rw [hg.2.2 j]; exact ordElem_localization_le_ordElem_of_le Q P hQP hPreg (g j))
      (Ideal.ordElem_mono (le_maximalIdeal_of_isPrime P) _)
  have hmaxA₁ : Q₁.map (algebraMap t.ring (Localization.AtPrime Q₁)) =
      maximalIdeal (Localization.AtPrime Q₁) := Localization.AtPrime.map_eq_maximalIdeal
  -- `ν_{M₁}(h_j) = ν_M(g_j) = ν_{Q₁R₁_{Q₁}}(h_j)` (Lemma 8 and Theorem 1 of §3)
  have hchain := fun j => ordElem_eq_and_ordElem_localization_eq_of_strictTransform Q P hQP hPneQ t hsep Q₁ hQ₁ x hx
    (g j) (ν j) (hν j) (h j) (hh j) (hMP j) (hg.2.2 j)
  -- (5) Theorem 5 for a standard base extracted from `(g_j)`
  obtain ⟨k, σ, -, hσ⟩ := exists_isStandardBase_comp R J g hg.1 hg.2.1.symm
  have h5 := isStandardBase_strictTransform J P (hJQ.trans hQP) t hsep x hxP hx (g ∘ σ)
    (ν ∘ σ) (h ∘ σ) (fun j => (hν _).trans (hMP _).symm) (fun j => hh _) hσ
    (fun j => (hMP _).symm) (fun j => (hchain _).1.trans ((hMP _).trans (hν _).symm))
  refine ⟨⟨fun j => Ideal.subset_span ⟨t.toRing x, hx.symm, g j, hg.1 j, ν j, (hν j).le, hh j⟩,
    le_antisymm ?_ ?_, fun j => ?_⟩, h5.2.symm⟩
  · rw [h5.1.2.2.2.1]
    refine Ideal.span_mono ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨σ j, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨h j, Ideal.subset_span ⟨t.toRing x, hx.symm, g j, hg.1 j, ν j,
      (hν j).le, hh j⟩, rfl⟩
  · rw [hmaxA₁]
    exact (hchain j).2.symm

end Corollary3

end Hironaka

