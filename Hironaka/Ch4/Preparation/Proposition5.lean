/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch4.Preparation.Proposition5Lemmas

/-!
# Ch. IV §2 (pp. 288–292): Proposition 5

The setting `PrepSetting` of the proof of Proposition 5, the conditions (1), (2), (3), (3)*, (3)**, (4),
(5) and the reductions establishing them one after the other, step 7 (p. 291), and Proposition 5, the
preparation theorem on `(ℜ^{N,n}_I, U)`.

This is part 3 of 3 of `Hironaka.Ch4.Preparation`, which imports all parts; its description holds the
notation and the formalization notes for the whole section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u v

noncomputable section

section PrepProposition

open Classical

variable {X : Scheme.{u}}

/-- An irreducible component of `D` contained in another irreducible component of `D` is equal to it
(maximality of the underlying irreducible closed sets). -/
theorem Subscheme.pts_eq_of_mem_irreducibleComponents_of_subset {D G F' : Subscheme X}
    (hG : G ∈ D.irreducibleComponents) (hF' : F' ∈ D.irreducibleComponents)
    (h : F'.pts ⊆ G.pts) : G.pts = F'.pts := by
  obtain ⟨Z, hZ, rfl⟩ := hG
  obtain ⟨Z', hZ', rfl⟩ := hF'
  have e1 : (Subscheme.ofClosed Z).pts = (Z : Set X) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  have e2 : (Subscheme.ofClosed Z').pts = (Z' : Set X) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z'
  rw [e1, e2]
  rw [e1, e2] at h
  have hle : Z' ≤ Z := h
  have := hZ'.2 hZ.1 hle
  exact Set.Subset.antisymm this h

/-- At a point `x` of an irreducible component `C` of `D` where the stalk `D_x` is prime, `C_x = D_x`
(`C_x` is a minimal prime over the prime `D_x`; `Subscheme.stalkIdeal_mem_minimalPrimes`). -/
theorem Subscheme.stalkIdeal_eq_of_mem_irreducibleComponents_of_isPrime {D C : Subscheme X}
    (hC : C ∈ D.irreducibleComponents) {x : X} (hx : x ∈ C.pts)
    (hP : (D.stalkIdeal x).IsPrime) : C.stalkIdeal x = D.stalkIdeal x := by
  have hq := Subscheme.stalkIdeal_mem_minimalPrimes hC hx
  exact le_antisymm (hq.2 ⟨hP, le_rfl⟩ hq.1.2) hq.1.2

/-- If `E = ⋃ E_i` has only normal crossings with `W` at `y` and `E_{i₀}` passes through `y`, then `E`
has only normal crossings with `W ∩ E_{i₀}` at `y`: the same regular system of parameters works, the
equation of `E_{i₀}` (a member of it) being adjoined to the generators of `W_y` (companion of
`Subscheme.isSimpleAt_inter_of_hasOnlyNormalCrossingsWithAt`).

Deviation from the paper (gap filled): tacit in p. 291, "(2) and (3) imply immediately that the
monoidal transformation `f : X' → X` with center `G` is permissible for the resolution datum
`(⋃_{i≥2} E_i; V_1, …, V_β; W)`" (the normal crossings of the tail with the center `G = W ∩ E_j`). -/
theorem Subscheme.hasOnlyNormalCrossingsWithAt_inter {Y : Scheme.{u}} (hY : Y.IsNonsingular)
    {ι : Type*} [Fintype ι] (E : ι → Subscheme Y)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) {W : Subscheme Y} {y : Y}
    (hnc : (Subscheme.unionFam E).HasOnlyNormalCrossingsWithAt W y) (i₀ : ι)
    (hyE : y ∈ (E i₀).pts) :
    (Subscheme.unionFam E).HasOnlyNormalCrossingsWithAt (W.inter (E i₀)) y := by
  classical
  have : IsRegularLocalRing (Y.presheaf.stalk y) := hY y
  have hred : (Subscheme.unionFam E).IsReduced := Subscheme.isReduced_unionFam E hE
  obtain ⟨Z, hZ, ⟨T, hTZ, hWT⟩, hEZ⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    E hE (fun i => iInf_le _ i) hnc
  obtain ⟨a, haZ, ha⟩ : ∃ a ∈ Z, (E i₀).stalkIdeal y = Ideal.span {a} := by
    rcases hEZ i₀ with h | h
    · exact absurd h ((Subscheme.mem_pts_iff_stalkIdeal_ne_top).mp hyE)
    · exact h
  have hst : (W.inter (E i₀)).stalkIdeal y = Ideal.span ((insert a T : Finset _) : Set _) := by
    show (W ⊔ E i₀).stalkIdeal y = _
    rw [Subscheme.stalkIdeal_sup_eq, ha, hWT, Finset.coe_insert, Ideal.span_insert, sup_comm]
  refine (Subscheme.hasOnlyNormalCrossingsWithAt_iff hred (hY y)).mpr ⟨Z, hZ, ?_,
    ⟨insert a T, Finset.insert_subset haZ hTZ, hst⟩⟩
  obtain ⟨K₁, hK₁, h⟩ := DatumTransform.iInf_eq_span_prod (fun i => (E i).stalkIdeal y)
    (ExtendsToRSOP.of_isRegularSystemOfParameters hZ) hEZ
  refine ⟨K₁, hK₁, ?_⟩
  rw [Subscheme.unionFam, DatumTransform.stalkIdeal_iInf_fintype]
  exact h

/-- A subscheme `W` which is simple at `x` has only one irreducible component through `x` (`W_x` is
prime, and is the stalk of every component through `x`).

Deviation from the paper (gap filled): tacit in the localization to an open set on which `W` is
irreducible (`exists_localization_of_mem_badComponents`), needed to apply Lemma 5 (p. 287, "`W` a
non-singular irreducible subscheme of `X`") on p. 291. -/
theorem Subscheme.eq_of_mem_irreducibleComponents_of_isSimpleAt {W W₁ W₂ : Subscheme X}
    (h₁ : W₁ ∈ W.irreducibleComponents) (h₂ : W₂ ∈ W.irreducibleComponents) {x : X}
    (hx₁ : x ∈ W₁.pts) (hx₂ : x ∈ W₂.pts) (hW : W.IsSimpleAt x) : W₁ = W₂ := by
  have hprime : (W.stalkIdeal x).IsPrime := by
    have := hW.2
    have := isDomain_of_isRegularLocalRing (X.presheaf.stalk x ⧸ W.stalkIdeal x)
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  exact Subscheme.eq_of_stalkIdeal_eq_of_mem_irreducibleComponents h₁ h₂ hx₁ hx₂
    ((Subscheme.stalkIdeal_eq_of_mem_irreducibleComponents_of_isPrime h₁ hx₁ hprime).trans
      (Subscheme.stalkIdeal_eq_of_mem_irreducibleComponents_of_isPrime h₂ hx₂ hprime).symm)

/-- The monoidal transformation with center `F^{(i)}` chosen at each stage of the iteration of Lemma 5
(p. 287: "we take the monoidal transformation `f' : X'' → X'` with center `F'`"; existence by
`MonoidalTransformation.exists_isProper`). -/
noncomputable def IterationStage.step [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (s : IterationStage.{u}) : MonoidalTransformation s.X s.F :=
  Classical.choose (MonoidalTransformation.exists_isProper s.X s.F)

/-- The `n`-th stage of the iteration of Lemma 5 started at `s`
(p. 287: `F ↦ F' ↦ F'' ↦ ⋯`). -/
noncomputable def IterationStage.run [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] : ℕ → IterationStage.{u} → IterationStage.{u}
  | 0, s => s
  | n + 1, s => IterationStage.run n (s.next s.step)

/-- The succession of the first `n` monoidal transformations of the iteration of Lemma 5 started at `s`. -/
noncomputable def IterationStage.runSucc [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] :
    ∀ (n : ℕ) (s : IterationStage.{u}), MonoidalSuccession s.X (IterationStage.run n s).X
  | 0, s => MonoidalSuccession.nil s.X
  | n + 1, s => MonoidalSuccession.cons s.F s.step (IterationStage.runSucc n (s.next s.step))

/-- `run (n + 1) s = (run n s).next (run n s).step`. -/
theorem IterationStage.run_succ [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] : ∀ (n : ℕ) (s : IterationStage.{u}),
    IterationStage.run (n + 1) s = (IterationStage.run n s).next (IterationStage.run n s).step
  | 0, _s => rfl
  | n + 1, s => IterationStage.run_succ n (s.next s.step)

/-- The stages `run n s` form an iteration in the sense of Lemma 5 (`IterationStage.IsIteration`). -/
theorem IterationStage.isIteration_run [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (s : IterationStage.{u}) :
    IterationStage.IsIteration (fun n => IterationStage.run n s) :=
  fun i => ⟨(IterationStage.run i s).step, IterationStage.run_succ i s⟩

/-- The succession of the first `n` steps of the iteration has length `n`. -/
theorem IterationStage.length_runSucc [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] : ∀ (n : ℕ) (s : IterationStage.{u}),
    (IterationStage.runSucc n s).length = n
  | 0, s => rfl
  | n + 1, s => by
      show (IterationStage.runSucc n (s.next s.step)).length + 1 = n + 1
      rw [IterationStage.length_runSucc n]

/-- The `W^{(n)}` and `E^{(n)}` of the iteration are the strict transforms of `W` and `E` by the succession
of its first `n` steps. -/
theorem IterationStage.strictTransform_runSucc [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] : ∀ (n : ℕ) (s : IterationStage.{u}),
    (IterationStage.runSucc n s).strictTransform s.W = (IterationStage.run n s).W ∧
    (IterationStage.runSucc n s).strictTransform s.E = (IterationStage.run n s).E
  | 0, _s => ⟨rfl, rfl⟩
  | n + 1, s => IterationStage.strictTransform_runSucc n (s.next s.step)

/-- The centers `F, F', F'', …` of the iteration are reduced and lie over `C` as soon as `F` does
(`F^{(i+1)} = f̃⁻¹(F^{(i)}) ⊆ f⁻¹(F^{(i)})`): the hypothesis "centers closed in `X`" of
`MonoidalSuccession.exists_extension` for the succession of the iteration of Lemma 5. -/
theorem IterationStage.centersClosedIn_runSucc [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] : ∀ (n : ℕ) (s : IterationStage.{u}) {Y : Scheme.{u}}
    (q : s.X ⟶ Y) (C : Set Y), s.F.IsReduced → q.base '' s.F.pts ⊆ C →
    (IterationStage.runSucc n s).CentersClosedIn q C
  | 0, s, Y, q, C, _, _ => trivial
  | n + 1, s, Y, q, C, hred, himg => by
      refine ⟨hred, himg, IterationStage.centersClosedIn_runSucc n (s.next s.step) (s.step.f ≫ q) C
        (Subscheme.ofClosed_isReduced _) ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      have hz' : z ∈ (Subscheme.inducedPreimage s.step s.W s.F).pts := hz
      rw [Subscheme.pts_inducedPreimage] at hz'
      exact himg ⟨s.step.f.base z, hz'.2, rfl⟩

namespace PrepSetting

variable (P : PrepSetting X)

/-- Condition (1) (p. 289): "`F = F_1 ∪ ⋯ ∪ F_δ` is a disjoint union of non-singular schemes
`F_1, …, F_δ` and `⋃_i E_i` has only normal crossings with `F`". -/
def Cond₁ : Prop :=
  (∀ F_i ∈ ((P.ℜ.prepWStar P.E₁).inter P.E₁).irreducibleComponents,
      (F_i.pts ∩ P.U).Nonempty → F_i.IsNonsingular) ∧
  (∀ F_i ∈ ((P.ℜ.prepWStar P.E₁).inter P.E₁).irreducibleComponents,
    ∀ F_j ∈ ((P.ℜ.prepWStar P.E₁).inter P.E₁).irreducibleComponents,
      (F_i.pts ∩ P.U).Nonempty → (F_j.pts ∩ P.U).Nonempty → F_i ≠ F_j →
        Disjoint F_i.pts F_j.pts) ∧
  P.ℜ.E.HasOnlyNormalCrossingsWith (P.ℜ.prepF P.E₁ P.U)

/-- Condition (2) (p. 290): "there exists an open subset `Ū` of `W` which contains `U` and `F`,
and such that the resolution datum `(⋃_{i≥2} E_i; V_1, …, V_β; W)` is resolved at every point of
`Ū`". -/
def Cond₂ (Ubar : Set X) : Prop :=
  (∃ V : Set X, IsOpen V ∧ Ubar = V ∩ P.ℜ.W.pts) ∧ P.U ⊆ Ubar ∧
    (P.ℜ.prepF P.E₁ P.U).pts ⊆ Ubar ∧
    ∀ x ∈ Ubar, ({ P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ } : DatumI.Raw X).ResolvedAt x

/-- Condition (3) (p. 291): "if `G` is any reduced irreducible component of `W_* ∩ E_1` which is
not in `F` and has non-empty intersection with `F`, then `G` is contained in `Ū` and of the form
`W ∩ E_j` with `j ≥ 2`, hence non-singular". -/
def Cond₃ (Ubar : Set X) : Prop :=
  ∀ G ∈ ((P.ℜ.prepWStar P.E₁).inter P.E₁).irreducibleComponents,
    ¬ G.pts ⊆ (P.ℜ.prepF P.E₁ P.U).pts → (G.pts ∩ (P.ℜ.prepF P.E₁ P.U).pts).Nonempty →
      G.pts ⊆ Ubar ∧ ∃ j : Fin P.α, j ≠ ⟨0, P.hα⟩ ∧
        G.pts = (P.ℜ.W.inter (P.E j)).pts ∧ G.IsNonsingular

/-- Condition (3)* (p. 291): "every reduced irreducible component of `W_* ∩ E_1` is either
contained in `F` (hence it is one of the `F_j`) or has empty intersection with `F`". -/
def Cond₃Star : Prop :=
  ∀ G ∈ ((P.ℜ.prepWStar P.E₁).inter P.E₁).irreducibleComponents,
    G.pts ⊆ (P.ℜ.prepF P.E₁ P.U).pts ∨ G.pts ∩ (P.ℜ.prepF P.E₁ P.U).pts = ∅

/-- Condition (3)** (p. 291): "`Ū ∩ W_* ∩ E_1 = F`, where `Ū ∩ W_*` is an open dense subset of
`W_*`". -/
def Cond₃SS (Ubar : Set X) : Prop :=
  Ubar ∩ (P.ℜ.prepWStar P.E₁).pts ∩ P.E₁.pts = (P.ℜ.prepF P.E₁ P.U).pts ∧
    (P.ℜ.prepWStar P.E₁).pts ⊆ closure (Ubar ∩ (P.ℜ.prepWStar P.E₁).pts)

/-- Condition (4) (p. 291): "`ℜ = (⋃_{i=1}^α E_i; V_1, …, V_β; W)` is resolved at every point of
`Ū ∩ W_*`". -/
def Cond₄ (Ubar : Set X) : Prop :=
  ∀ x ∈ Ubar ∩ (P.ℜ.prepWStar P.E₁).pts, P.ℜ.ResolvedAt x

/-- Condition (5)* (p. 291): "`E_1 ∩ W_* = F ⊆ Ū`" (condition (5) says that `E_1 − F` and
`W_* − F` have empty intersection). -/
def Cond₅ (Ubar : Set X) : Prop :=
  P.E₁.pts ∩ (P.ℜ.prepWStar P.E₁).pts = (P.ℜ.prepF P.E₁ P.U).pts ∧
    (P.ℜ.prepF P.E₁ P.U).pts ⊆ Ubar

/-- "We may assume (1) and (2)". -/
def Stage₁₂ : Prop := P.Cond₁ ∧ ∃ Ubar, P.Cond₂ Ubar

/-- "… and (3)". -/
def Stage₃ : Prop := P.Cond₁ ∧ ∃ Ubar, P.Cond₂ Ubar ∧ P.Cond₃ Ubar

/-- "… and (3)*". -/
def Stage₃Star : Prop := P.Cond₁ ∧ P.Cond₃Star ∧ ∃ Ubar, P.Cond₂ Ubar ∧ P.Cond₃ Ubar

/-- "… and (3)**". -/
def Stage₃SS : Prop := P.Cond₁ ∧ ∃ Ubar, P.Cond₂ Ubar ∧ P.Cond₃SS Ubar

/-- "… and (4)". -/
def Stage₄ : Prop := P.Cond₁ ∧ ∃ Ubar, P.Cond₂ Ubar ∧ P.Cond₃SS Ubar ∧ P.Cond₄ Ubar

/-- "… and (5)*". -/
def Stage₅ : Prop := P.Cond₁ ∧ ∃ Ubar, P.Cond₂ Ubar ∧ P.Cond₄ Ubar ∧ P.Cond₅ Ubar

/-- After a permissible succession for `(ℜ, U)`, the transform of `P` (with ambient scheme of
dimension `N` and `dim W ≤ n`) satisfies `Stage`. -/
def StepTo (N n : ℕ) (Stage : ∀ Y : Scheme.{u}, PrepSetting Y → Prop) : Prop :=
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y) (Q : PrepSetting Y),
    s.IsPermissibleIOpen P.ℜ P.U ∧ P.IsTransform s Q ∧ IsAmbient Y N ∧
      Q.ℜ.n ≤ (n : WithBot ℕ∞) ∧ Stage Y Q

variable {P}

/-- "Thus we may assume, without any loss of generality, …": the goal for every transform
satisfying `Stage` gives the goal for `P`. -/
theorem Goal.of_stepTo {N n : ℕ} {Stage : ∀ Y : Scheme.{u}, PrepSetting Y → Prop}
    (h : P.StepTo N n Stage)
    (hQ : ∀ (Y : Scheme.{u}) (Q : PrepSetting Y), IsAmbient Y N → Q.ℜ.n ≤ (n : WithBot ℕ∞) →
      Stage Y Q → Q.Goal) : P.Goal := by
  obtain ⟨Y, s, Q, hs, hT, hY, hn, hSt⟩ := h
  exact Goal.of_isTransform hs hT (hQ Y Q hY hn hSt)

variable (P)

/-- `dim F < dim W` (p. 289: "`n̄ < n`", used tacitly): each irreducible subset of `F ⊆ W_* ∩ E_1`
lies in a component `C` of `W` not contained in `E_1`, and the generic point of `C` is a point of
`W` outside `F` of which all points of `C` are specializations.

Deviation from the paper (gap filled): the paper writes "Since `n̄ < n`" without proof. -/
theorem dim_prepF_lt [IsAlgebraicScheme X] {n : ℕ} (hn : P.ℜ.n = (n : WithBot ℕ∞)) :
    (P.ℜ.prepF P.E₁ P.U).dim < P.ℜ.n := by
  classical
  have : TopologicalSpace.NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  set F := P.ℜ.prepF P.E₁ P.U with hFdef
  have hFsub : ∀ y ∈ F.pts, y ∈ (P.ℜ.prepWStar P.E₁).pts ∧ y ∈ P.E₁.pts := fun y hy =>
    Subscheme.mem_pts_inter_iff.mp (P.ℜ.pts_prepF_subset P.E₁ P.U hy)
  have hFW : F.pts ⊆ P.ℜ.W.pts := fun y hy => P.ℜ.pts_prepWStar_subset P.E₁ (hFsub y hy).1
  have hW : P.ℜ.W.dim = (n : WithBot ℕ∞) := hn
  rw [hn, Subscheme.dim_eq_topologicalKrullDim]
  rcases F.pts.eq_empty_or_nonempty with hempty | hne
  · rw [hempty]
    have : IsEmpty (IrreducibleCloseds (↥(∅ : Set X))) :=
      ⟨fun a => by obtain ⟨x, -⟩ := a.isIrreducible.nonempty; exact x.2⟩
    show Order.krullDim (IrreducibleCloseds (↥(∅ : Set X))) < n
    rw [Order.krullDim_eq_bot]
    exact WithBot.bot_lt_coe _
  · refine topologicalKrullDim_lt_of_forall_exists F.support.isClosed hFW hne ?_ n ?_
    · intro A hA hAF
      have hAW : A ⊆ (P.ℜ.prepWStar P.E₁).pts := fun y hy => (hFsub y (hAF hy)).1
      rw [DatumI.Raw.pts_prepWStar] at hAW
      set S := {Z : Closeds X | ∃ W₁ ∈ P.ℜ.W.irreducibleComponents, ¬ W₁.IsContainedIn P.E₁ ∧
        Z = W₁.support} with hS
      have hfin : S.Finite := by
        refine (finite_setOf_maximal_isIrreducible_subset (X := X) P.ℜ.W.support.isClosed).subset ?_
        rintro Z ⟨W₁, ⟨Zw, hZw, rfl⟩, -, rfl⟩
        have : (Subscheme.ofClosed Zw).support = Zw :=
          SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Zw)
        rw [this]
        exact hZw
      have hcl : IsClosed (⋃₀ ((↑) '' S : Set (Set X))) :=
        (hfin.image _).isClosed_sUnion (by rintro _ ⟨Z, -, rfl⟩; exact Z.isClosed)
      rw [hcl.closure_eq] at hAW
      obtain ⟨B, hB, hAB⟩ := isIrreducible_subset_of_finite_sUnion hA (hfin.image _)
        (by rintro _ ⟨Z, -, rfl⟩; exact Z.isClosed) hAW
      obtain ⟨Z, ⟨W₁, hW₁, hn1, rfl⟩, rfl⟩ := hB
      obtain ⟨Zw, hZw, hW₁eq⟩ := id hW₁
      have hW₁pts : W₁.pts = Zw := by
        rw [hW₁eq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Zw
      obtain ⟨c, hc⟩ : ∃ c, IsGenericPoint c (Zw : Set X) :=
        QuasiSober.sober hZw.1.1 Zw.isClosed
      have hcW : c ∈ P.ℜ.W.pts := hZw.1.2 hc.mem
      have hW₁red : W₁.IsReduced := by rw [hW₁eq]; exact Subscheme.ofClosed_isReduced Zw
      refine ⟨c, hcW, fun hcF => hn1 ?_, fun t ht => hc.specializes ?_⟩
      · refine Subscheme.isContainedIn_of_pts_subset hW₁red fun y hy => ?_
        rw [hW₁pts, ← hc.def] at hy
        exact closure_minimal (Set.singleton_subset_iff.mpr (hFsub c hcF).2)
          P.E₁.support.isClosed hy
      · have := hAB ht
        rwa [show (W₁.support : Set X) = Zw from hW₁pts] at this
    · rw [← Subscheme.dim_eq_topologicalKrullDim]
      exact hW.le

/-- `ℜ̄ = ℜ.extendBy F` is a datum (p. 289: "the resolution datum on `X`
`ℜ̄ = (⋃ E_j; V_1, …, V_β, W; F)`"): `F` is reduced and contained in `W ⊆ V_j`.

Deviation from the paper (gap filled): that `ℜ̄` is a datum is tacit. -/
theorem isDatum_extendBy_prepF : (P.ℜ.extendBy (P.ℜ.prepF P.E₁ P.U)).IsDatum := by
  have hFred : (P.ℜ.prepF P.E₁ P.U).IsReduced := Subscheme.ofClosed_isReduced _
  have hFW : (P.ℜ.prepF P.E₁ P.U).pts ⊆ P.ℜ.W.pts := fun y hy =>
    P.ℜ.pts_prepWStar_subset P.E₁ (Subscheme.mem_pts_inter_iff.mp
      (P.ℜ.pts_prepF_subset P.E₁ P.U hy)).1
  have hFWc : (P.ℜ.prepF P.E₁ P.U).IsContainedIn P.ℜ.W :=
    Subscheme.isContainedIn_of_pts_subset hFred hFW
  refine ⟨P.hℜ.1, P.hℜ.2.1, P.hℜ.2.2.1, hFred, fun j => ?_⟩
  induction j using Fin.lastCases with
  | last => simpa only [DatumI.Raw.extendBy, Fin.snoc_last] using hFWc
  | cast j =>
    simp only [DatumI.Raw.extendBy, Fin.snoc_castSucc]
    exact fun U => (P.hℜ.2.2.2.2 j U).trans (hFWc U)

/-- At a point `x` of `F ∩ U`, `F_x = W_x + E_{1,x}`: the transversality of `E_1` and `W` at the points of
`F` lying in the open restriction `U` (where `ℜ` is resolved).  Used for the normal flatness of
`W_* ∩ E_1` along `F` (p. 290: the datum `ℜ̄` is resolved at the points of `F ∩ U`).

Deviation from the paper (gap filled): tacit in the paper ("is resolved at every point of `F ∩ U`"). -/
theorem stalkIdeal_prepF_eq_sup [IsAlgebraicScheme X] (hX : X.IsNonsingular) {x : X}
    (hxF : x ∈ (P.ℜ.prepF P.E₁ P.U).pts) (hxU : x ∈ P.U) :
    (P.ℜ.prepF P.E₁ P.U).stalkIdeal x = P.ℜ.W.stalkIdeal x ⊔ P.E₁.stalkIdeal x := by
  classical
  have : TopologicalSpace.NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  set F := P.ℜ.prepF P.E₁ P.U with hFdef
  set Wst := P.ℜ.prepWStar P.E₁ with hWstdef
  set W := P.ℜ.W with hWdef
  set i₀ : Fin P.α := ⟨0, P.hα⟩ with hi₀
  have hFsub : ∀ y ∈ F.pts, y ∈ Wst.pts ∧ y ∈ P.E₁.pts := fun y hy =>
    Subscheme.mem_pts_inter_iff.mp (P.ℜ.pts_prepF_subset P.E₁ P.U hy)
  have hFW : F.pts ⊆ W.pts := fun y hy => P.ℜ.pts_prepWStar_subset P.E₁ (hFsub y hy).1
  obtain ⟨hWs, hVf, hnc⟩ := P.hU.2.2 x hxU
  have hFred : F.IsReduced := Subscheme.ofClosed_isReduced _
  have hFWc : F.IsContainedIn W := Subscheme.isContainedIn_of_pts_subset hFred hFW
  have hQreg : IsRegularLocalRing (X.presheaf.stalk x ⧸ W.stalkIdeal x) := hWs.2
  have hQprime : (W.stalkIdeal x).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
  -- the component `C₀` of `W` through `x` not contained in `E₁`
  obtain ⟨C₀, hC₀, hC₀E, hxC₀⟩ :=
    DatumI.Raw.exists_mem_irreducibleComponents_of_mem_pts_prepWStar P.ℜ P.E₁ (hFsub x hxF).1
  have hminQ : ∀ C ∈ W.irreducibleComponents, x ∈ C.pts → C.stalkIdeal x = W.stalkIdeal x := by
    intro C hC hxC
    have hq := Subscheme.stalkIdeal_mem_minimalPrimes hC hxC
    exact le_antisymm (hq.2 ⟨hQprime, le_rfl⟩ hq.1.2) hq.1.2
  have hC₀Q : C₀.stalkIdeal x = W.stalkIdeal x := hminQ C₀ hC₀ hxC₀
  have hC₀Wst : C₀.pts ⊆ Wst.pts := by
    obtain ⟨Z, -, hZeq⟩ := id hC₀
    intro y hy
    rw [DatumI.Raw.pts_prepWStar]
    exact subset_closure ⟨_, ⟨C₀.support, ⟨_, hC₀, hC₀E, rfl⟩, rfl⟩, hy⟩
  have hC₀red : C₀.IsReduced := by
    obtain ⟨Z, -, hZ⟩ := hC₀
    rw [hZ]; exact Subscheme.ofClosed_isReduced Z
  set D := W.inter P.E₁ with hD
  have hDpts : D.pts ⊆ W.pts ∩ P.E₁.pts := fun y hy => Subscheme.mem_pts_inter_iff.mp hy
  have hFD : F.pts ⊆ D.pts := fun y hy => Subscheme.mem_pts_inter_iff.mpr ⟨hFW hy, (hFsub y hy).2⟩
  -- a rsop adapted to `E` and `W`
  have hnc' : (Subscheme.unionFam P.E).HasOnlyNormalCrossingsWithAt W x := P.hEunion ▸ hnc
  obtain ⟨Z, hZ, ⟨T₀, hT₀Z, hWT⟩, hEZ⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    P.E P.hE (fun i => iInf_le _ i) hnc'
  obtain ⟨z, hzZ, hzE⟩ : ∃ z ∈ Z, P.E₁.stalkIdeal x = Ideal.span {z} := by
    rcases hEZ i₀ with h | h
    · exfalso
      have h1 := Subscheme.stalkIdeal_le_maximalIdeal P.E₁ (hFsub x hxF).2
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ h1))
    · exact h
  set J := W.stalkIdeal x ⊔ P.E₁.stalkIdeal x with hJ
  have hDx : D.stalkIdeal x = J := Subscheme.stalkIdeal_sup_eq _ _ x
  have hzQ : z ∉ W.stalkIdeal x := by
    intro hzQ
    have hJQ : J = W.stalkIdeal x := by
      rw [hJ, hzE]
      exact sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hzQ)
    have hQmin : W.stalkIdeal x ∈ J.minimalPrimes := by
      rw [hJQ]
      exact ⟨⟨hQprime, le_rfl⟩, fun q hq _ => hq.2⟩
    obtain ⟨G, hG, hxG, hGq⟩ :=
      Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes D x (hDx ▸ hQmin)
    have hGC : G = C₀ := Subscheme.eq_of_stalkIdeal_eq_of_mem_irreducibleComponents hG hC₀ hxG
      hxC₀ (hGq.trans hC₀Q.symm)
    apply hC₀E
    refine Subscheme.isContainedIn_of_pts_subset hC₀red fun y hy => ?_
    have : y ∈ G.pts := hGC ▸ hy
    obtain ⟨Z', hZmax, hZ'⟩ := hG
    have h2 : y ∈ (Z' : Set X) := by
      rw [hZ'] at this
      rwa [show (Subscheme.ofClosed Z').pts = Z' from
        Scheme.IdealSheafData.coe_support_vanishingIdeal Z'] at this
    exact (hDpts (hZmax.1.2 h2)).2
  have hzT₀ : z ∉ T₀ := fun h => hzQ (hWT ▸ Ideal.subset_span (Finset.mem_coe.mpr h))
  have hK : insert z T₀ ⊆ Z := Finset.insert_subset hzZ hT₀Z
  have hext : ExtendsToRSOP (X.presheaf.stalk x) (insert z T₀) := ⟨Z, hK, hZ⟩
  have hJspan : J = Ideal.span ((insert z T₀ : Finset _) : Set (X.presheaf.stalk x)) := by
    rw [hJ, hzE, hWT, Finset.coe_insert, Set.insert_eq, Ideal.span_union, sup_comm]
  have hJprime : J.IsPrime := by rw [hJspan]; exact hext.isPrime_span
  -- `F_x = J`
  have hFJ : F.stalkIdeal x = J := by
    refine le_antisymm ?_ ?_
    · have hJmin : J ∈ J.minimalPrimes := ⟨⟨hJprime, le_rfl⟩, fun q hq _ => hq.2⟩
      obtain ⟨G, hG, hxG, hGJ⟩ :=
        Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes D x
          (by rw [hDx]; exact hJmin)
      obtain ⟨Z', hZ'max, hGeq⟩ := id hG
      have hZ'pts : G.pts = Z' := by
        rw [hGeq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z'
      have hxZ' : x ∈ (Z' : Set X) := by rwa [hZ'pts] at hxG
      obtain ⟨g, hg⟩ : ∃ g, IsGenericPoint g (Z' : Set X) :=
        QuasiSober.sober hZ'max.1.1 Z'.isClosed
      have hgx : g ⤳ x := hg.specializes hxZ'
      have hgD : g ∈ D.pts := hZ'max.1.2 hg.mem
      have hgW : g ∈ W.pts := (hDpts hgD).1
      obtain ⟨C', hC', hgC'⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_pts W hgW
      have hxC' : x ∈ C'.pts := by
        obtain ⟨Z₁, -, rfl⟩ := hC'
        have h1 : g ∈ (Z₁ : Set X) := by
          rwa [show (Subscheme.ofClosed Z₁).pts = Z₁ from
            Scheme.IdealSheafData.coe_support_vanishingIdeal Z₁] at hgC'
        rw [show (Subscheme.ofClosed Z₁).pts = Z₁ from
            Scheme.IdealSheafData.coe_support_vanishingIdeal Z₁]
        exact closure_minimal (Set.singleton_subset_iff.mpr h1) Z₁.isClosed
          (specializes_iff_mem_closure.mp hgx)
      have hC'eq : C' = C₀ :=
        Subscheme.eq_of_stalkIdeal_eq hC' hC₀ hxC' hxC₀ ((hminQ C' hC' hxC').trans hC₀Q.symm)
      have hgC₀ : g ∈ C₀.pts := hC'eq ▸ hgC'
      have hgWE : g ∈ (Wst.inter P.E₁).pts :=
        Subscheme.mem_pts_inter_iff.mpr ⟨hC₀Wst hgC₀, (hDpts hgD).2⟩
      have hZ'sub : (Z' : Set X) ⊆ (Wst.inter P.E₁).pts := by
        rw [← hg.def]
        exact closure_minimal (Set.singleton_subset_iff.mpr hgWE)
          (Wst.inter P.E₁).support.isClosed
      have hWstD : (Wst.inter P.E₁).pts ⊆ D.pts := fun y hy =>
        Subscheme.mem_pts_inter_iff.mpr ⟨P.ℜ.pts_prepWStar_subset P.E₁
          (Subscheme.mem_pts_inter_iff.mp hy).1, (Subscheme.mem_pts_inter_iff.mp hy).2⟩
      have hGcomp : G ∈ (Wst.inter P.E₁).irreducibleComponents :=
        ⟨Z', ⟨⟨hZ'max.1.1, hZ'sub⟩, fun Y hY hle => hZ'max.2 ⟨hY.1, hY.2.trans hWstD⟩ hle⟩, hGeq⟩
      have hGF : G.pts ⊆ F.pts := P.ℜ.pts_subset_pts_prepF P.E₁ P.U hGcomp ⟨x, hxG, hxU⟩
      have hGred : G.IsReduced := by rw [hGeq]; exact Subscheme.ofClosed_isReduced Z'
      rw [← hGJ]
      exact Subscheme.stalkIdeal_mono (fun U => Subscheme.isContainedIn_of_pts_subset hGred hGF U) x
    · rw [← hDx]
      exact Subscheme.stalkIdeal_mono
        (fun U => Subscheme.isContainedIn_of_pts_subset hFred hFD U) x
  exact hFJ

/-- Resolvedness of `ℜ̄ = (⋃ E_j; V_1, …, V_β, W; F)` at the points of `F ∩ U` (p. 289: "is resolved at
every point of `F ∩ U`.  (See Corollary 1 of Proposition 1, §1, Ch. II.)").

At `x ∈ F ∩ U` the datum `ℜ` is resolved, so `W` is a simple point, `E` has normal crossings with
`W` and `E_{1,x} = (z)` with `z` part of a regular system of parameters adapted to `W_x = (T)`;
`z ∉ W_x` because `x ∈ W_*`.  Then `F_x = W_x + (z)` is generated by part of the system, so `F` is
non-singular at `x` and `E` has normal crossings with `F`; the normal flatness of the `V_j` and of
`W` along `F` at `x` is the pointwise Corollary 1 of Proposition 1
(`DatumI.isNormallyFlatAlongAt'_extendBy`).

Deviation from the paper (gap filled): the paper says only "is resolved at every point of
`F ∩ U`" with a reference to Corollary 1; the simple points of `F`, the normal crossings with `F`,
the identification `F_x = W_x + E_{1,x}` at points of `U`, and the pointwise form of Corollary 1 are tacit. -/
theorem resolvedAt_extendBy_prepF [IsAlgebraicScheme X] (hX : X.IsNonsingular) {x : X}
    (hxF : x ∈ (P.ℜ.prepF P.E₁ P.U).pts) (hxU : x ∈ P.U) :
    (P.ℜ.extendBy (P.ℜ.prepF P.E₁ P.U)).ResolvedAt x := by
  classical
  have : TopologicalSpace.NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  set F := P.ℜ.prepF P.E₁ P.U with hFdef
  set Wst := P.ℜ.prepWStar P.E₁ with hWstdef
  set W := P.ℜ.W with hWdef
  set i₀ : Fin P.α := ⟨0, P.hα⟩ with hi₀
  have hFsub : ∀ y ∈ F.pts, y ∈ Wst.pts ∧ y ∈ P.E₁.pts := fun y hy =>
    Subscheme.mem_pts_inter_iff.mp (P.ℜ.pts_prepF_subset P.E₁ P.U hy)
  have hFW : F.pts ⊆ W.pts := fun y hy => P.ℜ.pts_prepWStar_subset P.E₁ (hFsub y hy).1
  obtain ⟨hWs, hVf, hnc⟩ := P.hU.2.2 x hxU
  have hFred : F.IsReduced := Subscheme.ofClosed_isReduced _
  have hFWc : F.IsContainedIn W := Subscheme.isContainedIn_of_pts_subset hFred hFW
  have hQreg : IsRegularLocalRing (X.presheaf.stalk x ⧸ W.stalkIdeal x) := hWs.2
  have hQprime : (W.stalkIdeal x).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
  -- the component `C₀` of `W` through `x` not contained in `E₁`
  obtain ⟨C₀, hC₀, hC₀E, hxC₀⟩ :=
    DatumI.Raw.exists_mem_irreducibleComponents_of_mem_pts_prepWStar P.ℜ P.E₁ (hFsub x hxF).1
  have hminQ : ∀ C ∈ W.irreducibleComponents, x ∈ C.pts → C.stalkIdeal x = W.stalkIdeal x := by
    intro C hC hxC
    have hq := Subscheme.stalkIdeal_mem_minimalPrimes hC hxC
    exact le_antisymm (hq.2 ⟨hQprime, le_rfl⟩ hq.1.2) hq.1.2
  have hC₀Q : C₀.stalkIdeal x = W.stalkIdeal x := hminQ C₀ hC₀ hxC₀
  have hC₀Wst : C₀.pts ⊆ Wst.pts := by
    obtain ⟨Z, -, hZeq⟩ := id hC₀
    intro y hy
    rw [DatumI.Raw.pts_prepWStar]
    exact subset_closure ⟨_, ⟨C₀.support, ⟨_, hC₀, hC₀E, rfl⟩, rfl⟩, hy⟩
  have hC₀red : C₀.IsReduced := by
    obtain ⟨Z, -, hZ⟩ := hC₀
    rw [hZ]; exact Subscheme.ofClosed_isReduced Z
  set D := W.inter P.E₁ with hD
  have hDpts : D.pts ⊆ W.pts ∩ P.E₁.pts := fun y hy => Subscheme.mem_pts_inter_iff.mp hy
  have hFD : F.pts ⊆ D.pts := fun y hy => Subscheme.mem_pts_inter_iff.mpr ⟨hFW hy, (hFsub y hy).2⟩
  -- a rsop adapted to `E` and `W`
  have hnc' : (Subscheme.unionFam P.E).HasOnlyNormalCrossingsWithAt W x := P.hEunion ▸ hnc
  obtain ⟨Z, hZ, ⟨T₀, hT₀Z, hWT⟩, hEZ⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    P.E P.hE (fun i => iInf_le _ i) hnc'
  obtain ⟨z, hzZ, hzE⟩ : ∃ z ∈ Z, P.E₁.stalkIdeal x = Ideal.span {z} := by
    rcases hEZ i₀ with h | h
    · exfalso
      have h1 := Subscheme.stalkIdeal_le_maximalIdeal P.E₁ (hFsub x hxF).2
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ h1))
    · exact h
  set J := W.stalkIdeal x ⊔ P.E₁.stalkIdeal x with hJ
  have hDx : D.stalkIdeal x = J := Subscheme.stalkIdeal_sup_eq _ _ x
  have hzQ : z ∉ W.stalkIdeal x := by
    intro hzQ
    have hJQ : J = W.stalkIdeal x := by
      rw [hJ, hzE]
      exact sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hzQ)
    have hQmin : W.stalkIdeal x ∈ J.minimalPrimes := by
      rw [hJQ]
      exact ⟨⟨hQprime, le_rfl⟩, fun q hq _ => hq.2⟩
    obtain ⟨G, hG, hxG, hGq⟩ :=
      Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes D x (hDx ▸ hQmin)
    have hGC : G = C₀ := Subscheme.eq_of_stalkIdeal_eq_of_mem_irreducibleComponents hG hC₀ hxG
      hxC₀ (hGq.trans hC₀Q.symm)
    apply hC₀E
    refine Subscheme.isContainedIn_of_pts_subset hC₀red fun y hy => ?_
    have : y ∈ G.pts := hGC ▸ hy
    obtain ⟨Z', hZmax, hZ'⟩ := hG
    have h2 : y ∈ (Z' : Set X) := by
      rw [hZ'] at this
      rwa [show (Subscheme.ofClosed Z').pts = Z' from
        Scheme.IdealSheafData.coe_support_vanishingIdeal Z'] at this
    exact (hDpts (hZmax.1.2 h2)).2
  have hzT₀ : z ∉ T₀ := fun h => hzQ (hWT ▸ Ideal.subset_span (Finset.mem_coe.mpr h))
  have hK : insert z T₀ ⊆ Z := Finset.insert_subset hzZ hT₀Z
  have hext : ExtendsToRSOP (X.presheaf.stalk x) (insert z T₀) := ⟨Z, hK, hZ⟩
  have hJspan : J = Ideal.span ((insert z T₀ : Finset _) : Set (X.presheaf.stalk x)) := by
    rw [hJ, hzE, hWT, Finset.coe_insert, Set.insert_eq, Ideal.span_union, sup_comm]
  have hJprime : J.IsPrime := by rw [hJspan]; exact hext.isPrime_span
  -- `F_x = J`
  have hFJ : F.stalkIdeal x = J := by
    refine le_antisymm ?_ ?_
    · have hJmin : J ∈ J.minimalPrimes := ⟨⟨hJprime, le_rfl⟩, fun q hq _ => hq.2⟩
      obtain ⟨G, hG, hxG, hGJ⟩ :=
        Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes D x
          (by rw [hDx]; exact hJmin)
      obtain ⟨Z', hZ'max, hGeq⟩ := id hG
      have hZ'pts : G.pts = Z' := by
        rw [hGeq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z'
      have hxZ' : x ∈ (Z' : Set X) := by rwa [hZ'pts] at hxG
      obtain ⟨g, hg⟩ : ∃ g, IsGenericPoint g (Z' : Set X) :=
        QuasiSober.sober hZ'max.1.1 Z'.isClosed
      have hgx : g ⤳ x := hg.specializes hxZ'
      have hgD : g ∈ D.pts := hZ'max.1.2 hg.mem
      have hgW : g ∈ W.pts := (hDpts hgD).1
      obtain ⟨C', hC', hgC'⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_pts W hgW
      have hxC' : x ∈ C'.pts := by
        obtain ⟨Z₁, -, rfl⟩ := hC'
        have h1 : g ∈ (Z₁ : Set X) := by
          rwa [show (Subscheme.ofClosed Z₁).pts = Z₁ from
            Scheme.IdealSheafData.coe_support_vanishingIdeal Z₁] at hgC'
        rw [show (Subscheme.ofClosed Z₁).pts = Z₁ from
            Scheme.IdealSheafData.coe_support_vanishingIdeal Z₁]
        exact closure_minimal (Set.singleton_subset_iff.mpr h1) Z₁.isClosed
          (specializes_iff_mem_closure.mp hgx)
      have hC'eq : C' = C₀ :=
        Subscheme.eq_of_stalkIdeal_eq hC' hC₀ hxC' hxC₀ ((hminQ C' hC' hxC').trans hC₀Q.symm)
      have hgC₀ : g ∈ C₀.pts := hC'eq ▸ hgC'
      have hgWE : g ∈ (Wst.inter P.E₁).pts :=
        Subscheme.mem_pts_inter_iff.mpr ⟨hC₀Wst hgC₀, (hDpts hgD).2⟩
      have hZ'sub : (Z' : Set X) ⊆ (Wst.inter P.E₁).pts := by
        rw [← hg.def]
        exact closure_minimal (Set.singleton_subset_iff.mpr hgWE)
          (Wst.inter P.E₁).support.isClosed
      have hWstD : (Wst.inter P.E₁).pts ⊆ D.pts := fun y hy =>
        Subscheme.mem_pts_inter_iff.mpr ⟨P.ℜ.pts_prepWStar_subset P.E₁
          (Subscheme.mem_pts_inter_iff.mp hy).1, (Subscheme.mem_pts_inter_iff.mp hy).2⟩
      have hGcomp : G ∈ (Wst.inter P.E₁).irreducibleComponents :=
        ⟨Z', ⟨⟨hZ'max.1.1, hZ'sub⟩, fun Y hY hle => hZ'max.2 ⟨hY.1, hY.2.trans hWstD⟩ hle⟩, hGeq⟩
      have hGF : G.pts ⊆ F.pts := P.ℜ.pts_subset_pts_prepF P.E₁ P.U hGcomp ⟨x, hxG, hxU⟩
      have hGred : G.IsReduced := by rw [hGeq]; exact Subscheme.ofClosed_isReduced Z'
      rw [← hGJ]
      exact Subscheme.stalkIdeal_mono (fun U => Subscheme.isContainedIn_of_pts_subset hGred hGF U) x
    · rw [← hDx]
      exact Subscheme.stalkIdeal_mono
        (fun U => Subscheme.isContainedIn_of_pts_subset hFred hFD U) x
  have hFsimple : F.IsSimpleAt x := ⟨hxF, by rw [hFJ, hJspan]; exact hext.isRegularLocalRing_quotient⟩
  have hred : (Subscheme.unionFam P.E).IsReduced := P.hEunion ▸ P.hℜ.1
  have hNCF : (Subscheme.unionFam P.E).HasOnlyNormalCrossingsWithAt F x := by
    refine (Subscheme.hasOnlyNormalCrossingsWithAt_iff hred (hX x)).mpr ⟨Z, hZ, ?_,
      ⟨insert z T₀, hK, by rw [hFJ, hJspan]⟩⟩
    obtain ⟨K₁, hK₁, h⟩ := DatumTransform.iInf_eq_span_prod (fun i => (P.E i).stalkIdeal x)
      (ExtendsToRSOP.of_isRegularSystemOfParameters hZ) hEZ
    refine ⟨K₁, hK₁, ?_⟩
    rw [Subscheme.unionFam, DatumTransform.stalkIdeal_iInf_fintype]
    exact h
  refine ⟨hFsimple, DatumI.isNormallyFlatAlongAt'_extendBy P.hℜ hFWc hWs hFsimple hVf, ?_⟩
  show P.ℜ.E.HasOnlyNormalCrossingsWithAt F x
  rw [P.hEunion]
  exact hNCF

/-- `F ∩ U` is open and dense in `F` (p. 289: "We see that `F ∩ U` is an open dense subset of `F`"):
a point of `F` lies on a component `G` of `W_* ∩ E_1` meeting `U = U₀ ∩ W`, and the non-empty open
subset `G ∩ U₀` of the irreducible `G` is dense in `G`.

Deviation from the paper (gap filled): "we see that" is tacit. -/
theorem isOpenRestriction_extendBy_prepF [IsAlgebraicScheme X] (hX : X.IsNonsingular) :
    (P.ℜ.extendBy (P.ℜ.prepF P.E₁ P.U)).IsOpenRestriction
      ((P.ℜ.prepF P.E₁ P.U).pts ∩ P.U) := by
  classical
  have : TopologicalSpace.NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  obtain ⟨⟨U₀, hU₀, hUeq⟩, -, -⟩ := P.hU
  have hFW : (P.ℜ.prepF P.E₁ P.U).pts ⊆ P.ℜ.W.pts := fun y hy =>
    P.ℜ.pts_prepWStar_subset P.E₁ (Subscheme.mem_pts_inter_iff.mp
      (P.ℜ.pts_prepF_subset P.E₁ P.U hy)).1
  refine ⟨⟨U₀, hU₀, ?_⟩, ?_, fun x hx => P.resolvedAt_extendBy_prepF hX hx.1 hx.2⟩
  · have h1 : ∀ y, y ∈ P.U ↔ y ∈ U₀ ∧ y ∈ P.ℜ.W.pts := fun y =>
      Iff.of_eq (congrArg (y ∈ ·) hUeq)
    ext y
    show y ∈ (P.ℜ.prepF P.E₁ P.U).pts ∩ P.U ↔ y ∈ U₀ ∩ (P.ℜ.prepF P.E₁ P.U).pts
    rw [Set.mem_inter_iff, Set.mem_inter_iff, h1]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, hFW h.2⟩⟩
  · intro x hxF
    have hxF' : x ∈ (P.ℜ.prepF P.E₁ P.U).pts := hxF
    rw [DatumI.Raw.pts_prepF] at hxF'
    set S := {Z : Closeds X | ∃ F_i ∈ ((P.ℜ.prepWStar P.E₁).inter P.E₁).irreducibleComponents,
      (F_i.pts ∩ P.U).Nonempty ∧ Z = F_i.support} with hS
    have hfin : S.Finite := by
      refine (finite_setOf_maximal_isIrreducible_subset (X := X)
        ((P.ℜ.prepWStar P.E₁).inter P.E₁).support.isClosed).subset ?_
      rintro Z ⟨F_i, ⟨Zw, hZw, rfl⟩, -, rfl⟩
      have : (Subscheme.ofClosed Zw).support = Zw :=
        SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Zw)
      rw [this]
      exact hZw
    have hcl : IsClosed (⋃₀ ((↑) '' S : Set (Set X))) :=
      (hfin.image _).isClosed_sUnion (by rintro _ ⟨Z, -, rfl⟩; exact Z.isClosed)
    rw [hcl.closure_eq] at hxF'
    obtain ⟨_, ⟨Z, ⟨G, hG, hGU, rfl⟩, rfl⟩, hxG⟩ := hxF'
    have hGirr : _root_.IsIrreducible G.pts := by
      obtain ⟨Z', hZ'max, rfl⟩ := id hG
      rw [show (Subscheme.ofClosed Z').pts = Z' from
        Scheme.IdealSheafData.coe_support_vanishingIdeal Z']
      exact hZ'max.1.1
    obtain ⟨u, huG, huU⟩ := hGU
    have huU' := huU
    rw [hUeq] at huU'
    have hGF : G.pts ⊆ (P.ℜ.prepF P.E₁ P.U).pts := P.ℜ.pts_subset_pts_prepF P.E₁ P.U hG ⟨u, huG, huU⟩
    have hcl := subset_closure_inter_of_isPreirreducible_of_isOpen hGirr.isPreirreducible hU₀
      ⟨u, huG, huU'.1⟩
    refine closure_mono ?_ (hcl hxG)
    rintro v ⟨hvG, hvU⟩
    have : v ∈ P.U := by rw [hUeq]; exact ⟨hvU, hFW (hGF hvG)⟩
    exact ⟨hGF hvG, this⟩

/-- Step 1 (p. 289).  "Moreover, the resolution datum on `X`
`ℜ̄ = (⋃_{j=1}^α E_j; V_1, …, V_β, W; F)`, `n̄ = dim F`, is resolved at every point of `F ∩ U`.
(See Corollary 1 of Proposition 1, §1, Ch. II.)  We see that `F ∩ U` is an open dense subset of
`F`."  Here `ℜ̄ = ℜ.extendBy F` (Definition 6: `W` is adjoined to the `V_j` and replaced by `F`);
also `n̄ < n`, which the paper uses tacitly ("Since `n̄ < n`, we can apply Theorem I₂").

Proved from `isDatum_extendBy_prepF`, `isOpenRestriction_extendBy_prepF` (with
`resolvedAt_extendBy_prepF`) and `dim_prepF_lt`.

Deviation from the paper (gap filled): that `ℜ̄` is a datum (`F` reduced, `F ⊆ W ⊆ V_j`), that
`F ∩ U` is open and dense in `F`, that `F` is non-singular at the points of `F ∩ U` with
`F_x = W_x + E_{1,x}` and `E` has normal crossings with `F` there, and that `dim F < dim W`, are
tacit in the paper.  Deviation from the paper (statement modified, gap filled): Corollary 1 of
Proposition 1 (Ch. II) is used in its pointwise form (`Subscheme.isNormallyFlatAlongAt'_of_isContainedIn`),
for the `V_j` and `W` seen in `V_j`.  The hypothesis `hn`
(`W` non-empty of dimension `n`) is needed for `n̄ < n`. -/
theorem isDatum_and_isOpenRestriction_extendBy_prepF {N n : ℕ} (hX : IsAmbient X N)
    (hn : P.ℜ.n = (n : WithBot ℕ∞)) :
    (P.ℜ.extendBy (P.ℜ.prepF P.E₁ P.U)).IsDatum ∧
    (P.ℜ.extendBy (P.ℜ.prepF P.E₁ P.U)).IsOpenRestriction
      ((P.ℜ.prepF P.E₁ P.U).pts ∩ P.U) ∧
    (P.ℜ.extendBy (P.ℜ.prepF P.E₁ P.U)).n < P.ℜ.n := by
  have := hX.1
  exact ⟨P.isDatum_extendBy_prepF, P.isOpenRestriction_extendBy_prepF hX.2.1, P.dim_prepF_lt hn⟩

/-- Step 2, first sentences (p. 289): "Since `n̄ < n` we can apply Theorem I₂ to `(ℜ̄, F ∩ U)` and
find a permissible succession of monoidal transformations `f : X' → X` for `(ℜ̄, F ∩ U)` such that
`f*(ℜ̄)` is resolved at every point of the strict transform `F'` of `F`", together with "As is easily
seen, a permissible succession … for `(ℜ̄, F ∩ U)` is such a succession for `(ℜ, U)`".

Deviation from the paper (gap filled): when `F` is empty (`n̄` is then not a natural number) the
empty succession does the job; otherwise `n̄ = dim F` is a natural number `< n`. -/
theorem exists_isPermissibleIOpen_resolvedEverywhere_extendBy_prepF {N n : ℕ}
    (hX : IsAmbient X N) (hP : P.ℜ.n ≤ (n : WithBot ℕ∞))
    (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'') :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsPermissibleIOpen P.ℜ P.U ∧
      (s.transformI (P.ℜ.extendBy (P.ℜ.prepF P.E₁ P.U))).ResolvedEverywhere := by
  classical
  set F := P.ℜ.prepF P.E₁ P.U with hFdef
  rcases F.pts.eq_empty_or_nonempty with hFe | hFne
  · refine ⟨X, MonoidalSuccession.nil X, trivial, fun x hx => ?_⟩
    exact absurd hx (by
      show x ∉ F.pts
      rw [hFe]; exact id)
  · have hFW : F.pts ⊆ P.ℜ.W.pts := fun y hy =>
      P.ℜ.pts_prepWStar_subset P.E₁ (Subscheme.mem_pts_inter_iff.mp
        (P.ℜ.pts_prepF_subset P.E₁ P.U hy)).1
    have hWne : P.ℜ.n ≠ ⊥ := Subscheme.dim_ne_bot (hFne.mono hFW)
    obtain ⟨n₀, hn₀, hn₀n⟩ := LocSucc.exists_nat_of_le hWne hP
    obtain ⟨h1, h2, h3⟩ := P.isDatum_and_isOpenRestriction_extendBy_prepF hX hn₀
    have hFdimne : (P.ℜ.extendBy F).n ≠ ⊥ := Subscheme.dim_ne_bot hFne
    obtain ⟨m, hm, hmn₀⟩ := LocSucc.exists_nat_of_le hFdimne (N := n₀) (by
      rw [← hn₀]; exact h3.le)
    have hmlt : m < n₀ := by
      have := h3
      rw [hm, hn₀] at this
      exact_mod_cast this
    obtain ⟨Y, s, hs, hres⟩ := hI₂ m (by omega) X hX ⟨P.ℜ.extendBy F, h1⟩
      ((P.ℜ.prepF P.E₁ P.U).pts ∩ P.U) h2 hm
    have hFred : F.IsReduced := Subscheme.ofClosed_isReduced _
    refine ⟨Y, s, MonoidalSuccession.isPermissibleIOpen_of_isPermissibleIOpen_extendBy s P.ℜ F
      P.U _ hs (Subscheme.isContainedIn_of_pts_subset hFred hFW) subset_rfl, hres⟩

/-- The `F` of the transformed datum is the strict transform `F'` of `F` (p. 289: after `f`,
"`f*(ℜ̄) = (⋃ E_j'; V'; W'; F')`" and "Thus we may assume … (1)").

Proof.  `f` is an isomorphism over `U₀` (`U = U₀ ∩ W`): the centres lie in `W − U`, hence avoid `U₀`
(`MonoidalSuccession.centersAvoid_of_isPermissibleIOpen`), so the open immersion `j : U₀ → X` lifts to
an open immersion `j₁ : U₀ → Y` onto `f⁻¹(U₀)` compatible with strict transforms
(`MonoidalSuccession.exists_lift_of_centersAvoid`).  `F` is the topological construction `prepFT`
on `(W, E_1, U)` and `F_Q` the same on `(W', E_1', U')`; for a set `W` dense in its part over an open
embedding `j`, the construction is the closure of the image of the construction on the preimages
(`prepFT_eq`: components meeting `U ⊆ range j` correspond to components of the preimage), and the
preimages agree on `U₀` (`j₁⁻¹ W' = j⁻¹ W`, …).  The strict transform `F'` is dense in its part over
`f⁻¹(U₀)` (`MonoidalSuccession.pts_strictTransform_subset_closure_inter`), hence also the closure of
the image under `j₁` of the same set.

Deviation from the paper (gap filled): the identification of the `F` of the transformed datum with
the strict transform `F'` of `F` is tacit in the paper. -/
theorem prepF_transform_pts_eq {Y : Scheme.{u}} {s : MonoidalSuccession X Y} {Q : PrepSetting Y}
    (_hX : X.IsNonsingular) [IsAlgebraicScheme X] [IsAlgebraicScheme Y] (hs : s.IsPermissibleIOpen P.ℜ P.U)
    (hQ : P.IsTransform s Q) :
    (Q.ℜ.prepF Q.E₁ Q.U).pts = (s.strictTransform (P.ℜ.prepF P.E₁ P.U)).pts := by
  classical
  obtain ⟨hQℜ, hQU, hQE⟩ := hQ
  have : NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  have : NoetherianSpace Y := IsAlgebraicScheme.noetherianSpace Y
  obtain ⟨⟨U₀, hU₀, hUeq⟩, hUdense, -⟩ := P.hU
  let U₀' : X.Opens := ⟨U₀, hU₀⟩
  let j : Scheme.Opens.toScheme U₀' ⟶ X := Scheme.Opens.ι U₀'
  have hjemb : Topology.IsOpenEmbedding j.base := (Scheme.Opens.ι U₀').isOpenEmbedding
  have hrange : Set.range j.base = U₀ := Scheme.Opens.range_ι U₀'
  have hs' : s.CentersAvoid (Set.range j.base) :=
    s.centersAvoid_of_isPermissibleIOpen P.ℜ P.U _ hs (fun y hyW hyR => by
      rw [hUeq]; exact ⟨hrange ▸ hyR, hyW⟩)
  obtain ⟨j₁, hfl, hpre, hcomp, hr, hst, -⟩ := s.exists_lift_of_centersAvoid j hs'
  have hj₁ : Topology.IsOpenEmbedding j₁.base :=
    ⟨hpre.isEmbedding, by rw [hr, hrange]; exact hU₀.preimage s.composite.base.hom.continuous⟩
  have hjb : ∀ z, s.composite.base (j₁.base z) = j.base z := fun z => by
    rw [← hcomp]; rfl
  have hpre_pts : ∀ V : Subscheme X,
      j₁.base ⁻¹' (s.strictTransform V).pts = j.base ⁻¹' V.pts := fun V => by
    have := congrArg Subscheme.pts (hst V)
    rwa [FlatPreimm.pts_totalTransform, FlatPreimm.pts_totalTransform] at this
  have hrange₁ : Set.range j₁.base = s.composite.base ⁻¹' U₀ := by rw [hr, hrange]
  have hWc : IsClosed P.ℜ.W.pts := P.ℜ.W.support.isClosed
  have hEc : IsClosed P.E₁.pts := P.E₁.support.isClosed
  have hWd : P.ℜ.W.pts ⊆ closure (P.ℜ.W.pts ∩ U₀) := by
    refine hUdense.trans (closure_mono ?_)
    intro y hy
    rw [hUeq] at hy
    exact ⟨hy.2, hy.1⟩
  have hWd' : P.ℜ.W.pts ⊆ closure (P.ℜ.W.pts ∩ Set.range j.base) := by rw [hrange]; exact hWd
  have hUsub : P.U ⊆ Set.range j.base := by
    rw [hrange, hUeq]; exact fun y hy => hy.1
  have hW'pts : Q.ℜ.W.pts = (s.strictTransform P.ℜ.W).pts := by
    rw [hQℜ, MonoidalSuccession.transformI_W]
  have hQUeq : Q.U = s.composite.base ⁻¹' P.U := by
    rw [hQU, MonoidalSuccession.transformOpen_eq]
  have hQE₁ : Q.E₁.pts = (s.strictTransform P.E₁).pts := by rw [hQE]
  have hWd₁ : (s.strictTransform P.ℜ.W).pts ⊆
      closure ((s.strictTransform P.ℜ.W).pts ∩ Set.range j₁.base) := by
    rw [hrange₁]
    exact s.pts_strictTransform_subset_closure_inter P.ℜ.W U₀ hWd
  have hU₁ : Q.U ⊆ Set.range j₁.base := by
    rw [hrange₁, hQUeq]
    exact fun y hy => (hUsub.trans (by rw [hrange]) : P.U ⊆ U₀) hy
  set FZ := prepFT (j.base ⁻¹' P.ℜ.W.pts) (j.base ⁻¹' P.E₁.pts) (j.base ⁻¹' P.U) with hFZ
  have hXside : (P.ℜ.prepF P.E₁ P.U).pts = closure (j.base '' FZ) := by
    rw [DatumI.Raw.pts_prepF_eq]
    exact prepFT_eq hjemb hWc hEc hWd' hUsub
  have hYside : (Q.ℜ.prepF Q.E₁ Q.U).pts = closure (j₁.base '' FZ) := by
    rw [DatumI.Raw.pts_prepF_eq, hW'pts, hQE₁]
    have hW'c : IsClosed (s.strictTransform P.ℜ.W).pts := (s.strictTransform P.ℜ.W).support.isClosed
    have hE'c : IsClosed (s.strictTransform P.E₁).pts := (s.strictTransform P.E₁).support.isClosed
    rw [prepFT_eq hj₁ hW'c hE'c hWd₁ hU₁]
    have hU' : j₁.base ⁻¹' Q.U = j.base ⁻¹' P.U := by
      ext z
      rw [hQUeq]
      show s.composite.base (j₁.base z) ∈ P.U ↔ _
      rw [hjb]; rfl
    rw [hpre_pts, hpre_pts, hU']
  have hFd : (P.ℜ.prepF P.E₁ P.U).pts ⊆ closure ((P.ℜ.prepF P.E₁ P.U).pts ∩ U₀) := by
    rw [hXside]
    refine closure_mono (fun y hy => ?_)
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨subset_closure ⟨z, hz, rfl⟩, hrange ▸ Set.mem_range_self z⟩
  have hA1 := s.pts_strictTransform_subset_closure_inter _ U₀ hFd
  have hjpre : j.base ⁻¹' (P.ℜ.prepF P.E₁ P.U).pts = FZ := by
    rw [DatumI.Raw.pts_prepF_eq]
    exact preimage_prepFT hjemb hWc hEc hWd' hUsub
  have hAeq : (s.strictTransform (P.ℜ.prepF P.E₁ P.U)).pts ∩ s.composite.base ⁻¹' U₀ =
      j₁.base '' FZ := by
    rw [← hrange₁, ← Set.image_preimage_eq_inter_range, hpre_pts, hjpre]
  rw [hYside]
  rw [hAeq] at hA1
  have hAcl : IsClosed (s.strictTransform (P.ℜ.prepF P.E₁ P.U)).pts :=
    (s.strictTransform (P.ℜ.prepF P.E₁ P.U)).support.isClosed
  apply subset_antisymm
  · exact closure_minimal (by rw [← hAeq]; exact Set.inter_subset_left) hAcl
  · exact hA1

/-- Condition (1) for a transform, from its pointwise content: `F'` is simple at each of its points
and
`E'` has only normal crossings with it there (the form of `cond₁_transform` that does not need the
centers to lie in `F`; used for the blow-up at a bad component). -/
theorem cond₁_transform_of_pointwise {Y : Scheme.{u}} {s : MonoidalSuccession X Y} {Q : PrepSetting
    Y}
    (hX : X.IsNonsingular) [IsAlgebraicScheme X] [IsAlgebraicScheme Y] (hs : s.IsPermissibleIOpen P.ℜ P.U)
    (hQ : P.IsTransform s Q)
    (hres' : ∀ y ∈ (s.strictTransform (P.ℜ.prepF P.E₁ P.U)).pts,
      (s.strictTransform (P.ℜ.prepF P.E₁ P.U)).IsSimpleAt y ∧
        (s.transformI P.ℜ).E.HasOnlyNormalCrossingsWithAt
          (s.strictTransform (P.ℜ.prepF P.E₁ P.U)) y) : Q.Cond₁ := by
  classical
  obtain ⟨hQℜ, hQU, hQE⟩ := hQ
  have hFQ := P.prepF_transform_pts_eq hX hs ⟨hQℜ, hQU, hQE⟩
  set F' := s.strictTransform (P.ℜ.prepF P.E₁ P.U) with hF'
  set FQ := Q.ℜ.prepF Q.E₁ Q.U with hFQdef
  have hF'red : F'.IsReduced := by
    refine Subscheme.isReduced_of_isRadical_stalkIdeal fun y => ?_
    by_cases hy : y ∈ F'.pts
    · have := (hres' y hy).1.2
      have hp : (F'.stalkIdeal y).IsPrime :=
        (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
      exact hp.isRadical
    · rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hy]
      exact Ideal.radical_eq_iff.mp (Ideal.radical_top _)
  have hFeq : FQ = F' := by
    rw [Subscheme.eq_ofClosed_support F' hF'red]
    have : FQ.support = F'.support := SetLike.coe_injective hFQ
    rw [← this]
    exact Subscheme.eq_ofClosed_support FQ (Subscheme.ofClosed_isReduced _)
  have hprime : ∀ y ∈ F'.pts, (F'.stalkIdeal y).IsPrime := fun y hy => by
    have := (hres' y hy).1.2
    exact (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
  -- components of `W'_* ∩ E_1'` meeting `U'` are components of `F'` with stalk `F'_y`
  have hF'D : F'.pts ⊆ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts :=
    hFQ ▸ Q.ℜ.pts_prepF_subset Q.E₁ Q.U
  have hcomp : ∀ G ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).irreducibleComponents,
      (G.pts ∩ Q.U).Nonempty → G ∈ F'.irreducibleComponents ∧ G.pts ⊆ F'.pts := by
    intro G hG hGU
    have hGF : G.pts ⊆ F'.pts := hFQ ▸ Q.ℜ.pts_subset_pts_prepF Q.E₁ Q.U hG hGU
    obtain ⟨Z, hZmax, hZeq⟩ := id hG
    have hZpts : G.pts = Z := by
      rw [hZeq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z
    have hZsub : (Z : Set Y) ⊆ F'.pts := hZpts ▸ hGF
    exact ⟨⟨Z, ⟨⟨hZmax.1.1, hZsub⟩, fun Y' hY' hle => hZmax.2 ⟨hY'.1, hY'.2.trans hF'D⟩ hle⟩,
      hZeq⟩, hGF⟩
  have hGst : ∀ G ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).irreducibleComponents,
      (G.pts ∩ Q.U).Nonempty → ∀ y ∈ G.pts, G.stalkIdeal y = F'.stalkIdeal y := by
    intro G hG hGU y hy
    obtain ⟨hG', hGF⟩ := hcomp G hG hGU
    have hm := Subscheme.stalkIdeal_mem_minimalPrimes hG' hy
    have := hprime y (hGF hy)
    exact le_antisymm (hm.2 ⟨this, le_rfl⟩ hm.1.2) hm.1.2
  refine ⟨fun G hG hGU => ?_, fun G₁ hG₁ G₂ hG₂ h₁ h₂ hne => ?_, ?_⟩
  · exact Subscheme.isNonsingular_of_stalk_quot G fun y hy => by
      rw [hGst G hG hGU y hy]
      exact (hres' y ((hcomp G hG hGU).2 hy)).1.2
  · refine Set.disjoint_left.mpr fun y hy1 hy2 => hne ?_
    exact Subscheme.eq_of_stalkIdeal_eq (hcomp G₁ hG₁ h₁).1 (hcomp G₂ hG₂ h₂).1 hy1 hy2
      ((hGst G₁ hG₁ h₁ y hy1).trans (hGst G₂ hG₂ h₂ y hy2).symm)
  · intro y hy
    show Q.ℜ.E.HasOnlyNormalCrossingsWithAt FQ y
    rw [hFeq, hQℜ]
    exact (hres' y (hFQ ▸ hy)).2

/-- Step 2, conclusion (1) (p. 289): after `f`, `F' = F_1' ∪ ⋯` (the strict transform of `F`, which
is the `F` of the transformed datum, `prepF_transform_pts_eq`) is a disjoint union of non-singular
schemes and `⋃ E_i'` has only normal crossings with it.  Proved from the resolvedness of
`ℜ̄' = (s.transformI ℜ).extendBy F'` at every point of `F'` (`hres`): `F'` is non-singular
at its points (so reduced, and its stalks are prime), `E'` has normal crossings with `F'`; the
components `G` of `W'_* ∩ E_1'` meeting `U'` are components of `F'` (maximality), whose stalks are
the prime stalks of `F'`, so they are non-singular, and two of them through a point coincide.

Deviation from the paper (gap filled): "Since `f*(ℜ̄)` is resolved at every point of `F'`, `F'` is
non-singular" and the passage to the components of `W'_* ∩ E_1'` are tacit. -/
theorem cond₁_transform {Y : Scheme.{u}} {s : MonoidalSuccession X Y} {Q : PrepSetting Y}
    (hX : X.IsNonsingular) [IsAlgebraicScheme X] [IsAlgebraicScheme Y] (hs : s.IsPermissibleIOpen P.ℜ P.U)
    (hQ : P.IsTransform s Q)
    (hres : ((s.transformI P.ℜ).extendBy
      (s.strictTransform (P.ℜ.prepF P.E₁ P.U))).ResolvedEverywhere) : Q.Cond₁ :=
  P.cond₁_transform_of_pointwise hX hs hQ fun y hy => ⟨(hres y hy).1, (hres y hy).2.2⟩

/-- The `F` of the transformed datum equals the strict transform `F'` as a subscheme: `F'` is
non-singular, hence reduced, at its points (by the resolvedness of `ℜ̄'`, `hres`), and has the same
points as `F_Q` (`prepF_transform_pts_eq`). -/
theorem prepF_transform_eq {Y : Scheme.{u}} {s : MonoidalSuccession X Y} {Q : PrepSetting Y}
    (hX : X.IsNonsingular) [IsAlgebraicScheme X] [IsAlgebraicScheme Y]
    (hs : s.IsPermissibleIOpen P.ℜ P.U) (hQ : P.IsTransform s Q)
    (hres : ((s.transformI P.ℜ).extendBy
      (s.strictTransform (P.ℜ.prepF P.E₁ P.U))).ResolvedEverywhere) :
    Q.ℜ.prepF Q.E₁ Q.U = s.strictTransform (P.ℜ.prepF P.E₁ P.U) := by
  classical
  have hFQ := P.prepF_transform_pts_eq hX hs hQ
  set F' := s.strictTransform (P.ℜ.prepF P.E₁ P.U) with hF'
  set FQ := Q.ℜ.prepF Q.E₁ Q.U with hFQdef
  have hF'red : F'.IsReduced := by
    refine Subscheme.isReduced_of_isRadical_stalkIdeal fun y => ?_
    by_cases hy : y ∈ F'.pts
    · have : IsRegularLocalRing (Y.presheaf.stalk y ⧸ F'.stalkIdeal y) := (hres y hy).1.2
      have hp : (F'.stalkIdeal y).IsPrime :=
        (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
      exact hp.isRadical
    · rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hy]
      exact Ideal.radical_eq_iff.mp (Ideal.radical_top _)
  rw [Subscheme.eq_ofClosed_support F' hF'red]
  have : FQ.support = F'.support := SetLike.coe_injective hFQ
  rw [← this]
  exact Subscheme.eq_ofClosed_support FQ (Subscheme.ofClosed_isReduced _)

/-- The tail `(⋃_{E_i ≠ E_1} E_i; V; W)` of a datum with boundary `⋃ E_i` is a datum (the same regular
systems of parameters work). -/
theorem isDatum_rest {Y : Scheme.{u}} (Q : PrepSetting Y) (hY : Y.IsNonsingular) :
    ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).IsDatum := by
  classical
  have hred : (prepERest Q.E ⟨0, Q.hα⟩).IsReduced :=
    Subscheme.isReduced_unionFam (fun i : {i : Fin Q.α // Q.E i ≠ Q.E ⟨0, Q.hα⟩} => Q.E i)
      (fun i => Q.hE i)
  have hstalk : ∀ y, ∃ K : Finset (Y.presheaf.stalk y), ExtendsToRSOP _ K ∧
      (prepERest Q.E ⟨0, Q.hα⟩).stalkIdeal y = Ideal.span {∏ k ∈ K, k} := by
    intro y
    have : IsRegularLocalRing (Y.presheaf.stalk y) := hY y
    have h : (Subscheme.unionFam Q.E).HasOnlyNormalCrossingsAt y := Q.hEunion ▸ Q.hℜ.2.2.1 y
    obtain ⟨Z, hZ, -, hEZ⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
      Q.E Q.hE (fun i => iInf_le _ i) h
    obtain ⟨K₁, hK₁, h⟩ := DatumTransform.iInf_eq_span_prod
      (fun i : {i : Fin Q.α // Q.E i ≠ Q.E ⟨0, Q.hα⟩} => (Q.E i).stalkIdeal y)
      (ExtendsToRSOP.of_isRegularSystemOfParameters hZ) (fun i => hEZ i)
    refine ⟨K₁, (ExtendsToRSOP.of_isRegularSystemOfParameters hZ).mono hK₁, ?_⟩
    rw [prepERest, Subscheme.unionFam, DatumTransform.stalkIdeal_iInf_fintype]
    exact h
  exact ⟨hred, DatumTransform.isEverywhereCodimOne_of_forall_stalk hY hstalk,
    DatumTransform.hasOnlyNormalCrossings_of_forall_stalk hY hred hstalk, Q.hℜ.2.2.2.1,
    Q.hℜ.2.2.2.2⟩

/-- A point of `F` lies on a component of `W_* ∩ E_1` meeting `U` (`F` is a finite union of those). -/
theorem _root_.Hironaka.DatumI.Raw.exists_mem_irreducibleComponents_of_mem_pts_prepF' {Y : Scheme.{u}}
    [IsAlgebraicScheme Y] (ℜ : DatumI.Raw Y) (E₁ : Subscheme Y) (U : Set Y) {x : Y}
    (hx : x ∈ (ℜ.prepF E₁ U).pts) :
    ∃ G ∈ ((ℜ.prepWStar E₁).inter E₁).irreducibleComponents,
      (G.pts ∩ U).Nonempty ∧ x ∈ G.pts := by
  classical
  have : TopologicalSpace.NoetherianSpace Y := IsAlgebraicScheme.noetherianSpace Y
  rw [DatumI.Raw.pts_prepF] at hx
  set S := {Z : Closeds Y | ∃ F_i ∈ ((ℜ.prepWStar E₁).inter E₁).irreducibleComponents,
    (F_i.pts ∩ U).Nonempty ∧ Z = F_i.support} with hS
  have hfin : S.Finite := by
    refine (finite_setOf_maximal_isIrreducible_subset (X := Y)
      ((ℜ.prepWStar E₁).inter E₁).support.isClosed).subset ?_
    rintro Z ⟨F_i, ⟨Zw, hZw, rfl⟩, -, rfl⟩
    have : (Subscheme.ofClosed Zw).support = Zw :=
      SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Zw)
    rw [this]
    exact hZw
  have hcl : IsClosed (⋃₀ ((↑) '' S : Set (Set Y))) :=
    (hfin.image _).isClosed_sUnion (by rintro _ ⟨Z, -, rfl⟩; exact Z.isClosed)
  rw [hcl.closure_eq] at hx
  obtain ⟨_, ⟨Z, ⟨G, hG, hGU, rfl⟩, rfl⟩, hxG⟩ := hx
  exact ⟨G, hG, hGU, hxG⟩

/-- A generic point `η` of `F` (a point with `closure {η}` an irreducible component of `F`) lies in the
open restriction `U` (p. 291, the parenthetical remark in step (4)); see
`resolvedAt_of_isGenericPoint_prepF`. -/
theorem mem_U_of_isGenericPoint_prepF [IsAlgebraicScheme X] {η : X}
    (h : Maximal (fun S : Set X => _root_.IsIrreducible S ∧ S ⊆ (P.ℜ.prepF P.E₁ P.U).pts)
      (closure {η})) : η ∈ P.U := by
  classical
  have : TopologicalSpace.NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  obtain ⟨⟨U₀, hU₀, hUeq⟩, -, -⟩ := P.hU
  have hηF : η ∈ (P.ℜ.prepF P.E₁ P.U).pts := h.1.2 (subset_closure rfl)
  have hηW : η ∈ P.ℜ.W.pts :=
    P.ℜ.pts_prepWStar_subset P.E₁ (Subscheme.mem_pts_inter_iff.mp
      (P.ℜ.pts_prepF_subset P.E₁ P.U hηF)).1
  rw [DatumI.Raw.pts_prepF] at hηF
  set S := {Z : Closeds X | ∃ F_i ∈ ((P.ℜ.prepWStar P.E₁).inter P.E₁).irreducibleComponents,
    (F_i.pts ∩ P.U).Nonempty ∧ Z = F_i.support} with hS
  have hfin : S.Finite := by
    refine (finite_setOf_maximal_isIrreducible_subset (X := X)
      ((P.ℜ.prepWStar P.E₁).inter P.E₁).support.isClosed).subset ?_
    rintro Z ⟨F_i, ⟨Zw, hZw, rfl⟩, -, rfl⟩
    have : (Subscheme.ofClosed Zw).support = Zw :=
      SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Zw)
    rw [this]
    exact hZw
  have hcl : IsClosed (⋃₀ ((↑) '' S : Set (Set X))) :=
    (hfin.image _).isClosed_sUnion (by rintro _ ⟨Z, -, rfl⟩; exact Z.isClosed)
  rw [hcl.closure_eq] at hηF
  obtain ⟨_, ⟨Z, ⟨G, hG, hGU, rfl⟩, rfl⟩, hηG⟩ := hηF
  have hGirr : _root_.IsIrreducible G.pts := by
    obtain ⟨Z', hZ'max, rfl⟩ := id hG
    rw [show (Subscheme.ofClosed Z').pts = Z' from
      Scheme.IdealSheafData.coe_support_vanishingIdeal Z']
    exact hZ'max.1.1
  have hle : closure {η} ⊆ G.pts :=
    closure_minimal (Set.singleton_subset_iff.mpr hηG) G.support.isClosed
  have hGle : G.pts ⊆ closure {η} :=
    h.2 ⟨hGirr, P.ℜ.pts_subset_pts_prepF P.E₁ P.U hG hGU⟩ hle
  obtain ⟨u, huG, huU⟩ := hGU
  have hspec : η ⤳ u := specializes_iff_mem_closure.mpr (hGle huG)
  have huU' := huU
  rw [hUeq] at huU'
  have hηU : η ∈ P.U := by
    rw [hUeq]
    exact ⟨hspec.mem_open hU₀ huU'.1, hηW⟩
  exact hηU

/-- Contraction from a generization: if `η ⤳ y`, `G` is a subscheme with prime stalk at `y` whose stalk
at `η` is the maximal ideal, `W_y` is a prime contained in `G_y`, and `D_η ⊆ W_η`, then `D_y ⊆ W_y`
(`O_{Y,η}` is the localization of `O_{Y,y}` at the prime `G_y`, and `W_η` is the extension of the
prime `W_y ⊆ G_y`, so its contraction is `W_y`). -/
theorem stalkIdeal_le_of_stalkIdeal_le_of_specializes {Y : Scheme.{u}} {y η : Y} (hηy : η ⤳ y)
    (G W D : Subscheme Y)
    (hGη : G.stalkIdeal η = IsLocalRing.maximalIdeal (Y.presheaf.stalk η))
    (hGprime : (G.stalkIdeal y).IsPrime) (hWy : (W.stalkIdeal y).IsPrime)
    (hWyG : W.stalkIdeal y ≤ G.stalkIdeal y) (h : D.stalkIdeal η ≤ W.stalkIdeal η) :
    D.stalkIdeal y ≤ W.stalkIdeal y := by
  classical
  let _ : Algebra (Y.presheaf.stalk y) (Y.presheaf.stalk η) :=
    (Y.presheaf.stalkSpecializes hηy).hom.toAlgebra
  have hloc := isLocalization_stalkSpecializes_of_specializes hηy
  have hcomap : (IsLocalRing.maximalIdeal (Y.presheaf.stalk η)).comap
      (Y.presheaf.stalkSpecializes hηy).hom = G.stalkIdeal y :=
    Subscheme.comap_maximalIdeal_stalkSpecializes_eq G hηy hGη
  have hsubc : ((IsLocalRing.maximalIdeal (Y.presheaf.stalk η)).comap
      (Y.presheaf.stalkSpecializes hηy).hom).primeCompl = (G.stalkIdeal y).primeCompl := by
    ext z
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hcomap]
  have : IsLocalization (G.stalkIdeal y).primeCompl (Y.presheaf.stalk η) := by
    rw [← hsubc]; exact hloc
  have hdisj : Disjoint ((G.stalkIdeal y).primeCompl : Set (Y.presheaf.stalk y)) (W.stalkIdeal y) :=
    Set.disjoint_left.mpr fun z hz hzW => hz (hWyG hzW)
  have hW' := IsLocalization.under_map_of_isPrime_disjoint (G.stalkIdeal y).primeCompl
    (Y.presheaf.stalk η) (I := W.stalkIdeal y) hWy hdisj
  have hmapW : W.stalkIdeal η = (W.stalkIdeal y).map (algebraMap (Y.presheaf.stalk y)
      (Y.presheaf.stalk η)) := Subscheme.stalkIdeal_eq_map_stalkSpecializes W hηy
  have hmapE : D.stalkIdeal η = (D.stalkIdeal y).map (algebraMap (Y.presheaf.stalk y)
      (Y.presheaf.stalk η)) := Subscheme.stalkIdeal_eq_map_stalkSpecializes D hηy
  intro z hz
  have h1 : algebraMap (Y.presheaf.stalk y) (Y.presheaf.stalk η) z ∈ D.stalkIdeal η := by
    rw [hmapE]; exact Ideal.mem_map_of_mem _ hz
  have h2 := h h1
  rw [hmapW] at h2
  have h3 : z ∈ ((W.stalkIdeal y).map (algebraMap (Y.presheaf.stalk y)
      (Y.presheaf.stalk η))).under (Y.presheaf.stalk y) := h2
  rwa [hW'] at h3

/-- Reduction to the generic point (used for the sentence of p. 289 "for `i ≥ 2` …, `E_i` containing
`F_j` must contain …"): at a point `y` of `F` where the stalk of `F` is prime, a subscheme `D` with
`D_y ⊆ F_y` passes through the generic point `η` of the component `G` of `W_* ∩ E_1` through `y`,
which lies in `U` and has `F_η = G_η = M_η`. -/
theorem exists_isGenericPoint_of_mem_prepF {Y : Scheme.{u}} [IsAlgebraicScheme Y] (Q : PrepSetting Y)
    {y : Y} (hyF : y ∈ (Q.ℜ.prepF Q.E₁ Q.U).pts)
    (hFprime : ((Q.ℜ.prepF Q.E₁ Q.U).stalkIdeal y).IsPrime) (D : Subscheme Y)
    (hle : D.stalkIdeal y ≤ (Q.ℜ.prepF Q.E₁ Q.U).stalkIdeal y) :
    ∃ (G : Subscheme Y) (η : Y), η ⤳ y ∧ η ∈ Q.U ∧ η ∈ (Q.ℜ.prepF Q.E₁ Q.U).pts ∧
      (Q.ℜ.prepF Q.E₁ Q.U).stalkIdeal η = IsLocalRing.maximalIdeal (Y.presheaf.stalk η) ∧
      η ∈ D.pts ∧ G.stalkIdeal η = IsLocalRing.maximalIdeal (Y.presheaf.stalk η) ∧
      G.stalkIdeal y = (Q.ℜ.prepF Q.E₁ Q.U).stalkIdeal y ∧
      Q.ℜ.W.stalkIdeal y ≤ G.stalkIdeal y := by
  classical
  have : TopologicalSpace.NoetherianSpace Y := IsAlgebraicScheme.noetherianSpace Y
  set F := Q.ℜ.prepF Q.E₁ Q.U with hFdef
  set W := Q.ℜ.W with hWdef
  set Wst := Q.ℜ.prepWStar Q.E₁ with hWstdef
  have hFsub : ∀ z ∈ F.pts, z ∈ Wst.pts ∧ z ∈ Q.E₁.pts := fun z hz =>
    Subscheme.mem_pts_inter_iff.mp (Q.ℜ.pts_prepF_subset Q.E₁ Q.U hz)
  have hFD : F.pts ⊆ ((Wst).inter Q.E₁).pts := Q.ℜ.pts_prepF_subset Q.E₁ Q.U
  have hFred : F.IsReduced := Subscheme.ofClosed_isReduced _
  obtain ⟨G, hG, hGU, hyG⟩ := Q.ℜ.exists_mem_irreducibleComponents_of_mem_pts_prepF' Q.E₁ Q.U hyF
  obtain ⟨Z, hZmax, hGeq⟩ := id hG
  have hZpts : G.pts = Z := by
    rw [hGeq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  obtain ⟨η, hη⟩ : ∃ η, IsGenericPoint η (Z : Set Y) := QuasiSober.sober hZmax.1.1 Z.isClosed
  have hηy : η ⤳ y := hη.specializes (hZpts ▸ hyG)
  have hGF : G.pts ⊆ F.pts := Q.ℜ.pts_subset_pts_prepF Q.E₁ Q.U hG hGU
  have hZeq : Z = ⟨closure {η}, isClosed_closure⟩ := SetLike.coe_injective hη.def.symm
  have hmaxF : Maximal (fun S : Set Y => _root_.IsIrreducible S ∧ S ⊆ F.pts) (closure {η}) := by
    rw [hη.def]
    refine ⟨⟨hZmax.1.1, hZpts ▸ hGF⟩, fun S hS hle => ?_⟩
    have hcS : closure S ⊆ F.pts := closure_minimal hS.2 F.support.isClosed
    have hT := hZmax.2 (y := ⟨closure S, isClosed_closure⟩) ⟨hS.1.closure, hcS.trans hFD⟩
      (hle.trans subset_closure)
    exact subset_closure.trans hT
  have hηU : η ∈ Q.U := Q.mem_U_of_isGenericPoint_prepF hmaxF
  have hGcompF : G ∈ F.irreducibleComponents :=
    ⟨Z, ⟨⟨hZmax.1.1, hZpts ▸ hGF⟩, fun S hS hle => hZmax.2 ⟨hS.1, hS.2.trans hFD⟩ hle⟩, hGeq⟩
  have hGyF : G.stalkIdeal y = F.stalkIdeal y := by
    have hm := Subscheme.stalkIdeal_mem_minimalPrimes hGcompF hyG
    exact le_antisymm (hm.2 ⟨hFprime, le_rfl⟩ hm.1.2) hm.1.2
  have hFG : F.stalkIdeal y ≤ G.stalkIdeal y := hGyF.ge
  have hGη : G.stalkIdeal η = IsLocalRing.maximalIdeal (Y.presheaf.stalk η) := by
    rw [hGeq, hZeq]; exact stalkIdeal_ofClosed_closure_self' η
  have hηF : η ∈ F.pts := hGF (hZpts ▸ hη.mem)
  have hηD : η ∈ D.pts := by
    refine Subscheme.mem_pts_of_stalkIdeal_le_ofClosed_closure hηy D ?_
    rw [← hZeq, ← hGeq]; exact hle.trans hFG
  have hFη : F.stalkIdeal η = IsLocalRing.maximalIdeal (Y.presheaf.stalk η) := by
    rw [← hGη, Subscheme.stalkIdeal_eq_map_stalkSpecializes F hηy,
      Subscheme.stalkIdeal_eq_map_stalkSpecializes G hηy, hGyF]
  refine ⟨G, η, hηy, hηU, hηF, hFη, hηD, hGη, hGyF, ?_⟩
  exact (Subscheme.stalkIdeal_mono (fun U => Subscheme.isContainedIn_of_pts_subset hFred
    (fun z hz => Q.ℜ.pts_prepWStar_subset Q.E₁ (hFsub z hz).1) U) y).trans hFG

/-- The pointwise form of "for `i ≥ 2`, `E_i` containing `F_j` contains the component of `W` containing
`F_j`" (p. 289), at a point `y` of `F` where `W` is simple and the stalk of `F` is prime: if the
stalk of `E_j ≠ E_1` at `y` lies in that of `F`, it lies in that of `W`.  It is proved at the generic
point `η` of a component `G ∋ y` of `W_* ∩ E_1` meeting `U` (so `η ∈ U` and `ℜ` is resolved at `η`):
`W_η + E_{1,η}` is generated by part of a regular system of parameters and is the maximal ideal (`G`
is a component), so every other `E_{j,η}` (`≠ E_{1,η}`) lies in `W_η`; the stalk at `y` follows by
contraction from `O_η = (O_y)_{G_y}`. -/
theorem rest_stalkIdeal_le_of_prepF {Y : Scheme.{u}} [IsAlgebraicScheme Y] (Q : PrepSetting Y)
    (hY : Y.IsNonsingular) {y : Y} (hyF : y ∈ (Q.ℜ.prepF Q.E₁ Q.U).pts)
    (hWs : Q.ℜ.W.IsSimpleAt y) (hFprime : ((Q.ℜ.prepF Q.E₁ Q.U).stalkIdeal y).IsPrime)
    {j : Fin Q.α} (hj : Q.E j ≠ Q.E₁)
    (hle : (Q.E j).stalkIdeal y ≤ (Q.ℜ.prepF Q.E₁ Q.U).stalkIdeal y) :
    (Q.E j).stalkIdeal y ≤ Q.ℜ.W.stalkIdeal y := by
  classical
  have : TopologicalSpace.NoetherianSpace Y := IsAlgebraicScheme.noetherianSpace Y
  set F := Q.ℜ.prepF Q.E₁ Q.U with hFdef
  set W := Q.ℜ.W with hWdef
  set Wst := Q.ℜ.prepWStar Q.E₁ with hWstdef
  have hFsub : ∀ z ∈ F.pts, z ∈ Wst.pts ∧ z ∈ Q.E₁.pts := fun z hz =>
    Subscheme.mem_pts_inter_iff.mp (Q.ℜ.pts_prepF_subset Q.E₁ Q.U hz)
  have hFD : F.pts ⊆ ((Wst).inter Q.E₁).pts := Q.ℜ.pts_prepF_subset Q.E₁ Q.U
  have hFred : F.IsReduced := Subscheme.ofClosed_isReduced _
  -- the component `G` of `W_* ∩ E_1` through `y`, and its generic point `η`
  obtain ⟨G, hG, hGU, hyG⟩ := Q.ℜ.exists_mem_irreducibleComponents_of_mem_pts_prepF' Q.E₁ Q.U hyF
  obtain ⟨Z, hZmax, hGeq⟩ := id hG
  have hZpts : G.pts = Z := by
    rw [hGeq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  obtain ⟨η, hη⟩ : ∃ η, IsGenericPoint η (Z : Set Y) := QuasiSober.sober hZmax.1.1 Z.isClosed
  have hηy : η ⤳ y := hη.specializes (hZpts ▸ hyG)
  have hGF : G.pts ⊆ F.pts := Q.ℜ.pts_subset_pts_prepF Q.E₁ Q.U hG hGU
  have hGred : G.IsReduced := by rw [hGeq]; exact Subscheme.ofClosed_isReduced Z
  have hZeq : Z = ⟨closure {η}, isClosed_closure⟩ := SetLike.coe_injective hη.def.symm
  have hmaxF : Maximal (fun S : Set Y => _root_.IsIrreducible S ∧ S ⊆ F.pts) (closure {η}) := by
    rw [hη.def]
    refine ⟨⟨hZmax.1.1, hZpts ▸ hGF⟩, fun S hS hle => ?_⟩
    have hcS : closure S ⊆ F.pts := closure_minimal hS.2 F.support.isClosed
    have hT := hZmax.2 (y := ⟨closure S, isClosed_closure⟩) ⟨hS.1.closure, hcS.trans hFD⟩
      (hle.trans subset_closure)
    exact subset_closure.trans hT
  have hηU : η ∈ Q.U := Q.mem_U_of_isGenericPoint_prepF hmaxF
  obtain ⟨hηWs, hηVf, hηnc⟩ := Q.hU.2.2 η hηU
  -- `G_y = F_y`
  have hGcompF : G ∈ F.irreducibleComponents :=
    ⟨Z, ⟨⟨hZmax.1.1, hZpts ▸ hGF⟩, fun S hS hle => hZmax.2 ⟨hS.1, hS.2.trans hFD⟩ hle⟩, hGeq⟩
  have hGyF : G.stalkIdeal y = F.stalkIdeal y := by
    have hm := Subscheme.stalkIdeal_mem_minimalPrimes hGcompF hyG
    exact le_antisymm (hm.2 ⟨hFprime, le_rfl⟩ hm.1.2) hm.1.2
  have hFG : F.stalkIdeal y ≤ G.stalkIdeal y := hGyF.ge
  -- `η` lies on `E_j` and `E_1`
  have hGη : G.stalkIdeal η = IsLocalRing.maximalIdeal (Y.presheaf.stalk η) := by
    rw [hGeq, hZeq]; exact stalkIdeal_ofClosed_closure_self' η
  have hηF : η ∈ F.pts := hGF (hZpts ▸ hη.mem)
  have hηE₁ : η ∈ Q.E₁.pts := (hFsub η hηF).2
  have hηEj : η ∈ (Q.E j).pts := by
    refine Subscheme.mem_pts_of_stalkIdeal_le_ofClosed_closure hηy (Q.E j) ?_
    rw [← hZeq, ← hGeq]; exact hle.trans hFG
  -- normal crossings at `η`
  have : IsRegularLocalRing (Y.presheaf.stalk η) := hY η
  have hηnc' : (Subscheme.unionFam Q.E).HasOnlyNormalCrossingsWithAt W η := Q.hEunion ▸ hηnc
  obtain ⟨Zη, hZη, ⟨tη, htη, hWt⟩, hEη⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    Q.E Q.hE (fun i => iInf_le _ i) hηnc'
  obtain ⟨a, haZ, haE⟩ : ∃ a ∈ Zη, Q.E₁.stalkIdeal η = Ideal.span {a} := by
    rcases hEη ⟨0, Q.hα⟩ with h | h
    · exfalso
      have h1 := Subscheme.stalkIdeal_le_maximalIdeal Q.E₁ hηE₁
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ h1))
    · exact h
  obtain ⟨b, hbZ, hbE⟩ : ∃ b ∈ Zη, (Q.E j).stalkIdeal η = Ideal.span {b} := by
    rcases hEη j with h | h
    · exfalso
      have h1 := Subscheme.stalkIdeal_le_maximalIdeal (Q.E j) hηEj
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ h1))
    · exact h
  -- `W_η + E_{1,η}` is the maximal ideal: `G` is a component of `W ∩ E_1`
  have hηreg : IsRegularLocalRing (Y.presheaf.stalk η ⧸ W.stalkIdeal η) := hηWs.2
  have hWηp : (W.stalkIdeal η).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
  have hηWst : η ∈ Wst.pts := (hFsub η hηF).1
  obtain ⟨C₀, hC₀, hC₀E, hηC₀⟩ :=
    DatumI.Raw.exists_mem_irreducibleComponents_of_mem_pts_prepWStar Q.ℜ Q.E₁ hηWst
  have hminQ : ∀ C ∈ W.irreducibleComponents, η ∈ C.pts → C.stalkIdeal η = W.stalkIdeal η := by
    intro C hC hηC
    have hq := Subscheme.stalkIdeal_mem_minimalPrimes hC hηC
    exact le_antisymm (hq.2 ⟨hWηp, le_rfl⟩ hq.1.2) hq.1.2
  have hC₀Wst : C₀.pts ⊆ Wst.pts := by
    obtain ⟨Z', -, hZeq'⟩ := id hC₀
    intro z hz
    rw [DatumI.Raw.pts_prepWStar]
    exact subset_closure ⟨_, ⟨C₀.support, ⟨_, hC₀, hC₀E, rfl⟩, rfl⟩, hz⟩
  set D := W.inter Q.E₁ with hD
  have hDpts : D.pts ⊆ W.pts ∩ Q.E₁.pts := fun z hz => Subscheme.mem_pts_inter_iff.mp hz
  set J := W.stalkIdeal η ⊔ Q.E₁.stalkIdeal η with hJ
  have hDη : D.stalkIdeal η = J := Subscheme.stalkIdeal_sup_eq _ _ η
  have hext : ExtendsToRSOP (Y.presheaf.stalk η) (insert a tη) :=
    ⟨Zη, Finset.insert_subset haZ htη, hZη⟩
  have hJspan : J = Ideal.span ((insert a tη : Finset _) : Set (Y.presheaf.stalk η)) := by
    rw [hJ, haE, hWt, Finset.coe_insert, Set.insert_eq, Ideal.span_union, sup_comm]
  have hJprime : J.IsPrime := by rw [hJspan]; exact hext.isPrime_span
  have hJmin : J ∈ J.minimalPrimes := ⟨⟨hJprime, le_rfl⟩, fun q hq _ => hq.2⟩
  obtain ⟨G', hG', hηG', hG'J⟩ :=
    Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes D η (by rw [hDη]; exact hJmin)
  have hJm : J = IsLocalRing.maximalIdeal (Y.presheaf.stalk η) := by
    obtain ⟨Z', hZ'max, hG'eq⟩ := id hG'
    have hZ'pts : G'.pts = Z' := by
      rw [hG'eq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z'
    have hηZ' : η ∈ (Z' : Set Y) := by rwa [hZ'pts] at hηG'
    obtain ⟨g, hg⟩ : ∃ g, IsGenericPoint g (Z' : Set Y) := QuasiSober.sober hZ'max.1.1 Z'.isClosed
    have hgη : g ⤳ η := hg.specializes hηZ'
    have hgD : g ∈ D.pts := hZ'max.1.2 hg.mem
    have hgW : g ∈ W.pts := (hDpts hgD).1
    obtain ⟨C', hC', hgC'⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_pts W hgW
    have hηC' : η ∈ C'.pts := by
      obtain ⟨Z₁, -, rfl⟩ := hC'
      have h1 : g ∈ (Z₁ : Set Y) := by
        rwa [show (Subscheme.ofClosed Z₁).pts = Z₁ from
          Scheme.IdealSheafData.coe_support_vanishingIdeal Z₁] at hgC'
      rw [show (Subscheme.ofClosed Z₁).pts = Z₁ from
        Scheme.IdealSheafData.coe_support_vanishingIdeal Z₁]
      exact closure_minimal (Set.singleton_subset_iff.mpr h1) Z₁.isClosed
        (specializes_iff_mem_closure.mp hgη)
    have hC'eq : C' = C₀ :=
      Subscheme.eq_of_stalkIdeal_eq hC' hC₀ hηC' hηC₀
        ((hminQ C' hC' hηC').trans (hminQ C₀ hC₀ hηC₀).symm)
    have hgC₀ : g ∈ C₀.pts := hC'eq ▸ hgC'
    have hgWE : g ∈ (Wst.inter Q.E₁).pts :=
      Subscheme.mem_pts_inter_iff.mpr ⟨hC₀Wst hgC₀, (hDpts hgD).2⟩
    have hZ'sub : (Z' : Set Y) ⊆ (Wst.inter Q.E₁).pts := by
      rw [← hg.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hgWE)
        (Wst.inter Q.E₁).support.isClosed
    have hle' : Z ≤ Z' := by
      rw [hZeq]
      show closure {η} ⊆ Z'
      exact closure_minimal (Set.singleton_subset_iff.mpr hηZ') Z'.isClosed
    have hZ'Z : Z' ≤ Z := hZmax.2 ⟨hZ'max.1.1, hZ'sub⟩ hle'
    have hZZ' : Z' = Z := le_antisymm hZ'Z hle'
    rw [← hG'J, hG'eq, hZZ', hZeq]
    exact stalkIdeal_ofClosed_closure_self' η
  -- every member of the regular system of parameters is in `{a} ∪ tη`
  have hsub : insert a tη ⊆ Zη := Finset.insert_subset haZ htη
  have hbm : b ∈ insert a tη := by
    by_contra hnot
    refine rsop_notMem_span hZη hsub hbZ hnot ?_
    rw [← hJspan, hJm]
    exact hZη.1 ▸ Ideal.subset_span hbZ
  have hEjW : (Q.E j).stalkIdeal η ≤ W.stalkIdeal η := by
    rcases Finset.mem_insert.mp hbm with rfl | hbt
    · exfalso
      refine hj ?_
      -- `E_{j,η} = E_{1,η}`, both are components of themselves
      have hEjirr : (Q.E j).IsNonsingular ∧ (Q.E j).IsIrreducible := by
        have hne : Q.E j ≠ Subscheme.empty := by
          intro h
          rw [h, DatumTransform.pts_empty] at hηEj
          exact hηEj
        obtain ⟨hns, hirr, -⟩ := (Q.hE j).resolve_left hne
        exact ⟨hns, hirr⟩
      have hE₁irr : Q.E₁.IsNonsingular ∧ Q.E₁.IsIrreducible := by
        have hne : Q.E₁ ≠ Subscheme.empty := by
          intro h
          rw [h, DatumTransform.pts_empty] at hηE₁
          exact hηE₁
        obtain ⟨hns, hirr, -⟩ := (Q.hE ⟨0, Q.hα⟩).resolve_left hne
        exact ⟨hns, hirr⟩
      exact Subscheme.eq_of_stalkIdeal_eq_of_mem_irreducibleComponents
        (Subscheme.mem_irreducibleComponents_self _ hEjirr.1 hEjirr.2)
        (Subscheme.mem_irreducibleComponents_self _ hE₁irr.1 hE₁irr.2) hηEj hηE₁
        (hbE.trans haE.symm)
    · rw [hbE, hWt, Ideal.span_singleton_le_iff_mem]
      exact Ideal.subset_span (Finset.mem_coe.mpr hbt)
  -- contraction to `y`
  have hyreg : IsRegularLocalRing (Y.presheaf.stalk y ⧸ W.stalkIdeal y) := hWs.2
  have hWy : (W.stalkIdeal y).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
  have hWyG : W.stalkIdeal y ≤ G.stalkIdeal y :=
    (Subscheme.stalkIdeal_mono (fun U => Subscheme.isContainedIn_of_pts_subset hFred
      (fun z hz => Q.ℜ.pts_prepWStar_subset Q.E₁ (hFsub z hz).1) U) y).trans hFG
  exact stalkIdeal_le_of_stalkIdeal_le_of_specializes hηy G W (Q.E j) hGη (hGyF ▸ hFprime) hWy hWyG
    hEjW

/-- Normal flatness of `V` along `D` at `x` only depends on the stalk of `D` at `x`. -/
theorem _root_.Hironaka.Subscheme.isNormallyFlatAlongAt'_congr {Y : Scheme.{u}} (V D₁ D₂ : Subscheme Y)
    {x : Y} (h : D₁.stalkIdeal x = D₂.stalkIdeal x)
    (h₁ : Subscheme.IsNormallyFlatAlongAt' V D₁ x) : Subscheme.IsNormallyFlatAlongAt' V D₂ x := by
  obtain ⟨x', hx', hnf⟩ := h₁
  subst hx'
  refine ⟨x', rfl, ?_⟩
  have e : (Subscheme.totalTransform V.ι D₁).stalkIdeal x' =
      (Subscheme.totalTransform V.ι D₂).stalkIdeal x' := by
    rw [stalkIdeal_totalTransform, stalkIdeal_totalTransform, h]
  refine ⟨?_, ?_⟩
  · have := hnf.1
    rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top] at this ⊢
    rwa [← e]
  · rw [← e]; exact hnf.2

/-- The quotient of the stalk of `Y` at `V.ι z` by `W` is the quotient of the stalk of the scheme `V` at
`z` by the stalk of the total transform `V.ι⁻¹ W` (for `W ⊆ V`): `O_{V,z} = O_{Y,x}/V_x`. -/
theorem _root_.Hironaka.Subscheme.exists_quotEquiv_totalTransform {Y : Scheme.{u}} (V W : Subscheme Y) (hWV : W.IsContainedIn V)
    (z : V.toScheme) :
    ∃ τ : (Y.presheaf.stalk (V.ι z) ⧸ W.stalkIdeal (V.ι z)) ≃+*
        (V.toScheme.presheaf.stalk z ⧸ (Subscheme.totalTransform V.ι W).stalkIdeal z),
      ∀ a, τ (Ideal.Quotient.mk _ a) =
        Ideal.Quotient.mk _ ((V.ι.stalkMap z).hom a) := by
  set φ := (V.ι.stalkMap z).hom with hφ
  have hsurj : Function.Surjective φ := V.ι.stalkMap_surjective z
  have hker : RingHom.ker φ = V.stalkIdeal (V.ι z) := (stalkIdeal_eq_ker_stalkMap V z).symm
  have hVW : V.stalkIdeal (V.ι z) ≤ W.stalkIdeal (V.ι z) :=
    Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hWV _
  have hW1 : (Subscheme.totalTransform V.ι W).stalkIdeal z = (W.stalkIdeal (V.ι z)).map φ :=
    stalkIdeal_totalTransform V.ι W z
  set g : Y.presheaf.stalk (V.ι z) →+* (V.toScheme.presheaf.stalk z ⧸
      (Subscheme.totalTransform V.ι W).stalkIdeal z) :=
    (Ideal.Quotient.mk _).comp φ with hg
  have hgs : Function.Surjective g := fun b => by
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨a, rfl⟩ := hsurj b'
    exact ⟨a, rfl⟩
  have hgker : RingHom.ker g = W.stalkIdeal (V.ι z) := by
    ext a
    rw [RingHom.mem_ker, hg, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hW1]
    constructor
    · intro h
      obtain ⟨w, hw, hwa⟩ := (Ideal.mem_map_iff_of_surjective φ hsurj).mp h
      have : a - w ∈ V.stalkIdeal (V.ι z) := by
        rw [← hker, RingHom.mem_ker, map_sub, hwa, sub_self]
      have h2 : a = (a - w) + w := by ring
      rw [h2]
      exact add_mem (hVW this) hw
    · exact fun h => Ideal.mem_map_of_mem _ h
  refine ⟨((Ideal.quotEquivOfEq hgker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hgs)), fun a => ?_⟩
  rfl

/-- For `D ⊆ V`, the total transform of `D` in the scheme `V` is isomorphic to `D`. -/
private theorem nonempty_totalTransform_iso' {Y : Scheme.{u}} {V D : Subscheme Y} (hDV : D.IsContainedIn V) :
    Nonempty ((Subscheme.totalTransform V.ι D).toScheme ≅ D.toScheme) := by
  have hVD : V ≤ D := fun U => hDV U
  have hsq : CategoryTheory.IsPullback (Scheme.IdealSheafData.inclusion hVD)
      (CategoryTheory.CategoryStruct.id D.toScheme) V.ι D.ι :=
    CategoryTheory.IsPullback.of_vert_isIso_mono ⟨by
      rw [Scheme.IdealSheafData.inclusion_subschemeι, CategoryTheory.Category.id_comp]⟩
  exact ⟨D.comapIso V.ι ≪≫ hsq.isoPullback.symm⟩

private theorem isNonsingular_of_iso' {A B : Scheme.{u}} (e : A ≅ B) (hB : B.IsNonsingular) :
    A.IsNonsingular := by
  intro a
  have : IsRegularLocalRing (B.presheaf.stalk (e.hom a)) := hB (e.hom a)
  exact IsRegularLocalRing.of_ringEquiv (CategoryTheory.asIso
    (e.hom.stalkMap a)).commRingCatIsoToRingEquiv

private theorem irreducibleSpace_of_iso' {A B : Scheme.{u}} (e : A ≅ B) [IrreducibleSpace B] :
    IrreducibleSpace A := by
  have hsurj : Function.Surjective e.inv := fun a => ⟨e.hom a, by
    rw [← Scheme.Hom.comp_apply, CategoryTheory.Iso.hom_inv_id]
    rfl⟩
  rw [irreducibleSpace_def]
  have := (IrreducibleSpace.isIrreducible_univ B).image e.inv e.inv.continuous.continuousOn
  rwa [Set.image_univ, hsurj.range_eq] at this

/-- Corollary 4 of Proposition 1 and the Corollary of Theorem 3 (Ch. II), in the form used for the
`V_j` of a datum (`IsNormallyFlatAlongAt'`): let `D ⊆ W ⊆ V` be subschemes of an algebraic scheme, `D`
non-singular irreducible, `V` and `W` normally flat along `D` at its points, and suppose that `D`
contains a simple point of `W` at which `V` is normally flat along `W`.  Then every point of `D` is a
simple point of `W` and `V` is normally flat along `W` at every point of `D`.

Proof: `cor:II.1-prop1-4` and `cor:II.3-thm3` (`Subscheme.isSimpleAt_and_isNormallyFlatAlongAt_of_normallyFlat_chain`)
applied in the scheme `V` to `V.ι⁻¹ W ⊇ V.ι⁻¹ D`.  The transport needs: `V.ι⁻¹ D ≅ D` (non-singular,
irreducible), the identification `O_{V,z}/(V.ι⁻¹ W)_z ≅ O_{Y,x}/W_x` compatible with the ideals of
`D` (`Subscheme.exists_quotEquiv_totalTransform`; this turns `IsNormallyFlatAlongAt'` of `W` along `D`
into the normal flatness of the scheme `W₁ = V.ι⁻¹ W` along `D₁`, and the simple points of `W` into
those of `W₁`), and the normal flatness of `V` along `D` and `W` at the points, which are
`IsNormallyFlatAlongAt'` by definition.

Deviation from the paper (statement modified): the paper states the Corollary of Theorem 3 for a
subscheme `W` of an algebraic scheme `V`; in the datum `V` is the subscheme `V_j` of `X` and the
statement is read in `V_j` via `IsNormallyFlatAlongAt'`. -/
theorem _root_.Hironaka.Subscheme.isSimpleAt_and_isNormallyFlatAlongAt'_of_chain [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {Y : Scheme.{u}}
    [IsAlgebraicScheme Y] (V W D : Subscheme Y) (hWV : W.IsContainedIn V) (hDW : D.IsContainedIn W)
    (hD : D.IsNonsingular) (hirr : D.IsIrreducible)
    (hVD : ∀ x ∈ D.pts, Subscheme.IsNormallyFlatAlongAt' V D x)
    (hWD : ∀ x ∈ D.pts, Subscheme.IsNormallyFlatAlongAt' W D x)
    (hx : ∃ x ∈ D.pts, W.IsSimpleAt x ∧ Subscheme.IsNormallyFlatAlongAt' V W x) :
    ∀ x ∈ D.pts, W.IsSimpleAt x ∧ Subscheme.IsNormallyFlatAlongAt' V W x := by
  classical
  have hDV : D.IsContainedIn V := hDW.trans hWV
  have : IsAlgebraicScheme V.toScheme := isAlgebraicScheme_toScheme V
  set W₁ := Subscheme.totalTransform V.ι W with hW₁
  set D₁ := Subscheme.totalTransform V.ι D with hD₁
  have hD₁W₁ : D₁.IsContainedIn W₁ := fun U =>
    FlatPreimm.totalTransform_mono V.ι (Scheme.IdealSheafData.le_def.mpr hDW) U
  obtain ⟨e⟩ := nonempty_totalTransform_iso' hDV
  have : IrreducibleSpace D.toScheme := hirr
  have hD₁ns : D₁.IsNonsingular := isNonsingular_of_iso' e hD
  have hD₁irr : D₁.IsIrreducible := irreducibleSpace_of_iso' e
  have hpts : ∀ y : V.toScheme, y ∈ D₁.pts ↔ V.ι y ∈ D.pts := fun y => by
    show y ∈ ((D.comap V.ι).support : Set V.toScheme) ↔ _
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have hV₁ : D₁.IsNormallyFlatAlong := by
    intro y hy
    obtain ⟨y', hy', hnf⟩ := hVD (V.ι y) ((hpts y).mp hy)
    rwa [V.ι.isEmbedding.injective hy'] at hnf
  have hW₁pts : ∀ y : V.toScheme, y ∈ W₁.pts ↔ V.ι y ∈ W.pts := fun y => by
    show y ∈ ((W.comap V.ι).support : Set V.toScheme) ↔ _
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have hW₁nf : W₁.IsNormallyFlatAlong' D₁ := by
    intro y hy
    rw [Subscheme.isNormallyFlatAlongAt'_iff W₁ D₁ hD₁W₁]
    have h := hWD (V.ι y) ((hpts y).mp hy)
    rw [Subscheme.isNormallyFlatAlongAt'_iff W D hDW] at h
    refine ⟨hy, ?_⟩
    obtain ⟨τ, hτ⟩ := Subscheme.exists_quotEquiv_totalTransform V W hWV y
    refine isNormallyFlatAlongIdeal_of_ringEquiv τ _ _ ?_ h.2
    have hD1y : D₁.stalkIdeal y = (D.stalkIdeal (V.ι y)).map (V.ι.stalkMap y).hom :=
      stalkIdeal_totalTransform V.ι D y
    rw [hD1y, Ideal.map_map, Ideal.map_map]
    congr 1
    ext a
    exact hτ a
  have hsimple₁ : ∀ y : V.toScheme, W.IsSimpleAt (V.ι y) ↔ W₁.IsSimpleAt y := fun y => by
    obtain ⟨τ, -⟩ := Subscheme.exists_quotEquiv_totalTransform V W hWV y
    constructor
    · rintro ⟨h1, h2⟩
      have := h2
      exact ⟨(hW₁pts y).mpr h1, IsRegularLocalRing.of_ringEquiv τ⟩
    · rintro ⟨h1, h2⟩
      have := h2
      exact ⟨(hW₁pts y).mp h1, IsRegularLocalRing.of_ringEquiv τ.symm⟩
  obtain ⟨x₀, hx₀, hs₀, hnf₀⟩ := hx
  obtain ⟨y₀, rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts V (pts_subset_of_isContainedIn hDV hx₀)
  obtain ⟨y', hy', hnf'⟩ := hnf₀
  have hy'eq := V.ι.isEmbedding.injective hy'
  subst hy'eq
  obtain ⟨hs, hn⟩ := Subscheme.isSimpleAt_and_isNormallyFlatAlongAt_of_normallyFlat_chain W₁ D₁
    hD₁W₁ hD₁ns hD₁irr hV₁ hW₁nf ⟨y', (hpts y').mpr hx₀, (hsimple₁ y').mp hs₀, hnf'⟩
  intro x hx
  obtain ⟨y, rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts V (pts_subset_of_isContainedIn hDV hx)
  exact ⟨(hsimple₁ y).mpr (hs y ((hpts y).mpr hx)), y, rfl, hn y ((hpts y).mpr hx)⟩

/-- Step 2: "by Corollary 4 of Proposition 1, §1, Ch. II, every point of `F'` must be a simple point
of `W'`.  Moreover, by Corollary of Theorem 3, §3, Ch. II, all the `V_j'` are normally flat along `W'`
at every point of `F'`" (p. 289).  Applied to the components `G` of `F'` (non-singular and irreducible,
by `cond₁_transform`) and the subschemes `W' ⊇ F'`, `V_j' ⊇ W'`: the hypotheses are the normal flatness
of `V_j'` and of `W'` along `F'` (`hres`), and the existence of a simple point of `W'` in `G` at which
`V_j'` is normally flat along `W'`, namely the generic point of `G`, which lies in `U'` where `ℜ'` is
resolved (`resolvedAt_of_isGenericPoint_prepF`).

Proved from `Subscheme.isSimpleAt_and_isNormallyFlatAlongAt'_of_chain` (the Ch. II input:
`cor:II.1-prop1-4` and `cor:II.3-thm3` transported to the schemes `V_j'` by `ι`; proved in this file).

Deviation from the paper (gap filled; statement modified): the Corollary of Theorem 3 is used in the
form `Subscheme.isSimpleAt_and_isNormallyFlatAlongAt'_of_chain` for the `V_j` of a datum (read in
`V_j` via `IsNormallyFlatAlongAt'`), and applied to the non-singular irreducible components `G` of `F'`
(non-singularity and irreducibility of `G` are tacit in the paper). -/
theorem isSimpleAt_and_isNormallyFlatAlongAt'_prepF_transform [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {Y : Scheme.{u}}
    {s : MonoidalSuccession X Y} {Q : PrepSetting Y} (hX : X.IsNonsingular) [IsAlgebraicScheme X]
    [IsAlgebraicScheme Y] (hs : s.IsPermissibleIOpen P.ℜ P.U) (hQ : P.IsTransform s Q)
    (hres : ((s.transformI P.ℜ).extendBy
      (s.strictTransform (P.ℜ.prepF P.E₁ P.U))).ResolvedEverywhere) :
    ∀ y ∈ (Q.ℜ.prepF Q.E₁ Q.U).pts, Q.ℜ.W.IsSimpleAt y ∧
      ∀ j, Subscheme.IsNormallyFlatAlongAt' (Q.ℜ.V j) Q.ℜ.W y := by
  classical
  intro y hy
  have hQℜ := hQ.1
  have hres₂ : (Q.ℜ.extendBy (s.strictTransform (P.ℜ.prepF P.E₁ P.U))).ResolvedEverywhere := by
    rw [hQℜ]; exact hres
  have hFpts := P.prepF_transform_pts_eq hX hs hQ
  set F' := s.strictTransform (P.ℜ.prepF P.E₁ P.U) with hF'
  set FQ := Q.ℜ.prepF Q.E₁ Q.U with hFQdef
  have hyF' : y ∈ F'.pts := hFpts ▸ hy
  have hFD : F'.pts ⊆ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts := hFpts ▸ Q.ℜ.pts_prepF_subset Q.E₁ Q.U
  have hprime : ∀ z ∈ F'.pts, (F'.stalkIdeal z).IsPrime := fun z hz => by
    have : IsRegularLocalRing (Y.presheaf.stalk z ⧸ F'.stalkIdeal z) := (hres₂ z hz).1.2
    exact (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
  -- the component `G` of `W_* ∩ E_1` through `y` and its generic point `η`
  obtain ⟨G, hG, hGU, hyG⟩ := Q.ℜ.exists_mem_irreducibleComponents_of_mem_pts_prepF' Q.E₁ Q.U hy
  obtain ⟨Z, hZmax, hGeq⟩ := id hG
  have hZpts : G.pts = Z := by
    rw [hGeq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  have hGF : G.pts ⊆ F'.pts := hFpts ▸ Q.ℜ.pts_subset_pts_prepF Q.E₁ Q.U hG hGU
  have hGred : G.IsReduced := by rw [hGeq]; exact Subscheme.ofClosed_isReduced Z
  have hGcomp : G ∈ F'.irreducibleComponents :=
    ⟨Z, ⟨⟨hZmax.1.1, hZpts ▸ hGF⟩, fun S hS hle => hZmax.2 ⟨hS.1, hS.2.trans hFD⟩ hle⟩, hGeq⟩
  have hGst : ∀ z ∈ G.pts, G.stalkIdeal z = F'.stalkIdeal z := by
    intro z hz
    have hm := Subscheme.stalkIdeal_mem_minimalPrimes hGcomp hz
    have := hprime z (hGF hz)
    exact le_antisymm (hm.2 ⟨this, le_rfl⟩ hm.1.2) hm.1.2
  have hGns : G.IsNonsingular := Subscheme.isNonsingular_of_stalk_quot G fun z hz => by
    rw [hGst z hz]; exact (hres₂ z (hGF hz)).1.2
  have hGirr : G.IsIrreducible :=
    Subscheme.isIrreducible_of_pts G (by rw [hZpts]; exact hZmax.1.1)
  have hGW : G.IsContainedIn Q.ℜ.W := Subscheme.isContainedIn_of_pts_subset hGred (fun z hz =>
    Q.ℜ.pts_prepWStar_subset Q.E₁ (Subscheme.mem_pts_inter_iff.mp (hFD (hGF hz))).1)
  obtain ⟨η, hη⟩ : ∃ η, IsGenericPoint η (Z : Set Y) := QuasiSober.sober hZmax.1.1 Z.isClosed
  have hmaxF : Maximal (fun S : Set Y => _root_.IsIrreducible S ∧ S ⊆ FQ.pts) (closure {η}) := by
    rw [hη.def]
    refine ⟨⟨hZmax.1.1, hFpts ▸ hZpts ▸ hGF⟩, fun S hS hle => ?_⟩
    have hcS : closure S ⊆ FQ.pts := closure_minimal hS.2 FQ.support.isClosed
    have hT := hZmax.2 (y := ⟨closure S, isClosed_closure⟩) ⟨hS.1.closure, (hFpts ▸ hcS).trans hFD⟩
      (hle.trans subset_closure)
    exact subset_closure.trans hT
  have hηU : η ∈ Q.U := Q.mem_U_of_isGenericPoint_prepF hmaxF
  obtain ⟨hηWs, hηVf, -⟩ := Q.hU.2.2 η hηU
  have hηG : η ∈ G.pts := hZpts ▸ hη.mem
  -- the normal flatness hypotheses along `G`
  have hnfG : ∀ z ∈ G.pts, ∀ j' : Fin (Q.ℜ.β + 1),
      Subscheme.IsNormallyFlatAlongAt' ((Q.ℜ.extendBy F').V j') G z := fun z hz j' =>
    Subscheme.isNormallyFlatAlongAt'_congr _ F' G (hGst z hz).symm ((hres₂ z (hGF hz)).2.1 j')
  have hVlast : (Q.ℜ.extendBy F').V (Fin.last Q.ℜ.β) = Q.ℜ.W := by
    simp [DatumI.Raw.extendBy]
  have hVcast : ∀ j : Fin Q.ℜ.β, (Q.ℜ.extendBy F').V j.castSucc = Q.ℜ.V j := fun j => by
    simp [DatumI.Raw.extendBy]
  have hWD : ∀ z ∈ G.pts, Subscheme.IsNormallyFlatAlongAt' Q.ℜ.W G z := fun z hz => by
    have := hnfG z hz (Fin.last Q.ℜ.β)
    rwa [hVlast] at this
  have hsimple := Subscheme.isSimpleAt_and_isNormallyFlatAlongAt'_of_chain Q.ℜ.W Q.ℜ.W G
    (fun U => le_rfl) hGW hGns hGirr hWD hWD
    ⟨η, hηG, hηWs, Subscheme.isNormallyFlatAlongAt'_of_isSimpleAt (fun U => le_rfl) hηWs hηWs⟩
  refine ⟨(hsimple y hyG).1, fun j => ?_⟩
  have hVD : ∀ z ∈ G.pts, Subscheme.IsNormallyFlatAlongAt' (Q.ℜ.V j) G z := fun z hz => by
    have := hnfG z hz j.castSucc
    rwa [hVcast] at this
  exact (Subscheme.isSimpleAt_and_isNormallyFlatAlongAt'_of_chain (Q.ℜ.V j) Q.ℜ.W G
    (Q.hℜ.2.2.2.2 j) hGW hGns hGirr hVD hWD ⟨η, hηG, hηWs, hηVf j⟩ y hyG).2

/-- Step 2: "for `i ≥ 2` and `j`, `E_i` containing `F_j` must contain the unique irreducible component
of `W` containing `F_j`.  Since the above morphism `f` induces an isomorphism of
`X' − f⁻¹(W − U)` onto `X − (W − U)`, it follows that for `i ≥ 2`, `E_i'` containing an irreducible
component `F_j'` of `F'` must contain the unique irreducible component of `W'` containing `F_j'`"
(p. 289), in the stalk form: at a point `y` of `F'`, a component `E_j'` of the tail whose ideal lies in
the ideal of `F'` lies in the ideal of `W'`.

Proof, as printed.  (1) On `X` (first sentence): `rest_stalkIdeal_le_of_prepF` for `P`, at a point
`η ∈ U` of `F` with `F_η = M_η`: `ℜ` is resolved at `η ∈ U`, `W_η + E_{1,η}` is the maximal ideal, so
every `E_{i,η} ≠ E_{1,η}` through `η` lies in `W_η`.  (2) Transport along the isomorphism (second
sentence): the centers of `f` avoid `U₀ = X − (W − U)` (`MonoidalSuccession.exists_lift_of_centersAvoid`),
so `f` is an isomorphism over `U₀`, an open embedding `ι₁ : U₀ → X'` onto `f⁻¹(U₀)` which pulls back
the strict transforms to the pull-backs (`hst`); at the generic point `η'` of the component `F_j'`
through `y` (which lies in `U' = f⁻¹(U)`, and over which `F'_{η'} = M_{η'}`), the stalk ideals of
`E_i'`, `W'`, `F'` correspond to those of `E_i`, `W`, `F` at `η = f(η')`
(`stalkIdeal_totalTransform_le_iff`, `stalkIdeal_totalTransform_eq_maximalIdeal_iff`), so (1)
applies and gives `E'_{j,η'} ⊆ W'_{η'}`.  The exceptional components `E_j'`, `j > α`, do not pass
through `η'` (they lie over the centers, which avoid `U`).  (3) The conclusion at `y` follows by
contraction (`stalkIdeal_le_of_stalkIdeal_le_of_specializes`: `O_{η'}` is the localization of `O_y`
at the prime `F'_y`).

Deviation from the paper (gap filled): the unique-component statement ("must contain the unique
irreducible component") is tacit and is used here in its stalk form; the hypotheses `hcast`, `hexc`
record the presentation of the transformed boundary (the `E_i'` for `i ≤ α` are the strict transforms
of the `E_i`, the others are exceptional, `MonoidalSuccession.exists_presentation_transformI_tail`). -/
theorem rest_stalkIdeal_le_of_stalkIdeal_le_prepF [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {Y : Scheme.{u}}
    {s : MonoidalSuccession X Y} {Q : PrepSetting Y} (hX : X.IsNonsingular) [IsAlgebraicScheme X]
    [IsAlgebraicScheme Y] (_hY : Y.IsNonsingular) (hs : s.IsPermissibleIOpen P.ℜ P.U) (hQ : P.IsTransform s Q)
    (hα : P.α ≤ Q.α)
    (hcast : ∀ i : Fin P.α, Q.E (Fin.castLE hα i) = s.strictTransform (P.E i))
    (hexc : ∀ j : Fin Q.α, P.α ≤ j.val → Q.E j ∈ s.exceptionalDivisors)
    (hres : ((s.transformI P.ℜ).extendBy
      (s.strictTransform (P.ℜ.prepF P.E₁ P.U))).ResolvedEverywhere) :
    ∀ y ∈ (Q.ℜ.prepF Q.E₁ Q.U).pts, ∀ j : Fin Q.α, Q.E j ≠ Q.E₁ →
      (Q.E j).stalkIdeal y ≤ (Q.ℜ.prepF Q.E₁ Q.U).stalkIdeal y →
        (Q.E j).stalkIdeal y ≤ Q.ℜ.W.stalkIdeal y := by
  classical
  intro y hy j hj hle
  have hFeq := P.prepF_transform_eq hX hs hQ hres
  have hFpts := P.prepF_transform_pts_eq hX hs hQ
  have hyF' : y ∈ (s.strictTransform (P.ℜ.prepF P.E₁ P.U)).pts := hFpts ▸ hy
  have hWs := (P.isSimpleAt_and_isNormallyFlatAlongAt'_prepF_transform hX hs hQ hres y hy).1
  have hreg : IsRegularLocalRing (Y.presheaf.stalk y ⧸
      (s.strictTransform (P.ℜ.prepF P.E₁ P.U)).stalkIdeal y) := (hres y hyF').1.2
  have hFprime : ((Q.ℜ.prepF Q.E₁ Q.U).stalkIdeal y).IsPrime := by
    rw [hFeq]
    exact (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
  have hWyreg : IsRegularLocalRing (Y.presheaf.stalk y ⧸ Q.ℜ.W.stalkIdeal y) := hWs.2
  have hWy : (Q.ℜ.W.stalkIdeal y).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
  -- reduction to the generic point `η'` of the component `F_j'` through `y`
  obtain ⟨G, η', hη'y, hη'U, hη'F, hFη', hη'E, hGη', hGy, hWG⟩ :=
    Q.exists_isGenericPoint_of_mem_prepF hy hFprime (Q.E j) hle
  refine stalkIdeal_le_of_stalkIdeal_le_of_specializes hη'y G Q.ℜ.W (Q.E j) hGη'
    (hGy ▸ hFprime) hWy hWG ?_
  obtain ⟨hQℜ, hQU, hQE⟩ := hQ
  have hQUeq : Q.U = s.composite.base ⁻¹' P.U := by rw [hQU, MonoidalSuccession.transformOpen_eq]
  have hηP : s.composite.base η' ∈ P.U := by rw [← Set.mem_preimage, ← hQUeq]; exact hη'U
  -- the exceptional components do not pass through `η'`
  by_cases hjα : P.α ≤ j.val
  · exfalso
    have havoid := s.centersAvoid_of_isPermissibleIOpen P.ℜ P.U P.U hs (fun _ _ h => h)
    exact s.composite_base_notMem_of_mem_exceptionalDivisors havoid (hexc j hjα) η' hη'E hηP
  -- `E_j'` is the strict transform of `E_i`
  have hjlt : j.val < P.α := by omega
  set i : Fin P.α := ⟨j.val, hjlt⟩ with hi
  have hji : j = Fin.castLE hα i := Fin.ext rfl
  have hEj : Q.E j = s.strictTransform (P.E i) := by rw [hji]; exact hcast i
  have hiE₁ : P.E i ≠ P.E₁ := by
    intro h
    apply hj
    rw [hEj, h, hQE]
  -- the isomorphism over `U₀ = X − (W − U)`
  have : TopologicalSpace.NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  obtain ⟨⟨U₀, hU₀, hUeq⟩, -, -⟩ := P.hU
  let U₀' : X.Opens := ⟨U₀, hU₀⟩
  let ι : Scheme.Opens.toScheme U₀' ⟶ X := Scheme.Opens.ι U₀'
  have hrange : Set.range ι.base = U₀ := Scheme.Opens.range_ι U₀'
  have hs' : s.CentersAvoid (Set.range ι.base) :=
    s.centersAvoid_of_isPermissibleIOpen P.ℜ P.U _ hs (fun y hyW hyR => by
      rw [hUeq]; exact ⟨hrange ▸ hyR, hyW⟩)
  obtain ⟨ι₁, hfl, hpre, hcomp, hr, hst, -⟩ := s.exists_lift_of_centersAvoid ι hs'
  have hηU₀ : s.composite.base η' ∈ Set.range ι.base := by
    rw [hrange]; rw [hUeq] at hηP; exact hηP.1
  have hη'r : η' ∈ Set.range ι₁.base := by rw [hr]; exact hηU₀
  obtain ⟨v, hv⟩ := hη'r
  have hcv : s.composite.base η' = ι.base v := by
    rw [← hv]
    have := congrArg (fun φ => φ.base v) hcomp
    simpa using this
  -- transport of stalk ideals: `V₁_η ≤ V₂_η ↔ (V₁)'_η' ≤ (V₂)'_η'`, `V_η = M_η ↔ V'_η' = M_η'`
  have hle_iff : ∀ V₁ V₂ : Subscheme X,
      (s.strictTransform V₁).stalkIdeal η' ≤ (s.strictTransform V₂).stalkIdeal η' ↔
        V₁.stalkIdeal (ι v) ≤ V₂.stalkIdeal (ι v) := by
    intro V₁ V₂
    have h1 := stalkIdeal_totalTransform_le_iff ι₁ (s.strictTransform V₁) (s.strictTransform V₂) v
    have h2 := stalkIdeal_totalTransform_le_iff ι V₁ V₂ v
    rw [hst V₁, hst V₂] at h1
    rw [← hv]
    exact h1.symm.trans h2
  have hmax_iff : ∀ V : Subscheme X,
      (s.strictTransform V).stalkIdeal η' = IsLocalRing.maximalIdeal (Y.presheaf.stalk η') ↔
        V.stalkIdeal (ι v) = IsLocalRing.maximalIdeal (X.presheaf.stalk (ι v)) := by
    intro V
    have h1 := stalkIdeal_totalTransform_eq_maximalIdeal_iff ι₁ (s.strictTransform V) v
    have h2 := stalkIdeal_totalTransform_eq_maximalIdeal_iff ι V v
    rw [hst V] at h1
    rw [← hv]
    exact h1.symm.trans h2
  -- the first sentence, on `X`, at the point `η = f(η')` of `U`
  have hηU : ι v ∈ P.U := by
    rw [show (ι v : X) = ι.base v from rfl, ← hcv]; exact hηP
  have hηF : ι v ∈ (P.ℜ.prepF P.E₁ P.U).pts := by
    have h1 : η' ∈ (s.strictTransform (P.ℜ.prepF P.E₁ P.U)).pts := hFpts ▸ hη'F
    have := s.pts_strictTransform_subset _ h1
    rw [Set.mem_preimage, hcv] at this
    exact this
  have hFη : (P.ℜ.prepF P.E₁ P.U).stalkIdeal (ι v) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (ι v)) :=
    (hmax_iff _).mp (by rw [← hFeq]; exact hFη')
  have hηEi : ι v ∈ (P.E i).pts := by
    have h1 : η' ∈ (s.strictTransform (P.E i)).pts := hEj ▸ hη'E
    have := s.pts_strictTransform_subset _ h1
    rw [Set.mem_preimage, hcv] at this
    exact this
  have hX1 := P.rest_stalkIdeal_le_of_prepF hX hηF (P.hU.2.2 (ι v) hηU).1
    (by rw [hFη]; exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime) hiE₁
    (by rw [hFη]; exact Subscheme.stalkIdeal_le_maximalIdeal (P.E i) hηEi)
  -- the second sentence: transport to `X'` along the isomorphism over `U₀`
  rw [hEj, hQℜ, MonoidalSuccession.transformI_W, hle_iff]
  exact hX1

/-- Step 2, conclusion (2) (p. 289): "In virtue of Lemma 3, the resolution datum
`(⋃_{i≥2} E_i'; V_1', …, V_β'; W')` on `X'` must be resolved at every point of `F'`.  Thus we may
assume … (2) there exists an open subset `Ũ` of `W` which contains `U` and `F`, and such that
`(⋃_{i≥2} E_i; V; W)` is resolved at every point of `Ũ`."  The open set is the set of points of `W'`
at which the tail datum is resolved (open in `W'` by Lemma 1 of Ch. IV §1, `resolvedSetIsOpen_holds`);
it contains `U'` (the datum `ℜ'` is resolved there, and a subfamily of a family with normal crossings
has normal crossings) and `F'` (simple points and normal flatness by
`isSimpleAt_and_isNormallyFlatAlongAt'_prepF_transform`, normal crossings by Lemma 3 in the pointwise
form `Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_of_prime_flag`, with its hypothesis (iii) from
`rest_stalkIdeal_le_of_stalkIdeal_le_prepF`).

Deviation from the paper (gap filled): the choice of `Ũ` as the set of resolved points, whose openness is
Lemma 1 of Ch. IV §1, and the verification that the tail is a datum (`isDatum_rest`), are tacit. -/
theorem cond₂_transform_resolvedSet [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {Y : Scheme.{u}} {s : MonoidalSuccession X Y}
    {Q : PrepSetting Y}
    (hX : X.IsNonsingular) [IsAlgebraicScheme X] [IsAlgebraicScheme Y] (hY : Y.IsNonsingular)
    (hs : s.IsPermissibleIOpen P.ℜ P.U) (hQ : P.IsTransform s Q)
    (hα : P.α ≤ Q.α)
    (hcast : ∀ i : Fin P.α, Q.E (Fin.castLE hα i) = s.strictTransform (P.E i))
    (hexc : ∀ j : Fin Q.α, P.α ≤ j.val → Q.E j ∈ s.exceptionalDivisors)
    (hres : ((s.transformI P.ℜ).extendBy
      (s.strictTransform (P.ℜ.prepF P.E₁ P.U))).ResolvedEverywhere) :
    Q.Cond₂ {y ∈ ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).W.pts |
      ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).ResolvedAt y} := by
  classical
  have hFeq := P.prepF_transform_eq hX hs hQ hres
  have hFpts := P.prepF_transform_pts_eq hX hs hQ
  have hQℜ := hQ.1
  set R' : DatumI.Raw Y := { Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } with hR'
  have hR'dat := Q.isDatum_rest hY
  obtain ⟨U₀, hU₀, hUeq⟩ := resolvedSetIsOpen_holds Y inferInstance hY R' hR'dat
  refine ⟨⟨U₀, hU₀, hUeq⟩, ?_, ?_, fun x hx => hx.2⟩
  · intro y hy
    obtain ⟨hWs, hVf, hnc⟩ := Q.hU.2.2 y hy
    refine ⟨hWs.1, hWs, hVf, ?_⟩
    show (prepERest Q.E ⟨0, Q.hα⟩).HasOnlyNormalCrossingsWithAt Q.ℜ.W y
    exact Subscheme.hasOnlyNormalCrossingsWithAt_prepERest hY Q.E Q.hE _ (Q.hEunion ▸ hnc)
  · intro y hy
    have hyW : y ∈ Q.ℜ.W.pts := Q.ℜ.pts_prepWStar_subset Q.E₁
      (Subscheme.mem_pts_inter_iff.mp (Q.ℜ.pts_prepF_subset Q.E₁ Q.U hy)).1
    obtain ⟨hWs, hVf⟩ := P.isSimpleAt_and_isNormallyFlatAlongAt'_prepF_transform hX hs hQ hres y hy
    refine ⟨hyW, hWs, hVf, ?_⟩
    show (prepERest Q.E ⟨0, Q.hα⟩).HasOnlyNormalCrossingsWithAt Q.ℜ.W y
    have hyF' : y ∈ (s.strictTransform (P.ℜ.prepF P.E₁ P.U)).pts := hFpts ▸ hy
    have hnc : (Subscheme.unionFam Q.E).HasOnlyNormalCrossingsWithAt (Q.ℜ.prepF Q.E₁ Q.U) y := by
      rw [hFeq, ← Q.hEunion, hQℜ]
      exact (hres y hyF').2.2
    have hFred : (Q.ℜ.prepF Q.E₁ Q.U).IsReduced := Subscheme.ofClosed_isReduced _
    have hQF : Q.ℜ.W.stalkIdeal y ≤ (Q.ℜ.prepF Q.E₁ Q.U).stalkIdeal y :=
      Subscheme.stalkIdeal_mono (fun U => Subscheme.isContainedIn_of_pts_subset hFred
        (fun z hz => Q.ℜ.pts_prepWStar_subset Q.E₁ (Subscheme.mem_pts_inter_iff.mp
          (Q.ℜ.pts_prepF_subset Q.E₁ Q.U hz)).1) U) y
    exact Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_of_prime_flag hY
      (fun i : {i : Fin Q.α // Q.E i ≠ Q.E ⟨0, Q.hα⟩} => Q.E i) (fun i => Q.hE i) hWs
      (Subscheme.hasOnlyNormalCrossingsWithAt_prepERest hY Q.E Q.hE _ hnc) hQF
      (fun j => P.rest_stalkIdeal_le_of_stalkIdeal_le_prepF hX hY hs hQ hα hcast hexc hres y hy j.1 j.2)

/-- Condition (2) for the transform `Q` of `P` (p. 289); see `cond₂_transform_resolvedSet`. -/
theorem cond₂_transform [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {Y : Scheme.{u}} {s : MonoidalSuccession X Y} {Q : PrepSetting Y}
    (hX : X.IsNonsingular) [IsAlgebraicScheme X] [IsAlgebraicScheme Y] (hY : Y.IsNonsingular)
    (hs : s.IsPermissibleIOpen P.ℜ P.U) (hQ : P.IsTransform s Q)
    (hα : P.α ≤ Q.α)
    (hcast : ∀ i : Fin P.α, Q.E (Fin.castLE hα i) = s.strictTransform (P.E i))
    (hexc : ∀ j : Fin Q.α, P.α ≤ j.val → Q.E j ∈ s.exceptionalDivisors)
    (hres : ((s.transformI P.ℜ).extendBy
      (s.strictTransform (P.ℜ.prepF P.E₁ P.U))).ResolvedEverywhere) :
    ∃ Ubar, Q.Cond₂ Ubar :=
  ⟨_, P.cond₂_transform_resolvedSet hX hY hs hQ hα hcast hexc hres⟩

/-- Step 3, "Then in view of Lemma 4 of this section and Corollary 2 of Theorem 5, §6, Ch. III, the
resolution datum `(⋃_{i≥2} E_i'; V_1', …, V_β'; W')` is resolved at every point of `Ũ'`" (p. 290), with
`Ũ' = f⁻¹(Ũ) ∩ W'`: for a point `y` of `W'` over `Ũ`, the tail `(⋃_{E_j' ≠ E_1'} E_j'; V'; W')` of the
presentation of `f*(ℜ)` is resolved at `y`.  The hypothesis `hJ3` says that the boundary of `f*` of the
tail datum of `ℜ` is the sub-union `⋃_{j∈J'} E_j'` of the presentation, `J'` containing all the `j`
with `E_j' ≠ E_1'` (`MonoidalSuccession.exists_presentation_transformI_tail`).

Deviation from the paper (gap filled): see `MonoidalSuccession.resolvedAt_transformI_tail` (the
tail is a datum, `U` is an open restriction for it, the succession is permissible for it) and, in
addition, that a sub-union of the components of the boundary has again only normal crossings with `W'`
(`Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_comp`), which is how the tail `⋃_{i≥2} E_i'` of the
paper's presentation is compared with `f*` of the tail datum. -/
theorem tail_resolvedAt_transform [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} {Y : Scheme.{u}} {s : MonoidalSuccession X Y}
    {Q : PrepSetting Y} (hX : IsAmbient X N) (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) (hY : Y.IsNonsingular)
    (hs : s.IsPermissibleIOpen P.ℜ P.U) (hQ : P.IsTransform s Q) {Ubar : Set X}
    (hC2 : P.Cond₂ Ubar) (J' : Set (Fin Q.α))
    (hJ3 : (s.transformI ({ P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ } : DatumI.Raw X)).E =
      Subscheme.unionFam (fun j : J' => Q.E j))
    (hJ' : ∀ j, Q.E j ≠ Q.E ⟨0, Q.hα⟩ → j ∈ J') {y : Y} (hyW : y ∈ Q.ℜ.W.pts)
    (hyU : s.composite.base y ∈ Ubar) :
    ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).ResolvedAt y := by
  have hQℜ := hQ.1
  have hyW' : y ∈ (s.transformI P.ℜ).W.pts := hQℜ ▸ hyW
  have hres0 := hC2.2.2.2 _ hyU
  have hR := MonoidalSuccession.resolvedAt_transformI_tail s P.E P.hE (N := N) (n := n)
    ⟨hX, P.hℜ, hP⟩ P.hEunion P.hU hs {i | P.E i ≠ P.E ⟨0, P.hα⟩} hyW' hres0
  let R : DatumI.Raw X := { P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ }
  have hR' : ({ s.transformI P.ℜ with E := (s.transformI R).E } : DatumI.Raw Y).ResolvedAt y := by
    rw [← MonoidalSuccession.transformI_withE]
    exact hR
  obtain ⟨hS, hNF, hnc⟩ := hR'
  rw [hQℜ]
  refine ⟨hS, hNF, ?_⟩
  show (prepERest Q.E ⟨0, Q.hα⟩).HasOnlyNormalCrossingsWithAt (s.transformI P.ℜ).W y
  have hnc' : (Subscheme.unionFam (fun j : J' => Q.E j)).HasOnlyNormalCrossingsWithAt
      (s.transformI P.ℜ).W y := hJ3 ▸ hnc
  exact Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_comp hY (fun j : J' => Q.E j)
    (fun j => Q.hE j) (fun k : {i : Fin Q.α // Q.E i ≠ Q.E ⟨0, Q.hα⟩} => ⟨k.1, hJ' k.1 k.2⟩) hnc'

/-- Step 2 (p. 289).  "We shall consider the resolution datum `(ℜ̄, F ∩ U)` on `X` with open
restriction `F ∩ U`. As is easily seen, a permissible succession of monoidal transformations of
`X` for `(ℜ̄, F ∩ U)` is such a succession for `(ℜ, U)`.  Since `n̄ < n` we can apply Theorem
I₂ to `(ℜ̄, F ∩ U)` and find a permissible succession `f : X' → X` for `(ℜ̄, F ∩ U)` such that
`f*(ℜ̄)` is resolved at every point of the strict transform `F'` of `F`. … Since `f*(ℜ̄)` is
resolved at every point of `F'`, `F'` is non-singular and `V_1', …, V_β', W'` are all normally
flat along `F'`.  In particular, by Corollary 4 of Proposition 1, §1, Ch. II, every point of `F'`
must be a simple point of `W'`.  Moreover, by Corollary of Theorem 3, §3, Ch. II, all the `V_j'`
are normally flat along `W'` at every point of `F'`.  On the other hand, … for `i ≥ 2` any `E_i`
containing an irreducible component `F_j'` of `F'` must contain the unique irreducible
component of `W'` containing `F_j'`.  In virtue of Lemma 3, the resolution datum
`(⋃_{i≥2} E_i'; V_1', …, V_β'; W')` must be resolved at every point of `F'`.  Thus we may
assume … (1) … (2)".

Deviation from the paper (gap filled): the application of Lemma 3 requires the
presentation `⋃ E_i'` of the transform (strict transforms of the `E_i`, exceptional divisors), a
convention of the paper; and the unique-component statements are tacit.

Status: proved from `exists_isPermissibleIOpen_resolvedEverywhere_extendBy_prepF` ((a), (b)), the
presentation lemmas ((c)), `IsGoodDatumI.succession_open`, `prepF_transform_pts_eq` and `cond₁_transform`
((d)) and `cond₂_transform` ((e)); the Ch. II input it uses is
`Subscheme.isSimpleAt_and_isNormallyFlatAlongAt'_of_chain` (Corollaries 4 of Prop. 1 and of Th. 3 for
the `V_j` of a datum).  Plan.  (a) Step 1 (`isDatum_and_isOpenRestriction_extendBy_prepF`,
proved) gives the datum `ℜ̄ = ℜ.extendBy F` with open restriction `F ∩ U` and `n̄ < n`; if `F` is
empty take `f = id`, otherwise `n̄ = dim F` is a natural number `< n` and `hI₂ n̄` applies, giving a
succession `s` permissible for `(ℜ̄, F ∩ U)` with `s.transformI ℜ̄` resolved everywhere.
(b) `MonoidalSuccession.isPermissibleIOpen_of_isPermissibleIOpen_extendBy` (proved) shows that `s` is
permissible for `(ℜ, U)`.  (c) Build the `PrepSetting` of the transform `Q` with
`MonoidalSuccession.exists_presentation_transformI` (proved; the presentation `E'` with `E_1'` the
strict transform of `E_1`), `DatumI.Raw.transform_isDatum`-type lemmas for `Q.hℜ`, the open
restriction `transformOpen U`, `IsAmbient` of the target and `dim W' ≤ dim W`.  (d) `Q.Cond₁`: the
new `F` is the strict transform `F'` of `F` (components of `W'_* ∩ E_1'` meeting `U'`, where
`W'_* ∩ E_1' ⊇ (W_* ∩ E_1)'` and every other component lies in some `W' ∩ E_j'`, `j > α`): `F'` is
non-singular and a disjoint union because `ℜ̄' = s.transformI ℜ̄` is resolved at `F'`
(Definition 4: simple points of `F'`), and `E'` has normal crossings with `F'` by the same
resolvedness.  (e) `Q.Cond₂`: with `Ũ' = f⁻¹(Ũ) ∩ W'`, Lemma 4 (applied on a neighbourhood,
`DatumI.Raw.hasOnlyNormalCrossingsWithAt_transform_of_resolvedAt_localized`) gives the resolvedness of
`(⋃_{i≥2} E_i'; V'; W')` on `Ũ'`, and on `F'` Lemma 3 (the variant
`Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_of_stalkIdeal_le`) with Corollary 4 of Proposition
1 (Ch. II) and the Corollary of Theorem 3 (Ch. II, §3) for the simple points of `W'` and the
normal flatness of the `V_j'` along `W'` at the points of `F'`; the hypothesis "`E_i'` containing
`F_j'` contains the component of `W'` through it" comes from `X' − f⁻¹(W−U) ≅ X − (W−U)`. -/
theorem stepTo_stage₁₂ [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {N n : ℕ} (hX : IsAmbient X N) (hP : P.ℜ.n ≤ (n : WithBot ℕ∞))
    (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'') :
    P.StepTo N n (fun _ Q => Q.Stage₁₂) := by
  classical
  have := hX.1
  obtain ⟨Y, s, hs, hres⟩ :=
    P.exists_isPermissibleIOpen_resolvedEverywhere_extendBy_prepF hX hP hI₂
  obtain ⟨⟨hY, hdat, hdim⟩, hopen⟩ := IsGoodDatumI.succession_open s ⟨hX, P.hℜ, hP⟩ P.hU hs
  obtain ⟨α', hα', E', hE', hEq', hcs, -, -, -, -, -, -, -, hexc⟩ :=
    s.exists_presentation_transformI_tail hX.1 hX.2.1 P.E P.hE P.ℜ P.hℜ P.hEunion hs.isPermissibleI ∅
  have := hY.1
  let Q : PrepSetting Y := ⟨α', P.hα.trans_le hα', E', hE', s.transformI P.ℜ, hdat, hEq',
    s.transformOpen P.U, hopen⟩
  have hQ : P.IsTransform s Q := ⟨rfl, rfl, hcs ⟨0, P.hα⟩⟩
  rw [MonoidalSuccession.transformI_extendBy] at hres
  exact ⟨Y, s, Q, hs, hQ, hY, hdim, P.cond₁_transform hX.2.1 hs hQ hres,
    P.cond₂_transform hX.2.1 hY.2.1 hs hQ hα' hcs hexc hres⟩

/-- The datum `ℜ̄ = (⋃ E_i; V_1, …, V_β, W, W_* ∩ E_1; F)` of step 3 (p. 290): the datum `ℜ` with `W` and
`W_* ∩ E_1` adjoined to the `V_j` and `F` as principal subscheme. -/
noncomputable def barℜ : DatumI.Raw X :=
  (P.ℜ.extendBy ((P.ℜ.prepWStar P.E₁).inter P.E₁)).extendBy (P.ℜ.prepF P.E₁ P.U)

/-- `ℜ̄` of step 3 is a datum: `F` is reduced and contained in `W`, in `W_* ∩ E_1` and in the `V_j`. -/
theorem isDatum_barℜ : P.barℜ.IsDatum := by
  have hFred : (P.ℜ.prepF P.E₁ P.U).IsReduced := Subscheme.ofClosed_isReduced _
  have hFD : (P.ℜ.prepF P.E₁ P.U).pts ⊆ ((P.ℜ.prepWStar P.E₁).inter P.E₁).pts :=
    P.ℜ.pts_prepF_subset P.E₁ P.U
  have hFW : (P.ℜ.prepF P.E₁ P.U).pts ⊆ P.ℜ.W.pts := fun y hy =>
    P.ℜ.pts_prepWStar_subset P.E₁ (Subscheme.mem_pts_inter_iff.mp (hFD hy)).1
  have hFWc : (P.ℜ.prepF P.E₁ P.U).IsContainedIn P.ℜ.W :=
    Subscheme.isContainedIn_of_pts_subset hFred hFW
  refine ⟨P.hℜ.1, P.hℜ.2.1, P.hℜ.2.2.1, hFred, fun j => ?_⟩
  induction j using Fin.lastCases with
  | last => simpa only [barℜ, DatumI.Raw.extendBy, Fin.snoc_last] using
      Subscheme.isContainedIn_of_pts_subset hFred hFD
  | cast j =>
    induction j using Fin.lastCases with
    | last => simpa only [barℜ, DatumI.Raw.extendBy, Fin.snoc_last, Fin.snoc_castSucc] using hFWc
    | cast j =>
      simp only [barℜ, DatumI.Raw.extendBy, Fin.snoc_castSucc]
      exact fun U => (P.hℜ.2.2.2.2 j U).trans (hFWc U)

/-- `ℜ̄` is resolved at the points of `F ∩ U` (p. 290: "Let us consider the following resolution datum
`ℜ̄ … with open restriction `U ∩ F`"): as for `ℜ.extendBy F`, and `W_* ∩ E_1` is normally flat along
`F` at `x ∈ F ∩ U` because `(W_* ∩ E_1)_x = F_x` there (`stalkIdeal_prepF_eq_sup`).

Deviation from the paper (gap filled): tacit.  The paper's `W_* ∩ E_1` is the subscheme with the sum of
the ideal sheaves (`Subscheme.inter`). -/
theorem resolvedAt_barℜ [IsAlgebraicScheme X] (hX : X.IsNonsingular) {x : X}
    (hxF : x ∈ (P.ℜ.prepF P.E₁ P.U).pts) (hxU : x ∈ P.U) : P.barℜ.ResolvedAt x := by
  classical
  obtain ⟨hFs, hnf, hnc⟩ := P.resolvedAt_extendBy_prepF hX hxF hxU
  set F := P.ℜ.prepF P.E₁ P.U with hFdef
  set B := (P.ℜ.prepWStar P.E₁).inter P.E₁ with hB
  have hFred : F.IsReduced := Subscheme.ofClosed_isReduced _
  have hFD : F.pts ⊆ B.pts := P.ℜ.pts_prepF_subset P.E₁ P.U
  have hFB : F.IsContainedIn B := Subscheme.isContainedIn_of_pts_subset hFred hFD
  have hWst : P.ℜ.W.stalkIdeal x ≤ (P.ℜ.prepWStar P.E₁).stalkIdeal x := by
    have hred : (P.ℜ.prepWStar P.E₁).IsReduced := Subscheme.ofClosed_isReduced _
    exact Subscheme.stalkIdeal_mono (fun U => Subscheme.isContainedIn_of_pts_subset hred
      (P.ℜ.pts_prepWStar_subset P.E₁) U) x
  have hBx : B.stalkIdeal x = F.stalkIdeal x := by
    refine le_antisymm (Subscheme.stalkIdeal_mono (fun U => hFB U) x) ?_
    rw [hFdef, P.stalkIdeal_prepF_eq_sup hX hxF hxU, hB, Subscheme.inter, Subscheme.stalkIdeal_sup_eq]
    exact sup_le_sup_right hWst _
  have hBs : B.IsSimpleAt x := ⟨hFD hxF, by
    rw [hBx]; exact hFs.2⟩
  refine ⟨hFs, fun j => ?_, hnc⟩
  induction j using Fin.lastCases with
  | last =>
    simp only [barℜ, DatumI.Raw.extendBy, Fin.snoc_last]
    exact Subscheme.isNormallyFlatAlongAt'_of_isSimpleAt hFB hBs hFs
  | cast j =>
    have e : P.barℜ.V j.castSucc = (P.ℜ.extendBy F).V j := by
      simp only [barℜ, DatumI.Raw.extendBy]
      exact Fin.snoc_castSucc (α := fun _ => Subscheme X) _ _ j
    show (P.barℜ.V j.castSucc).IsNormallyFlatAlongAt' F x
    rw [e]
    exact hnf j

/-- `ℜ̄` has the open restriction `F ∩ U` (p. 290). -/
theorem isOpenRestriction_barℜ [IsAlgebraicScheme X] (hX : X.IsNonsingular) :
    P.barℜ.IsOpenRestriction ((P.ℜ.prepF P.E₁ P.U).pts ∩ P.U) := by
  obtain ⟨h1, h2, -⟩ := P.isOpenRestriction_extendBy_prepF hX
  exact ⟨h1, h2, fun x hx => P.resolvedAt_barℜ hX hx.1 hx.2⟩

/-- Step 3, first sentences (p. 290): "By Theorem I₂ we have a permissible succession of monoidal
transformations of `X` for `(ℜ̄, U ∩ F)`, say `f : X' → X`, such that `f*(ℜ̄)` is resolved at every
point of the strict transform `F'` of `F`.  It is clear that `f` is permissible for `(ℜ, U)`."

Deviation from the paper (gap filled): as for step 2 (`exists_isPermissibleIOpen_resolvedEverywhere_extendBy_prepF`):
the dimension `n̄ = dim F < n`, the case `F = ∅`, and "it is clear" (two applications of
`isPermissibleIOpen_of_isPermissibleIOpen_extendBy`, for `F ⊆ W_* ∩ E_1` and `W_* ∩ E_1 ⊆ W`). -/
theorem exists_isPermissibleIOpen_resolvedEverywhere_barℜ {N n : ℕ}
    (hX : IsAmbient X N) (hP : P.ℜ.n ≤ (n : WithBot ℕ∞))
    (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'') :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsPermissibleIOpen P.ℜ P.U ∧
      s.IsPermissibleIOpen P.barℜ ((P.ℜ.prepF P.E₁ P.U).pts ∩ P.U) ∧
      (s.transformI P.barℜ).ResolvedEverywhere := by
  classical
  have := hX.1
  set F := P.ℜ.prepF P.E₁ P.U with hFdef
  set B := (P.ℜ.prepWStar P.E₁).inter P.E₁ with hB
  rcases F.pts.eq_empty_or_nonempty with hFe | hFne
  · refine ⟨X, MonoidalSuccession.nil X, trivial, trivial, fun x hx => ?_⟩
    exact absurd hx (by
      show x ∉ F.pts
      rw [hFe]; exact id)
  · have hFW : F.pts ⊆ P.ℜ.W.pts := fun y hy =>
      P.ℜ.pts_prepWStar_subset P.E₁ (Subscheme.mem_pts_inter_iff.mp
        (P.ℜ.pts_prepF_subset P.E₁ P.U hy)).1
    have hFD : F.pts ⊆ B.pts := P.ℜ.pts_prepF_subset P.E₁ P.U
    have hFred : F.IsReduced := Subscheme.ofClosed_isReduced _
    have hWne : P.ℜ.n ≠ ⊥ := Subscheme.dim_ne_bot (hFne.mono hFW)
    obtain ⟨n₀, hn₀, hn₀n⟩ := LocSucc.exists_nat_of_le hWne hP
    have h3 := P.dim_prepF_lt hn₀
    have hFdimne : P.barℜ.n ≠ ⊥ := Subscheme.dim_ne_bot hFne
    obtain ⟨m, hm, hmn₀⟩ := LocSucc.exists_nat_of_le hFdimne (N := n₀) (by
      rw [← hn₀]; exact h3.le)
    have hmlt : m < n₀ := by
      have := h3
      have hm' : (F.dim : WithBot ℕ∞) = m := hm
      rw [hm', hn₀] at this
      exact_mod_cast this
    obtain ⟨Y, s, hs, hres⟩ := hI₂ m (by omega) X hX ⟨P.barℜ, P.isDatum_barℜ⟩
      (F.pts ∩ P.U) (P.isOpenRestriction_barℜ hX.2.1) hm
    refine ⟨Y, s, ?_, hs, hres⟩
    -- permissible for `(ℜ.extendBy B, U)`, then for `(ℜ, U)`
    have h1 : s.IsPermissibleIOpen (P.ℜ.extendBy B) P.U :=
      MonoidalSuccession.isPermissibleIOpen_of_isPermissibleIOpen_extendBy s (P.ℜ.extendBy B) F
        P.U _ hs (Subscheme.isContainedIn_of_pts_subset hFred hFD) subset_rfl
    have hBred : B.IsContainedIn P.ℜ.W := by
      have hWst : P.ℜ.W ≤ P.ℜ.prepWStar P.E₁ := Scheme.IdealSheafData.le_def.mpr
        (Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced _)
          (P.ℜ.pts_prepWStar_subset P.E₁))
      have hWB : P.ℜ.W ≤ B := hWst.trans le_sup_left
      exact fun U => Scheme.IdealSheafData.le_def.mp hWB U
    exact MonoidalSuccession.isPermissibleIOpen_of_isPermissibleIOpen_extendBy s P.ℜ B P.U P.U
      h1 hBred (fun y hy => hy.2)

/-- The resolvedness of `f*(ℜ̄)` on `F'` contains that of `f*(ℜ.extendBy F)` (the same `E`, the same
`V_j'` and `W'` among the `V`'s of `f*(ℜ̄)`, the same principal subscheme `F'`): the hypothesis of
`cond₁_transform` and `cond₂_transform` for the succession of step 3 (p. 290: "such that `f*(ℜ̄)` is
resolved at every point of the strict transform `F'` of `F`", used as in step 2, p. 289).

Deviation from the paper (gap filled): tacit; `ℜ̄ = (ℜ.extendBy (W_* ∩ E_1)).extendBy F` and `f*`
commutes with `extendBy` (`MonoidalSuccession.transformI_extendBy`). -/
theorem resolvedEverywhere_extendBy_prepF_of_barℜ {Y : Scheme.{u}} (s : MonoidalSuccession X Y)
    (h : (s.transformI P.barℜ).ResolvedEverywhere) :
    ((s.transformI P.ℜ).extendBy (s.strictTransform (P.ℜ.prepF P.E₁ P.U))).ResolvedEverywhere := by
  have hb : s.transformI P.barℜ =
      (((s.transformI P.ℜ).extendBy
        (s.strictTransform ((P.ℜ.prepWStar P.E₁).inter P.E₁))).extendBy
          (s.strictTransform (P.ℜ.prepF P.E₁ P.U))) := by
    simp only [barℜ, MonoidalSuccession.transformI_extendBy]
  intro x hx
  have hx' : x ∈ (s.transformI P.barℜ).W.pts := by rw [hb]; exact hx
  have hx'' := h x hx'
  rw [hb] at hx''
  obtain ⟨h1, h2, h3⟩ := hx''
  refine ⟨h1, fun j => ?_, h3⟩
  have e : (((s.transformI P.ℜ).extendBy
        (s.strictTransform ((P.ℜ.prepWStar P.E₁).inter P.E₁))).extendBy
          (s.strictTransform (P.ℜ.prepF P.E₁ P.U))).V j.castSucc =
      ((s.transformI P.ℜ).extendBy (s.strictTransform (P.ℜ.prepF P.E₁ P.U))).V j :=
    Fin.snoc_castSucc (α := fun _ => Subscheme Y) _ _ _
  have := h2 j.castSucc
  rw [e] at this
  exact this

/-- Step 3, last sentence (p. 290), the part "contained in `Ũ'`": a point of `W' ∩ E_j'` with `j > α`
(the strict transform of an exceptional divisor of one of the steps) lies over a center, hence over
`F` (the centers of `s` are permissible for `ℜ̄`, whose principal subscheme is `F`), hence over `Ũ`
(`F ⊆ Ũ` by (2)), and the tail datum of `f*(ℜ)` is resolved there by `tail_resolvedAt_transform`.

Deviation from the paper (gap filled): "We can prove that `W' ∩ E_j'` … [is] contained in `Ũ'`" is
tacit; the containment of the images of the exceptional divisors in the centers, and of the centers
in `F`, is `MonoidalSuccession.exists_presentation_transformI_tail` (last conjunct) together with
`MonoidalSuccession.centersIn_of_isPermissibleIOpen` for `(ℜ̄, F ∩ U)`. -/
theorem pts_inter_exceptional_subset_resolvedSet [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} {Y : Scheme.{u}}
    {s : MonoidalSuccession X Y} {Q : PrepSetting Y} (hX : IsAmbient X N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) (hY : Y.IsNonsingular) (hs : s.IsPermissibleIOpen P.ℜ P.U)
    (hQ : P.IsTransform s Q) {Ubar : Set X} (hC2 : P.Cond₂ Ubar) (J' : Set (Fin Q.α))
    (hJ3 : (s.transformI ({ P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ } : DatumI.Raw X)).E =
      Subscheme.unionFam (fun j : J' => Q.E j))
    (hJ' : ∀ j, Q.E j ≠ Q.E ⟨0, Q.hα⟩ → j ∈ J')
    (hcentF : ∀ j : Fin Q.α, P.α ≤ j.val → ∀ x ∈ (Q.E j).pts,
      s.composite.base x ∈ (P.ℜ.prepF P.E₁ P.U).pts)
    (j : Fin Q.α) (hj : P.α ≤ j.val) :
    (Q.ℜ.W.inter (Q.E j)).pts ⊆
      {y ∈ ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).W.pts |
        ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).ResolvedAt y} := by
  intro x hx
  obtain ⟨hxW, hxE⟩ := Subscheme.mem_pts_inter_iff.mp hx
  exact ⟨hxW, P.tail_resolvedAt_transform hX hP hY hs hQ hC2 J' hJ3 hJ' hxW
    (hC2.2.2.1 (hcentF j hj x hxE))⟩

/-- Over `X − Fc` the transformation `f` is an isomorphism (the centers lie over the closed `Fc`, `W`
is dense off `Fc`), and the constructions `W_*`, `E_1` commute with it. -/
theorem pts_inter_preimage_compl_eq_of_dense {N : ℕ} {Y : Scheme.{u}}
    {s : MonoidalSuccession X Y} {Q : PrepSetting Y} (hX : IsAmbient X N) (hY : IsAmbient Y N)
    (Fc : Subscheme X) (hdens : P.ℜ.W.pts ⊆ closure (P.ℜ.W.pts \ Fc.pts))
    (hcenters : s.CentersIn Fc) (hQ : P.IsTransform s Q) :
    ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts ∩ s.composite.base ⁻¹' Fc.ptsᶜ =
      (s.strictTransform ((P.ℜ.prepWStar P.E₁).inter P.E₁)).pts ∩
        s.composite.base ⁻¹' Fc.ptsᶜ := by
  classical
  have := hX.1
  have := hY.1
  have hXn : NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  have hYn : NoetherianSpace Y := IsAlgebraicScheme.noetherianSpace Y
  obtain ⟨hQℜ, hQU, hQE⟩ := hQ
  set F := Fc with hFdef
  set D := (P.ℜ.prepWStar P.E₁).inter P.E₁ with hD
  obtain ⟨Z, j, j₁, hjemb, hj₁, hrange, hrange₁, hjb, hpre_pts⟩ :=
    s.exists_isOpenEmbedding_lift_of_centersIn F hcenters
  have hWc : IsClosed P.ℜ.W.pts := P.ℜ.W.support.isClosed
  have hEc : IsClosed P.E₁.pts := P.E₁.support.isClosed
  have hWd : P.ℜ.W.pts ⊆ closure (P.ℜ.W.pts ∩ Set.range j) := by
    rw [hrange]
    refine hdens.trans (closure_mono ?_)
    intro y hy; exact ⟨hy.1, hy.2⟩
  have hW'pts : Q.ℜ.W.pts = (s.strictTransform P.ℜ.W).pts := by
    rw [hQℜ, MonoidalSuccession.transformI_W]
  have hQE₁ : Q.E₁.pts = (s.strictTransform P.E₁).pts := by rw [hQE]
  have hWd₁ : (s.strictTransform P.ℜ.W).pts ⊆
      closure ((s.strictTransform P.ℜ.W).pts ∩ Set.range j₁.base) := by
    rw [hrange₁]
    refine s.pts_strictTransform_subset_closure_inter P.ℜ.W F.ptsᶜ ?_
    rw [← hrange]; exact hWd
  have hW'c : IsClosed (s.strictTransform P.ℜ.W).pts :=
    (s.strictTransform P.ℜ.W).support.isClosed
  have hE'c : IsClosed (s.strictTransform P.E₁).pts := (s.strictTransform P.E₁).support.isClosed
  have hDQ : ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts =
      prepWStarT (s.strictTransform P.ℜ.W).pts (s.strictTransform P.E₁).pts ∩
        (s.strictTransform P.E₁).pts := by
    ext y
    rw [Subscheme.mem_pts_inter_iff, DatumI.Raw.pts_prepWStar_eq, hW'pts, hQE₁]
    rfl
  have hDX : D.pts = prepWStarT P.ℜ.W.pts P.E₁.pts ∩ P.E₁.pts := by
    ext y
    rw [hD, Subscheme.mem_pts_inter_iff, DatumI.Raw.pts_prepWStar_eq]
    rfl
  have hpreD : j₁.base ⁻¹' ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts =
      j₁.base ⁻¹' (s.strictTransform D).pts := by
    rw [hDQ, Set.preimage_inter, preimage_prepWStarT hj₁ hW'c hE'c hWd₁, hpre_pts, hpre_pts,
      hpre_pts, hDX, Set.preimage_inter, preimage_prepWStarT hjemb hWc hEc hWd]
  rw [← hrange₁]
  ext y
  constructor
  · rintro ⟨hy1, ⟨z, rfl⟩⟩
    refine ⟨?_, ⟨z, rfl⟩⟩
    have h2 : z ∈ j₁.base ⁻¹' ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts := hy1
    rw [hpreD] at h2
    exact h2
  · rintro ⟨hy1, ⟨z, rfl⟩⟩
    refine ⟨?_, ⟨z, rfl⟩⟩
    have h2 : z ∈ j₁.base ⁻¹' (s.strictTransform D).pts := hy1
    rw [← hpreD] at h2
    exact h2

/-- Over `X − F` the transformation `f` is an isomorphism, and the constructions `W_*`, `E_1`
(pp. 289–290) commute with it: the points of `W_*' ∩ E_1'` over `X − F` are those of the strict
transform of `W_* ∩ E_1`. -/
theorem pts_inter_preimage_compl_eq {N : ℕ} {Y : Scheme.{u}}
    {s : MonoidalSuccession X Y} {Q : PrepSetting Y} (hX : IsAmbient X N) (hY : IsAmbient Y N)
    (hcenters : s.CentersIn (P.ℜ.prepF P.E₁ P.U)) (hQ : P.IsTransform s Q) :
    ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts ∩ s.composite.base ⁻¹' (P.ℜ.prepF P.E₁ P.U).ptsᶜ =
      (s.strictTransform ((P.ℜ.prepWStar P.E₁).inter P.E₁)).pts ∩
        s.composite.base ⁻¹' (P.ℜ.prepF P.E₁ P.U).ptsᶜ :=
  have := hX.1
  P.pts_inter_preimage_compl_eq_of_dense hX hY (P.ℜ.prepF P.E₁ P.U)
    (P.ℜ.pts_subset_closure_diff_prepF P.E₁ P.U) hcenters hQ

/-- Step 3, "`W_*' ∩ E_1' ⊇ (W_* ∩ E_1)'`" (p. 290; the relation printed is `⊇`, with a doubled bar, not `=`).

Proof.  Over `X − F` the two sides agree (`pts_inter_preimage_compl_eq`).  The strict transform of
`W_* ∩ E_1` is contained in the union of the strict transform of the closure `D₁` of
`(W_* ∩ E_1) − F` (dense over `X − F`, hence contained in the closure of its part over `X − F`) and
of `F'`; and `F'` is the `F` of the transform, contained in `W_*' ∩ E_1'`.

Deviation from the paper (gap filled): "as is easily seen" is tacit. -/
theorem pts_strictTransform_subset_wStar_inter {N : ℕ} {Y : Scheme.{u}}
    {s : MonoidalSuccession X Y} {Q : PrepSetting Y} (hX : IsAmbient X N) (hY : IsAmbient Y N)
    (hs : s.IsPermissibleIOpen P.ℜ P.U) (hcenters : s.CentersIn (P.ℜ.prepF P.E₁ P.U))
    (hQ : P.IsTransform s Q) :
    (s.strictTransform ((P.ℜ.prepWStar P.E₁).inter P.E₁)).pts ⊆
      ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts := by
  classical
  have := hX.1
  have := hY.1
  have hK := P.pts_inter_preimage_compl_eq hX hY hcenters hQ
  have hFpts := P.prepF_transform_pts_eq hX.2.1 hs hQ
  set F := P.ℜ.prepF P.E₁ P.U with hFdef
  set D := (P.ℜ.prepWStar P.E₁).inter P.E₁ with hD
  have hDQc : IsClosed ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts :=
    ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).support.isClosed
  let D₁ : Subscheme X := Subscheme.ofClosed ⟨closure (D.pts \ F.pts), isClosed_closure⟩
  have hD₁pts : D₁.pts = closure (D.pts \ F.pts) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hDsub : D.pts ⊆ D₁.pts ∪ F.pts := fun y hy => by
    by_cases hyF : y ∈ F.pts
    · exact Or.inr hyF
    · exact Or.inl (by rw [hD₁pts]; exact subset_closure ⟨hy, hyF⟩)
  have hD₁D : D₁.pts ⊆ D.pts := by
    rw [hD₁pts]; exact closure_minimal Set.sdiff_subset D.support.isClosed
  have hD₁dense : D₁.pts ⊆ closure (D₁.pts ∩ F.ptsᶜ) := by
    rw [hD₁pts]
    refine closure_mono ?_
    intro y hy
    exact ⟨subset_closure hy, hy.2⟩
  have h1 := s.pts_strictTransform_subset_union hDsub
  have h2 := s.pts_strictTransform_subset_closure_inter D₁ F.ptsᶜ hD₁dense
  have h3 : (s.strictTransform D₁).pts ∩ s.composite.base ⁻¹' F.ptsᶜ ⊆
      ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts := by
    intro y hy
    have : y ∈ (s.strictTransform D).pts ∩ s.composite.base ⁻¹' F.ptsᶜ :=
      ⟨s.pts_strictTransform_mono hD₁D hy.1, hy.2⟩
    rw [← hK] at this
    exact this.1
  have h4 : (s.strictTransform D₁).pts ⊆ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts :=
    h2.trans (closure_minimal h3 hDQc)
  intro y hy
  rcases h1 hy with hy1 | hy1
  · exact h4 hy1
  · rw [← hFpts] at hy1
    exact Q.ℜ.pts_prepF_subset Q.E₁ Q.U hy1

/-- Step 3, second sentence of the paragraph on components (p. 290): "every reduced irreducible
component of `W_*' ∩ E_1'` is either contained in `(W_* ∩ E_1)'` or contained in `W' ∩ E_j'` with `j`
such that `α < j ≤ α'`".

Proof.  The centers of `s` lie over `F` (`hcenters`), so `s` is an isomorphism over `X − F`.  If the
generic point of the component lies over `X − F`, it lies in the strict transform of `W_* ∩ E_1` (the
constructions `W_*`, `E_1` are compatible with the open immersion over `X − F`, `preimage_prepWStarT`);
otherwise it lies in `f⁻¹(F)`, which is the union of the strict transform of `F` (contained in the
strict transform of `W_* ∩ E_1`) and the exceptional divisors `E_j'`, `j > α` (`hG1`).

Deviation from the paper (gap filled): "as is easily seen" is tacit. -/
theorem pts_subset_strictTransform_or_exists_subset_inter_exceptional_of_dense {N : ℕ} {Y : Scheme.{u}}
    {s : MonoidalSuccession X Y} {Q : PrepSetting Y} (hX : IsAmbient X N) (hY : IsAmbient Y N)
    (Fc : Subscheme X) (hdens : P.ℜ.W.pts ⊆ closure (P.ℜ.W.pts \ Fc.pts))
    (hFcD : Fc.pts ⊆ ((P.ℜ.prepWStar P.E₁).inter P.E₁).pts)
    (hcenters : s.CentersIn Fc)
    (hQ : P.IsTransform s Q)
    (hG1 : ∀ T : Subscheme X, ∀ y : Y, s.composite.base y ∈ T.pts →
      y ∈ (s.strictTransform T).pts ∨ ∃ j : Fin Q.α, P.α ≤ j.val ∧ y ∈ (Q.E j).pts)
    {G : Subscheme Y} (hG : G ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).irreducibleComponents) :
    G.pts ⊆ (s.strictTransform ((P.ℜ.prepWStar P.E₁).inter P.E₁)).pts ∨
      ∃ j : Fin Q.α, P.α ≤ j.val ∧ G.pts ⊆ (Q.ℜ.W.inter (Q.E j)).pts := by
  classical
  have := hX.1
  have := hY.1
  have hYn : NoetherianSpace Y := IsAlgebraicScheme.noetherianSpace Y
  have hK := P.pts_inter_preimage_compl_eq_of_dense hX hY Fc hdens hcenters hQ
  obtain ⟨hQℜ, hQU, hQE⟩ := hQ
  set F := Fc with hFdef
  set D := (P.ℜ.prepWStar P.E₁).inter P.E₁ with hD
  obtain ⟨Z, hZmax, rfl⟩ := hG
  have hZpts : (Subscheme.ofClosed Z).pts = Z :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  rw [hZpts]
  have hD'c : IsClosed (s.strictTransform D).pts := (s.strictTransform D).support.isClosed
  obtain ⟨ξ, hξ⟩ : ∃ ξ, IsGenericPoint ξ (Z : Set Y) := QuasiSober.sober hZmax.1.1 Z.isClosed
  by_cases hξr : s.composite.base ξ ∈ F.ptsᶜ
  · left
    have hξD : ξ ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts := hZmax.1.2 hξ.mem
    have hξD' : ξ ∈ (s.strictTransform D).pts := by
      have h3 : ξ ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts ∩
          s.composite.base ⁻¹' Fc.ptsᶜ := ⟨hξD, hξr⟩
      rw [hK] at h3
      exact h3.1
    rw [← hξ.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hξD') hD'c
  · have hξF : s.composite.base ξ ∈ F.pts := by
      by_contra h
      exact hξr h
    rcases hG1 F ξ hξF with hF' | ⟨k, hk, hξk⟩
    · left
      have hmono : (s.strictTransform F).pts ⊆ (s.strictTransform D).pts :=
        s.pts_strictTransform_mono hFcD
      rw [← hξ.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (hmono hF')) hD'c
    · right
      refine ⟨k, hk, ?_⟩
      have hξW : ξ ∈ Q.ℜ.W.pts := by
        have := hZmax.1.2 hξ.mem
        exact (Subscheme.mem_pts_inter_iff.mp this).1 |> fun h => Q.ℜ.pts_prepWStar_subset Q.E₁ h
      have hmem : ξ ∈ (Q.ℜ.W.inter (Q.E k)).pts := Subscheme.mem_pts_inter_iff.mpr ⟨hξW, hξk⟩
      rw [← hξ.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hmem)
        (Q.ℜ.W.inter (Q.E k)).support.isClosed

theorem pts_subset_strictTransform_or_exists_subset_inter_exceptional {N : ℕ} {Y : Scheme.{u}}
    {s : MonoidalSuccession X Y} {Q : PrepSetting Y} (hX : IsAmbient X N) (hY : IsAmbient Y N)
    (hcenters : s.CentersIn (P.ℜ.prepF P.E₁ P.U))
    (hQ : P.IsTransform s Q)
    (hG1 : ∀ T : Subscheme X, ∀ y : Y, s.composite.base y ∈ T.pts →
      y ∈ (s.strictTransform T).pts ∨ ∃ j : Fin Q.α, P.α ≤ j.val ∧ y ∈ (Q.E j).pts)
    {G : Subscheme Y} (hG : G ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).irreducibleComponents) :
    G.pts ⊆ (s.strictTransform ((P.ℜ.prepWStar P.E₁).inter P.E₁)).pts ∨
      ∃ j : Fin Q.α, P.α ≤ j.val ∧ G.pts ⊆ (Q.ℜ.W.inter (Q.E j)).pts := by
  have := hX.1
  exact P.pts_subset_strictTransform_or_exists_subset_inter_exceptional_of_dense hX hY
    (P.ℜ.prepF P.E₁ P.U) (P.ℜ.pts_subset_closure_diff_prepF P.E₁ P.U)
    (P.ℜ.pts_prepF_subset P.E₁ P.U) hcenters hQ hG1 hG

/-- Step 3, "Since `f*(ℜ̄)` is resolved at every point of `F'`, `(W_* ∩ E_1)'` is normally flat along
`F'`, hence, every component of `(W_* ∩ E_1)'` is either in `F'` or has empty intersection with `F'`"
(p. 290), for the components of `W_*' ∩ E_1'` lying in `(W_* ∩ E_1)'`.

Proof.  At `x ∈ G ∩ F'` let `R = O_{X',x}` (regular), `Q = W'_x` (prime, `R/Q` regular since `W'` is
simple at `x`), `P_F = F'_x`, `z` the equation of `E_1'` and `J = ((W_* ∩ E_1)')_x`.  Then
`Q ⊆ J ⊆ P_F`, `z ∈ J ∖ Q` (`E_1'` does not contain the component of `W'` through `x`, which lies in
`W_*'`), and `P_F` is minimal over `Q + (z) = (W_*' ∩ E_1')_x` (`F'` is a component of `W_*' ∩ E_1'`
meeting `U'`).  In the regular local domain `R/Q` the prime `P_F/Q` has height one (Krull), has regular
quotient and contains no other non-zero prime, so it is principal, `(π)`
(`exists_span_singleton_eq_of_isRegularLocalRing_quotient`).  The normal flatness of `R/J` along `P_F`
(the slot of `W_* ∩ E_1` among the `V_j` of `ℜ̄`) gives a power `π^a ∈ J` by the graded-piece argument
of `exists_pow_mem_of_isNormallyFlatAlongIdeal_span` (the piece `P^n/P^{n+1}` is a cyclic free module
over the domain `R/P_F`, hence torsion free, so an element of exact `π`-order in `J` kills a non-zero
generator); hence every prime `q ⊇ J`, in particular `G_x`, contains `π`, i.e. `F'_x ⊆ G_x`, and
`G ⊆ F'` (`le_of_isNormallyFlatAlongIdeal_of_mem_minimalPrimes`).

Deviation from the paper (alternative proof; gap filled): the paper gives "hence" for this sentence
(Ch. II type: a scheme normally flat along one of its components has no other component through the
point).  Lean proves it in the hypersurface situation `W' ∩ E_1'` of a regular local ring, by the
graded-piece argument above, which does not use the Hilbert–Samuel function; the identification of
the stalks of `W_*'` and `W'` at `x` (`DatumI.Raw.stalkIdeal_prepWStar_eq`), the equation `z` of `E_1'`,
and the minimality of `F'_x` over `Q + (z)` are tacit. -/
theorem pts_subset_prepF_of_mem_irreducibleComponents_of_pts_subset_strictTransform [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}]
    {N : ℕ} {Y : Scheme.{u}} {s : MonoidalSuccession X Y} {Q : PrepSetting Y}
    (hX : IsAmbient X N) (hY : IsAmbient Y N) (hs : s.IsPermissibleIOpen P.ℜ P.U)
    (hQ : P.IsTransform s Q) (hresbar : (s.transformI P.barℜ).ResolvedEverywhere)
    {G : Subscheme Y} (hG : G ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).irreducibleComponents)
    (hGD : G.pts ⊆ (s.strictTransform ((P.ℜ.prepWStar P.E₁).inter P.E₁)).pts)
    (hmeet : (G.pts ∩ (s.strictTransform (P.ℜ.prepF P.E₁ P.U)).pts).Nonempty) :
    G.pts ⊆ (s.strictTransform (P.ℜ.prepF P.E₁ P.U)).pts := by
  classical
  have := hX.1
  have := hY.1
  have hres := P.resolvedEverywhere_extendBy_prepF_of_barℜ s hresbar
  have hXn := hX.2.1
  have hYn := hY.2.1
  have hFeq := P.prepF_transform_eq hXn hs hQ hres
  have hFpts := P.prepF_transform_pts_eq hXn hs hQ
  have hQ' := hQ
  obtain ⟨hQℜ, hQU, hQE⟩ := hQ'
  set F' := s.strictTransform (P.ℜ.prepF P.E₁ P.U) with hF'
  set D := (P.ℜ.prepWStar P.E₁).inter P.E₁ with hD
  set DQ := (Q.ℜ.prepWStar Q.E₁).inter Q.E₁ with hDQ
  obtain ⟨x, hxG, hxF'⟩ := hmeet
  have hxDQ : x ∈ DQ.pts := Subscheme.pts_subset_of_mem_irreducibleComponents hG hxG
  have hxF'' : x ∈ (Q.ℜ.prepF Q.E₁ Q.U).pts := by rw [hFpts]; exact hxF'
  obtain ⟨hxWS, hxE1⟩ := Subscheme.mem_pts_inter_iff.mp hxDQ
  have hWs := (P.isSimpleAt_and_isNormallyFlatAlongAt'_prepF_transform hXn hs hQ hres x hxF'').1
  have hFs : F'.IsSimpleAt x := (hres x hxF').1
  have hWp := Subscheme.isPrime_stalkIdeal_of_isSimpleAt hWs
  have hQW : Q.ℜ.W = s.strictTransform P.ℜ.W := by rw [hQℜ, MonoidalSuccession.transformI_W]
  obtain ⟨hWSst, C₁, hC₁, hC₁E, hxC₁, hC₁st⟩ := Q.ℜ.stalkIdeal_prepWStar_eq Q.E₁ hxWS hWp
  -- the equation `z` of `E_1'`
  have hnc : (Subscheme.unionFam Q.E).HasOnlyNormalCrossingsWithAt F' x := by
    rw [← Q.hEunion, hQℜ]
    exact (hres x hxF').2.2
  have : IsRegularLocalRing (Y.presheaf.stalk x) := hYn x
  obtain ⟨Z, hZ, -, hEZ⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    Q.E Q.hE (fun i => iInf_le _ i) hnc
  obtain ⟨z, hz⟩ : ∃ z, Q.E₁.stalkIdeal x = Ideal.span {z} := by
    rcases hEZ ⟨0, Q.hα⟩ with h | ⟨a, -, h⟩
    · exact absurd h ((Subscheme.mem_pts_iff_stalkIdeal_ne_top).mp hxE1)
    · exact ⟨a, h⟩
  -- `z ∉ W'_x`: the component of `W'` through `x` is not contained in `E_1'`
  have hzW : z ∉ Q.ℜ.W.stalkIdeal x := by
    intro hzQ
    apply hC₁E
    obtain ⟨Z₁, hZ₁, rfl⟩ := hC₁
    obtain ⟨ω, hω⟩ : ∃ ω, IsGenericPoint ω (Z₁ : Set Y) := QuasiSober.sober hZ₁.1.1 Z₁.isClosed
    have hZ₁eq : Z₁ = ⟨closure {ω}, isClosed_closure⟩ := Closeds.ext hω.def.symm
    have hxZ₁ : x ∈ Z₁ := by
      have := hxC₁
      rwa [Subscheme.pts_ofClosed] at this
    have hωx : ω ⤳ x := by
      rw [specializes_iff_mem_closure, hω.def]; exact hxZ₁
    have hst : Q.E₁.stalkIdeal x ≤ (Subscheme.ofClosed ⟨closure {ω}, isClosed_closure⟩).stalkIdeal x := by
      rw [← hZ₁eq, hC₁st, hz, Ideal.span_singleton_le_iff_mem]
      exact hzQ
    have hωE : ω ∈ Q.E₁.pts := Subscheme.mem_pts_of_stalkIdeal_le_ofClosed_closure hωx Q.E₁ hst
    refine Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced Z₁) ?_
    rw [Subscheme.pts_ofClosed, ← hω.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hωE) Q.E₁.support.isClosed
  -- the stalk of `W_*' ∩ E_1'`
  have hDQst : DQ.stalkIdeal x = Q.ℜ.W.stalkIdeal x ⊔ Ideal.span {z} := by
    rw [hDQ, Subscheme.inter, Subscheme.stalkIdeal_sup_eq, hWSst, ← hz]
  -- `F'_x` is a minimal prime of `DQ_x`
  obtain ⟨G₀, hG₀, hG₀U, hxG₀⟩ := Q.ℜ.exists_mem_irreducibleComponents_of_mem_pts_prepF' Q.E₁ Q.U
    hxF''
  have hG₀min := Subscheme.stalkIdeal_mem_minimalPrimes hG₀ hxG₀
  have hFp : (F'.stalkIdeal x).IsPrime := Subscheme.isPrime_stalkIdeal_of_isSimpleAt hFs
  have hG₀F : G₀.IsContainedIn F' := by
    rw [← hFeq]
    obtain ⟨Z₀, hZ₀, rfl⟩ := hG₀
    refine Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced Z₀) ?_
    intro y hy
    rw [DatumI.Raw.pts_prepF]
    refine subset_closure ⟨_, ⟨Z₀, ⟨Subscheme.ofClosed Z₀, ⟨Z₀, hZ₀, rfl⟩, hG₀U, (Subscheme.support_ofClosed Z₀).symm⟩, rfl⟩, ?_⟩
    exact hy
  have hFDQ : F'.IsContainedIn DQ := by
    rw [← hFeq]
    exact Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced _)
      (Q.ℜ.pts_prepF_subset Q.E₁ Q.U)
  have hmin : F'.stalkIdeal x ∈ (Q.ℜ.W.stalkIdeal x ⊔ Ideal.span {z}).minimalPrimes := by
    rw [← hDQst]
    have h1 := hG₀min.2 ⟨hFp, Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hFDQ x⟩
      (Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hG₀F x)
    have h2 : G₀.stalkIdeal x = F'.stalkIdeal x :=
      le_antisymm h1 (Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hG₀F x)
    rw [← h2]; exact hG₀min
  -- containments
  have hFD : (P.ℜ.prepF P.E₁ P.U).IsContainedIn D :=
    Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced _)
      (P.ℜ.pts_prepF_subset P.E₁ P.U)
  have hWst : P.ℜ.W ≤ P.ℜ.prepWStar P.E₁ := Scheme.IdealSheafData.le_def.mpr
    (Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced _)
      (P.ℜ.pts_prepWStar_subset P.E₁))
  have hDW : D.IsContainedIn P.ℜ.W := fun U =>
    Scheme.IdealSheafData.le_def.mp (hWst.trans le_sup_left) U
  have hDE : D.IsContainedIn P.E₁ := fun U =>
    Scheme.IdealSheafData.le_def.mp (le_sup_right : P.E₁ ≤ D) U
  have hFD' : F'.IsContainedIn (s.strictTransform D) := s.isContainedIn_strictTransform hFD
  have hDW' : (s.strictTransform D).IsContainedIn Q.ℜ.W := by
    rw [hQW]; exact s.isContainedIn_strictTransform hDW
  have hDE' : (s.strictTransform D).IsContainedIn Q.E₁ := by
    rw [hQE]; exact s.isContainedIn_strictTransform hDE
  have hzD : z ∈ (s.strictTransform D).stalkIdeal x := by
    have := Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hDE' x
    rw [hz] at this
    exact this (Ideal.mem_span_singleton_self z)
  -- normal flatness of `D'` along `F'`
  have hb : s.transformI P.barℜ =
      (((s.transformI P.ℜ).extendBy
        (s.strictTransform ((P.ℜ.prepWStar P.E₁).inter P.E₁))).extendBy
          (s.strictTransform (P.ℜ.prepF P.E₁ P.U))) := by
    simp only [barℜ, MonoidalSuccession.transformI_extendBy]
  have hnf : Subscheme.IsNormallyFlatAlongAt' (s.strictTransform D) F' x := by
    have hx' : x ∈ (s.transformI P.barℜ).W.pts := by rw [hb]; exact hxF'
    have hx'' := hresbar x hx'
    rw [hb] at hx''
    have e : (((s.transformI P.ℜ).extendBy
        (s.strictTransform ((P.ℜ.prepWStar P.E₁).inter P.E₁))).extendBy
          (s.strictTransform (P.ℜ.prepF P.E₁ P.U))).V (Fin.last _) =
        s.strictTransform ((P.ℜ.prepWStar P.E₁).inter P.E₁) :=
      Fin.snoc_last (α := fun _ => Subscheme Y) _ _
    have h3 := hx''.2.1 (Fin.last _)
    rw [e] at h3
    exact h3
  -- the prime `G_x`
  have hGp : (G.stalkIdeal x).IsPrime := (Subscheme.stalkIdeal_mem_minimalPrimes hG hxG).1.1
  have hGred : G.IsReduced := by
    obtain ⟨Z, -, rfl⟩ := hG; exact Subscheme.ofClosed_isReduced Z
  have hq : (s.strictTransform D).stalkIdeal x ≤ G.stalkIdeal x :=
    Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn (Subscheme.isContainedIn_of_pts_subset hGred hGD) x
  have hle := Subscheme.stalkIdeal_le_of_isNormallyFlatAlongAt'_of_mem_minimalPrimes hYn hWs hFs
    hFD' hDW' hzD hzW hmin hnf hq
  -- `G ⊆ F'`
  obtain ⟨Z, hZ, rfl⟩ := hG
  obtain ⟨ξ, hξ⟩ : ∃ ξ, IsGenericPoint ξ (Z : Set Y) := QuasiSober.sober hZ.1.1 Z.isClosed
  have hZeq : Z = ⟨closure {ξ}, isClosed_closure⟩ := Closeds.ext hξ.def.symm
  have hxZ : x ∈ Z := by
    have := hxG
    rwa [Subscheme.pts_ofClosed] at this
  have hξx : ξ ⤳ x := by
    rw [specializes_iff_mem_closure, hξ.def]; exact hxZ
  have hξF : ξ ∈ F'.pts := by
    refine Subscheme.mem_pts_of_stalkIdeal_le_ofClosed_closure hξx F' ?_
    rw [← hZeq]; exact hle
  rw [Subscheme.pts_ofClosed, ← hξ.def]
  exact closure_minimal (Set.singleton_subset_iff.mpr hξF) F'.support.isClosed

/-- The exceptional divisors `E_j'` (`j > α`) do not contain the branch of `W'` at a simple point `y`:
the generic point of the component of `W'` through `y` lies over `X − F` (the strict transform of `W`
is dense over `X − F`), whereas `E_j'` lies over `F`.

Deviation from the paper (gap filled): tacit in "we can prove that `W' ∩ E_j'` … [is] non-singular"
(p. 290): `W'` is not contained in `E_j'`. -/
theorem not_stalkIdeal_le_of_exceptional_of_dense {Y : Scheme.{u}} {s : MonoidalSuccession X Y}
    {Q : PrepSetting Y} [IsAlgebraicScheme X] [IsAlgebraicScheme Y] (hQ : P.IsTransform s Q)
    (Fc : Subscheme X) (hdens : P.ℜ.W.pts ⊆ closure (P.ℜ.W.pts \ Fc.pts))
    (hcentF : ∀ j : Fin Q.α, P.α ≤ j.val → ∀ x ∈ (Q.E j).pts,
      s.composite.base x ∈ Fc.pts) (j : Fin Q.α) (hj : P.α ≤ j.val) {y : Y}
    (hy : Q.ℜ.W.IsSimpleAt y) : ¬ (Q.E j).stalkIdeal y ≤ Q.ℜ.W.stalkIdeal y := by
  classical
  intro hle
  have hYn : NoetherianSpace Y := IsAlgebraicScheme.noetherianSpace Y
  have hWp := Subscheme.isPrime_stalkIdeal_of_isSimpleAt hy
  have hQW : Q.ℜ.W.pts = (s.strictTransform P.ℜ.W).pts := by
    rw [hQ.1, MonoidalSuccession.transformI_W]
  have hdense : (s.strictTransform P.ℜ.W).pts ⊆
      closure ((s.strictTransform P.ℜ.W).pts ∩ s.composite.base ⁻¹' Fc.ptsᶜ) := by
    refine s.pts_strictTransform_subset_closure_inter P.ℜ.W _ ?_
    refine hdens.trans (closure_mono ?_)
    intro w hw; exact ⟨hw.1, hw.2⟩
  have hmin : Q.ℜ.W.stalkIdeal y ∈ (Q.ℜ.W.stalkIdeal y).minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl
  obtain ⟨C, hC, hyC, hCst⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes
    Q.ℜ.W y hmin
  obtain ⟨Zc, hZc, rfl⟩ := hC
  have hZpts : (Subscheme.ofClosed Zc).pts = Zc := Scheme.IdealSheafData.coe_support_vanishingIdeal Zc
  have hyZ : y ∈ Zc := by rwa [hZpts] at hyC
  obtain ⟨ω, hω⟩ : ∃ ω, IsGenericPoint ω (Zc : Set Y) := QuasiSober.sober hZc.1.1 Zc.isClosed
  have hωy : ω ⤳ y := by rw [specializes_iff_mem_closure, hω.def]; exact hyZ
  have hZeq : Zc = ⟨closure {ω}, isClosed_closure⟩ := Closeds.ext hω.def.symm
  have hst : (Q.E j).stalkIdeal y ≤
      (Subscheme.ofClosed ⟨closure {ω}, isClosed_closure⟩).stalkIdeal y := by
    rw [← hZeq, hCst]; exact hle
  have hωE : ω ∈ (Q.E j).pts := Subscheme.mem_pts_of_stalkIdeal_le_ofClosed_closure hωy (Q.E j) hst
  have hωF := hcentF j hj ω hωE
  have hR : IsOpen (s.composite.base ⁻¹' Fc.ptsᶜ) :=
    Fc.support.isClosed.isOpen_compl.preimage s.composite.base.hom.continuous
  have hdense' : Q.ℜ.W.pts ⊆ closure (Q.ℜ.W.pts ∩ s.composite.base ⁻¹' Fc.ptsᶜ) := by
    rw [hQW]; exact hdense
  have hmeet := prepComps_meets (W := Q.ℜ.W.pts) Q.ℜ.W.support.isClosed hdense'
    (O := s.composite.base ⁻¹' Fc.ptsᶜ) (G := Zc) hZc
  have hωR : ω ∈ s.composite.base ⁻¹' Fc.ptsᶜ :=
    (hω.mem_open_set_iff hR).mpr hmeet
  exact hωR hωF

theorem not_stalkIdeal_le_of_exceptional {Y : Scheme.{u}} {s : MonoidalSuccession X Y}
    {Q : PrepSetting Y} [IsAlgebraicScheme X] [IsAlgebraicScheme Y] (hQ : P.IsTransform s Q)
    (hcentF : ∀ j : Fin Q.α, P.α ≤ j.val → ∀ x ∈ (Q.E j).pts,
      s.composite.base x ∈ (P.ℜ.prepF P.E₁ P.U).pts) (j : Fin Q.α) (hj : P.α ≤ j.val) {y : Y}
    (hy : Q.ℜ.W.IsSimpleAt y) : ¬ (Q.E j).stalkIdeal y ≤ Q.ℜ.W.stalkIdeal y :=
  P.not_stalkIdeal_le_of_exceptional_of_dense hQ (P.ℜ.prepF P.E₁ P.U)
    (P.ℜ.pts_subset_closure_diff_prepF P.E₁ P.U) hcentF j hj hy

/-- If `E_1 ⊄ F`, the exceptional divisors `E_j'` (`j > α`) differ from `E_1'`: all points of `E_j'`
lie over `F`, while `E_1'` has a point over a point of `E_1 − F` (over which `f` is an isomorphism). -/
theorem Q_E_ne_E₁_of_not_pts_subset {Y : Scheme.{u}} {s : MonoidalSuccession X Y} {Q : PrepSetting Y}
    (hcenters : s.CentersIn (P.ℜ.prepF P.E₁ P.U)) (hQ : P.IsTransform s Q)
    (hcentF : ∀ j : Fin Q.α, P.α ≤ j.val → ∀ x ∈ (Q.E j).pts,
      s.composite.base x ∈ (P.ℜ.prepF P.E₁ P.U).pts)
    (hE1 : ¬ P.E₁.pts ⊆ (P.ℜ.prepF P.E₁ P.U).pts) (j : Fin Q.α) (hj : P.α ≤ j.val) :
    Q.E j ≠ Q.E₁ := by
  intro hjE
  obtain ⟨η, hηE, hηF⟩ := Set.not_subset.mp hE1
  obtain ⟨Z, jm, j₁, hjemb, hj₁, hrange, hrange₁, hjb, hpre_pts⟩ :=
    s.exists_isOpenEmbedding_lift_of_centersIn (P.ℜ.prepF P.E₁ P.U) hcenters
  have hηr : η ∈ Set.range jm.base := by rw [hrange]; exact hηF
  obtain ⟨z, rfl⟩ := hηr
  have h1 : z ∈ jm.base ⁻¹' P.E₁.pts := hηE
  rw [← hpre_pts] at h1
  have h2 : j₁.base z ∈ Q.E₁.pts := by rw [hQ.2.2]; exact h1
  rw [← hjE] at h2
  have h3 := hcentF j hj _ h2
  rw [hjb] at h3
  exact hηF h3

/-- Step 3, "We can prove that `W' ∩ E_j'` for `α < j ≤ α'` are non-singular … subschemes" (p. 290),
non-singularity: at each point `y` of `W' ∩ E_j'` the tail datum `(⋃_{i≥2} E_i'; V'; W')` is resolved
(`pts_inter_exceptional_subset_resolvedSet`), so `W'_y` and `(E_j')_y` are generated by parts of one
regular system of parameters, the equation of `E_j'` not being among those of `W'_y`
(`not_stalkIdeal_le_of_exceptional`).

Deviation from the paper (gap filled): "we can prove" has no proof in the paper. -/
theorem isNonsingular_inter_exceptional {N : ℕ} {Y : Scheme.{u}} {s : MonoidalSuccession X Y}
    {Q : PrepSetting Y} (hX : IsAmbient X N) (hY : IsAmbient Y N) (hQ : P.IsTransform s Q)
    (hcentF : ∀ j : Fin Q.α, P.α ≤ j.val → ∀ x ∈ (Q.E j).pts,
      s.composite.base x ∈ (P.ℜ.prepF P.E₁ P.U).pts)
    (j : Fin Q.α) (hj : P.α ≤ j.val) (hne1 : Q.E j ≠ Q.E₁)
    (hresS : (Q.ℜ.W.inter (Q.E j)).pts ⊆
      {y ∈ ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).W.pts |
        ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).ResolvedAt y}) :
    (Q.ℜ.W.inter (Q.E j)).IsNonsingular := by
  classical
  have := hX.1
  have := hY.1
  refine Subscheme.isNonsingular_of_stalk_quot _ fun z hz => ?_
  obtain ⟨-, hzres⟩ := hresS hz
  obtain ⟨hzW, hzE⟩ := Subscheme.mem_pts_inter_iff.mp hz
  have hne := P.not_stalkIdeal_le_of_exceptional hQ hcentF j hj hzres.1
  exact (Subscheme.isSimpleAt_inter_of_hasOnlyNormalCrossingsWithAt hY.2.1
    (fun i : {i : Fin Q.α // Q.E i ≠ Q.E ⟨0, Q.hα⟩} => Q.E i) (fun i => Q.hE i) hzW hzres.2.2
    ⟨j, hne1⟩ hzE hne).2

/-- Step 3, "We can prove that `W' ∩ E_j'` for `α < j ≤ α'` are non-singular irreducible subschemes
of `X'`" (p. 290), irreducibility (when non-empty).

Status: proved from the one-step statement `MonoidalTransformation.isIrreducible_pts_strictTransform_inter_exceptional`
(proved, from `Compat/StrictTransformExceptional.lean`; cited leaves only), by
`MonoidalSuccession.isIrreducible_pts_inter_of_mem_exceptionalDivisors`.  The non-singularity is
`isNonsingular_inter_exceptional`.

Truth check (compare Lemma (AB.4), p. 299, whose irreducibility is false as printed).  The claim
holds under the standing hypotheses of Proposition 5.  Let `E_j'` (`j > α`) be the strict transform, under
the steps after the `k`-th, of the exceptional divisor `Exc_k` of the `k`-th step, whose center `B_k` is
non-singular irreducible and lies over `F ⊆ Ũ` (a permissible center for `(ℜ̄, F ∩ U)`).  (1) `W_k` is
simple at every point of `B_k`: the tail datum of `f_{<k}*(ℜ)` is resolved at the points over `Ũ`
(`resolvedAt_transformI_tail`), in particular `W_k` is simple there; so exactly one component `C` of `W_k`
passes through each point of `B_k`, and as `B_k` is connected the same `C` for all of them.  (2) `B_k ⊊ C`:
`B_k ⊆ F_k ⊆ W_*^{(k)} ∩ E_1^{(k)}` and `C` is a component of `W_*^{(k)}` not in `E_1^{(k)}`, so
`B_k` has positive codimension `r` in `C`.  (3) Hence `W_{k+1} ∩ Exc_k` is the exceptional divisor of the
blow-up of the non-singular `C` along the irreducible `B_k`: the projective bundle `P(N_{B_k/C})`, with
fibres `P^{r-1}` (a point if `r = 1`), irreducible; components of `W_k` not through `B_k` do not meet it.
(4) For the later steps `l > k`, `W_{l+1} ∩ E_j^{(l+1)} = (W_l ∩ E_j^{(l)})'` as sets: over a point of
`B_l` the tail datum of the transform is resolved (Lemma 4), so `W'`, `E_j'` and the exceptional divisor
`g` of step `l` have equations in one regular system of parameters, `g ∉ (W'_y) + (e_j')`, and the generic
point of the branch of `W' ∩ E_j'` at `y` is not in `g`; the strict transform of an irreducible set not
contained in `B_l` is irreducible.  The possible sources of two components (two components of `W` through
`B_k`, a disconnected fibre, a splitting by later blow-ups) are all excluded by (1), (3), (4).
No counterexample exists: the counterexample to the irreducibility in Lemma (AB.4) (see
`mem_xHatPrimeStar_and_isGoodComponent_of_cond`, blueprint `lem:IV.AB-4-componentwise`)
needs a center meeting two branches of `W` (the two sheets of `W` through the nodal curve), excluded
here by (1).

Proof in Lean: induction on the succession (`MonoidalSuccession.isIrreducible_pts_inter_of_mem_exceptionalDivisors`),
`W' ∩ E_j'` being the strict transform of `W_k ∩ Exc_k` (`MonoidalSuccession.pts_inter_strictTransform_subset`,
from the one-step identity `MonoidalTransformation.pts_inter_strictTransform_subset`), irreducible by the first-step
case `MonoidalTransformation.isIrreducible_pts_strictTransform_inter_exceptional` and
`MonoidalSuccession.isIrreducible_pts_strictTransform`.

Deviation from the paper (gap filled, once the first-step case is proved): "we can prove" has no proof in the
paper. -/
theorem isIrreducible_inter_exceptional [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} {Y : Scheme.{u}}
    {s : MonoidalSuccession X Y} {Q : PrepSetting Y} (hX : IsAmbient X N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) (hQ : P.IsTransform s Q) {Ubar : Set X} (hC2 : P.Cond₂ Ubar)
    (hperm : s.IsPermissibleIOpen ({ P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ } : DatumI.Raw X) P.U)
    (hcenters : s.CentersIn (P.ℜ.prepF P.E₁ P.U))
    (hexc : ∀ j : Fin Q.α, P.α ≤ j.val → Q.E j ∈ s.exceptionalDivisors)
    (j : Fin Q.α) (hj : P.α ≤ j.val) (hne : (Q.ℜ.W.inter (Q.E j)).pts.Nonempty) :
    (Q.ℜ.W.inter (Q.E j)).IsIrreducible := by
  classical
  have := hX.1
  set R : DatumI.Raw X := { P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ } with hR
  -- a `Fin`-indexed presentation of the tail
  let e := Fintype.equivFin {i : Fin P.α // P.E i ≠ P.E ⟨0, P.hα⟩}
  have hEunion : R.E = Subscheme.unionFam (fun k => P.E (e.symm k).1) := by
    show Subscheme.unionFam (fun i : {i : Fin P.α // P.E i ≠ P.E ⟨0, P.hα⟩} => P.E i) = _
    unfold Subscheme.unionFam
    exact (Equiv.iInf_comp (g := fun i : {i : Fin P.α // P.E i ≠ P.E ⟨0, P.hα⟩} => P.E i) e.symm).symm
  have H : StageHyp N n s R P.U Ubar (P.ℜ.prepF P.E₁ P.U) :=
    ⟨⟨hX, P.isDatum_rest hX.2.1, hP⟩,
      DatumI.Raw.IsOpenRestriction.tail hX.2.1 P.E P.hE P.hEunion P.hU Subtype.val, hperm,
      fun x hx _ => hC2.2.2.2 x hx, hcenters, hC2.2.2.1⟩
  have hQW : Q.ℜ.W.pts = (s.strictTransform P.ℜ.W).pts := by
    rw [hQ.1, MonoidalSuccession.transformI_W]
  have hne' : ((s.strictTransform R.W).pts ∩ (Q.E j).pts).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨hx1, hx2⟩ := Subscheme.mem_pts_inter_iff.mp hx
    exact ⟨x, by rw [← hQW]; exact hx1, hx2⟩
  have hirr := s.isIrreducible_pts_inter_of_mem_exceptionalDivisors H
    (fun k => P.E (e.symm k).1) (fun k => P.hE _) hEunion (hexc j hj) hne'
  refine Subscheme.isIrreducible_of_pts _ ?_
  convert hirr using 1
  ext y
  rw [Subscheme.mem_pts_inter_iff, hQW]
  rfl

/-- Step 3, "every irreducible component of `W_*' ∩ E_1'` is either a reduced irreducible component
of `F'` or such of `W' ∩ E_j'` with `j (α < j ≤ α')`, provided it has non-empty intersection with
`F'`", second case: a component `G` of `W_*' ∩ E_1'` through a point of `F'` and contained in
`W' ∩ E_j'` (`j > α`, `W' ∩ E_j'` non-singular irreducible) equals `W' ∩ E_j'`.

Proof.  At `x ∈ G ∩ F'` the primes `G_x` (minimal over `W'_x + (z)`, `E_1' = (z)`) and
`(W' ∩ E_j')_x = W'_x + (e)` satisfy `(W' ∩ E_j')_x ⊆ G_x`; by Krull's principal ideal theorem in the
regular local domain `O_{W',x}` they are equal (`sup_span_eq_of_le_of_mem_minimalPrimes`), so the
generic point of the irreducible `W' ∩ E_j'` lies in `G`
(`Subscheme.pts_eq_of_mem_irreducibleComponents_of_inter`).

Deviation from the paper (gap filled): "such of `W' ∩ E_j'`" is read as "a component of `W' ∩ E_j'`,
which is `W' ∩ E_j'` itself because it is irreducible". -/
theorem pts_eq_inter_exceptional_of_mem_irreducibleComponents [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {N : ℕ} {Y : Scheme.{u}}
    {s : MonoidalSuccession X Y} {Q : PrepSetting Y} (hX : IsAmbient X N) (hY : IsAmbient Y N)
    (hs : s.IsPermissibleIOpen P.ℜ P.U) (hQ : P.IsTransform s Q)
    (hresbar : (s.transformI P.barℜ).ResolvedEverywhere)
    (hcentF : ∀ j : Fin Q.α, P.α ≤ j.val → ∀ x ∈ (Q.E j).pts,
      s.composite.base x ∈ (P.ℜ.prepF P.E₁ P.U).pts)
    {G : Subscheme Y} (hG : G ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).irreducibleComponents)
    (j : Fin Q.α) (hj : P.α ≤ j.val) (hne1 : Q.E j ≠ Q.E₁)
    (hresS : (Q.ℜ.W.inter (Q.E j)).pts ⊆
      {y ∈ ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).W.pts |
        ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).ResolvedAt y})
    (hirr : (Q.ℜ.W.inter (Q.E j)).IsIrreducible) (hsub : G.pts ⊆ (Q.ℜ.W.inter (Q.E j)).pts)
    (hmeet : (G.pts ∩ (s.strictTransform (P.ℜ.prepF P.E₁ P.U)).pts).Nonempty) :
    G.pts = (Q.ℜ.W.inter (Q.E j)).pts := by
  classical
  have := hX.1
  have := hY.1
  have hres := P.resolvedEverywhere_extendBy_prepF_of_barℜ s hresbar
  have hXn := hX.2.1
  have hYn := hY.2.1
  have hFpts := P.prepF_transform_pts_eq hXn hs hQ
  have hQ' := hQ
  obtain ⟨hQℜ, hQU, hQE⟩ := hQ'
  obtain ⟨x, hxG, hxF'⟩ := hmeet
  have hxDQ : x ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts :=
    Subscheme.pts_subset_of_mem_irreducibleComponents hG hxG
  have hxF'' : x ∈ (Q.ℜ.prepF Q.E₁ Q.U).pts := by rw [hFpts]; exact hxF'
  obtain ⟨hxWS, hxE1⟩ := Subscheme.mem_pts_inter_iff.mp hxDQ
  have hWs := (P.isSimpleAt_and_isNormallyFlatAlongAt'_prepF_transform hXn hs hQ hres x hxF'').1
  have hWp := Subscheme.isPrime_stalkIdeal_of_isSimpleAt hWs
  obtain ⟨hWSst, -⟩ := Q.ℜ.stalkIdeal_prepWStar_eq Q.E₁ hxWS hWp
  have hnc : (Subscheme.unionFam Q.E).HasOnlyNormalCrossingsWithAt (s.strictTransform (P.ℜ.prepF P.E₁ P.U)) x := by
    rw [← Q.hEunion, hQℜ]
    exact (hres x hxF').2.2
  have : IsRegularLocalRing (Y.presheaf.stalk x) := hYn x
  obtain ⟨Z, hZ, -, hEZ⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    Q.E Q.hE (fun i => iInf_le _ i) hnc
  obtain ⟨z, hz⟩ : ∃ z, Q.E₁.stalkIdeal x = Ideal.span {z} := by
    rcases hEZ ⟨0, Q.hα⟩ with h | ⟨a, -, h⟩
    · exact absurd h ((Subscheme.mem_pts_iff_stalkIdeal_ne_top).mp hxE1)
    · exact ⟨a, h⟩
  have hxEj : x ∈ (Q.E j).pts := (Subscheme.mem_pts_inter_iff.mp (hsub hxG)).2
  obtain ⟨e, he⟩ := Subscheme.exists_stalkIdeal_eq_span_of_isNonsingularIrreducibleCodimOne hYn
    (Q.hE j) hxEj
  have heQ : e ∉ Q.ℜ.W.stalkIdeal x := fun h => P.not_stalkIdeal_le_of_exceptional hQ hcentF j hj hWs
    (by rw [he, Ideal.span_singleton_le_iff_mem]; exact h)
  have hns := P.isNonsingular_inter_exceptional hX hY hQ hcentF j hj hne1 hresS
  have hsimple : (Q.ℜ.W.inter (Q.E j)).IsSimpleAt x := by
    obtain ⟨-, hxres⟩ := hresS (hsub hxG)
    exact Subscheme.isSimpleAt_inter_of_hasOnlyNormalCrossingsWithAt hYn
      (fun i : {i : Fin Q.α // Q.E i ≠ Q.E ⟨0, Q.hα⟩} => Q.E i) (fun i => Q.hE i)
      (Subscheme.mem_pts_inter_iff.mp (hsub hxG)).1 hxres.2.2 ⟨j, hne1⟩ hxEj
      (P.not_stalkIdeal_le_of_exceptional hQ hcentF j hj hWs)
  exact Subscheme.pts_eq_of_mem_irreducibleComponents_of_inter hWSst hWp hz he heQ
    (Subscheme.isReduced_of_isNonsingular hns) hirr
    (Subscheme.isPrime_stalkIdeal_of_isSimpleAt hsimple) hG hxG hsub

/-- Step 3, condition (3) for the transform (pp. 290–291): "Moreover, as is easily seen, if `W_*'`
denotes the union of those irreducible components of `W'` which are not contained in `E_1'` then
`W_*' ∩ E_1' ⊇ (W_* ∩ E_1)'` and every reduced irreducible component of `W_*' ∩ E_1'` is either
contained in `(W_* ∩ E_1)'` or contained in `W' ∩ E_j'` with `j` such that `α < j ≤ α'`.  Since
`f*(ℜ̄)` is resolved at every point of `F'`, `(W_* ∩ E_1)'` is normally flat along `F'`, hence every
component of `(W_* ∩ E_1)'` is either in `F'` or has empty intersection with `F'`.  Therefore every
irreducible component of `W_*' ∩ E_1'` is either a reduced irreducible component of `F'` or such of
`W' ∩ E_j'` with `j (α < j ≤ α')`, provided it has non-empty intersection with `F'`.  We can prove that
`W' ∩ E_j'` for `α < j ≤ α'` are non-singular irreducible subschemes of `X'` and contained in `Ũ'`."
(The relation printed is `⊇`, with a doubled bar, not `=`.)

Here `Ũ'` is realized as the set of points of `W'` at which the tail datum of `f*(ℜ)` is resolved
(it contains `f⁻¹(Ũ) ∩ W'` by `tail_resolvedAt_transform`, and is the open set of
`cond₂_transform_resolvedSet`).

Status: proved from the sentences below, all of which are proved; the irreducibility of `W' ∩ E_j'`
(`isIrreducible_inter_exceptional`) is reduced by induction on the succession to the first-step statement
`MonoidalTransformation.isIrreducible_pts_strictTransform_inter_exceptional`.  In the order of the paper:
(i) "`W_*' ∩ E_1' ⊇ (W_* ∩ E_1)'`": `pts_strictTransform_subset_wStar_inter` (proved; over `X − F` the two
sides agree, `pts_inter_preimage_compl_eq`; not needed for the assembly).
(ii) "every reduced irreducible component of `W_*' ∩ E_1'` is either contained in `(W_* ∩ E_1)'` or
contained in `W' ∩ E_j'` with `j` such that `α < j ≤ α'`":
`pts_subset_strictTransform_or_exists_subset_inter_exceptional` (proved).
(iii) "Since `f*(ℜ̄)` is resolved at every point of `F'`, `(W_* ∩ E_1)'` is normally flat along `F'`,
hence every component of `(W_* ∩ E_1)'` is either in `F'` or has empty intersection with `F'`":
`pts_subset_prepF_of_mem_irreducibleComponents_of_pts_subset_strictTransform` (proved; the Ch. II type
step is `exists_pow_mem_of_isNormallyFlatAlongIdeal_span`, a graded-piece argument).
(iv) "We can prove that `W' ∩ E_j'` for `α < j ≤ α'` are non-singular irreducible subschemes of `X'`
and contained in `Ũ'`": non-singular `isNonsingular_inter_exceptional` (proved), contained in `Ũ'`
`pts_inter_exceptional_subset_resolvedSet` (proved), irreducible `isIrreducible_inter_exceptional` (proved);
and, to conclude "or such of `W' ∩ E_j'`", `pts_eq_inter_exceptional_of_mem_irreducibleComponents`
(proved, given the irreducibility).
Two further tacit points are proved here: if `E_1 ⊆ F` then every component lies in `F'` (so (3) is
vacuous), and otherwise `E_j' ≠ E_1'` for `j > α` (`Q_E_ne_E₁_of_not_pts_subset`), which puts `E_j'`
into the tail `⋃_{i≥2} E_i'`.

Deviation from the paper (gap filled): "as is easily seen", "hence", "therefore", "we can prove"
are tacit; see the individual lemmas. -/
theorem cond₃_transform [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} {Y : Scheme.{u}} {s : MonoidalSuccession X Y}
    {Q : PrepSetting Y} (hX : IsAmbient X N) (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) (hY : IsAmbient Y N)
    (hs : s.IsPermissibleIOpen P.ℜ P.U) (hQ : P.IsTransform s Q)
    (hresbar : (s.transformI P.barℜ).ResolvedEverywhere) {Ubar : Set X} (_hC1 : P.Cond₁)
    (hC2 : P.Cond₂ Ubar) (J' : Set (Fin Q.α))
    (hJ3 : (s.transformI ({ P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ } : DatumI.Raw X)).E =
      Subscheme.unionFam (fun j : J' => Q.E j))
    (hJ' : ∀ j, Q.E j ≠ Q.E ⟨0, Q.hα⟩ → j ∈ J')
    (hcentF : ∀ j : Fin Q.α, P.α ≤ j.val → ∀ x ∈ (Q.E j).pts,
      s.composite.base x ∈ (P.ℜ.prepF P.E₁ P.U).pts)
    (hG1 : ∀ T : Subscheme X, ∀ y : Y, s.composite.base y ∈ T.pts →
      y ∈ (s.strictTransform T).pts ∨ ∃ j : Fin Q.α, P.α ≤ j.val ∧ y ∈ (Q.E j).pts)
    (hcenters : s.CentersIn (P.ℜ.prepF P.E₁ P.U))
    (hperm : s.IsPermissibleIOpen ({ P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ } : DatumI.Raw X) P.U)
    (hexc : ∀ j : Fin Q.α, P.α ≤ j.val → Q.E j ∈ s.exceptionalDivisors) :
    Q.Cond₃ {y ∈ ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).W.pts |
      ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).ResolvedAt y} := by
  classical
  have := hX.1
  have := hY.1
  have hFpts := P.prepF_transform_pts_eq hX.2.1 hs hQ
  intro G hG hGF hGmeet
  rw [hFpts] at hGF hGmeet
  by_cases hE1 : P.E₁.pts ⊆ (P.ℜ.prepF P.E₁ P.U).pts
  · -- `E_1 ⊆ F`: then `E_1' ⊆ F'` and every component of `W_*' ∩ E_1'` lies in `F'`
    exfalso
    apply hGF
    intro y hy
    have h1 := (Subscheme.mem_pts_inter_iff.mp
      (Subscheme.pts_subset_of_mem_irreducibleComponents hG hy)).2
    have h2 : y ∈ (s.strictTransform P.E₁).pts := hQ.2.2 ▸ h1
    exact s.pts_strictTransform_mono hE1 h2
  rcases P.pts_subset_strictTransform_or_exists_subset_inter_exceptional hX hY hcenters hQ hG1
      hG with hD | ⟨j, hj, hsub⟩
  · exact absurd (P.pts_subset_prepF_of_mem_irreducibleComponents_of_pts_subset_strictTransform hX hY
      hs hQ hresbar hG hD hGmeet) hGF
  · have hne1 := P.Q_E_ne_E₁_of_not_pts_subset hcenters hQ hcentF hE1 j hj
    have hresS := P.pts_inter_exceptional_subset_resolvedSet hX hP hY.2.1 hs hQ hC2 J' hJ3 hJ'
      hcentF j hj
    have hne : (Q.ℜ.W.inter (Q.E j)).pts.Nonempty := by
      obtain ⟨x, hx, -⟩ := hGmeet
      exact ⟨x, hsub hx⟩
    have hns := P.isNonsingular_inter_exceptional hX hY hQ hcentF j hj hne1 hresS
    have hirr := P.isIrreducible_inter_exceptional hX hP hQ hC2 hperm hcenters hexc j hj hne
    have heq := P.pts_eq_inter_exceptional_of_mem_irreducibleComponents hX hY hs hQ hresbar hcentF
      hG j hj hne1 hresS hirr hsub hGmeet
    refine ⟨heq ▸ hresS, j, ?_, heq, ?_⟩
    · intro hj0
      have := congrArg Fin.val hj0
      simp only at this
      have := P.hα
      omega
    · obtain ⟨Z, hZ, rfl⟩ := hG
      have h1 : (Subscheme.ofClosed Z).pts = Z := Scheme.IdealSheafData.coe_support_vanishingIdeal Z
      have h2 : Z = (Q.ℜ.W.inter (Q.E j)).support := Closeds.ext (by
        have h3 := heq
        rw [h1] at h3
        exact h3)
      have hGeq : Subscheme.ofClosed Z = Q.ℜ.W.inter (Q.E j) := by
        rw [h2]
        exact (Subscheme.eq_ofClosed_support (Q.ℜ.W.inter (Q.E j))
          (Subscheme.isReduced_of_isNonsingular hns)).symm
      rw [hGeq]
      exact hns

/-- Step 3 (p. 290).  "Let us consider the resolution datum `ℜ̄ = (⋃ E_i; V_1, …, V_β, W,
W_* ∩ E_1; F)` with open restriction `U ∩ F` on `X`.  By Theorem I₂ we have a permissible
succession `f : X' → X` for `(ℜ̄, U ∩ F)` such that `f*(ℜ̄)` is resolved at every point of the
strict transform `F'` of `F`; it is clear that `f` is permissible for `(ℜ, U)`. … Let `Ũ'` be the
open subset `f⁻¹(Ũ) ∩ W'` of `W'`.  Then in view of Lemma 4 of this section and Corollary 2 of
Theorem 5, §6, Ch. III, the resolution datum `(⋃_{i≥2} E_i'; V_1', …, V_β'; W')` is resolved at
every point of `Ũ'`.  Moreover, as is easily seen, … every reduced irreducible component of
`W_*' ∩ E_1'` is either contained in `(W_* ∩ E_1)'` or contained in `W' ∩ E_j'` with `α < j ≤ α'`.
Since `f*(ℜ̄)` is resolved at every point of `F'`, `(W_* ∩ E_1)'` is normally flat along `F'`, hence
every component of `(W_* ∩ E_1)'` is either in `F'` or has empty intersection with `F'`.  Therefore
every irreducible component of `W_*' ∩ E_1'` is either a reduced irreducible component of `F'` or such
of `W' ∩ E_j'` with `α < j ≤ α'`, provided it has non-empty intersection with `F'`.  We can prove that
the `W' ∩ E_j'` for `α < j ≤ α'` are non-singular irreducible subschemes of `X'` contained in `Ũ'`.
Thus, without any loss of generality, we may assume … (3)".  Here
`ℜ̄ = P.barℜ = (ℜ.extendBy (W_* ∩ E_1)).extendBy F`.  (The open restriction is `U ∩ F`.)

Status.  `stepTo_stage₃` is assembled from `cond₃_transform` and the Ch. II input
`Subscheme.isSimpleAt_and_isNormallyFlatAlongAt'_of_chain` of step 2.
In detail: the datum `ℜ̄` (`isDatum_barℜ`), its open restriction `U ∩ F` (`isOpenRestriction_barℜ`, with
`resolvedAt_barℜ`; `(W_* ∩ E_1)_x = F_x` at `x ∈ F ∩ U` by `stalkIdeal_prepF_eq_sup`), Theorem I₂ for it
together with "it is clear that `f` is permissible for `(ℜ, U)`"
(`exists_isPermissibleIOpen_resolvedEverywhere_barℜ`, which also returns the permissibility for
`(ℜ̄, F ∩ U)`); the passage from "`f*(ℜ̄)` is resolved at every point of `F'`" to the hypothesis of steps 1
and 2 (`resolvedEverywhere_extendBy_prepF_of_barℜ`); the presentation `f*(ℜ) = ⋃ E_i'` together with that of
the transformed tail (`MonoidalSuccession.exists_presentation_transformI_tail`: the `E_i'` for `i ≤ α` are the
strict transforms, the tail datum transforms to the sub-union over a set `J'` containing the `j > α`, and the
`E_j'`, `j > α`, lie over the centers); `Q.Cond₁` and `Q.Cond₂` (`cond₁_transform`,
`cond₂_transform_resolvedSet`).

The sentence of p. 290 "Let `Ũ'` be the open subset `f⁻¹(Ũ) ∩ W'` of `W'`.  Then in view of Lemma 4 of this
section and Corollary 2 of Theorem 5, §6, Ch. III, the resolution datum `(⋃_{i≥2} E_i'; V_1', …, V_β'; W')`
is resolved at every point of `Ũ'`" is proved, as follows.  Corollary 2 of Theorem 5 is
`isNormallyFlatAlongAt'_strictTransform` (Ch. III) and Lemma 4 is applied on a neighbourhood of the point
(`DatumI.Raw.hasOnlyNormalCrossingsWithAt_transform_of_resolvedAt_localized`); together they give one transformation
(`DatumI.Raw.resolvedAt_transform_of_resolvedAt`), then a succession
(`MonoidalSuccession.resolvedAt_transformI_of_resolvedAt_open`), then the tail datum
(`MonoidalSuccession.resolvedAt_transformI_tail`) and the tail of the paper's presentation
(`tail_resolvedAt_transform`).  The two cited results do NOT suffice by themselves.  Tacit points, all
"gap filled": (1) `W − B` is dense in `W` (a hypothesis of Corollary 2) because `U ∩ W` is dense in `W` and
misses the center `B` (`DatumI.Raw.pts_subset_closure_diff_of_isPermissibleOpen`); (2) `B` is non-singular
irreducible because it is a nonempty center (`f(y) ∈ B`), and `W` is simple at `f(y)` because `ℜ` is resolved
there; (3) off the exceptional divisor `f` is a local isomorphism, so resolvedness is transported
(`DatumI.Raw.resolvedAt_transform_of_resolvedAt_of_notMem_exceptional`); (4) over the center, simplicity of
`W'` follows from the normal crossings of `E'` with `W'` (`Subscheme.IsSimpleAt.of_hasOnlyNormalCrossingsWithAt`);
(5) the tail `(⋃_{i≥2} E_i; V; W)` is a datum, `U` is an open restriction for it, and `s` is permissible for
it (the normal crossings of `E` with `B` pass to sub-unions: `DatumI.Raw.isDatum_tail`,
`DatumI.Raw.IsOpenRestriction.tail`, `DatumI.Raw.IsPermissible.tail`,
`Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_comp`); (6) the boundary of `f*` of the tail is the
sub-union of the `E_j'` indexed by `J'`, because the strict transform of a sub-union of the components is the
sub-union of the strict transforms (`DatumI.Raw.transform_tail_E`), and the tail of the presentation of
`f*(ℜ)` (the `E_j' ≠ E_1'`) is contained in it; (7) `X` irreducible and non-singular is needed by
Corollary 2.

Condition (3) for the transform is `cond₃_transform`, whose sentences of p. 290 are all proved: `W_*' ∩ E_1' ⊇
(W_* ∩ E_1)'` (the relation printed is `⊇`, with a doubled bar, not `=`) is `pts_strictTransform_subset_wStar_inter`;
the dichotomy for the components of `W_*' ∩ E_1'` is
`pts_subset_strictTransform_or_exists_subset_inter_exceptional`; the normal flatness step is
`pts_subset_prepF_of_mem_irreducibleComponents_of_pts_subset_strictTransform` (using
`exists_pow_mem_of_isNormallyFlatAlongIdeal_span`); non-singularity of `W' ∩ E_j'` and its containment in
`Ũ'` are `isNonsingular_inter_exceptional` and `pts_inter_exceptional_subset_resolvedSet`; irreducibility
of `W' ∩ E_j'` is `isIrreducible_inter_exceptional`.

Deviation from the paper (gap filled): "it is clear", "as is easily seen", "we can prove" are tacit; the
tacit points (1)–(7) above; the dimension `n̄ < n` and the case `F = ∅`. -/
theorem stepTo_stage₃ [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} (hX : IsAmbient X N) (hP : P.ℜ.n ≤ (n : WithBot ℕ∞))
    (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'') (h : P.Stage₁₂) :
    P.StepTo N n (fun _ Q => Q.Stage₃) := by
  classical
  have := hX.1
  obtain ⟨hC1, Ubar, hC2⟩ := h
  obtain ⟨Y, s, hs, hsbar, hresbar⟩ := P.exists_isPermissibleIOpen_resolvedEverywhere_barℜ hX hP hI₂
  have hres := P.resolvedEverywhere_extendBy_prepF_of_barℜ s hresbar
  obtain ⟨⟨hY, hdat, hdim⟩, hopen⟩ := IsGoodDatumI.succession_open s ⟨hX, P.hℜ, hP⟩ P.hU hs
  obtain ⟨α', hα', E', hE', hEq', hcs, J', hJ1, hJ2, hJ3, hperm, hcent, hG1, hexc⟩ :=
    s.exists_presentation_transformI_tail hX.1 hX.2.1 P.E P.hE P.ℜ P.hℜ P.hEunion
      hs.isPermissibleI {i | P.E i ≠ P.E ⟨0, P.hα⟩}
  have := hY.1
  let Q : PrepSetting Y := ⟨α', P.hα.trans_le hα', E', hE', s.transformI P.ℜ, hdat, hEq',
    s.transformOpen P.U, hopen⟩
  have hQ : P.IsTransform s Q := ⟨rfl, rfl, hcs ⟨0, P.hα⟩⟩
  have hJ' : ∀ j : Fin α', Q.E j ≠ Q.E ⟨0, Q.hα⟩ → j ∈ J' := by
    intro j hj
    by_cases hjα : P.α ≤ j.val
    · exact hJ2 j hjα
    · have hlt : j.val < P.α := by omega
      have hji : j = Fin.castLE hα' ⟨j.val, hlt⟩ := Fin.ext rfl
      rw [hji, hJ1]
      intro hi
      apply hj
      have hi' : P.E ⟨j.val, hlt⟩ = P.E ⟨0, P.hα⟩ := by simpa using hi
      show E' j = E' ⟨0, _⟩
      rw [hji]
      have h0 : (⟨0, P.hα.trans_le hα'⟩ : Fin α') = Fin.castLE hα' ⟨0, P.hα⟩ := Fin.ext rfl
      rw [h0, hcs, hcs, hi']
  exact ⟨Y, s, Q, hs, hQ, hY, hdim, P.cond₁_transform hX.2.1 hs hQ hres, _,
    P.cond₂_transform_resolvedSet hX.2.1 hY.2.1 hs hQ hα' hcs hexc hres,
    P.cond₃_transform hX hP hY hs hQ hresbar hC1 hC2 J' hJ3 hJ' (fun j hj x hx =>
      hcent _ (s.centersIn_of_isPermissibleIOpen P.barℜ _ hsbar) j hj x hx) hG1
      (s.centersIn_of_isPermissibleIOpen P.barℜ _ hsbar) (hperm P.U hs) hexc⟩

/-- The components `G` of `W_* ∩ E_1` which are not contained in `F` but meet `F` (p. 291: the
components to be removed by Lemma 5 in order to reach condition (3)*). -/
def badComponents : Set (Subscheme X) :=
  {G | G ∈ ((P.ℜ.prepWStar P.E₁).inter P.E₁).irreducibleComponents ∧
    ¬ G.pts ⊆ (P.ℜ.prepF P.E₁ P.U).pts ∧ (G.pts ∩ (P.ℜ.prepF P.E₁ P.U).pts).Nonempty}

/-- Condition (3)* says that there are no bad components. -/
theorem cond₃Star_iff_badComponents_eq_empty : P.Cond₃Star ↔ P.badComponents = ∅ := by
  constructor
  · intro h
    refine Set.eq_empty_of_forall_notMem fun G hG => ?_
    rcases h G hG.1 with h1 | h2
    · exact hG.2.1 h1
    · obtain ⟨x, hx⟩ := hG.2.2
      exact (Set.eq_empty_iff_forall_notMem.mp h2) x hx
  · intro h G hG
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    exact (Set.eq_empty_iff_forall_notMem.mp h) G ⟨hG, h1, h2⟩

/-- There are finitely many bad components. -/
theorem badComponents_finite [IsAlgebraicScheme X] : P.badComponents.Finite := by
  have : TopologicalSpace.NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  have hfin := finite_setOf_maximal_isIrreducible_subset (X := X)
    ((P.ℜ.prepWStar P.E₁).inter P.E₁).support.isClosed
  refine (hfin.image Subscheme.ofClosed).subset ?_
  rintro G ⟨⟨Z, hZ, rfl⟩, -⟩
  exact ⟨Z, hZ, rfl⟩

/-- A bad component misses `U`: the components meeting `U` lie in `F` (definition of `F`). -/
theorem inter_U_eq_empty_of_mem_badComponents [IsAlgebraicScheme X] {G : Subscheme X}
    (hG : G ∈ P.badComponents) : G.pts ∩ P.U = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx => hG.2.1 ?_
  exact P.ℜ.pts_subset_pts_prepF P.E₁ P.U hG.1 ⟨x, hx⟩

/-- First sentence of p. 291 ("If `G` is any reduced irreducible component of `W_* ∩ E_1` as above, (2) and
(3) imply immediately that the monoidal transformation with center `G` is permissible …"), the part about
the center itself: by (3) a bad component `G` is non-singular, contained in `Ũ` and equal to `W ∩ E_j`
(`j ≥ 2`); being an irreducible component it is irreducible, and it lies in `W`.

Deviation from the paper (gap filled): tacit ("immediately"); the permissibility proper (normal crossings
with `G`, normal flatness of the `V_k` and of `W` along `G` at the points of `G ⊆ Ũ`) is the next step of
`exists_stepTo_lt_badComponents`. -/
theorem isNonsingular_and_isIrreducible_of_mem_badComponents {Ubar : Set X} (hC3 : P.Cond₃ Ubar)
    {G : Subscheme X} (hG : G ∈ P.badComponents) :
    G.IsNonsingular ∧ G.IsIrreducible ∧ G.pts ⊆ Ubar ∧ G.IsContainedIn P.ℜ.W := by
  obtain ⟨hGU, j, -, hGeq, hGns⟩ := hC3 G hG.1 hG.2.1 hG.2.2
  have hGred : G.IsReduced := Subscheme.isReduced_of_isNonsingular hGns
  refine ⟨hGns, ?_, hGU, ?_⟩
  · obtain ⟨Z, hZ, rfl⟩ := hG.1
    refine Subscheme.isIrreducible_of_pts _ ?_
    have h1 : (Subscheme.ofClosed Z).pts = Z := Scheme.IdealSheafData.coe_support_vanishingIdeal Z
    rw [h1]
    exact hZ.1.1
  · exact Subscheme.isContainedIn_of_pts_subset hGred (fun x hx =>
      (Subscheme.mem_pts_inter_iff.mp (hGeq ▸ hx)).1)

/-- At a point `x` of a bad component `G = W ∩ E_j`, the divisor `E_j` does not contain the branch of
`W` through `x`: otherwise every component of `W` through `x`, in particular the component `W_1 ⊄ E_1`
of `W_*` through `x`, would lie in `E_j`, hence in `W ∩ E_j` (the points of `G`), hence in `E_1`
(`G ⊆ E_1`), a contradiction.  This is what makes `W ∩ E_j` simple at `x`.

Deviation from the paper (gap filled): tacit in p. 291, "(2) and (3) imply immediately that the
monoidal transformation `f : X' → X` with center `G` is permissible for the resolution datum
`(⋃_{i≥2} E_i; V_1, …, V_β; W)`". -/
theorem not_stalkIdeal_le_of_mem_badComponents [IsAlgebraicScheme X] {G : Subscheme X}
    (hG : G ∈ P.badComponents) {j : Fin P.α}
    (hGeq : G.pts = (P.ℜ.W.inter (P.E j)).pts) {x : X} (hx : x ∈ G.pts) :
    ¬ (P.E j).stalkIdeal x ≤ P.ℜ.W.stalkIdeal x := by
  intro hle
  have : TopologicalSpace.NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  have hxD : x ∈ ((P.ℜ.prepWStar P.E₁).inter P.E₁).pts :=
    Subscheme.pts_subset_of_mem_irreducibleComponents hG.1 hx
  obtain ⟨hxWs, -⟩ := Subscheme.mem_pts_inter_iff.mp hxD
  obtain ⟨W₁, hW₁, hn, hxW₁⟩ := P.ℜ.exists_mem_irreducibleComponents_of_mem_pts_prepWStar P.E₁ hxWs
  obtain ⟨Z, hZ, rfl⟩ := hW₁
  have hZpts : (Subscheme.ofClosed Z).pts = (Z : Set X) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  have hZirr : IsIrreducible (Z : Set X) := hZ.1.1
  have hxZ : x ∈ (Z : Set X) := hZpts ▸ hxW₁
  set η := hZirr.genericPoint with hη
  have hgen : closure ({η} : Set X) = Z := by
    rw [hη, hZirr.genericPoint_closure_eq, Z.isClosed.closure_eq]
  have hηx : η ⤳ x := by
    rw [specializes_iff_mem_closure, hgen]; exact hxZ
  have hZW : (Subscheme.ofClosed Z).pts ⊆ P.ℜ.W.pts :=
    Subscheme.pts_subset_of_mem_irreducibleComponents ⟨Z, hZ, rfl⟩
  have hcont : (Subscheme.ofClosed Z).IsContainedIn P.ℜ.W :=
    Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced Z) hZW
  have hle' : (P.E j).stalkIdeal x ≤ (Subscheme.ofClosed ⟨closure {η}, isClosed_closure⟩).stalkIdeal x := by
    have e : (⟨closure {η}, isClosed_closure⟩ : Closeds X) = Z := Closeds.ext hgen
    rw [e]
    exact hle.trans (Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hcont x)
  have hηE := Subscheme.mem_pts_of_stalkIdeal_le_ofClosed_closure hηx (P.E j) hle'
  have hZE : (Z : Set X) ⊆ (P.E j).pts := by
    rw [← hgen]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηE) (P.E j).support.isClosed
  have hZG : (Z : Set X) ⊆ G.pts := by
    rw [hGeq]
    exact fun y hy => Subscheme.mem_pts_inter_iff.mpr ⟨hZW (hZpts ▸ hy), hZE hy⟩
  have hGE : G.pts ⊆ P.E₁.pts := fun y hy =>
    (Subscheme.mem_pts_inter_iff.mp (Subscheme.pts_subset_of_mem_irreducibleComponents hG.1 hy)).2
  exact hn (Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced Z)
    (fun y hy => hGE (hZG (hZpts ▸ hy))))

/-- The `E_j` of Condition (3), "`G` is … of the form `W ∩ E_j` with `j ≥ 2`", is different from `E_1`
as a subscheme (the convention of p. 274 allows `E_j = E_1` for `j ≠ 1`): otherwise
`W_* ∩ E_1 ⊆ W ∩ E_1 = G`, so `G` is the only component of `W_* ∩ E_1`, and a component of it meeting
`G` is `G` itself, hence `G ⊆ F`, contradicting "not in `F`".

Deviation from the paper (gap filled; slip in the index convention): Condition (3) is read with
`E_j ≠ E_1` so that `E_j` belongs to the tail `⋃_{i≥2} E_i` of p. 290 (`prepERest`). -/
theorem ne_E₁_of_mem_badComponents [IsAlgebraicScheme X] {G : Subscheme X}
    (hG : G ∈ P.badComponents) {j : Fin P.α}
    (hGeq : G.pts = (P.ℜ.W.inter (P.E j)).pts) : P.E j ≠ P.E₁ := by
  intro hj
  rw [hj] at hGeq
  obtain ⟨y, hyG, hyF⟩ := hG.2.2
  obtain ⟨F_i, hF_i, hFU, hyFi⟩ := P.ℜ.exists_mem_irreducibleComponents_of_mem_pts_prepF' P.E₁ P.U hyF
  have hD : ((P.ℜ.prepWStar P.E₁).inter P.E₁).pts ⊆ G.pts := by
    rw [hGeq]
    intro z hz
    obtain ⟨h1, h2⟩ := Subscheme.mem_pts_inter_iff.mp hz
    exact Subscheme.mem_pts_inter_iff.mpr ⟨P.ℜ.pts_prepWStar_subset P.E₁ h1, h2⟩
  have hsub : F_i.pts ⊆ G.pts := (Subscheme.pts_subset_of_mem_irreducibleComponents hF_i).trans hD
  have heq := Subscheme.pts_eq_of_mem_irreducibleComponents_of_subset hG.1 hF_i hsub
  refine hG.2.1 ?_
  rw [heq]
  exact P.ℜ.pts_subset_pts_prepF P.E₁ P.U hF_i hFU

/-- At a point `x` of a bad component `G = W ∩ E_j`, the intersection `W ∩ E_j` is simple and has the
same stalk as `G` (both are prime, and `G` is a component of `W ∩ E_j`).  Here `hnc` is the normal
crossing of the tail with `W` at `x`, i.e. Condition (2) at `x ∈ G ⊆ Ũ`.

Deviation from the paper (gap filled): tacit in p. 291, "(2) and (3) imply immediately that …
`f : X' → X` with center `G` is permissible". -/
theorem isSimpleAt_and_stalkIdeal_eq_of_mem_badComponents [IsAlgebraicScheme X]
    (hXns : X.IsNonsingular) {G : Subscheme X} (hG : G ∈ P.badComponents) {j : Fin P.α}
    (hGeq : G.pts = (P.ℜ.W.inter (P.E j)).pts) {x : X} (hx : x ∈ G.pts)
    (hnc : (prepERest P.E ⟨0, P.hα⟩).HasOnlyNormalCrossingsWithAt P.ℜ.W x) :
    (P.ℜ.W.inter (P.E j)).IsSimpleAt x ∧ G.stalkIdeal x = (P.ℜ.W.inter (P.E j)).stalkIdeal x := by
  have hj : P.E j ≠ P.E₁ := P.ne_E₁_of_mem_badComponents hG hGeq
  have hxH : x ∈ (P.ℜ.W.inter (P.E j)).pts := hGeq ▸ hx
  obtain ⟨hxW, hxE⟩ := Subscheme.mem_pts_inter_iff.mp hxH
  have hsimple : (P.ℜ.W.inter (P.E j)).IsSimpleAt x :=
    Subscheme.isSimpleAt_inter_of_hasOnlyNormalCrossingsWithAt hXns
      (fun i : {i : Fin P.α // P.E i ≠ P.E₁} => P.E i) (fun i => P.hE i) hxW hnc ⟨j, hj⟩ hxE
      (P.not_stalkIdeal_le_of_mem_badComponents hG hGeq hx)
  refine ⟨hsimple, ?_⟩
  have : IsRegularLocalRing (X.presheaf.stalk x) := hXns x
  have hprime : ((P.ℜ.W.inter (P.E j)).stalkIdeal x).IsPrime := by
    have := hsimple.2
    have := isDomain_of_isRegularLocalRing (X.presheaf.stalk x ⧸ (P.ℜ.W.inter (P.E j)).stalkIdeal x)
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  have hcomp : G ∈ (P.ℜ.W.inter (P.E j)).irreducibleComponents := by
    obtain ⟨Z, hZ, rfl⟩ := hG.1
    have hZpts : (Subscheme.ofClosed Z).pts = (Z : Set X) :=
      Scheme.IdealSheafData.coe_support_vanishingIdeal Z
    refine ⟨Z, ⟨⟨hZ.1.1, ?_⟩, fun y hy hZy => ?_⟩, rfl⟩
    · rw [← hGeq, hZpts]
    · have := hy.2
      rw [← hGeq, hZpts] at this
      exact this
  exact Subscheme.stalkIdeal_eq_of_mem_irreducibleComponents_of_isPrime hcomp hx hprime

/-- Item 1 of the step (3)* (p. 291): "If `G` is any reduced irreducible component of `W_* ∩ E_1` as
above, (2) and (3) imply immediately that the monoidal transformation `f : X' → X` with center `G` is
permissible for the resolution datum `(⋃_{i≥2} E_i; V_1, …, V_β; W)`, hence, for `(ℜ, U)`."  This is the
permissibility for `ℜ = (⋃_{i≥1} E_i; V; W)` itself; the tail is `isPermissible_tail_of_mem_badComponents`
and `(ℜ, U)` is `isPermissibleOpen_of_mem_badComponents`.

Proof.  By (3) `G` is non-singular irreducible, `G ⊆ Ũ` and `G = W ∩ E_j` (`j ≥ 2`).  At `x ∈ G`, by (2) the
tail is resolved: `W` is simple, the `V_k` are normally flat along `W`, and the tail has normal crossings
with `W`.  Then `G` is simple, the `V_k` and `W` are normally flat along `G`
(`DatumI.isNormallyFlatAlongAt'_extendBy`), the tail has normal crossings with `G = W ∩ E_j`
(`Subscheme.hasOnlyNormalCrossingsWithAt_inter`), and, since `G ⊆ E_1`, so does `E = E_1 ∪ ⋯`
(Lemma 3, `Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_of_stalkIdeal_le`).  The "`E_1` factor
tangent to `E_j` modulo `W`" causes no difficulty: `ℜ` need not be resolved at `G`, only `G ⊆ E_1` is used.

Deviation from the paper (gap filled): "immediately" hides the following, all proved: `E_j ≠ E_1`
(`ne_E₁_of_mem_badComponents`), `E_j ⊉ W` at `x` (`not_stalkIdeal_le_of_mem_badComponents`), the equality
`G_x = (W ∩ E_j)_x` and the simplicity of `W ∩ E_j` (`isSimpleAt_and_stalkIdeal_eq_of_mem_badComponents`),
the normal crossings of the tail and of `E` with `G`, and the normal flatness along `G`. -/
theorem isPermissible_of_mem_badComponents [IsAlgebraicScheme X] (hXns : X.IsNonsingular)
    {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar) {G : Subscheme X}
    (hG : G ∈ P.badComponents) : P.ℜ.IsPermissible G := by
  obtain ⟨hGns, hGirr, hGU, hGW⟩ := P.isNonsingular_and_isIrreducible_of_mem_badComponents h₃ hG
  obtain ⟨-, j, -, hGeq, -⟩ := h₃ G hG.1 hG.2.1 hG.2.2
  have hGred : G.IsReduced := Subscheme.isReduced_of_isNonsingular hGns
  have hGWpts : G.pts ⊆ P.ℜ.W.pts := pts_subset_of_isContainedIn hGW
  have hdat := DatumI.Raw.isDatum_extendBy P.hℜ hGred hGWpts
  refine ⟨Or.inr ⟨hGns, hGirr⟩, hdat, fun x hx => ?_⟩
  obtain ⟨hWs, hVf, hrest⟩ := h₂.2.2.2 x (hGU hx)
  have hsimpG : G.IsSimpleAt x := ⟨hx, Subscheme.isRegular_stalk_quot G hGns hx⟩
  refine ⟨hsimpG, DatumI.isNormallyFlatAlongAt'_extendBy P.hℜ hGW hWs hsimpG hVf, ?_⟩
  obtain ⟨hsimple, hst⟩ := P.isSimpleAt_and_stalkIdeal_eq_of_mem_badComponents hXns hG hGeq hx hrest
  have hxH : x ∈ (P.ℜ.W.inter (P.E j)).pts := hGeq ▸ hx
  obtain ⟨-, hxE⟩ := Subscheme.mem_pts_inter_iff.mp hxH
  have hj : P.E j ≠ P.E₁ := P.ne_E₁_of_mem_badComponents hG hGeq
  have hrestG : (prepERest P.E ⟨0, P.hα⟩).HasOnlyNormalCrossingsWithAt G x := by
    have h1 := Subscheme.hasOnlyNormalCrossingsWithAt_inter hXns
      (fun i : {i : Fin P.α // P.E i ≠ P.E₁} => P.E i) (fun i => P.hE i) hrest ⟨j, hj⟩ hxE
    obtain ⟨z, hz, hc, t, htz, ht⟩ := h1
    exact ⟨z, hz, hc, t, htz, hst ▸ ht⟩
  have hGE : G.pts ⊆ P.E₁.pts := fun y hy =>
    (Subscheme.mem_pts_inter_iff.mp (Subscheme.pts_subset_of_mem_irreducibleComponents hG.1 hy)).2
  have hz : (P.E ⟨0, P.hα⟩).stalkIdeal x ≤ G.stalkIdeal x :=
    Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn
      (Subscheme.isContainedIn_of_pts_subset hGred hGE) x
  have hi : (Subscheme.unionFam P.E).HasOnlyNormalCrossingsAt x := P.hEunion ▸ P.hℜ.2.2.1 x
  have := Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_of_stalkIdeal_le hXns P.E P.hE
    ⟨0, P.hα⟩ (Subscheme.isReduced_unionFam P.E P.hE) hx hi hrestG hz
  show P.ℜ.E.HasOnlyNormalCrossingsWithAt G x
  rw [P.hEunion]
  exact this

/-- "hence, for `(ℜ, U)`" (p. 291): the center `G` of a bad component is permissible for `ℜ`
(`isPermissible_of_mem_badComponents`) and lies in `W − U` (a component meeting `U` lies in `F`:
`inter_U_eq_empty_of_mem_badComponents`). -/
theorem isPermissibleOpen_of_mem_badComponents [IsAlgebraicScheme X] (hXns : X.IsNonsingular)
    {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar) {G : Subscheme X}
    (hG : G ∈ P.badComponents) : P.ℜ.IsPermissibleOpen P.U G := by
  obtain ⟨-, -, -, hGW⟩ := P.isNonsingular_and_isIrreducible_of_mem_badComponents h₃ hG
  refine ⟨P.isPermissible_of_mem_badComponents hXns h₂ h₃ hG, fun x hx => ⟨pts_subset_of_isContainedIn hGW hx, fun hU => ?_⟩⟩
  exact (Set.eq_empty_iff_forall_notMem.mp (P.inter_U_eq_empty_of_mem_badComponents hG)) x ⟨hx, hU⟩

/-- "… the monoidal transformation `f : X' → X` with center `G` is permissible for the resolution datum
`(⋃_{i≥2} E_i; V_1, …, V_β; W)`" (p. 291): permissibility passes from `ℜ` to the tail
(`DatumI.Raw.IsPermissible.tail`), the normal crossings with `G` passing to the sub-union `⋃_{i≥2} E_i`. -/
theorem isPermissible_tail_of_mem_badComponents [IsAlgebraicScheme X] (hXns : X.IsNonsingular)
    {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar) {G : Subscheme X}
    (hG : G ∈ P.badComponents) :
    ({ P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ } : DatumI.Raw X).IsPermissible G :=
  DatumI.Raw.IsPermissible.tail hXns P.E P.hE P.hEunion
    (P.isPermissible_of_mem_badComponents hXns h₂ h₃ hG) (Subtype.val : {i : Fin P.α // P.E i ≠ P.E₁} → Fin P.α)

/-- A bad component `G ⊆ W_*` lies in a component `W_1` of `W` which is not contained in `E_1` (the
closure of the generic point of `G`).  Tacit on p. 291 (the component of `W` "through `G`"). -/
theorem exists_comp_of_mem_badComponents [IsAlgebraicScheme X] {G : Subscheme X}
    (hG : G ∈ P.badComponents) :
    ∃ W₁ ∈ P.ℜ.W.irreducibleComponents, ¬ W₁.IsContainedIn P.E₁ ∧ G.pts ⊆ W₁.pts := by
  have : TopologicalSpace.NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  obtain ⟨Z, hZ, rfl⟩ := hG.1
  have hZpts : (Subscheme.ofClosed Z).pts = (Z : Set X) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  have hZirr : IsIrreducible (Z : Set X) := hZ.1.1
  set η := hZirr.genericPoint with hη
  have hgen : closure ({η} : Set X) = Z := by
    rw [hη, hZirr.genericPoint_closure_eq, Z.isClosed.closure_eq]
  have hηZ : η ∈ (Z : Set X) := by rw [← hgen]; exact subset_closure rfl
  have hηD : η ∈ ((P.ℜ.prepWStar P.E₁).inter P.E₁).pts :=
    Subscheme.pts_subset_of_mem_irreducibleComponents hG.1 (hZpts ▸ hηZ)
  obtain ⟨hηWs, -⟩ := Subscheme.mem_pts_inter_iff.mp hηD
  obtain ⟨W₁, hW₁, hn, hηW₁⟩ := P.ℜ.exists_mem_irreducibleComponents_of_mem_pts_prepWStar P.E₁ hηWs
  refine ⟨W₁, hW₁, hn, ?_⟩
  rw [hZpts, ← hgen]
  exact closure_minimal (Set.singleton_subset_iff.mpr hηW₁) W₁.support.isClosed

/-- Localization to an open set `O ⊇ G` on which Lemma 5 applies.  Lemma 5 (p. 287) is stated for "a
non-singular irreducible algebraic scheme", "`W` a non-singular irreducible subscheme of `X`", "`E` a
non-singular irreducible subscheme of codimension 1 of `X` such that `E` does not contain `W`" and "`F` a
reduced irreducible component of `W ∩ E`" which is non-singular.  In its application on p. 291 ("Therefore,
by Lemma 5, we may assume (3)*"), `W` is neither irreducible nor non-singular.  Take `O = V − K`, where
`V` is the open set of Condition (2) (`Ũ = V ∩ W`, so `W` is simple on `O`) and `K` the union of the
components of `W` other than the one `W_1` through `G` (it does not meet `G`, since `W` is simple at the
points of `G ⊆ Ũ`).  Then on `O` the pull-backs of `W`, `E_1` and `G` satisfy the hypotheses of Lemma 5.

Deviation from the paper (gap filled): the localization is tacit. -/
theorem exists_localization_of_mem_badComponents [IsAlgebraicScheme X]
    {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar) {G : Subscheme X}
    (hG : G ∈ P.badComponents) :
    ∃ O : X.Opens, G.pts ⊆ O ∧
      (Subscheme.totalTransform O.ι P.ℜ.W).IsNonsingular ∧
      (Subscheme.totalTransform O.ι P.ℜ.W).IsIrreducible ∧
      (Subscheme.totalTransform O.ι P.E₁).IsNonsingularIrreducibleCodimOne ∧
      ¬ (Subscheme.totalTransform O.ι P.ℜ.W).IsContainedIn (Subscheme.totalTransform O.ι P.E₁) ∧
      Subscheme.totalTransform O.ι G ∈ ((Subscheme.totalTransform O.ι P.ℜ.W).inter
        (Subscheme.totalTransform O.ι P.E₁)).irreducibleComponents ∧
      (Subscheme.totalTransform O.ι G).IsNonsingular := by
  classical
  have : TopologicalSpace.NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  obtain ⟨⟨V, hV, hUbar⟩, -, -, hres⟩ := h₂
  obtain ⟨hGns, hGirr, hGU, hGW⟩ := P.isNonsingular_and_isIrreducible_of_mem_badComponents h₃ hG
  obtain ⟨W₁, hW₁, hW₁E, hGW₁⟩ := P.exists_comp_of_mem_badComponents hG
  have hGsimple : ∀ g ∈ G.pts, P.ℜ.W.IsSimpleAt g := fun g hg => (hres g (hGU hg)).1
  set K : Set X := ⋃ W₂ ∈ {W₂ ∈ P.ℜ.W.irreducibleComponents | W₂ ≠ W₁}, W₂.pts with hK
  have hKcl : IsClosed K := by
    have hfin := finite_setOf_maximal_isIrreducible_subset (X := X) P.ℜ.W.support.isClosed
    refine Set.Finite.isClosed_biUnion ?_ fun W₂ _ => W₂.support.isClosed
    refine (hfin.image Subscheme.ofClosed).subset ?_
    rintro W₂ ⟨⟨Z, hZ, rfl⟩, -⟩
    exact ⟨Z, hZ, rfl⟩
  have hGK : ∀ g ∈ G.pts, g ∉ K := by
    intro g hg hgK
    obtain ⟨W₂, ⟨hW₂, hne⟩, hgW₂⟩ := Set.mem_iUnion₂.mp hgK
    exact hne (Subscheme.eq_of_mem_irreducibleComponents_of_isSimpleAt hW₂ hW₁ hgW₂ (hGW₁ hg)
      (hGsimple g hg))
  let O : X.Opens := ⟨V ∩ Kᶜ, hV.inter hKcl.isOpen_compl⟩
  have hGO : G.pts ⊆ (O : Set X) := fun g hg =>
    ⟨(hUbar ▸ hGU hg : g ∈ V ∩ P.ℜ.W.pts).1, hGK g hg⟩
  have hOW : ∀ x ∈ P.ℜ.W.pts, x ∈ (O : Set X) → x ∈ W₁.pts := by
    intro x hxW hxO
    obtain ⟨W₂, hW₂, hxW₂⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_pts P.ℜ.W hxW
    by_contra hx1
    exact hxO.2 (Set.mem_iUnion₂.mpr ⟨W₂, ⟨hW₂, fun h => hx1 (h ▸ hxW₂)⟩, hxW₂⟩)
  have hOS : ∀ x ∈ (O : Set X), x ∈ P.ℜ.W.pts → P.ℜ.W.IsSimpleAt x := fun x hxO hxW =>
    (hres x (hUbar ▸ ⟨hxO.1, hxW⟩ : x ∈ Ubar)).1
  refine ⟨O, hGO, ?_⟩
  have hjemb : Topology.IsOpenEmbedding (O.ι).base := O.ι.isOpenEmbedding
  have hrange : Set.range (O.ι).base = (O : Set X) := Scheme.Opens.range_ι O
  have hW₁irr : IsIrreducible W₁.pts := by
    obtain ⟨Z, hZ, hZeq⟩ := hW₁
    rw [hZeq, Subscheme.pts_ofClosed]
    exact hZ.1.1
  have hW₁W : W₁.pts ⊆ P.ℜ.W.pts := Subscheme.pts_subset_of_mem_irreducibleComponents hW₁
  obtain ⟨g₀, hg₀⟩ : G.pts.Nonempty := (Subscheme.isIrreducible_pts G hGirr).nonempty
  obtain ⟨g₀', hg₀'⟩ : g₀ ∈ Set.range (O.ι).base := by rw [hrange]; exact hGO hg₀
  have hpreW : (O.ι).base ⁻¹' P.ℜ.W.pts = (O.ι).base ⁻¹' W₁.pts := by
    ext y
    constructor
    · intro hy
      exact hOW _ hy (by rw [← hrange]; exact ⟨y, rfl⟩)
    · intro hy
      exact hW₁W hy
  have hnonempty : ((O.ι).base ⁻¹' W₁.pts).Nonempty := ⟨g₀', by
    show (O.ι).base g₀' ∈ W₁.pts
    rw [hg₀']; exact hGW₁ hg₀⟩
  have hW₁Ws : W₁.pts ⊆ (P.ℜ.prepWStar P.E₁).pts := by
    intro x hx
    rw [DatumI.Raw.pts_prepWStar]
    exact subset_closure ⟨_, ⟨W₁.support, ⟨W₁, hW₁, hW₁E, rfl⟩, rfl⟩, hx⟩
  refine ⟨?_, ?_, FlatPreimm.isNonsingularIrreducibleCodimOne_totalTransform O.ι P.E₁
    (P.hE ⟨0, P.hα⟩), ?_, ?_, FlatPreimm.isNonsingular_totalTransform O.ι G hGns⟩
  · refine Subscheme.isNonsingular_of_stalk_quot _ fun y hy => ?_
    have hjy : (O.ι).base y ∈ P.ℜ.W.pts := by
      rw [FlatPreimm.pts_totalTransform] at hy; exact hy
    have hsimple := hOS ((O.ι).base y) (by rw [← hrange]; exact ⟨y, rfl⟩) hjy
    obtain ⟨e⟩ := FlatPreimm.quotEquiv O.ι P.ℜ.W y
    have := hsimple.2
    exact IsRegularLocalRing.of_ringEquiv e
  · refine Subscheme.isIrreducible_of_pts _ ?_
    rw [FlatPreimm.pts_totalTransform, hpreW]
    exact ⟨hnonempty, hW₁irr.isPreirreducible.preimage hjemb⟩
  · intro hcon
    have h1 := pts_subset_of_isContainedIn hcon
    rw [FlatPreimm.pts_totalTransform, FlatPreimm.pts_totalTransform] at h1
    have h2 : W₁.pts ∩ (O : Set X) ⊆ P.E₁.pts := by
      rintro x ⟨hx1, hxO⟩
      obtain ⟨y, rfl⟩ : x ∈ Set.range (O.ι).base := by rw [hrange]; exact hxO
      exact h1 (show (O.ι).base y ∈ P.ℜ.W.pts from hW₁W hx1)
    have h3 : W₁.pts ⊆ P.E₁.pts :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen hW₁irr.isPreirreducible O.isOpen
        ⟨g₀, hGW₁ hg₀, hGO hg₀⟩).trans (closure_minimal h2 P.E₁.support.isClosed)
    exact hW₁E (Subscheme.isContainedIn_of_pts_subset (by
      obtain ⟨Z, -, hZeq⟩ := hW₁; rw [hZeq]; exact Subscheme.ofClosed_isReduced Z) h3)
  · have h1 := FlatPreimm.totalTransform_mem_irreducibleComponents O.ι
      ((P.ℜ.prepWStar P.E₁).inter P.E₁) hG.1 (y := g₀') (by rw [hg₀']; exact hg₀)
    have hpts : (Subscheme.totalTransform O.ι ((P.ℜ.prepWStar P.E₁).inter P.E₁)).pts =
        ((Subscheme.totalTransform O.ι P.ℜ.W).inter (Subscheme.totalTransform O.ι P.E₁)).pts := by
      ext y
      rw [FlatPreimm.pts_totalTransform, Set.mem_preimage, Subscheme.mem_pts_inter_iff,
        Subscheme.mem_pts_inter_iff, FlatPreimm.pts_totalTransform, FlatPreimm.pts_totalTransform]
      have hyO : (O.ι).base y ∈ (O : Set X) := by rw [← hrange]; exact ⟨y, rfl⟩
      simp only [Set.mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨P.ℜ.pts_prepWStar_subset P.E₁ h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨hW₁Ws (hOW _ h1 hyO), h2⟩
    exact (Subscheme.irreducibleComponents_congr hpts) ▸ h1

/-- The initial stage `(O, W ∩ O, E_1 ∩ O, G ∩ O)` of the iteration of Lemma 5 on the open subscheme `O`. -/
noncomputable def localStage (O : X.Opens) (G : Subscheme X) : IterationStage.{u} :=
  ⟨O.toScheme, Subscheme.totalTransform O.ι P.ℜ.W, Subscheme.totalTransform O.ι P.E₁,
    Subscheme.totalTransform O.ι G⟩

/-- Item 2 of step (3)* (p. 291): "Therefore, by Lemma 5, we may assume that (3)*".  For a bad component
`G`, on the open set `O ⊇ G` of `exists_localization_of_mem_badComponents` the iteration of Lemma 5
(p. 287: "If `F' ⊂ W' ∩ E'`, then we take the monoidal transformation `f' : X'' → X'` with center `F'` …
Then this process ends up by a finite number of steps.") is carried out until the first `n` with
`F^{(n)} ⊄ W^{(n)} ∩ E^{(n)}`; `n ≥ 1` and the first center is `G ∩ O`.  The succession `σ` of the first
`n` monoidal transformations of `O` has strict transforms `W^{(n)}`, `E^{(n)}`, and *its centers are
reduced and lie over `G`, which is closed in `X` and contained in `O`*: this is the hypothesis
"centers closed in `X`" of `MonoidalSuccession.exists_extension` (`Hironaka/Compat/ExtendSuccession.lean`),
by which `σ` extends to a succession of `X` (applied by the caller with `j = O.ι`, `C = G.pts`).

Deviation from the paper (gap filled): the paper applies Lemma 5 on `X` itself, to "a non-singular
irreducible subscheme `W`" which `W` is not; the choice of the iteration (a monoidal transformation with
each center, `MonoidalTransformation.exists_isProper`), its stopping index (`Nat.find` of Lemma 5's
last assertion) and the extension to `X` are tacit. -/
theorem exists_localized_iteration_of_mem_badComponents [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {N : ℕ} (hX : IsAmbient X N)
    {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar) {G : Subscheme X}
    (hG : G ∈ P.badComponents) :
    ∃ (O : X.Opens), G.pts ⊆ O ∧ ∃ n : ℕ, 1 ≤ n ∧
      (IterationStage.runSucc n (P.localStage O G)).length = n ∧
      (∀ i < n, ((IterationStage.run i (P.localStage O G)).F).IsContainedIn
        ((IterationStage.run i (P.localStage O G)).W.inter
          (IterationStage.run i (P.localStage O G)).E)) ∧
      ¬ ((IterationStage.run n (P.localStage O G)).F).IsContainedIn
        ((IterationStage.run n (P.localStage O G)).W.inter
          (IterationStage.run n (P.localStage O G)).E) ∧
      (IterationStage.runSucc n (P.localStage O G)).strictTransform
        (Subscheme.totalTransform O.ι P.ℜ.W) = (IterationStage.run n (P.localStage O G)).W ∧
      (IterationStage.runSucc n (P.localStage O G)).strictTransform
        (Subscheme.totalTransform O.ι P.E₁) = (IterationStage.run n (P.localStage O G)).E ∧
      IsClosed G.pts ∧ G.pts ⊆ Set.range O.ι.base ∧
      (IterationStage.runSucc n (P.localStage O G)).CentersClosedIn O.ι G.pts := by
  classical
  have hXalg : IsAlgebraicScheme X := hX.1
  have hXns : X.IsNonsingular := hX.2.1
  have hXirr : IrreducibleSpace X := hX.2.2.1
  obtain ⟨O, hGO, hWns, hWirr, hE, hEW, hGcomp, hGns⟩ :=
    P.exists_localization_of_mem_badComponents h₂ h₃ hG
  obtain ⟨hGns', hGirr, -, hGW⟩ := P.isNonsingular_and_isIrreducible_of_mem_badComponents h₃ hG
  obtain ⟨g₀, hg₀⟩ : G.pts.Nonempty := (Subscheme.isIrreducible_pts G hGirr).nonempty
  have hrange : Set.range O.ι.base = (O : Set X) := Scheme.Opens.range_ι O
  obtain ⟨g₀', hg₀'⟩ : g₀ ∈ Set.range O.ι.base := by rw [hrange]; exact hGO hg₀
  have : Nonempty O.toScheme := ⟨g₀'⟩
  have : IsAlgebraicScheme O.toScheme := isAlgebraicScheme_of_isOpenImmersion O.ι
  have : IrreducibleSpace X := hXirr
  have hOns : O.toScheme.IsNonsingular := LocSucc.isNonsingular O.ι hXns
  have hOirr : IrreducibleSpace O.toScheme := irreducibleSpace_of_flat_preimmersion O.ι
  set s₀ := P.localStage O G with hs₀
  -- Lemma 5 on `O`
  have hL5 := exists_not_isContainedIn_of_isIteration (X := O.toScheme) inferInstance hOns
    (Subscheme.totalTransform O.ι P.ℜ.W) hWns hWirr (Subscheme.totalTransform O.ι P.E₁) hE hEW
    (Subscheme.totalTransform O.ι G) hGcomp hGns (fun n => IterationStage.run n s₀)
    (IterationStage.isIteration_run s₀) rfl
  classical
  set n := Nat.find hL5 with hn
  have hnspec : ¬ ((IterationStage.run n s₀).F).IsContainedIn
      ((IterationStage.run n s₀).W.inter (IterationStage.run n s₀).E) := Nat.find_spec hL5
  have hlt : ∀ i < n, ((IterationStage.run i s₀).F).IsContainedIn
      ((IterationStage.run i s₀).W.inter (IterationStage.run i s₀).E) := fun i hi =>
    not_not.mp (Nat.find_min hL5 hi)
  have h0 : (s₀.F).IsContainedIn (s₀.W.inter s₀.E) := by
    have hGred : (Subscheme.totalTransform O.ι G).IsReduced :=
      FlatPreimm.isReduced_totalTransform O.ι G (Subscheme.isReduced_of_isNonsingular hGns')
    refine Subscheme.isContainedIn_of_pts_subset hGred ?_
    intro y hy
    have hy' : O.ι.base y ∈ G.pts := by
      have : y ∈ (Subscheme.totalTransform O.ι G).pts := hy
      rwa [FlatPreimm.pts_totalTransform] at this
    refine Subscheme.mem_pts_inter_iff.mpr ⟨?_, ?_⟩
    · show y ∈ (Subscheme.totalTransform O.ι P.ℜ.W).pts
      rw [FlatPreimm.pts_totalTransform]; exact pts_subset_of_isContainedIn hGW hy'
    · show y ∈ (Subscheme.totalTransform O.ι P.E₁).pts
      rw [FlatPreimm.pts_totalTransform]
      exact (Subscheme.mem_pts_inter_iff.mp
        (Subscheme.pts_subset_of_mem_irreducibleComponents hG.1 hy')).2
  refine ⟨O, hGO, n, ?_, IterationStage.length_runSucc n s₀, hlt, hnspec,
    (IterationStage.strictTransform_runSucc n s₀).1, (IterationStage.strictTransform_runSucc n s₀).2,
    G.support.isClosed, fun g hg => by rw [hrange]; exact hGO hg, ?_⟩
  · by_contra hcon
    have : n = 0 := by omega
    rw [this] at hnspec
    exact hnspec h0
  · refine IterationStage.centersClosedIn_runSucc n s₀ O.ι G.pts
      (FlatPreimm.isReduced_totalTransform O.ι G (Subscheme.isReduced_of_isNonsingular hGns')) ?_
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ (Subscheme.totalTransform O.ι G).pts := hz
    rw [FlatPreimm.pts_totalTransform] at hz'
    exact hz'

/-- One blow-up at a bad component (p. 291: "the monoidal transformation `f : X' → X` with center `G`"): its
transform `Q` of `P` (presentation `E'` of `exists_presentation_transformI_tail`, open restriction `U'`) with
the succession `cons G t nil` permissible for `(ℜ, U)` and for the tail, and the data of the presentation
needed for conditions (2) and (3) for `Q`.  Deviation from the paper (gap filled): the construction of the
transformed `(ℜ, U)` is tacit in "replace `(ℜ, U)` by `f*(ℜ, U)`". -/
theorem exists_transform_blowup_of_mem_badComponents [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {N n : ℕ} (hX : IsAmbient X N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar)
    {G : Subscheme X} (hG : G ∈ P.badComponents) (t : MonoidalTransformation X G) :
    ∃ Q : PrepSetting t.X',
      (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).IsPermissibleIOpen P.ℜ P.U ∧
      P.IsTransform (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')) Q ∧
      IsAmbient t.X' N ∧ Q.ℜ.n ≤ (n : WithBot ℕ∞) ∧
      ∃ J' : Set (Fin Q.α),
        ((MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).transformI
          ({ P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ } : DatumI.Raw X)).E =
          Subscheme.unionFam (fun j : J' => Q.E j) ∧
        (∀ j, Q.E j ≠ Q.E ⟨0, Q.hα⟩ → j ∈ J') ∧
        (∀ T : Subscheme X, ∀ y : t.X',
          (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).composite.base y ∈ T.pts →
          y ∈ ((MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).strictTransform T).pts ∨
            ∃ j : Fin Q.α, P.α ≤ j.val ∧ y ∈ (Q.E j).pts) ∧
        (∀ j : Fin Q.α, P.α ≤ j.val →
          Q.E j ∈ (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).exceptionalDivisors) ∧
        (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).IsPermissibleIOpen
          ({ P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ } : DatumI.Raw X) P.U ∧
        ∃ h : P.α ≤ Q.α, ∀ i : Fin P.α, Q.E (Fin.castLE h i) =
          (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).strictTransform (P.E i) := by
  classical
  have := hX.1
  have hperm : P.ℜ.IsPermissibleOpen P.U G := P.isPermissibleOpen_of_mem_badComponents hX.2.1 h₂ h₃ hG
  set s : MonoidalSuccession X t.X' := MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')
    with hsdef
  have hs : s.IsPermissibleIOpen P.ℜ P.U := ⟨hperm, trivial⟩
  obtain ⟨⟨hY, hdat, hdim⟩, hopen⟩ := IsGoodDatumI.succession_open s ⟨hX, P.hℜ, hP⟩ P.hU hs
  obtain ⟨α', hα', E', hE', hEq', hcs, J', hJ1, hJ2, hJ3, hperm', hcent, hG1, hexc⟩ :=
    s.exists_presentation_transformI_tail hX.1 hX.2.1 P.E P.hE P.ℜ P.hℜ P.hEunion
      hs.isPermissibleI {i | P.E i ≠ P.E ⟨0, P.hα⟩}
  have := hY.1
  let Q : PrepSetting t.X' := ⟨α', P.hα.trans_le hα', E', hE', s.transformI P.ℜ, hdat, hEq',
    s.transformOpen P.U, hopen⟩
  have hQ : P.IsTransform s Q := ⟨rfl, rfl, hcs ⟨0, P.hα⟩⟩
  have hJ' : ∀ j : Fin α', Q.E j ≠ Q.E ⟨0, Q.hα⟩ → j ∈ J' := by
    intro j hj
    by_cases hjα : P.α ≤ j.val
    · exact hJ2 j hjα
    · have hlt : j.val < P.α := by omega
      have hji : j = Fin.castLE hα' ⟨j.val, hlt⟩ := Fin.ext rfl
      rw [hji, hJ1]
      intro hi
      apply hj
      have hi' : P.E ⟨j.val, hlt⟩ = P.E ⟨0, P.hα⟩ := by simpa using hi
      show E' j = E' ⟨0, _⟩
      rw [hji]
      have h0 : (⟨0, P.hα.trans_le hα'⟩ : Fin α') = Fin.castLE hα' ⟨0, P.hα⟩ := Fin.ext rfl
      rw [h0, hcs, hcs, hi']
  exact ⟨Q, hs, hQ, hY, hdim, J', hJ3, hJ', hG1, hexc, hperm' P.U hs, hα', hcs⟩

/-- Condition (2) for the transform under any succession permissible for `(ℜ, U)` (in particular one blow-up at
a bad component): p. 291 "Moreover, the conditions (1), (2) and (3) remain to be satisfied if we replace
`(ℜ, U)` by `f*(ℜ, U)`, and `Ũ` by `f⁻¹(Ũ) ∩ (the strict transform of `W` on `X')`" (p. 291).  `F_Q` is the
strict transform of `F` (`prepF_transform_pts_eq`), so lies over `F ⊆ Ũ`, and the tail is resolved over `Ũ`
(`tail_resolvedAt_transform`).  Deviation from the paper (gap filled): the assertion is unproved there. -/
theorem cond₂_transform_of_tail [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} {Y : Scheme.{u}} {s : MonoidalSuccession X Y}
    {Q : PrepSetting Y} (hX : IsAmbient X N) (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) (hY : IsAmbient Y N)
    (hs : s.IsPermissibleIOpen P.ℜ P.U) (hQ : P.IsTransform s Q) {Ubar : Set X}
    (hC2 : P.Cond₂ Ubar) (J' : Set (Fin Q.α))
    (hJ3 : (s.transformI ({ P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ } : DatumI.Raw X)).E =
      Subscheme.unionFam (fun j : J' => Q.E j))
    (hJ' : ∀ j, Q.E j ≠ Q.E ⟨0, Q.hα⟩ → j ∈ J') :
    Q.Cond₂ {y ∈ ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).W.pts |
      ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).ResolvedAt y} := by
  classical
  have := hX.1
  have := hY.1
  have hFpts := P.prepF_transform_pts_eq hX.2.1 hs hQ
  set R' : DatumI.Raw Y := { Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } with hR'
  have hR'dat := Q.isDatum_rest hY.2.1
  obtain ⟨U₀, hU₀, hUeq⟩ := resolvedSetIsOpen_holds Y inferInstance hY.2.1 R' hR'dat
  refine ⟨⟨U₀, hU₀, hUeq⟩, ?_, ?_, fun x hx => hx.2⟩
  · intro y hy
    obtain ⟨hWs, hVf, hnc⟩ := Q.hU.2.2 y hy
    refine ⟨hWs.1, hWs, hVf, ?_⟩
    show (prepERest Q.E ⟨0, Q.hα⟩).HasOnlyNormalCrossingsWithAt Q.ℜ.W y
    exact Subscheme.hasOnlyNormalCrossingsWithAt_prepERest hY.2.1 Q.E Q.hE _ (Q.hEunion ▸ hnc)
  · intro y hy
    have hyW : y ∈ Q.ℜ.W.pts := Q.ℜ.pts_prepWStar_subset Q.E₁
      (Subscheme.mem_pts_inter_iff.mp (Q.ℜ.pts_prepF_subset Q.E₁ Q.U hy)).1
    have hyF' : y ∈ (s.strictTransform (P.ℜ.prepF P.E₁ P.U)).pts := hFpts ▸ hy
    exact ⟨hyW, P.tail_resolvedAt_transform hX hP hY.2.1 hs hQ hC2 J' hJ3 hJ' hyW
      (hC2.2.2.1 (s.pts_strictTransform_subset _ hyF'))⟩

/-- Two of the `E_i` through `x` with the same stalk at `x` are equal. -/
theorem eq_of_stalkIdeal_eq_of_mem_pts {i k : Fin P.α} {x : X} (hi : x ∈ (P.E i).pts)
    (hk : x ∈ (P.E k).pts) (h : (P.E i).stalkIdeal x = (P.E k).stalkIdeal x) : P.E i = P.E k := by
  have hirr : ∀ i, x ∈ (P.E i).pts → (P.E i).IsNonsingular ∧ (P.E i).IsIrreducible := by
    intro i hxi
    have hne : P.E i ≠ Subscheme.empty := by
      intro h
      rw [h, DatumTransform.pts_empty] at hxi
      exact hxi
    obtain ⟨hns, hirr, -⟩ := (P.hE i).resolve_left hne
    exact ⟨hns, hirr⟩
  exact Subscheme.eq_of_stalkIdeal_eq_of_mem_irreducibleComponents
    (Subscheme.mem_irreducibleComponents_self _ (hirr i hi).1 (hirr i hi).2)
    (Subscheme.mem_irreducibleComponents_self _ (hirr k hk).1 (hirr k hk).2) hi hk h

/-- If `E_x ⊆ C_x` for a component `C` through `x`, then `C ⊆ E` (generic point of `C`). -/
theorem pts_subset_of_stalkIdeal_le_of_mem_irreducibleComponents {D C E : Subscheme X}
    (hC : C ∈ D.irreducibleComponents) {x : X} (hx : x ∈ C.pts)
    (h : E.stalkIdeal x ≤ C.stalkIdeal x) : C.pts ⊆ E.pts := by
  obtain ⟨Z, hZmax, rfl⟩ := hC
  have hZpts : (Subscheme.ofClosed Z).pts = (Z : Set X) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  have hZirr : IsIrreducible (Z : Set X) := hZmax.1.1
  set η := hZirr.genericPoint with hη
  have hgen : closure ({η} : Set X) = Z := by
    rw [hη, hZirr.genericPoint_closure_eq, Z.isClosed.closure_eq]
  have hηZ : η ∈ (Z : Set X) := by rw [← hgen]; exact subset_closure rfl
  have hηx : η ⤳ x := specializes_iff_mem_closure.mpr (by rw [hgen]; exact hZpts ▸ hx)
  have hηE : η ∈ E.pts := mem_pts_of_stalkIdeal_le_of_specializes hηx (hZpts ▸ hηZ) h
  rw [hZpts, ← hgen]
  exact closure_minimal (Set.singleton_subset_iff.mpr hηE) E.support.isClosed

/-- The local algebra behind "(1) remains after the blow-up" (p. 291), at a point `x ∈ G ∩ F` of a
bad
component `G = W ∩ E_j`: one regular system of parameters `Z` of `O_{X,x}` such that `G_x`, `E_x`
(`E = ⋃ E_i`, including `E_1`) and `F_x` are generated by a subset, a product of a subset, and a
subset of `Z`.

Proof.  Flag lemma (`exists_rsop_adapted_to_flag`, `W_x ⊆ F_x`) for the tail components, using the
normal crossings of `E` with `F` (condition (1)) and of the tail with `W` (condition (2)); then the
generator `z_1` of `E_1` (which lies in `F_x` and in `G_x = W_x + (z_j)`, and is independent of the
tail components modulo `m²`) replaces one generator `w` of `W_x` (`exists_rsop_replace_of_mem`).

Deviation from the paper (gap filled): the paper asserts that (1) is preserved without proof.  Note
that
`E_1` need not have normal crossings with `W` (it can be tangent to `W` along `G`), so the usual
Lemma 4 computation (`B ⊆ W`, `E` with normal crossings with `W`) does not apply to `F`. -/
theorem exists_adapted_rsop_of_mem_badComponents [IsAlgebraicScheme X] (hXns : X.IsNonsingular)
    (hC1 : P.Cond₁) {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar) {G : Subscheme X}
    (hG : G ∈ P.badComponents) {x : X} (hxG : x ∈ G.pts) (hxF : x ∈ (P.ℜ.prepF P.E₁ P.U).pts) :
    ∃ (Z T J S : Finset (X.presheaf.stalk x)),
      IsRegularSystemOfParameters (X.presheaf.stalk x) Z ∧ T ⊆ Z ∧ J ⊆ Z ∧ S ⊆ Z ∧
      G.stalkIdeal x = Ideal.span (T : Set _) ∧
      P.ℜ.E.stalkIdeal x = Ideal.span {∏ z ∈ J, z} ∧
      (P.ℜ.prepF P.E₁ P.U).stalkIdeal x = Ideal.span (S : Set _) := by
  classical
  have : IsRegularLocalRing (X.presheaf.stalk x) := hXns x
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk x)
  set F := P.ℜ.prepF P.E₁ P.U with hFdef
  have hFred : F.IsReduced := Subscheme.ofClosed_isReduced _
  have hFD : F.pts ⊆ ((P.ℜ.prepWStar P.E₁).inter P.E₁).pts := P.ℜ.pts_prepF_subset P.E₁ P.U
  have hFW : F.IsContainedIn P.ℜ.W := Subscheme.isContainedIn_of_pts_subset hFred fun y hy =>
    P.ℜ.pts_prepWStar_subset P.E₁ (Subscheme.mem_pts_inter_iff.mp (hFD hy)).1
  have hFE1 : F.IsContainedIn P.E₁ := Subscheme.isContainedIn_of_pts_subset hFred fun y hy =>
    (Subscheme.mem_pts_inter_iff.mp (hFD hy)).2
  obtain ⟨hGU, j, -, hGeq, hGns⟩ := h₃ G hG.1 hG.2.1 hG.2.2
  have hGred : G.IsReduced := Subscheme.isReduced_of_isNonsingular hGns
  have hj : P.E j ≠ P.E₁ := P.ne_E₁_of_mem_badComponents hG hGeq
  -- the `F`-side system
  have hNC : (Subscheme.unionFam P.E).HasOnlyNormalCrossingsWithAt F x := P.hEunion ▸ hC1.2.2 x hxF
  obtain ⟨ZF, hZF, ⟨tF, htFZ, hFt⟩, hEF⟩ :=
    DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt P.E P.hE (fun i => iInf_le _ i) hNC
  -- the `W`-side system (tail)
  obtain ⟨hWs, hVf, hrest⟩ := h₂.2.2.2 x (hGU hxG)
  obtain ⟨ZW, hZW, ⟨tW, htWZ, hWt⟩, hEW⟩ :=
    DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
      (fun i : {i : Fin P.α // P.E i ≠ P.E₁} => P.E i) (fun i => P.hE i)
      (fun i => iInf_le _ i) hrest
  have hx1 : x ∈ P.E₁.pts := pts_subset_of_isContainedIn hFE1 hxF
  obtain ⟨b₁, hb₁Z, hb₁⟩ : ∃ b ∈ ZF, P.E₁.stalkIdeal x = Ideal.span {b} := by
    rcases hEF ⟨0, P.hα⟩ with h | h
    · exact absurd h (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hx1)
    · exact h
  have hxEj : x ∈ (P.E j).pts := (Subscheme.mem_pts_inter_iff.mp (hGeq ▸ hxG)).2
  obtain ⟨aj, hajZ, haj⟩ : ∃ a ∈ ZF, (P.E j).stalkIdeal x = Ideal.span {a} := by
    rcases hEF j with h | h
    · exact absurd h (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hxEj)
    · exact h
  have hajb : aj ≠ b₁ := by
    rintro rfl
    exact hj (P.eq_of_stalkIdeal_eq_of_mem_pts hxEj hx1 (haj.trans hb₁.symm))
  set Cf : Finset (X.presheaf.stalk x) := ZF.filter fun b =>
    ∃ i : {i : Fin P.α // P.E i ≠ P.E₁}, (P.E i).stalkIdeal x = Ideal.span {b} with hCf
  set C : Finset (X.presheaf.stalk x) := Cf.erase b₁ with hCdef
  have hajC : aj ∈ C := Finset.mem_erase.mpr ⟨hajb, Finset.mem_filter.mpr ⟨hajZ, ⟨j, hj⟩, haj⟩⟩
  have hCZF : C ⊆ ZF := fun c hc => (Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)).1
  have hQP : P.ℜ.W.stalkIdeal x ≤ F.stalkIdeal x :=
    Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hFW x
  obtain ⟨Z, hZ, hCZ, tP, htPZ, hPt, tQ, htQ, hQt⟩ :=
    exists_rsop_adapted_to_flag (P.ℜ.W.stalkIdeal x) (F.stalkIdeal x) hQP ZF tF ZW tW C
      hZF htFZ hFt hZW htWZ hWt hCZF (by
        intro c hc _
        obtain ⟨-, ⟨i, hi⟩⟩ := Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)
        rcases hEW i with h | ⟨a, ha, hia⟩
        · exfalso
          rw [hi, Ideal.span_singleton_eq_top] at h
          exact (IsLocalRing.mem_maximalIdeal c).mp
            (hZF.1 ▸ Ideal.subset_span (hCZF hc)) h
        · exact ⟨a, ha, hi.symm.trans hia⟩)
  -- the stalk of `G`
  have hGx : G.stalkIdeal x = Ideal.span ((insert aj tQ : Finset (X.presheaf.stalk x)) : Set
      (X.presheaf.stalk x)) := by
    obtain ⟨-, hst⟩ := P.isSimpleAt_and_stalkIdeal_eq_of_mem_badComponents hXns hG hGeq hxG hrest
    rw [hst, show (P.ℜ.W.inter (P.E j)) = P.ℜ.W ⊔ P.E j from rfl, Subscheme.stalkIdeal_sup_eq,
      hQt, haj, Finset.coe_insert, Ideal.span_insert, sup_comm]
  have hZFext := ExtendsToRSOP.of_isRegularSystemOfParameters hZF
  have hPprime : (Ideal.span (tP : Set (X.presheaf.stalk x))).IsPrime := by
    rw [← hPt, hFt]; exact (hZFext.mono htFZ).isPrime_span
  -- `E_j ⊄ F` at `x`
  have hzj : aj ∉ Ideal.span (tP : Set (X.presheaf.stalk x)) := by
    intro hmem
    have hle : (P.E j).stalkIdeal x ≤ F.stalkIdeal x := by
      rw [haj, Ideal.span_singleton_le_iff_mem, hPt]; exact hmem
    obtain ⟨Fi, hFi, hFU, hxFi⟩ := P.ℜ.exists_mem_irreducibleComponents_of_mem_pts_prepF' P.E₁ P.U
        hxF
    have hFiF : Fi.IsContainedIn F := by
      obtain ⟨Z0, hZ0, rfl⟩ := id hFi
      exact Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced _)
        (P.ℜ.pts_subset_pts_prepF P.E₁ P.U hFi hFU)
    have h1 : (P.E j).stalkIdeal x ≤ Fi.stalkIdeal x :=
      hle.trans (Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hFiF x)
    have h2 := pts_subset_of_stalkIdeal_le_of_mem_irreducibleComponents hFi hxFi h1
    have hsub : Fi.pts ⊆ G.pts := by
      intro z hz
      have hzD := Subscheme.pts_subset_of_mem_irreducibleComponents hFi hz
      rw [hGeq]
      exact Subscheme.mem_pts_inter_iff.mpr
        ⟨P.ℜ.pts_prepWStar_subset P.E₁ (Subscheme.mem_pts_inter_iff.mp hzD).1, h2 hz⟩
    have heq := Subscheme.pts_eq_of_mem_irreducibleComponents_of_subset hG.1 hFi hsub
    refine hG.2.1 ?_
    rw [heq]
    exact P.ℜ.pts_subset_pts_prepF P.E₁ P.U hFi hFU
  have hz1P : b₁ ∈ Ideal.span (tP : Set (X.presheaf.stalk x)) := by
    rw [← hPt]
    exact Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hFE1 x
      (hb₁ ▸ Ideal.mem_span_singleton_self b₁)
  have hz1G : b₁ ∈ Ideal.span ((insert aj tQ : Finset (X.presheaf.stalk x)) : Set (X.presheaf.stalk
      x)) := by
    have hGE : G.pts ⊆ P.E₁.pts := fun y hy =>
      (Subscheme.mem_pts_inter_iff.mp (Subscheme.pts_subset_of_mem_irreducibleComponents hG.1 hy)).2
    rw [← hGx]
    exact Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn
      (Subscheme.isContainedIn_of_pts_subset hGred hGE) x
      (hb₁ ▸ Ideal.mem_span_singleton_self b₁)
  have hb₁C : b₁ ∉ C := Finset.notMem_erase _ _
  have hind : b₁ ∉ Ideal.span (C : Set (X.presheaf.stalk x)) ⊔ IsLocalRing.maximalIdeal
      (X.presheaf.stalk x) ^ 2 :=
    rsop_notMem_span_sup_sq hZF hCZF hb₁Z hb₁C
  obtain ⟨w, hwQ, hwC, hZ', hspanP, hspanG⟩ :=
    exists_rsop_replace_of_mem hZ hCZ htQ htPZ hajC hPprime hzj hz1P hz1G hind
  have hCZ' : C ⊆ insert b₁ (Z.erase w) := fun c hc =>
    Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun h => hwC (h ▸ hc), hCZ hc⟩)
  -- `E_x` as a product of members of `C ∪ {b₁}`
  have hL : ∀ i, ∃ L : Finset (X.presheaf.stalk x), L ⊆ insert b₁ C ∧
      (P.E i).stalkIdeal x = Ideal.span {∏ z ∈ L, z} := by
    intro i
    rcases hEF i with h | ⟨a, ha, hia⟩
    · exact ⟨∅, Finset.empty_subset _, by simpa using h⟩
    · refine ⟨{a}, ?_, by simpa using hia⟩
      rw [Finset.singleton_subset_iff]
      by_cases hiE : P.E i = P.E₁
      · rw [hiE, hb₁] at hia
        have : a = b₁ := hZFext.span_singleton_injOn ha hb₁Z hia.symm
        exact Finset.mem_insert.mpr (Or.inl this)
      · by_cases hab : a = b₁
        · exact Finset.mem_insert.mpr (Or.inl hab)
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hab,
            Finset.mem_filter.mpr ⟨ha, ⟨i, hiE⟩, hia⟩⟩)
  choose L hLsub hLe using hL
  have hLZ : ∀ i, L i ⊆ ZF := fun i c hc => by
    rcases Finset.mem_insert.mp (hLsub i hc) with rfl | h
    · exact hb₁Z
    · exact hCZF h
  have hEx : P.ℜ.E.stalkIdeal x = Ideal.span {∏ z ∈ Finset.univ.biUnion L, z} := by
    rw [P.hEunion, Subscheme.unionFam, DatumTransform.stalkIdeal_iInf_fintype]
    rw [← DatumTransform.iInf_span_prod_of_subset hZFext L hLZ]
    exact iInf_congr hLe
  refine ⟨insert b₁ (Z.erase w), insert b₁ ((insert aj tQ).erase w),
    Finset.univ.biUnion L, insert b₁ (tP.erase w), hZ', ?_, ?_, ?_, ?_, hEx, ?_⟩
  · intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hc).1, ?_⟩)
      rcases Finset.mem_insert.mp (Finset.mem_erase.mp hc).2 with rfl | h
      · exact hCZ hajC
      · exact htPZ (htQ h)
  · intro c hc
    obtain ⟨i, -, hci⟩ := Finset.mem_biUnion.mp hc
    rcases Finset.mem_insert.mp (hLsub i hci) with rfl | h
    · exact Finset.mem_insert_self _ _
    · exact hCZ' h
  · intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.erase_subset_erase w htPZ hc)
  · rw [hGx, ← hspanG]
  · rw [hFdef, hPt, ← hspanP]

/-- Condition (1) after one blow-up, pointwise (p. 291: "the conditions (1), (2) and (3) remain to
be
satisfied if we replace `(ℜ, U)` by `f*(ℜ, U)`", the part about `F'`). -/
theorem simple_and_hasOnlyNormalCrossingsWithAt_strictTransform_prepF_of_mem_badComponents
    {N : ℕ} (hX : IsAmbient X N) (hC1 : P.Cond₁) {Ubar : Set X} (h₂ : P.Cond₂ Ubar)
    (h₃ : P.Cond₃ Ubar) {G : Subscheme X} (hG : G ∈ P.badComponents)
    (t : MonoidalTransformation X G) {y : t.X'}
    (hy : y ∈ (Subscheme.strictTransform t (P.ℜ.prepF P.E₁ P.U)).pts) :
    (Subscheme.strictTransform t (P.ℜ.prepF P.E₁ P.U)).IsSimpleAt y ∧
      (P.ℜ.transform t).E.HasOnlyNormalCrossingsWithAt
        (Subscheme.strictTransform t (P.ℜ.prepF P.E₁ P.U)) y := by
  classical
  have := hX.1
  have hXns := hX.2.1
  obtain ⟨hGns, -, -, -⟩ := P.isNonsingular_and_isIrreducible_of_mem_badComponents h₃ hG
  have hB := P.isPermissible_of_mem_badComponents hXns h₂ h₃ hG
  have hX' := (t.isNonsingular_and_isNonsingular_exceptional hXns hGns).1
  have : IsRegularLocalRing (t.X'.presheaf.stalk y) := hX' y
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hXns _
  have hred : (P.ℜ.transform t).E.IsReduced :=
    (DatumI.Raw.transform_isDatum hXns P.ℜ P.hℜ t hB).1.1
  have hxF : t.f y ∈ (P.ℜ.prepF P.E₁ P.U).pts := MonoidalTransformation.pts_strictTransform_subset t
      _ hy
  suffices h : (P.ℜ.transform t).E.HasOnlyNormalCrossingsWithAt
      (Subscheme.strictTransform t (P.ℜ.prepF P.E₁ P.U)) y from
    ⟨Subscheme.IsSimpleAt.of_hasOnlyNormalCrossingsWithAt (hX' y) hy h, h⟩
  by_cases hxG : t.f y ∈ G.pts
  · obtain ⟨Z, T, J, S, hZ, hTZ, hJZ, hSZ, hGT, hEJ, hFS⟩ :=
      P.exists_adapted_rsop_of_mem_badComponents hXns hC1 h₂ h₃ hG hxG hxF
    obtain ⟨K, ⟨Z', hKZ', hZ'⟩, ⟨K₁, hK₁, hD⟩, ⟨T', hT', hW⟩⟩ :=
      t.exists_extendsToRSOP_stalkIdeal_of_adapted hXns hGns hZ hTZ hJZ hSZ hGT hEJ hFS hy
    exact (Subscheme.hasOnlyNormalCrossingsWithAt_iff hred (hX' y)).mpr
      ⟨Z', hZ', ⟨K₁, hK₁.trans hKZ', hD⟩, ⟨T', hT'.trans hKZ', hW⟩⟩
  · -- off the center `f` is a local isomorphism
    obtain ⟨e, hexc, hstr⟩ := DatumTransform.exists_offCenter hXns t y hxG
    have hNC : P.ℜ.E.HasOnlyNormalCrossingsWithAt (P.ℜ.prepF P.E₁ P.U) (t.f y) := hC1.2.2 _ hxF
    obtain ⟨Z, hZ, ⟨J, hJZ, hEJ⟩, ⟨T, hTZ, hFT⟩⟩ :=
      (Subscheme.hasOnlyNormalCrossingsWithAt_iff P.hℜ.1 (hXns _)).mp hNC
    obtain ⟨Z', hZZ', hZ'⟩ := ExtendsToRSOP.map_ringEquiv e
      (ExtendsToRSOP.of_isRegularSystemOfParameters hZ)
    refine (Subscheme.hasOnlyNormalCrossingsWithAt_iff hred (hX' y)).mpr
      ⟨Z', hZ', ⟨J.image e, (Finset.image_subset_image hJZ).trans hZZ', ?_⟩,
        ⟨T.image e, (Finset.image_subset_image hTZ).trans hZZ', ?_⟩⟩
    · show ((Subscheme.strictTransform t P.ℜ.E) ⊓ t.exceptional).stalkIdeal y = _
      rw [Subscheme.stalkIdeal_inf_eq, hstr, hexc, inf_top_eq, hEJ, Ideal.map_span,
        Set.image_singleton, map_prod, Finset.prod_image (fun a _ b _ h => e.injective h)]
    · rw [hstr, hFT, Ideal.map_span, Finset.coe_image]

/-- Condition (1) for the transform under one blow-up with center a bad component (p. 291:
"the conditions (1), (2) and (3) remain to be satisfied if we replace `(ℜ, U)` by `f*(ℜ, U)`", part
(1)).

Deviation from the paper (gap filled): the assertion is unproved there.  Lean proves it by the
local computation of `exists_adapted_rsop_of_mem_badComponents` (one regular system of parameters
adapted to `E`, `F` and `G`; the generator of `E_1` replaces a generator of `W`, which is possible
because `E_1 ⊇ G` and `E_1 ⊇ F`, while `E_1` may be tangent to `W`), and the chart formulas. -/
theorem cond₁_transform_of_mem_badComponents {N : ℕ} (hX : IsAmbient X N) (hC1 : P.Cond₁)
    {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar) {G : Subscheme X}
    (hG : G ∈ P.badComponents) (t : MonoidalTransformation X G) {Q : PrepSetting t.X'}
    (hY : IsAmbient t.X' N)
    (hs : (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).IsPermissibleIOpen P.ℜ P.U)
    (hQ : P.IsTransform (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')) Q) :
    Q.Cond₁ := by
  have := hX.1
  have := hY.1
  exact P.cond₁_transform_of_pointwise hX.2.1 hs hQ fun y hy =>
    P.simple_and_hasOnlyNormalCrossingsWithAt_strictTransform_prepF_of_mem_badComponents hX hC1
      h₂ h₃ hG t hy

/-- Composition of reductions: if `P` steps to a transform satisfying `Stage₁`, and every such
transform steps to one satisfying `Stage₂`, then `P` steps to `Stage₂` (composition of the successions,
`MonoidalSuccession.append`, and of the transforms of `(ℜ, U)`, of `U` and of `E_1`).

Deviation from the paper (gap filled): the paper's iterated "we may assume" (pp. 290–291). -/
theorem StepTo.trans {P : PrepSetting X} {N n : ℕ}
    {Stage₁ Stage₂ : ∀ Y : Scheme.{u}, PrepSetting Y → Prop} (h : P.StepTo N n Stage₁)
    (h' : ∀ (Y : Scheme.{u}) (Q : PrepSetting Y), IsAmbient Y N → Q.ℜ.n ≤ (n : WithBot ℕ∞) →
      Stage₁ Y Q → Q.StepTo N n Stage₂) : P.StepTo N n Stage₂ := by
  obtain ⟨Y, s, Q, hs, hT, hY, hn, hSt⟩ := h
  obtain ⟨Z, s₂, Q₂, hs₂, hT₂, hZ, hn₂, hSt₂⟩ := h' Y Q hY hn hSt
  obtain ⟨hQℜ, hQU, hQE⟩ := hT
  obtain ⟨hQ₂ℜ, hQ₂U, hQ₂E⟩ := hT₂
  rw [hQℜ, hQU] at hs₂
  refine ⟨Z, s.append s₂, Q₂, (MonoidalSuccession.isPermissibleIOpen_append s s₂ _ _).mpr ⟨hs, hs₂⟩,
    ⟨?_, ?_, ?_⟩, hZ, hn₂, hSt₂⟩
  · rw [hQ₂ℜ, hQℜ, MonoidalSuccession.transformI_append]
  · rw [hQ₂U, hQU, MonoidalSuccession.transformOpen_append]
  · rw [hQ₂E, hQE, MonoidalSuccession.strictTransform_append]

/-- If there is no bad component, `P` itself satisfies (3)* (the empty succession). -/
theorem stepTo_of_badComponents_eq_empty {N n : ℕ} (hX : IsAmbient X N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) (h : P.Stage₃) (hbad : P.badComponents = ∅) :
    P.StepTo N n (fun _ Q => Q.Stage₃Star) :=
  ⟨X, MonoidalSuccession.nil X, P, trivial, ⟨rfl, rfl, rfl⟩, hX, hP,
    h.1, (P.cond₃Star_iff_badComponents_eq_empty).mpr hbad, h.2⟩

/-- The strict transform of the center of a monoidal transformation is empty: its stalk ideal is the
saturation of the ideal of the exceptional divisor by itself. -/
theorem _root_.Hironaka.MonoidalTransformation.pts_strictTransform_center {X : Scheme.{u}} {B : Subscheme X}
    (t : MonoidalTransformation X B) : (Subscheme.strictTransform t B).pts = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun y hy => ?_
  have hne := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hy
  apply hne
  rw [Subscheme.strictTransform_stalkIdeal]
  refine top_le_iff.mp (le_trans ?_ (le_iSup _ 1))
  intro a _
  refine Submodule.mem_colon.mpr fun p hp => ?_
  rw [pow_one, SetLike.mem_coe] at hp
  rw [smul_eq_mul]
  exact Ideal.mul_mem_left _ _ hp

/-! ### condition (3) after one blow-up at a bad component -/

section PrepPhase20

open IsLocalRing Classical

/-- The ideal of a bad component `G` in `W` is invertible (`G` is a Cartier divisor in `W`): the
first half of the proof of `exists_iso_strictTransform_of_mem_badComponents`. -/
theorem isInvertibleIdeal_totalTransform_of_mem_badComponents [IsAlgebraicScheme X]
    (hXns : X.IsNonsingular) {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar)
    {G : Subscheme X} (hG : G ∈ P.badComponents) :
    (Subscheme.totalTransform P.ℜ.W.ι G).IsInvertibleIdeal := by
  classical
  have := isAlgebraicScheme_toScheme P.ℜ.W
  have := IsAlgebraicScheme.isNoetherian P.ℜ.W.toScheme
  refine Subscheme.isInvertibleIdeal_of_forall_stalkIdeal_eq_span _ fun y => ?_
  rw [stalkIdeal_totalTransform]
  set x := P.ℜ.W.ι y with hxdef
  by_cases hxG : x ∈ G.pts
  swap
  · exact ⟨1, by rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hxG, Ideal.map_top,
      Ideal.span_singleton_one], one_mem _⟩
  obtain ⟨hGU, j, -, hGeq, -⟩ := h₃ G hG.1 hG.2.1 hG.2.2
  obtain ⟨hWs, -, hrest⟩ := h₂.2.2.2 x (hGU hxG)
  obtain ⟨-, hst⟩ := P.isSimpleAt_and_stalkIdeal_eq_of_mem_badComponents hXns hG hGeq hxG hrest
  have hnle := P.not_stalkIdeal_le_of_mem_badComponents hG hGeq hxG
  obtain ⟨e, he⟩ := Subscheme.exists_stalkIdeal_eq_span_of_isNonsingularIrreducibleCodimOne hXns
    (P.hE j) (Subscheme.mem_pts_inter_iff.mp (hGeq ▸ hxG)).2
  have hreg : IsRegularLocalRing (P.ℜ.W.toScheme.presheaf.stalk y) := by
    obtain ⟨e'⟩ := nonempty_stalk_quot_equiv P.ℜ.W y
    have : IsRegularLocalRing (X.presheaf.stalk x ⧸ P.ℜ.W.stalkIdeal x) := hWs.2
    exact IsRegularLocalRing.of_ringEquiv e'
  have := isDomain_of_isRegularLocalRing (P.ℜ.W.toScheme.presheaf.stalk y)
  set φ := (P.ℜ.W.ι.stalkMap y).hom with hφdef
  have hφ : Function.Surjective φ := P.ℜ.W.ι.stalkMap_surjective y
  have hker : RingHom.ker φ = P.ℜ.W.stalkIdeal x := (stalkIdeal_eq_ker_stalkMap P.ℜ.W y).symm
  have hē : φ e ≠ 0 := by
    intro h
    apply hnle
    rw [he, Ideal.span_singleton_le_iff_mem, ← hker]
    exact h
  have hHst : G.stalkIdeal x = P.ℜ.W.stalkIdeal x ⊔ Ideal.span {e} := by
    rw [hst, show (P.ℜ.W.inter (P.E j)) = P.ℜ.W ⊔ P.E j from rfl, Subscheme.stalkIdeal_sup_eq, he]
  refine ⟨φ e, ?_, mem_nonZeroDivisors_of_ne_zero hē⟩
  rw [hHst, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have : (P.ℜ.W.stalkIdeal x).map φ = ⊥ := by
    rw [← hker]; exact (Ideal.map_eq_bot_iff_le_ker φ).mpr le_rfl
  rw [this, bot_sup_eq]

/-- The strict transform `W'` of `W` under the blow-up at a bad component `G` is isomorphic to `W`
(first assertion of Lemma 5, p. 287, in the situation of p. 291 where `W` is only simple along `G`).

Proof.  The ideal of `G` in `O_{W,x}`, `x ∈ G ⊆ Ũ`, is generated by the image of the equation `e_j`
of
`E_j` (`G_x = W_x + (e_j)`), which is non-zero in the domain `O_{W,x}` (`e_j ∉ W_x`); hence `G` is
an
invertible ideal on `W`, and a monoidal transformation with invertible center is an isomorphism.

Deviation from the paper (gap filled): Lemma 5 is global (`W` non-singular irreducible); here only
the
stalks at the points of `G` are used. -/
theorem exists_iso_strictTransform_of_mem_badComponents [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [IsAlgebraicScheme X] (hXns :
    X.IsNonsingular)
    {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar) {G : Subscheme X}
    (hG : G ∈ P.badComponents) (t : MonoidalTransformation X G) :
    ∃ e : (Subscheme.strictTransform t P.ℜ.W).toScheme ≅ P.ℜ.W.toScheme,
      e.hom ≫ P.ℜ.W.ι = (Subscheme.strictTransform t P.ℜ.W).ι ≫ t.f := by
  exact Subscheme.exists_iso_strictTransform_of_isInvertibleIdeal t P.ℜ.W
    (P.isInvertibleIdeal_totalTransform_of_mem_badComponents hXns h₂ h₃ hG)

end PrepPhase20

section PrepPhase20b

/-- Topological content of `W' ≅ W`: `f` reflects specialization on the points of `W'` and maps them
onto
the points of `W`. -/
theorem _root_.Hironaka.MonoidalTransformation.specializes_and_surjective_of_iso_strictTransform {X
    : Scheme.{u}}
    {B : Subscheme X} (t : MonoidalTransformation X B) (W : Subscheme X)
    (e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f) :
    (∀ y ∈ (Subscheme.strictTransform t W).pts, ∀ z ∈ (Subscheme.strictTransform t W).pts,
      t.f.base y ⤳ t.f.base z → y ⤳ z) ∧
    (∀ w ∈ W.pts, ∃ y ∈ (Subscheme.strictTransform t W).pts, t.f.base y = w) := by
  have hcomp : ∀ u, W.ι.base (e.hom.base u) = t.f.base ((Subscheme.strictTransform t W).ι.base u) :=
    fun u => by
      have := congrArg (fun g => g.base u) he
      simpa using this
  have hWemb : Topology.IsClosedEmbedding W.ι.base := W.ι.isClosedEmbedding
  have heemb : Topology.IsClosedEmbedding e.hom.base := e.hom.isClosedEmbedding
  constructor
  · intro y hy z hz hyz
    have hy' : y ∈ Set.range (Subscheme.strictTransform t W).ι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hy
    have hz' : z ∈ Set.range (Subscheme.strictTransform t W).ι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hz
    obtain ⟨u, rfl⟩ := hy'
    obtain ⟨v, rfl⟩ := hz'
    rw [← hcomp, ← hcomp] at hyz
    have h1 := (hWemb.isInducing.specializes_iff).mp hyz
    have h2 := (heemb.isInducing.specializes_iff).mp h1
    exact h2.map (Subscheme.strictTransform t W).ι.base.hom.continuous
  · intro w hw
    have hw' : w ∈ Set.range W.ι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hw
    obtain ⟨u, rfl⟩ := hw'
    have hu : e.hom.base (e.inv.base u) = u := by
      have := congrArg (fun g => g.base u) e.inv_hom_id
      simpa using this
    refine ⟨(Subscheme.strictTransform t W).ι.base (e.inv.base u), ?_, ?_⟩
    · have : (Subscheme.strictTransform t W).ι.base (e.inv.base u) ∈
          Set.range (Subscheme.strictTransform t W).ι := Set.mem_range_self _
      rwa [Scheme.IdealSheafData.range_subschemeι] at this
    · rw [← hcomp, hu]

end PrepPhase20b

section PrepPhase20g

/-- If `W_x` is prime and `E_x ⊄ W_x`, the generic point of the component of `W` through `x` is a
generization of `x` in `W` not lying on `E`. -/
theorem _root_.Hironaka.Subscheme.exists_specializes_mem_pts_not_mem_of_not_stalkIdeal_le
    {Y : Scheme.{u}} {W E : Subscheme Y} {x : Y} (_hx : x ∈ W.pts) (hWp : (W.stalkIdeal x).IsPrime)
    (hnle : ¬ E.stalkIdeal x ≤ W.stalkIdeal x) : ∃ ω ∈ W.pts, ω ⤳ x ∧ ω ∉ E.pts := by
  classical
  have hmin : W.stalkIdeal x ∈ (W.stalkIdeal x).minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl
  obtain ⟨C, hC, hxC, hCst⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes W x
      hmin
  obtain ⟨Zc, hZc, rfl⟩ := id hC
  have hZpts : (Subscheme.ofClosed Zc).pts = Zc := Scheme.IdealSheafData.coe_support_vanishingIdeal Zc
  obtain ⟨ω, hω⟩ : ∃ ω, IsGenericPoint ω (Zc : Set Y) := QuasiSober.sober hZc.1.1 Zc.isClosed
  have hωx : ω ⤳ x := by
    rw [specializes_iff_mem_closure, hω.def]; rw [hZpts] at hxC; exact hxC
  refine ⟨ω, Subscheme.pts_subset_of_mem_irreducibleComponents hC (hZpts ▸ hω.mem), hωx, fun hωE =>
      ?_⟩
  apply hnle
  have hsub : (Subscheme.ofClosed Zc).pts ⊆ E.pts := by
    rw [hZpts, ← hω.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hωE) E.support.isClosed
  have := Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn
    (Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced Zc) hsub) x
  rw [hCst] at this
  exact this

end PrepPhase20g

section PrepPhase20c

open IsLocalRing Classical

variable {Y : Scheme.{u}}

/-- Condition (3) for one component, from its position inside `W' ∩ E_k'`: let `H = W' ∩ E_k'`
(`k ≠ 1`, i.e. `E_k' ≠ E_1'`) be irreducible with the tail datum of `Q` resolved at its points and
the
equation of `E_k'` not in the ideal of `W'` there.  A component `C` of `W_*' ∩ E_1'` with `C ⊆ H`
and a
point `x ∈ C` is then equal to `H`, and `H` is non-singular (Krull's principal ideal theorem in
`O_{W',x}`, as in `pts_eq_inter_exceptional_of_mem_irreducibleComponents`).

Deviation from the paper (gap filled): "or such of `W' ∩ E_j'`" (p. 290) is read as "equal to
`W' ∩ E_j'`", `W' ∩ E_j'` being irreducible. -/
theorem pts_eq_and_isNonsingular_of_mem_irreducibleComponents_of_pts_subset
    [IsAlgebraicScheme Y] (Q : PrepSetting Y) (hYn : Y.IsNonsingular)
    (k : Fin Q.α) (hk : Q.E k ≠ Q.E₁)
    (hres : (Q.ℜ.W.inter (Q.E k)).pts ⊆
      {y ∈ ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).W.pts |
        ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).ResolvedAt y})
    (hnle : ∀ y ∈ (Q.ℜ.W.inter (Q.E k)).pts, ¬ (Q.E k).stalkIdeal y ≤ Q.ℜ.W.stalkIdeal y)
    (hirr : (Q.ℜ.W.inter (Q.E k)).IsIrreducible)
    {C : Subscheme Y} (hC : C ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).irreducibleComponents)
    {x : Y} (hxC : x ∈ C.pts) (hsub : C.pts ⊆ (Q.ℜ.W.inter (Q.E k)).pts) :
    C.pts = (Q.ℜ.W.inter (Q.E k)).pts ∧ (Q.ℜ.W.inter (Q.E k)).IsNonsingular := by
  classical
  have hns : (Q.ℜ.W.inter (Q.E k)).IsNonsingular := by
    refine Subscheme.isNonsingular_of_stalk_quot _ fun z hz => ?_
    obtain ⟨-, hzres⟩ := hres hz
    obtain ⟨hzW, hzE⟩ := Subscheme.mem_pts_inter_iff.mp hz
    exact (Subscheme.isSimpleAt_inter_of_hasOnlyNormalCrossingsWithAt hYn
      (fun i : {i : Fin Q.α // Q.E i ≠ Q.E ⟨0, Q.hα⟩} => Q.E i) (fun i => Q.hE i) hzW hzres.2.2
      ⟨k, hk⟩ hzE (hnle z hz)).2
  refine ⟨?_, hns⟩
  have hxH : x ∈ (Q.ℜ.W.inter (Q.E k)).pts := hsub hxC
  have hxDQ : x ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts :=
    Subscheme.pts_subset_of_mem_irreducibleComponents hC hxC
  obtain ⟨hxWS, hxE1⟩ := Subscheme.mem_pts_inter_iff.mp hxDQ
  obtain ⟨-, hxres⟩ := hres hxH
  have hWs := hxres.1
  have hWp := Subscheme.isPrime_stalkIdeal_of_isSimpleAt hWs
  obtain ⟨hWSst, -⟩ := Q.ℜ.stalkIdeal_prepWStar_eq Q.E₁ hxWS hWp
  have : IsRegularLocalRing (Y.presheaf.stalk x) := hYn x
  obtain ⟨z, hz⟩ := Subscheme.exists_stalkIdeal_eq_span_of_isNonsingularIrreducibleCodimOne hYn
    (Q.hE ⟨0, Q.hα⟩) hxE1
  obtain ⟨e, he⟩ := Subscheme.exists_stalkIdeal_eq_span_of_isNonsingularIrreducibleCodimOne hYn
    (Q.hE k) (Subscheme.mem_pts_inter_iff.mp hxH).2
  have heQ : e ∉ Q.ℜ.W.stalkIdeal x := fun h => hnle x hxH
    (by rw [he, Ideal.span_singleton_le_iff_mem]; exact h)
  have hsimple : (Q.ℜ.W.inter (Q.E k)).IsSimpleAt x := by
    obtain ⟨-, hxres⟩ := hres hxH
    exact Subscheme.isSimpleAt_inter_of_hasOnlyNormalCrossingsWithAt hYn
      (fun i : {i : Fin Q.α // Q.E i ≠ Q.E ⟨0, Q.hα⟩} => Q.E i) (fun i => Q.hE i)
      (Subscheme.mem_pts_inter_iff.mp hxH).1 hxres.2.2 ⟨k, hk⟩ (Subscheme.mem_pts_inter_iff.mp
          hxH).2
      (hnle x hxH)
  exact Subscheme.pts_eq_of_mem_irreducibleComponents_of_inter hWSst hWp hz he heQ
    (Subscheme.isReduced_of_isNonsingular hns) hirr
    (Subscheme.isPrime_stalkIdeal_of_isSimpleAt hsimple) hC hxC hsub

end PrepPhase20c

section PrepPhase20d

/-- Irreducible closed subsets of `W` pull back to irreducible subsets of `W'` (`W' ≅ W`). -/
theorem _root_.Hironaka.MonoidalTransformation.exists_eq_closure_pts_inter_preimage {X : Scheme.{u}}
    {B : Subscheme X} (t : MonoidalTransformation X B) (W : Subscheme X)
    (h1 : ∀ y ∈ (Subscheme.strictTransform t W).pts, ∀ z ∈ (Subscheme.strictTransform t W).pts,
      t.f.base y ⤳ t.f.base z → y ⤳ z)
    (h2 : ∀ w ∈ W.pts, ∃ y ∈ (Subscheme.strictTransform t W).pts, t.f.base y = w)
    {S : Set X} (hSc : IsClosed S) (hSW : S ⊆ W.pts) {γ : X} (hγ : IsGenericPoint γ S) :
    ∃ y₀ ∈ (Subscheme.strictTransform t W).pts, t.f.base y₀ = γ ∧
      (Subscheme.strictTransform t W).pts ∩ t.f.base ⁻¹' S = closure {y₀} := by
  obtain ⟨y₀, hy₀, hfy₀⟩ := h2 γ (hSW hγ.mem)
  have hW'c : IsClosed (Subscheme.strictTransform t W).pts :=
    (Subscheme.strictTransform t W).support.isClosed
  have hpc : IsClosed (t.f.base ⁻¹' S) := hSc.preimage t.f.base.hom.continuous
  refine ⟨y₀, hy₀, hfy₀, le_antisymm ?_ ?_⟩
  · rintro y ⟨hy, hyS⟩
    have hγy : γ ⤳ t.f.base y := by
      rw [specializes_iff_mem_closure, hγ.def]; exact hyS
    rw [← hfy₀] at hγy
    exact specializes_iff_mem_closure.mp (h1 y₀ hy₀ y hy hγy)
  · refine closure_minimal (Set.singleton_subset_iff.mpr ⟨hy₀, ?_⟩) (hW'c.inter hpc)
    show t.f.base y₀ ∈ S
    rw [hfy₀]; exact hγ.mem

end PrepPhase20d

section PrepPhase20e

/-- Over a point `u ∉ B` of `V` there is a point of the strict transform of `V`. -/
theorem _root_.Hironaka.MonoidalTransformation.exists_pts_strictTransform_over {X : Scheme.{u}}
    {B : Subscheme X} (t : MonoidalTransformation X B) {u : X} (hu : u ∉ B.pts) (V : Subscheme X)
    (hV : u ∈ V.pts) : ∃ y ∈ (Subscheme.strictTransform t V).pts, t.f.base y = u := by
  obtain ⟨Z, j, j₁, hjemb, hj₁, hrange, hrange₁, hjb, hpre_pts⟩ :=
    (MonoidalSuccession.cons B t (MonoidalSuccession.nil
        t.X')).exists_isOpenEmbedding_lift_of_centersIn
      B ⟨subset_rfl, trivial⟩
  have hu' : u ∈ Set.range j.base := by rw [hrange]; exact hu
  obtain ⟨z, rfl⟩ := hu'
  refine ⟨j₁.base z, ?_, ?_⟩
  · have h1 : z ∈ j.base ⁻¹' V.pts := hV
    rw [← hpre_pts] at h1
    exact h1
  · have := hjb z
    simpa [MonoidalSuccession.composite] using this

end PrepPhase20e

section PrepPhase20f

/-- If `V` has a point off the center, its strict transform is not the exceptional divisor. -/
theorem _root_.Hironaka.MonoidalTransformation.strictTransform_ne_exceptional {X : Scheme.{u}} {B :
    Subscheme X}
    (t : MonoidalTransformation X B) (V : Subscheme X) (hu : ∃ u ∈ V.pts, u ∉ B.pts) :
    Subscheme.strictTransform t V ≠ t.exceptional := by
  obtain ⟨u, huV, huB⟩ := hu
  obtain ⟨y, hy, rfl⟩ := t.exists_pts_strictTransform_over huB V huV
  intro h
  rw [h, MonoidalTransformation.pts_exceptional] at hy
  exact huB hy

/-- A reduced subscheme with the same points as a non-singular subscheme is non-singular. -/
theorem _root_.Hironaka.Subscheme.isNonsingular_of_pts_eq_of_isNonsingular {Z : Scheme.{u}} {C H :
    Subscheme Z}
    (hC : C.IsReduced) (hH : H.IsNonsingular) (h : C.pts = H.pts) : C.IsNonsingular := by
  have hHred := Subscheme.isReduced_of_isNonsingular hH
  have : C = H := by
    rw [Subscheme.eq_ofClosed_support C hC, Subscheme.eq_ofClosed_support H hHred]
    congr 1
    exact SetLike.coe_injective h
  rw [this]; exact hH

end PrepPhase20f

/-- The conclusion of Condition (3) for a component `C` of `W_*' ∩ E_1'` equal to `W' ∩ E_k'`. -/
theorem cond₃_conclusion_of_pts_eq {Y : Scheme.{u}} [IsAlgebraicScheme Y]
    (Q : PrepSetting Y) (k : Fin Q.α) (hk : Q.E k ≠ Q.E₁)
    (hres : (Q.ℜ.W.inter (Q.E k)).pts ⊆
      {y ∈ ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).W.pts |
        ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).ResolvedAt y})
    {C : Subscheme Y} (hC : C ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).irreducibleComponents)
    (hCH : C.pts = (Q.ℜ.W.inter (Q.E k)).pts) (hns : (Q.ℜ.W.inter (Q.E k)).IsNonsingular) :
    C.pts ⊆ {y ∈ ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).W.pts |
        ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw Y).ResolvedAt y} ∧
      ∃ j : Fin Q.α, j ≠ ⟨0, Q.hα⟩ ∧ C.pts = (Q.ℜ.W.inter (Q.E j)).pts ∧ C.IsNonsingular := by
  refine ⟨hCH ▸ hres, k, ?_, hCH, ?_⟩
  · intro hj0
    apply hk
    have : k = ⟨0, Q.hα⟩ := hj0
    rw [this]; rfl
  · obtain ⟨Z, hZ, rfl⟩ := hC
    exact Subscheme.isNonsingular_of_pts_eq_of_isNonsingular (Subscheme.ofClosed_isReduced Z) hns
        hCH

/-- Condition (3) for one component, together with the dichotomy: such a component is either
`H = W' ∩ f⁻¹(G)` or lies over a bad component `C₁ ≠ G` of `P` (it is the closure of the point of
`W'`
over the generic point of `C₁`).  Used for the count of bad components. -/
theorem cond₃_and_dichotomy_of_mem_badComponents [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} (hX : IsAmbient X N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar)
    {G : Subscheme X} (hG : G ∈ P.badComponents) (t : MonoidalTransformation X G)
    {Q : PrepSetting t.X'} (hY : IsAmbient t.X' N)
    (hs : (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).IsPermissibleIOpen P.ℜ P.U)
    (hQ : P.IsTransform (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')) Q)
    (J' : Set (Fin Q.α))
    (hJ3 : ((MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).transformI
          ({ P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ } : DatumI.Raw X)).E =
          Subscheme.unionFam (fun j : J' => Q.E j))
    (hJ' : ∀ j, Q.E j ≠ Q.E ⟨0, Q.hα⟩ → j ∈ J')
    (hG1 : ∀ T : Subscheme X, ∀ y : t.X',
          (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).composite.base y ∈ T.pts →
          y ∈ ((MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).strictTransform T).pts ∨
            ∃ j : Fin Q.α, P.α ≤ j.val ∧ y ∈ (Q.E j).pts)
    (hexc : ∀ j : Fin Q.α, P.α ≤ j.val →
          Q.E j ∈ (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).exceptionalDivisors)
    (hα : P.α ≤ Q.α) (hcs : ∀ i : Fin P.α, Q.E (Fin.castLE hα i) =
          (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).strictTransform (P.E i)) :
    ∀ C ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).irreducibleComponents,
      ¬ C.pts ⊆ (Q.ℜ.prepF Q.E₁ Q.U).pts → (C.pts ∩ (Q.ℜ.prepF Q.E₁ Q.U).pts).Nonempty →
      (C.pts ⊆ {y ∈ ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw t.X').W.pts |
      ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw t.X').ResolvedAt y} ∧
        ∃ j : Fin Q.α, j ≠ ⟨0, Q.hα⟩ ∧ C.pts = (Q.ℜ.W.inter (Q.E j)).pts ∧ C.IsNonsingular) ∧
      (C.pts = (Subscheme.strictTransform t P.ℜ.W).pts ∩ t.f.base ⁻¹' G.pts ∨
        ∃ C₁ ∈ P.badComponents, C₁ ≠ G ∧ ∃ y₀ ∈ (Subscheme.strictTransform t P.ℜ.W).pts,
          IsGenericPoint (t.f.base y₀) C₁.pts ∧ C.pts = closure {y₀}):= by
  classical
  have := hX.1
  have := hY.1
  have hXns := hX.2.1
  have hYns := hY.2.1
  set s := MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X') with hsdef
  have hcomp : ∀ y, s.composite.base y = t.f.base y := fun y => by
    simp [hsdef, MonoidalSuccession.composite]
  have hQℜ := hQ.1
  have hW'pts : Q.ℜ.W.pts = (Subscheme.strictTransform t P.ℜ.W).pts := by
    rw [hQℜ]; rfl
  obtain ⟨hGns, hGirr, hGU, hGW⟩ := P.isNonsingular_and_isIrreducible_of_mem_badComponents h₃ hG
  have hperm : P.ℜ.IsPermissibleOpen P.U G := P.isPermissibleOpen_of_mem_badComponents hXns h₂ h₃ hG
  have hdensG : P.ℜ.W.pts ⊆ closure (P.ℜ.W.pts \ G.pts) :=
    DatumI.Raw.pts_subset_closure_diff_of_isPermissibleOpen P.hU hperm
  obtain ⟨e, he⟩ := P.exists_iso_strictTransform_of_mem_badComponents hXns h₂ h₃ hG t
  obtain ⟨hTL1, hTL2⟩ :=
      _root_.Hironaka.MonoidalTransformation.specializes_and_surjective_of_iso_strictTransform
    t P.ℜ.W e he
  -- the resolved set
  set Ubar' := {y ∈ ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw t.X').W.pts |
      ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw t.X').ResolvedAt y} with hUbar'
  have hresAt : ∀ y ∈ Q.ℜ.W.pts, t.f.base y ∈ Ubar → y ∈ Ubar' := fun y hy hyU =>
    ⟨hy, P.tail_resolvedAt_transform hX hP hYns hs hQ h₂ J' hJ3 hJ' hy (hcomp y ▸ hyU)⟩
  intro C hC hCF hCmeet
  obtain ⟨x₀, hx₀C, hx₀F'⟩ := hCmeet
  have hFpts := P.prepF_transform_pts_eq hXns hs hQ
  have hx₀F : t.f.base x₀ ∈ (P.ℜ.prepF P.E₁ P.U).pts := by
    rw [hFpts] at hx₀F'
    exact _root_.Hironaka.MonoidalTransformation.pts_strictTransform_subset t _ hx₀F'
  -- a point of `E_1` outside `G`
  have hu : ∃ u ∈ P.E₁.pts, u ∉ G.pts := by
    obtain ⟨Fi, hFi, ⟨u, huFi, huU⟩, -⟩ :=
      P.ℜ.exists_mem_irreducibleComponents_of_mem_pts_prepF' P.E₁ P.U hx₀F
    refine ⟨u, (Subscheme.mem_pts_inter_iff.mp
      (Subscheme.pts_subset_of_mem_irreducibleComponents hFi huFi)).2, fun huG => ?_⟩
    exact (Set.eq_empty_iff_forall_notMem.mp (P.inter_U_eq_empty_of_mem_badComponents hG)) u
      ⟨huG, huU⟩
  have hEj : ∀ j : Fin Q.α, P.α ≤ j.val → Q.E j = t.exceptional := fun j hj => by
    have := hexc j hj
    simpa [hsdef, MonoidalSuccession.exceptionalDivisors, MonoidalSuccession.strictTransform]
      using this
  obtain ⟨Z, hZmax, rfl⟩ := hC
  have hZpts : (Subscheme.ofClosed Z).pts = Z := Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  obtain ⟨ξ, hξ⟩ : ∃ ξ, IsGenericPoint ξ (Z : Set t.X') := QuasiSober.sober hZmax.1.1 Z.isClosed
  have hξD' : ξ ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts := hZmax.1.2 hξ.mem
  have hξW : ξ ∈ Q.ℜ.W.pts :=
    Q.ℜ.pts_prepWStar_subset Q.E₁ (Subscheme.mem_pts_inter_iff.mp hξD').1
  by_cases hξG : t.f.base ξ ∈ G.pts
  · -- (a) `ξ` lies over `G`
    rcases hG1 G ξ (hcomp ξ ▸ hξG) with hst | ⟨k, hk, hξk⟩
    · exfalso
      have : ξ ∈ (Subscheme.strictTransform t G).pts := hst
      rw [_root_.Hironaka.MonoidalTransformation.pts_strictTransform_center] at this
      exact this
    · have hEk := hEj k hk
      have hEkpts : (Q.E k).pts = t.f.base ⁻¹' G.pts := by
        rw [hEk, MonoidalTransformation.pts_exceptional]
      have hHpts : (Q.ℜ.W.inter (Q.E k)).pts =
          (Subscheme.strictTransform t P.ℜ.W).pts ∩ t.f.base ⁻¹' G.pts := by
        ext y; rw [Subscheme.mem_pts_inter_iff, hW'pts, hEkpts]; rfl
      obtain ⟨γ, hγ⟩ := QuasiSober.sober (Subscheme.isIrreducible_pts G hGirr) G.support.isClosed
      obtain ⟨y₀, hy₀, -, hcl⟩ :=
          _root_.Hironaka.MonoidalTransformation.exists_eq_closure_pts_inter_preimage
        t P.ℜ.W hTL1 hTL2 (S := G.pts) G.support.isClosed
        (pts_subset_of_isContainedIn hGW) hγ
      have hirr : (Q.ℜ.W.inter (Q.E k)).IsIrreducible := by
        refine Subscheme.isIrreducible_of_pts _ ?_
        rw [hHpts, hcl]; exact isIrreducible_singleton.closure
      have hres : (Q.ℜ.W.inter (Q.E k)).pts ⊆ Ubar' := by
        intro y hy
        rw [hHpts] at hy
        exact hresAt y (hW'pts ▸ hy.1) (hGU hy.2)
      have hnle : ∀ y ∈ (Q.ℜ.W.inter (Q.E k)).pts,
          ¬ (Q.E k).stalkIdeal y ≤ Q.ℜ.W.stalkIdeal y := fun y hy =>
        P.not_stalkIdeal_le_of_exceptional_of_dense hQ G hdensG
          (fun j hj x hx => by
            rw [hcomp, hEj j hj, MonoidalTransformation.pts_exceptional] at *
            exact hx)
          k hk (hres hy).2.1
      have hne1 : Q.E k ≠ Q.E₁ := by
        rw [hEk, hQ.2.2]
        exact (t.strictTransform_ne_exceptional P.E₁ hu).symm
      have hsub : (Subscheme.ofClosed Z).pts ⊆ (Q.ℜ.W.inter (Q.E k)).pts := by
        rw [hZpts, ← hξ.def]
        refine closure_minimal (Set.singleton_subset_iff.mpr ?_) (Q.ℜ.W.inter (Q.E
            k)).support.isClosed
        exact Subscheme.mem_pts_inter_iff.mpr ⟨hξW, hEkpts ▸ hξG⟩
      obtain ⟨heq, hns⟩ := Q.pts_eq_and_isNonsingular_of_mem_irreducibleComponents_of_pts_subset
          hYns
        k hne1 hres hnle hirr ⟨Z, hZmax, rfl⟩ (x := x₀) hx₀C hsub
      exact ⟨cond₃_conclusion_of_pts_eq Q k hne1 hres ⟨Z, hZmax, rfl⟩ heq hns,
        Or.inl (heq.trans hHpts)⟩
  · -- (b) `f` is a local isomorphism at `ξ`
    have hcenters : s.CentersIn G := ⟨subset_rfl, trivial⟩
    have hK := P.pts_inter_preimage_compl_eq_of_dense hX hY G hdensG hcenters hQ
    have hξD : ξ ∈ (Subscheme.strictTransform t ((P.ℜ.prepWStar P.E₁).inter P.E₁)).pts := by
      have h3 : ξ ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts ∩ s.composite.base ⁻¹' G.ptsᶜ :=
        ⟨hξD', by rw [Set.mem_preimage, hcomp]; exact hξG⟩
      rw [hK] at h3
      exact h3.1
    have hfξD : t.f.base ξ ∈ ((P.ℜ.prepWStar P.E₁).inter P.E₁).pts :=
      _root_.Hironaka.MonoidalTransformation.pts_strictTransform_subset t _ hξD
    obtain ⟨C₁, hC₁, hfξC₁⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_pts _ hfξD
    obtain ⟨Z₁, hZ₁max, rfl⟩ := id hC₁
    have hZ₁pts : (Subscheme.ofClosed Z₁).pts = Z₁ :=
      Scheme.IdealSheafData.coe_support_vanishingIdeal Z₁
    obtain ⟨η₁, hη₁⟩ : ∃ η, IsGenericPoint η (Z₁ : Set X) := QuasiSober.sober hZ₁max.1.1 Z₁.isClosed
    have hη₁G : η₁ ∉ G.pts := by
      intro hη
      apply hξG
      have : (Z₁ : Set X) ⊆ G.pts := by
        rw [← hη₁.def]; exact closure_minimal (Set.singleton_subset_iff.mpr hη) G.support.isClosed
      exact this (hZ₁pts ▸ hfξC₁)
    -- `C₁` is a bad component
    have hC₁F : ¬ (Subscheme.ofClosed Z₁).pts ⊆ (P.ℜ.prepF P.E₁ P.U).pts := by
      intro hsubF
      have hξF : t.f.base ξ ∈ (P.ℜ.prepF P.E₁ P.U).pts := hsubF hfξC₁
      have hξexc : ξ ∉ t.exceptional.pts := by
        rw [MonoidalTransformation.pts_exceptional]; exact hξG
      have : ξ ∈ (Subscheme.strictTransform t (P.ℜ.prepF P.E₁ P.U)).pts :=
        (MonoidalTransformation.mem_pts_strictTransform_iff_of_notMem t _ hξexc).mpr hξF
      have this' : ξ ∈ (Q.ℜ.prepF Q.E₁ Q.U).pts := by rw [hFpts]; exact this
      apply hCF
      rw [hZpts, ← hξ.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr this')
        (Q.ℜ.prepF Q.E₁ Q.U).support.isClosed
    have hC₁meet : ((Subscheme.ofClosed Z₁).pts ∩ (P.ℜ.prepF P.E₁ P.U).pts).Nonempty := by
      refine ⟨t.f.base x₀, ?_, hx₀F⟩
      rw [hZ₁pts, ← hη₁.def]
      have hx₀Z : x₀ ∈ closure {ξ} := by
        have : x₀ ∈ (Z : Set t.X') := hZpts ▸ hx₀C
        rwa [← hξ.def] at this
      have hfx : t.f.base ξ ∈ closure {η₁} := by rw [hη₁.def]; exact hZ₁pts ▸ hfξC₁
      have hsp : t.f.base ξ ⤳ t.f.base x₀ :=
        (specializes_iff_mem_closure.mpr hx₀Z).map t.f.base.hom.continuous
      exact closure_minimal (Set.singleton_subset_iff.mpr hfx) isClosed_closure
        (specializes_iff_mem_closure.mp hsp)
    have hbad : Subscheme.ofClosed Z₁ ∈ P.badComponents := ⟨hC₁, hC₁F, hC₁meet⟩
    obtain ⟨hC₁U, i, hi0, hC₁eq, hC₁ns⟩ := h₃ _ hC₁ hC₁F hC₁meet
    have hiE₁ : P.E i ≠ P.E₁ := P.ne_E₁_of_mem_badComponents hbad hC₁eq
    set k : Fin Q.α := Fin.castLE hα i with hkdef
    have hEk : Q.E k = Subscheme.strictTransform t (P.E i) := hcs i
    have hC₁Wi : (Subscheme.ofClosed Z₁).pts = (P.ℜ.W.inter (P.E i)).pts := hC₁eq
    have hη₁C₁ : η₁ ∈ (Subscheme.ofClosed Z₁).pts := hZ₁pts ▸ hη₁.mem
    have hη₁Ei : η₁ ∈ (P.E i).pts := (Subscheme.mem_pts_inter_iff.mp (hC₁Wi ▸ hη₁C₁)).2
    have hC₁W : (Subscheme.ofClosed Z₁).pts ⊆ P.ℜ.W.pts := fun y hy =>
      (Subscheme.mem_pts_inter_iff.mp (hC₁Wi ▸ hy)).1
    have hη₁gen : IsGenericPoint η₁ (Subscheme.ofClosed Z₁).pts := by rw [hZ₁pts]; exact hη₁
    obtain ⟨y₀, hy₀, hfy₀, hcl0⟩ :=
        _root_.Hironaka.MonoidalTransformation.exists_eq_closure_pts_inter_preimage
      t P.ℜ.W hTL1 hTL2 (Subscheme.ofClosed Z₁).support.isClosed hC₁W hη₁gen
    have hcl : (Subscheme.strictTransform t P.ℜ.W).pts ∩ t.f.base ⁻¹' (Subscheme.ofClosed Z₁).pts =
        closure {y₀} := hcl0
    have hy₀exc : y₀ ∉ t.exceptional.pts := by
      rw [MonoidalTransformation.pts_exceptional]
      intro h
      exact hη₁G (hfy₀ ▸ h)
    have hy₀E : y₀ ∈ (Subscheme.strictTransform t (P.E i)).pts :=
      (MonoidalTransformation.mem_pts_strictTransform_iff_of_notMem t _ hy₀exc).mpr
        (hfy₀ ▸ hη₁Ei)
    have hHpts : (Q.ℜ.W.inter (Q.E k)).pts =
        (Subscheme.strictTransform t P.ℜ.W).pts ∩ t.f.base ⁻¹' (Subscheme.ofClosed Z₁).pts := by
      ext y
      rw [Subscheme.mem_pts_inter_iff, hW'pts, hEk]
      constructor
      · rintro ⟨hyW, hyE⟩
        refine ⟨hyW, ?_⟩
        rw [Set.mem_preimage, hC₁Wi]
        exact Subscheme.mem_pts_inter_iff.mpr
          ⟨_root_.Hironaka.MonoidalTransformation.pts_strictTransform_subset t _ hyW,
            _root_.Hironaka.MonoidalTransformation.pts_strictTransform_subset t _ hyE⟩
      · intro hy
        refine ⟨hy.1, ?_⟩
        have : y ∈ closure {y₀} := hcl ▸ hy
        exact closure_minimal (Set.singleton_subset_iff.mpr hy₀E)
          (Subscheme.strictTransform t (P.E i)).support.isClosed this
    have hirr : (Q.ℜ.W.inter (Q.E k)).IsIrreducible := by
      refine Subscheme.isIrreducible_of_pts _ ?_
      rw [hHpts, hcl]; exact isIrreducible_singleton.closure
    have hres : (Q.ℜ.W.inter (Q.E k)).pts ⊆ Ubar' := by
      intro y hy
      rw [hHpts] at hy
      exact hresAt y (hW'pts ▸ hy.1) (hC₁U (hZ₁pts ▸ hy.2))
    have hnle : ∀ y ∈ (Q.ℜ.W.inter (Q.E k)).pts,
        ¬ (Q.E k).stalkIdeal y ≤ Q.ℜ.W.stalkIdeal y := by
      intro y hy hle
      have hy' := hy
      rw [hHpts] at hy'
      have hxC₁ : t.f.base y ∈ (Subscheme.ofClosed Z₁).pts := hy'.2
      obtain ⟨hWs, -⟩ := (hres hy).2
      have hWx : (P.ℜ.W.IsSimpleAt (t.f.base y)) := (h₂.2.2.2 _ (hC₁U hxC₁)).1
      have hnleP := P.not_stalkIdeal_le_of_mem_badComponents hbad hC₁eq hxC₁
      obtain ⟨ω, hωW, hωx, hωE⟩ :=
        _root_.Hironaka.Subscheme.exists_specializes_mem_pts_not_mem_of_not_stalkIdeal_le
          hWx.1
          (Subscheme.isPrime_stalkIdeal_of_isSimpleAt hWx) hnleP
      obtain ⟨ω', hω'W, rfl⟩ := hTL2 ω hωW
      have hω'y : ω' ⤳ y := hTL1 ω' hω'W y (hW'pts ▸ (Subscheme.mem_pts_inter_iff.mp hy).1) hωx
      have := mem_pts_of_stalkIdeal_le_of_specializes hω'y (hW'pts ▸ hω'W) hle
      rw [hEk] at this
      exact hωE (_root_.Hironaka.MonoidalTransformation.pts_strictTransform_subset t _ this)
    have hne1 : Q.E k ≠ Q.E₁ := by
      intro heq
      rw [hEk, hQ.2.2] at heq
      obtain ⟨e', hexc', hstr⟩ := DatumTransform.exists_offCenter hXns t y₀ (hfy₀ ▸ hη₁G)
      have h1 := hstr (P.E i)
      have h2 := hstr P.E₁
      rw [heq] at h1
      have h3 : Ideal.map e' ((P.E i).stalkIdeal (t.f.base y₀)) =
          Ideal.map e' (P.E₁.stalkIdeal (t.f.base y₀)) := h1.symm.trans h2
      have h4 : (P.E i).stalkIdeal (t.f.base y₀) = P.E₁.stalkIdeal (t.f.base y₀) := by
        have := congrArg (Ideal.comap e') h3
        rwa [Ideal.comap_map_of_bijective _ e'.bijective,
          Ideal.comap_map_of_bijective _ e'.bijective] at this
      rw [hfy₀] at h4
      have hη₁E1 : η₁ ∈ (P.E ⟨0, P.hα⟩).pts :=
        (Subscheme.mem_pts_inter_iff.mp (Subscheme.pts_subset_of_mem_irreducibleComponents hC₁
          (hZ₁pts ▸ hη₁.mem))).2
      exact hiE₁ (P.eq_of_stalkIdeal_eq_of_mem_pts hη₁Ei hη₁E1 h4)
    have hsub : (Subscheme.ofClosed Z).pts ⊆ (Q.ℜ.W.inter (Q.E k)).pts := by
      rw [hZpts, ← hξ.def, hHpts]
      refine closure_minimal (Set.singleton_subset_iff.mpr ?_) ?_
      · exact ⟨hW'pts ▸ hξW, hfξC₁⟩
      · exact (Subscheme.strictTransform t P.ℜ.W).support.isClosed.inter
          ((Subscheme.ofClosed Z₁).support.isClosed.preimage t.f.base.hom.continuous)
    obtain ⟨heq, hns⟩ := Q.pts_eq_and_isNonsingular_of_mem_irreducibleComponents_of_pts_subset hYns
      k hne1 hres hnle hirr ⟨Z, hZmax, rfl⟩ (x := x₀) hx₀C hsub
    refine ⟨cond₃_conclusion_of_pts_eq Q k hne1 hres ⟨Z, hZmax, rfl⟩ heq hns, Or.inr ?_⟩
    refine ⟨Subscheme.ofClosed Z₁, hbad, fun h => hη₁G ?_, y₀, hy₀, ?_, ?_⟩
    · exact h ▸ hη₁C₁
    · rw [hfy₀]; exact hη₁gen
    · exact heq.trans (hHpts.trans hcl)

/-- Condition (3) for the transform under one blow-up with center a bad component `G`
(p. 291: "the conditions (1), (2) and (3) remain to be satisfied if we replace `(ℜ, U)` by
`f*(ℜ, U)`", part (3)); the set `Ũ'` is the one of `cond₂_transform_of_tail`.

Proof, following p. 290 and Lemma 5 (p. 287).  Let `C` be a component of `W_*' ∩ E_1'` not in `F'`
but meeting `F'`, with generic point `ξ`.  (a) If `ξ` lies over `G`, then `ξ` lies on the
exceptional divisor `E_new = f⁻¹(G)` and `C ⊆ W' ∩ E_new`, which is irreducible (it corresponds to
`G` under the isomorphism `W' ≅ W` of Lemma 5,
`exists_iso_strictTransform_of_mem_badComponents`).  (b) Otherwise `f` is a local isomorphism at
`ξ`, `C` is the strict transform of a component `C₁` of `W_* ∩ E_1` which is not in `F` and meets
`F`, i.e. a bad component, so `C₁ = W ∩ E_i` by (3), and `C ⊆ W' ∩ E_i'`, again irreducible.  In
both cases Krull's principal ideal theorem in `O_{W',x}` shows that `C` is the whole of
`W' ∩ E_k'` (`pts_eq_and_isNonsingular_of_mem_irreducibleComponents_of_pts_subset`).

Deviation from the paper (gap filled): "remain to be satisfied" is unproved in the paper. -/
theorem cond₃_transform_of_mem_badComponents [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} (hX : IsAmbient X N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar)
    {G : Subscheme X} (hG : G ∈ P.badComponents) (t : MonoidalTransformation X G)
    {Q : PrepSetting t.X'} (hY : IsAmbient t.X' N)
    (hs : (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).IsPermissibleIOpen P.ℜ P.U)
    (hQ : P.IsTransform (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')) Q)
    (J' : Set (Fin Q.α))
    (hJ3 : ((MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).transformI
          ({ P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ } : DatumI.Raw X)).E =
          Subscheme.unionFam (fun j : J' => Q.E j))
    (hJ' : ∀ j, Q.E j ≠ Q.E ⟨0, Q.hα⟩ → j ∈ J')
    (hG1 : ∀ T : Subscheme X, ∀ y : t.X',
          (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).composite.base y ∈ T.pts →
          y ∈ ((MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).strictTransform T).pts ∨
            ∃ j : Fin Q.α, P.α ≤ j.val ∧ y ∈ (Q.E j).pts)
    (hexc : ∀ j : Fin Q.α, P.α ≤ j.val →
          Q.E j ∈ (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).exceptionalDivisors)
    (hα : P.α ≤ Q.α) (hcs : ∀ i : Fin P.α, Q.E (Fin.castLE hα i) =
          (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).strictTransform (P.E i)) :
    Q.Cond₃ {y ∈ ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw t.X').W.pts |
      ({ Q.ℜ with E := prepERest Q.E ⟨0, Q.hα⟩ } : DatumI.Raw t.X').ResolvedAt y} :=
  fun C hC hCF hCm =>
    (P.cond₃_and_dichotomy_of_mem_badComponents hX hP h₂ h₃ hG t hY hs hQ J' hJ3 hJ' hG1 hexc hα hcs
        C hC hCF hCm).1

/-- The data of the transform `Q` of `P` under the single blow-up `t` with center `G` (the output of
`exists_transform_blowup_of_mem_badComponents`): the succession is permissible for `(ℜ, U)`, `Q` is
the
transform, the tail of the transformed boundary is indexed by `J'`, every point of `X` has its
strict
transform or an exceptional divisor above it, the new divisors `E_j'` (`j ≥ α`) are exceptional, and
the
first `α` members of the presentation of `Q` are the strict transforms of the `E_i`. -/
def BlowupTransform {G : Subscheme X} (t : MonoidalTransformation X G) (Q : PrepSetting t.X') : Prop
    :=
  (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).IsPermissibleIOpen P.ℜ P.U ∧
  P.IsTransform (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')) Q ∧
  ∃ J' : Set (Fin Q.α),
    ((MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).transformI
      ({ P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ } : DatumI.Raw X)).E =
        Subscheme.unionFam (fun j : J' => Q.E j) ∧
    (∀ j, Q.E j ≠ Q.E ⟨0, Q.hα⟩ → j ∈ J') ∧
    (∀ T : Subscheme X, ∀ y : t.X',
      (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).composite.base y ∈ T.pts →
      y ∈ ((MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).strictTransform T).pts ∨
        ∃ j : Fin Q.α, P.α ≤ j.val ∧ y ∈ (Q.E j).pts) ∧
    (∀ j : Fin Q.α, P.α ≤ j.val →
      Q.E j ∈ (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).exceptionalDivisors) ∧
    ∃ hα : P.α ≤ Q.α, ∀ i : Fin P.α, Q.E (Fin.castLE hα i) =
      (MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X')).strictTransform (P.E i)

/-- Reformulation of `exists_transform_blowup_of_mem_badComponents` with `BlowupTransform`. -/
theorem exists_blowupTransform_of_mem_badComponents [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {N n : ℕ} (hX : IsAmbient X N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar)
    {G : Subscheme X} (hG : G ∈ P.badComponents) (t : MonoidalTransformation X G) :
    ∃ Q : PrepSetting t.X', P.BlowupTransform t Q ∧ IsAmbient t.X' N ∧ Q.ℜ.n ≤ (n : WithBot ℕ∞)
        := by
  obtain ⟨Q, hs, hQ, hY, hn, J', hJ3, hJ', hG1, hexc, -, hα, hcs⟩ :=
    P.exists_transform_blowup_of_mem_badComponents hX hP h₂ h₃ hG t
  exact ⟨Q, ⟨hs, hQ, J', hJ3, hJ', hG1, hexc, hα, hcs⟩, hY, hn⟩

/-- `cond₃_and_dichotomy_of_mem_badComponents` for a `BlowupTransform`. -/
theorem cond₃_and_dichotomy_of_blowupTransform [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} (hX : IsAmbient X N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar)
    {G : Subscheme X} (hG : G ∈ P.badComponents) (t : MonoidalTransformation X G)
    {Q : PrepSetting t.X'} (hY : IsAmbient t.X' N) (hBT : P.BlowupTransform t Q) :
    ∀ C ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).irreducibleComponents,
      ¬ C.pts ⊆ (Q.ℜ.prepF Q.E₁ Q.U).pts → (C.pts ∩ (Q.ℜ.prepF Q.E₁ Q.U).pts).Nonempty →
      (C.pts = (Subscheme.strictTransform t P.ℜ.W).pts ∩ t.f.base ⁻¹' G.pts ∨
        ∃ C₁ ∈ P.badComponents, C₁ ≠ G ∧ ∃ y₀ ∈ (Subscheme.strictTransform t P.ℜ.W).pts,
          IsGenericPoint (t.f.base y₀) C₁.pts ∧ C.pts = closure {y₀}) := by
  obtain ⟨hs, hQ, J', hJ3, hJ', hG1, hexc, hα, hcs⟩ := hBT
  intro C hC hCF hCm
  exact (P.cond₃_and_dichotomy_of_mem_badComponents hX hP h₂ h₃ hG t hY hs hQ J' hJ3 hJ' hG1 hexc
    hα hcs C hC hCF hCm).2

/-- Two irreducible components of the same subscheme with the same points are equal. -/
theorem _root_.Hironaka.Subscheme.eq_of_pts_eq_of_mem_irreducibleComponents {Z : Scheme.{u}}
    {D C C' : Subscheme Z} (hC : C ∈ D.irreducibleComponents) (hC' : C' ∈ D.irreducibleComponents)
    (h : C.pts = C'.pts) : C = C' := by
  obtain ⟨A, -, rfl⟩ := hC
  obtain ⟨A', -, rfl⟩ := hC'
  rw [Subscheme.pts_ofClosed, Subscheme.pts_ofClosed] at h
  rw [SetLike.coe_injective h]

/-- The image of a subscheme of `X'` in `X`, as the reduced subscheme on the closure of the image.
-/
noncomputable def imageOfClosure {Y Z : Scheme.{u}} (g : Y ⟶ Z) (C : Subscheme Y) : Subscheme Z :=
  Subscheme.ofClosed ⟨closure (g.base '' C.pts), isClosed_closure⟩

theorem imageOfClosure_eq_of_closure_eq {Y Z : Scheme.{u}} (g : Y ⟶ Z) (C : Subscheme Y)
    {D : Subscheme Z} (hD : D.IsReduced) (h : closure (g.base '' C.pts) = D.pts) :
    imageOfClosure g C = D := by
  unfold imageOfClosure
  have : (⟨closure (g.base '' C.pts), isClosed_closure⟩ : TopologicalSpace.Closeds Z) = D.support :=
    TopologicalSpace.Closeds.ext h
  rw [this, ← Subscheme.eq_ofClosed_support D hD]

/-- One blow-up at a bad component `G`: the map `C ↦ closure f(C)` sends the bad components of `Q`
to bad components of `P`, injectively; the bad components of `Q` lying over `G` (equal to
`H = W' ∩ f⁻¹(G)`) go to `G`, the others to bad components `≠ G`.

This is the counting step behind "Lemma 5 removes the bad component `G`" (p. 291, p. 288).  Over
the generic point of a bad component `C₁ ≠ G` there is exactly one point of `W'` (as `W' ≅ W`), so
a component of `W'_* ∩ E_1'` over `C₁` is determined by `C₁`. -/
theorem imageOfClosure_mapsTo_injOn_badComponents [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} (hX : IsAmbient X N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar)
    {G : Subscheme X} (hG : G ∈ P.badComponents) (t : MonoidalTransformation X G)
    {Q : PrepSetting t.X'} (hY : IsAmbient t.X' N) (hBT : P.BlowupTransform t Q) :
    Set.MapsTo (imageOfClosure t.f) Q.badComponents P.badComponents ∧
      Set.InjOn (imageOfClosure t.f) Q.badComponents ∧
      ∀ C ∈ Q.badComponents, imageOfClosure t.f C = G →
        C.pts = (Subscheme.strictTransform t P.ℜ.W).pts ∩ t.f.base ⁻¹' G.pts := by
  classical
  have := hX.1
  have hXns := hX.2.1
  obtain ⟨hGns, hGirr, hGU, hGW⟩ := P.isNonsingular_and_isIrreducible_of_mem_badComponents h₃ hG
  obtain ⟨e, he⟩ := P.exists_iso_strictTransform_of_mem_badComponents hXns h₂ h₃ hG t
  obtain ⟨hTL1, hTL2⟩ :=
      _root_.Hironaka.MonoidalTransformation.specializes_and_surjective_of_iso_strictTransform
    t P.ℜ.W e he
  have hdich := P.cond₃_and_dichotomy_of_blowupTransform hX hP h₂ h₃ hG t hY hBT
  have hGred : G.IsReduced := Subscheme.isReduced_of_isNonsingular hGns
  have hcomp_red : ∀ {D C : Subscheme X}, C ∈ D.irreducibleComponents → C.IsReduced := by
    intro D C hC
    obtain ⟨A, -, rfl⟩ := hC
    exact Subscheme.ofClosed_isReduced A
  -- the image of `H` is `G`
  have hHimg : t.f.base '' ((Subscheme.strictTransform t P.ℜ.W).pts ∩ t.f.base ⁻¹' G.pts) =
      G.pts := by
    apply Set.Subset.antisymm
    · rintro _ ⟨y, ⟨-, hy⟩, rfl⟩; exact hy
    · intro g hg
      obtain ⟨y, hy, rfl⟩ := hTL2 g (pts_subset_of_isContainedIn hGW hg)
      exact ⟨y, ⟨hy, hg⟩, rfl⟩
  have himg : ∀ C ∈ Q.badComponents,
      (C.pts = (Subscheme.strictTransform t P.ℜ.W).pts ∩ t.f.base ⁻¹' G.pts ∧
        imageOfClosure t.f C = G) ∨
      (∃ C₁ ∈ P.badComponents, C₁ ≠ G ∧ imageOfClosure t.f C = C₁ ∧
        ∃ y₀ ∈ (Subscheme.strictTransform t P.ℜ.W).pts, IsGenericPoint (t.f.base y₀) C₁.pts ∧
          C.pts = closure {y₀}) := by
    intro C hC
    rcases hdich C hC.1 hC.2.1 hC.2.2 with hH | ⟨C₁, hC₁, hne, y₀, hy₀, hgen, hcl⟩
    · refine Or.inl ⟨hH, imageOfClosure_eq_of_closure_eq _ _ hGred ?_⟩
      rw [hH, hHimg]; exact G.support.isClosed.closure_eq
    · refine Or.inr ⟨C₁, hC₁, hne, imageOfClosure_eq_of_closure_eq _ _ (hcomp_red hC₁.1) ?_, y₀,
        hy₀, hgen, hcl⟩
      rw [hcl, closure_image_closure t.f.base.hom.continuous, Set.image_singleton]
      exact hgen.def
  refine ⟨fun C hC => ?_, fun C hC C' hC' hCC' => ?_, fun C hC hCG => ?_⟩
  · rcases himg C hC with ⟨-, h⟩ | ⟨C₁, hC₁, -, h, -⟩
    · rw [h]; exact hG
    · rw [h]; exact hC₁
  · rcases himg C hC with ⟨hH, h⟩ | ⟨C₁, hC₁, hne, h, y₀, hy₀, hgen, hcl⟩ <;>
      rcases himg C' hC' with ⟨hH', h'⟩ | ⟨C₁', hC₁', hne', h', y₀', hy₀', hgen', hcl'⟩
    · exact Subscheme.eq_of_pts_eq_of_mem_irreducibleComponents hC.1 hC'.1 (hH.trans hH'.symm)
    · exact absurd (h.symm.trans (hCC'.trans h')).symm hne'
    · exact absurd (h'.symm.trans (hCC'.symm.trans h)).symm hne
    · have h1 : C₁ = C₁' := h.symm.trans (hCC'.trans h')
      subst h1
      have h2 : t.f.base y₀ = t.f.base y₀' := hgen.eq hgen'
      have h3 : y₀ = y₀' :=
        ((hTL1 y₀ hy₀ y₀' hy₀' (by rw [h2])).antisymm (hTL1 y₀' hy₀' y₀ hy₀ (by rw [h2]))).eq
      subst h3
      exact Subscheme.eq_of_pts_eq_of_mem_irreducibleComponents hC.1 hC'.1 (hcl.trans hcl'.symm)
  · rcases himg C hC with ⟨hH, -⟩ | ⟨C₁, hC₁, hne, h, -⟩
    · exact hH
    · exact absurd (h.symm.trans hCG) hne

/-- One blow-up at a bad component does not increase the number of bad components. -/
theorem ncard_badComponents_transform_le [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} (hX : IsAmbient X N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar)
    {G : Subscheme X} (hG : G ∈ P.badComponents) (t : MonoidalTransformation X G)
    {Q : PrepSetting t.X'} (hY : IsAmbient t.X' N) (hBT : P.BlowupTransform t Q) :
    Q.badComponents.ncard ≤ P.badComponents.ncard := by
  have := hX.1
  obtain ⟨hmaps, hinj, -⟩ := P.imageOfClosure_mapsTo_injOn_badComponents hX hP h₂ h₃ hG t hY hBT
  exact Set.ncard_le_ncard_of_injOn _ hmaps hinj P.badComponents_finite

/-- p. 291, via Lemma 5: if `H = W' ∩ f⁻¹(G) ⊄ E_1'`, one blow-up at the bad component `G`
strictly decreases the number of bad components (the bad components of `Q` are the strict
transforms of the bad components of `P` other than `G`). -/
theorem ncard_badComponents_transform_lt [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} (hX : IsAmbient X N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar)
    {G : Subscheme X} (hG : G ∈ P.badComponents) (t : MonoidalTransformation X G)
    {Q : PrepSetting t.X'} (hY : IsAmbient t.X' N) (hBT : P.BlowupTransform t Q)
    (hH : ¬ (Subscheme.strictTransform t P.ℜ.W).pts ∩ t.f.base ⁻¹' G.pts ⊆ Q.E₁.pts) :
    Q.badComponents.ncard < P.badComponents.ncard := by
  have := hX.1
  obtain ⟨hmaps, hinj, hG'⟩ := P.imageOfClosure_mapsTo_injOn_badComponents hX hP h₂ h₃ hG t hY hBT
  have hmaps' : Set.MapsTo (imageOfClosure t.f) Q.badComponents (P.badComponents \ {G}) := by
    intro C hC
    refine ⟨hmaps hC, fun hCG => hH ?_⟩
    have hCG' := hG' C hC hCG
    rw [← hCG']
    intro y hy
    exact (Subscheme.mem_pts_inter_iff.mp
      (Subscheme.pts_subset_of_mem_irreducibleComponents hC.1 hy)).2
  calc Q.badComponents.ncard ≤ (P.badComponents \ {G}).ncard :=
        Set.ncard_le_ncard_of_injOn _ hmaps' hinj (P.badComponents_finite.diff)
    _ < P.badComponents.ncard := Set.ncard_diff_singleton_lt_of_mem hG P.badComponents_finite

section PrepPhase21b

open Set Topology

/-- Closed conditions lift through `W' ≅ W`: if `x ∈ closure A` with `A ⊆ W`, and `K ⊆ X'` is closed
and contains every point of `W'` lying over `A`, then it contains the point of `W'` over `x`. -/
theorem _root_.Hironaka.MonoidalTransformation.mem_of_forall_of_mem_closure {X : Scheme.{u}}
    {B : Subscheme X} (t : MonoidalTransformation X B) (W : Subscheme X)
    (e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f) {A : Set X} (hAW : A ⊆ W.pts)
    {x : X} (hx : x ∈ closure A) {K : Set t.X'} (hK : IsClosed K)
    (hA : ∀ z ∈ (Subscheme.strictTransform t W).pts, t.f.base z ∈ A → z ∈ K) {z : t.X'}
    (hz : z ∈ (Subscheme.strictTransform t W).pts) (hzx : t.f.base z = x) : z ∈ K := by
  have hcomm : ∀ u, W.ι.base (e.hom.base u) = t.f.base ((Subscheme.strictTransform t W).ι.base u) :=
    fun u => by
      have := congrArg (fun g => g.base u) he
      simpa using this
  have hz' : z ∈ Set.range (Subscheme.strictTransform t W).ι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hz
  obtain ⟨sz, rfl⟩ := hz'
  set φ := Scheme.homeoOfIso e with hφ
  have hφapp : ∀ u, φ u = e.hom.base u := fun u => rfl
  have hind : IsInducing W.ι.base := W.ι.isClosedEmbedding.isInducing
  -- `e sz` lies in the closure of `ι⁻¹ A`
  have hB : e.hom.base sz ∈ closure (W.ι.base ⁻¹' A) := by
    rw [hind.closure_eq_preimage_closure_image, Set.image_preimage_eq_inter_range]
    show W.ι.base (e.hom.base sz) ∈ closure (A ∩ Set.range W.ι.base)
    rw [hcomm, hzx]
    have : A ∩ Set.range W.ι.base = A := by
      apply Set.inter_eq_left.mpr
      intro a ha
      have : a ∈ Set.range W.ι := by rw [Scheme.IdealSheafData.range_subschemeι]; exact hAW ha
      exact this
    rw [this]; exact hx
  have hKpre : IsClosed ((Subscheme.strictTransform t W).ι.base ⁻¹' K) :=
    hK.preimage (Subscheme.strictTransform t W).ι.base.hom.continuous
  have hsub : φ.symm '' (W.ι.base ⁻¹' A) ⊆ (Subscheme.strictTransform t W).ι.base ⁻¹' K := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' : W.ι.base u ∈ A := hu
    have hφu : φ (φ.symm u) = u := φ.apply_symm_apply u
    have hmem : (Subscheme.strictTransform t W).ι.base (φ.symm u) ∈ (Subscheme.strictTransform t
        W).pts := by
      have : (Subscheme.strictTransform t W).ι.base (φ.symm u) ∈
          Set.range (Subscheme.strictTransform t W).ι := Set.mem_range_self _
      rwa [Scheme.IdealSheafData.range_subschemeι] at this
    apply hA _ hmem
    rw [← hcomm, ← hφapp, hφu]
    exact hu'
  have : φ.symm (e.hom.base sz) ∈ φ.symm '' closure (W.ι.base ⁻¹' A) := ⟨_, hB, rfl⟩
  have h2 : φ.symm '' closure (W.ι.base ⁻¹' A) ⊆ closure (φ.symm '' (W.ι.base ⁻¹' A)) :=
    image_closure_subset_closure_image φ.symm.continuous
  have h3 := h2 this
  have h4 : sz ∈ (Subscheme.strictTransform t W).ι.base ⁻¹' K := by
    have := closure_minimal hsub hKpre h3
    simpa [hφapp] using (show φ.symm (e.hom.base sz) = sz from φ.symm_apply_apply sz) ▸ this
  exact h4

end PrepPhase21b

section PrepPhase21c

open Set Topology TopologicalSpace

/-- An irreducible set not contained in a closed set `E` lies in the closure of its part off `E`. -/
theorem subset_closure_diff_of_isIrreducible {Y : Type*} [TopologicalSpace Y] {S E : Set Y}
    (hS : _root_.IsIrreducible S) (hE : IsClosed E) (hSE : ¬ S ⊆ E) : S ⊆ closure (S \ E) := by
  obtain ⟨z, hzS, hzE⟩ := Set.not_subset.mp hSE
  have : IrreducibleSpace S := Subtype.irreducibleSpace hS
  have hopen : IsOpen ((Subtype.val : S → Y) ⁻¹' Eᶜ) :=
    hE.isOpen_compl.preimage continuous_subtype_val
  have hdense := hopen.dense ⟨⟨z, hzS⟩, hzE⟩
  intro y hy
  have h1 := hdense ⟨y, hy⟩
  have h2 := (Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image
    ((Subtype.val : S → Y) ⁻¹' Eᶜ)) ▸ h1
  have h3 : y ∈ closure (Subtype.val '' ((Subtype.val : S → Y) ⁻¹' Eᶜ)) := h2
  rw [Set.image_preimage_eq_inter_range, Subtype.range_coe] at h3
  simpa [Set.sdiff_eq, Set.inter_comm] using h3

/-- `W_* = closure (W − E)` for closed `W` and `E` in a noetherian space (the union of the
components of
`W` not contained in `E` is the closure of `W − E`). -/
theorem prepWStarT_eq_closure_diff {Y : Type*} [TopologicalSpace Y] [NoetherianSpace Y] {W E : Set
    Y}
    (hW : IsClosed W) (hE : IsClosed E) : prepWStarT W E = closure (W \ E) := by
  apply Set.Subset.antisymm
  · refine closure_minimal ?_ isClosed_closure
    rintro y ⟨_, ⟨Z, ⟨hZ, hZE⟩, rfl⟩, hy⟩
    have hZW : (Z : Set Y) ⊆ W := hZ.1.2
    have := subset_closure_diff_of_isIrreducible hZ.1.1 hE hZE hy
    exact closure_mono (Set.diff_subset_diff_left hZW) this
  · refine closure_mono fun y hy => ?_
    obtain ⟨G, hG, hsub⟩ := exists_prepComps_ge hW (isIrreducible_singleton (x := y)).closure
      (closure_minimal (Set.singleton_subset_iff.mpr hy.1) hW)
    refine ⟨G, ⟨G, ⟨hG, fun hGE => hy.2 (hGE (hsub (subset_closure rfl)))⟩, rfl⟩, hsub
        (subset_closure rfl)⟩

end PrepPhase21c

/-- `F ⊆ closure (F − G)` for a bad component `G`: every component `F_i` of `F` is a component of
`W_* ∩ E_1` different from `G`, hence not contained in `G`. -/
theorem pts_prepF_subset_closure_diff_of_mem_badComponents [IsAlgebraicScheme X] {G : Subscheme X}
    (hG : G ∈ P.badComponents) :
    (P.ℜ.prepF P.E₁ P.U).pts ⊆ closure ((P.ℜ.prepF P.E₁ P.U).pts \ G.pts) := by
  classical
  rw [DatumI.Raw.pts_prepF]
  refine closure_minimal ?_ isClosed_closure
  rintro y ⟨_, ⟨Z, ⟨Fi, hFi, hFU, hZ⟩, rfl⟩, hy⟩
  subst hZ
  have hy' : y ∈ Fi.pts := hy
  have hFiF : Fi.pts ⊆ (P.ℜ.prepF P.E₁ P.U).pts := P.ℜ.pts_subset_pts_prepF P.E₁ P.U hFi hFU
  have hFiG : ¬ Fi.pts ⊆ G.pts := fun hsub => by
    have := Subscheme.pts_eq_of_mem_irreducibleComponents_of_subset hG.1 hFi hsub
    exact hG.2.1 (this ▸ hFiF)
  obtain ⟨A, hAmax, hFiA⟩ := id hFi
  have hirr : _root_.IsIrreducible Fi.pts := by
    have : Fi.pts = A := by
      rw [hFiA]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal A
    rw [this]; exact hAmax.1.1
  have := subset_closure_diff_of_isIrreducible hirr G.support.isClosed hFiG hy'
  exact closure_mono (Set.diff_subset_diff_left hFiF) this

/-- p. 288 and p. 291 (case `H ⊆ E_1'`): if `H = W' ∩ f⁻¹(G)` is contained in `E_1'`, then `H` is a
bad
component of the transformed setting `Q`: it is an irreducible component of `W_*' ∩ E_1'` (a larger
irreducible subset would have a generic point over `G`, which is that of `H`), it is not contained
in
`F'` (the points of `H` over `G − F`) and it meets `F'` (the point of `W'` over a point of `G ∩ F`
lies in `F'` since `F` is the closure of `F − G`).

Deviation from the paper (gap filled): p. 288 continues the process of Lemma 5 with center
`f̃⁻¹(F)` "if `F' ⊂ W' ∩ E'`" without checking that the center is again a component to which the
hypotheses of p. 291 apply; this is proved here. -/
theorem exists_mem_badComponents_pts_eq_of_subset [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {N n : ℕ} (hX : IsAmbient X N)
    (_hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar)
    {G : Subscheme X} (hG : G ∈ P.badComponents) (t : MonoidalTransformation X G)
    {Q : PrepSetting t.X'} (hY : IsAmbient t.X' N) (hBT : P.BlowupTransform t Q)
    (hH : (Subscheme.strictTransform t P.ℜ.W).pts ∩ t.f.base ⁻¹' G.pts ⊆ Q.E₁.pts) :
    ∃ C ∈ Q.badComponents,
      C.pts = (Subscheme.strictTransform t P.ℜ.W).pts ∩ t.f.base ⁻¹' G.pts := by
  classical
  have := hX.1
  have := hY.1
  have hXns := hX.2.1
  obtain ⟨hs, hQ, -⟩ := hBT
  obtain ⟨hGns, hGirr, hGU, hGW⟩ := P.isNonsingular_and_isIrreducible_of_mem_badComponents h₃ hG
  obtain ⟨e, he⟩ := P.exists_iso_strictTransform_of_mem_badComponents hXns h₂ h₃ hG t
  obtain ⟨hTL1, hTL2⟩ :=
      _root_.Hironaka.MonoidalTransformation.specializes_and_surjective_of_iso_strictTransform
    t P.ℜ.W e he
  have hFpts := P.prepF_transform_pts_eq hXns hs hQ
  have hW'pts : Q.ℜ.W.pts = (Subscheme.strictTransform t P.ℜ.W).pts := by
    rw [hQ.1]; rfl
  have hE'pts : Q.E₁.pts = (Subscheme.strictTransform t P.E₁).pts := by rw [hQ.2.2]; rfl
  have hNX : NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  have hNY : NoetherianSpace t.X' := IsAlgebraicScheme.noetherianSpace t.X'
  have hf_sub : ∀ V : Subscheme X, ∀ y ∈ (Subscheme.strictTransform t V).pts, t.f.base y ∈ V.pts :=
    fun V y hy => _root_.Hironaka.MonoidalTransformation.pts_strictTransform_subset t V hy
  set Hs : Set t.X' := (Subscheme.strictTransform t P.ℜ.W).pts ∩ t.f.base ⁻¹' G.pts with hHs
  obtain ⟨γ, hγ⟩ := QuasiSober.sober (Subscheme.isIrreducible_pts G hGirr) G.support.isClosed
  obtain ⟨y₀, hy₀, hfy₀, hcl⟩ :=
      _root_.Hironaka.MonoidalTransformation.exists_eq_closure_pts_inter_preimage
    t P.ℜ.W hTL1 hTL2 (S := G.pts) G.support.isClosed (pts_subset_of_isContainedIn hGW) hγ
  have hHcl : Hs = closure {y₀} := hcl
  have hy₀H : y₀ ∈ Hs := hHcl ▸ subset_closure rfl
  have hHclosed : IsClosed Hs := by rw [hHcl]; exact isClosed_closure
  have hHirr : _root_.IsIrreducible Hs := by rw [hHcl]; exact isIrreducible_singleton.closure
  have hWc : IsClosed P.ℜ.W.pts := P.ℜ.W.support.isClosed
  have hE1c : IsClosed P.E₁.pts := P.E₁.support.isClosed
  have hW'c : IsClosed (Subscheme.strictTransform t P.ℜ.W).pts :=
    (Subscheme.strictTransform t P.ℜ.W).support.isClosed
  have hE'c : IsClosed (Subscheme.strictTransform t P.E₁).pts :=
    (Subscheme.strictTransform t P.E₁).support.isClosed
  -- `D'` as a set
  have hD'pts : ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts =
      closure ((Subscheme.strictTransform t P.ℜ.W).pts \ (Subscheme.strictTransform t P.E₁).pts) ∩
        (Subscheme.strictTransform t P.E₁).pts := by
    ext y
    rw [Subscheme.mem_pts_inter_iff, DatumI.Raw.pts_prepWStar_eq, hW'pts, hE'pts,
      prepWStarT_eq_closure_diff hW'c hE'c]
    exact Iff.rfl
  have hDpts : ((P.ℜ.prepWStar P.E₁).inter P.E₁).pts = closure (P.ℜ.W.pts \ P.E₁.pts) ∩ P.E₁.pts
      := by
    ext y
    rw [Subscheme.mem_pts_inter_iff, DatumI.Raw.pts_prepWStar_eq,
      prepWStarT_eq_closure_diff hWc hE1c]
    exact Iff.rfl
  have hγD : γ ∈ closure (P.ℜ.W.pts \ P.E₁.pts) := by
    have : γ ∈ ((P.ℜ.prepWStar P.E₁).inter P.E₁).pts :=
      Subscheme.pts_subset_of_mem_irreducibleComponents hG.1 hγ.mem
    rw [hDpts] at this; exact this.1
  -- points of `W'` off `E_1'` lie over `W − E_1`; conversely
  have hW'E : ∀ z ∈ (Subscheme.strictTransform t P.ℜ.W).pts,
      z ∉ (Subscheme.strictTransform t P.E₁).pts → t.f.base z ∈ P.ℜ.W.pts \ P.E₁.pts := by
    intro z hz hzE
    refine ⟨hf_sub _ z hz, fun hfz => hzE ?_⟩
    by_cases hzexc : z ∈ t.exceptional.pts
    · rw [MonoidalTransformation.pts_exceptional] at hzexc
      exact hE'pts ▸ hH ⟨hz, hzexc⟩
    · exact (MonoidalTransformation.mem_pts_strictTransform_iff_of_notMem t _ hzexc).mpr hfz
  -- (1) `y₀ ∈ D'`
  have hy₀D : y₀ ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts := by
    rw [hD'pts]
    refine ⟨?_, hE'pts ▸ hH hy₀H⟩
    refine _root_.Hironaka.MonoidalTransformation.mem_of_forall_of_mem_closure t P.ℜ.W e he
      (A := P.ℜ.W.pts \ P.E₁.pts) Set.diff_subset (hfy₀ ▸ hγD) isClosed_closure ?_ hy₀ hfy₀
    intro z hz hfz
    exact subset_closure ⟨hz, fun hzE => hfz.2 (hf_sub _ z hzE)⟩
  have hHD : Hs ⊆ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts := by
    rw [hHcl]
    exact closure_minimal (Set.singleton_subset_iff.mpr hy₀D)
      ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).support.isClosed
  -- (2) `H` is an irreducible component of `D'`
  have hmax : Maximal (fun Z : TopologicalSpace.Closeds t.X' =>
      _root_.IsIrreducible (Z : Set t.X') ∧ (Z : Set t.X') ⊆ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts)
      ⟨Hs, hHclosed⟩ := by
    refine ⟨⟨hHirr, hHD⟩, fun Z' hZ' hle => ?_⟩
    obtain ⟨c, hc⟩ := QuasiSober.sober hZ'.1 Z'.isClosed
    have hy₀Z' : y₀ ∈ (Z' : Set t.X') := hle hy₀H
    have hcy₀ : c ⤳ y₀ := hc.specializes hy₀Z'
    have hcD : c ∈ ((Q.ℜ.prepWStar Q.E₁).inter Q.E₁).pts := hZ'.2 hc.mem
    have hcD' := hcD
    rw [hD'pts] at hcD'
    have hcW' : c ∈ (Subscheme.strictTransform t P.ℜ.W).pts :=
      (Subscheme.mem_pts_inter_iff.mp hcD).1 |> fun h => hW'pts ▸ Q.ℜ.pts_prepWStar_subset Q.E₁ h
    have hfc_cl : t.f.base c ∈ closure (P.ℜ.W.pts \ P.E₁.pts) := by
      have h1 : t.f.base '' ((Subscheme.strictTransform t P.ℜ.W).pts \
          (Subscheme.strictTransform t P.E₁).pts) ⊆ P.ℜ.W.pts \ P.E₁.pts := by
        rintro _ ⟨z, ⟨hz, hzE⟩, rfl⟩; exact hW'E z hz hzE
      exact closure_mono h1 (image_closure_subset_closure_image t.f.base.hom.continuous
        ⟨c, hcD'.1, rfl⟩)
    have hfcD : t.f.base c ∈ ((P.ℜ.prepWStar P.E₁).inter P.E₁).pts := by
      rw [hDpts]; exact ⟨hfc_cl, hf_sub _ c hcD'.2⟩
    have hfcγ : t.f.base c ⤳ γ := hfy₀ ▸ hcy₀.map t.f.base.hom.continuous
    obtain ⟨ZG, hZGmax, hGeq⟩ := id hG.1
    have hGpts : G.pts = (ZG : Set X) := by
      rw [hGeq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal ZG
    have hcl_fc : closure {t.f.base c} ⊆ G.pts := by
      have hirrc : _root_.IsIrreducible (closure {t.f.base c}) := isIrreducible_singleton.closure
      have hsubD : closure {t.f.base c} ⊆ ((P.ℜ.prepWStar P.E₁).inter P.E₁).pts :=
        closure_minimal (Set.singleton_subset_iff.mpr hfcD)
          ((P.ℜ.prepWStar P.E₁).inter P.E₁).support.isClosed
      have hle : ZG ≤ (⟨closure {t.f.base c}, isClosed_closure⟩ : TopologicalSpace.Closeds X) := by
        show (ZG : Set X) ⊆ closure {t.f.base c}
        rw [← hGpts, ← hγ.def]
        exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hfcγ))
          isClosed_closure
      have := hZGmax.2 (y := ⟨closure {t.f.base c}, isClosed_closure⟩) ⟨hirrc, hsubD⟩ hle
      rw [hGpts]; exact this
    have hfcG : t.f.base c ∈ G.pts := hcl_fc (subset_closure rfl)
    have hfcγ' : t.f.base c = γ := by
      have h1 : γ ⤳ t.f.base c := by
        rw [specializes_iff_mem_closure, hγ.def]; exact hfcG
      exact (hfcγ.antisymm h1).eq
    have hcy : c = y₀ :=
      (hcy₀.antisymm (hTL1 y₀ hy₀ c hcW' (by rw [hfy₀, hfcγ']))).eq
    show (Z' : Set t.X') ⊆ Hs
    rw [← hc.def, hcy, ← hHcl]
  -- (3) the component `C = H` and its position with respect to `F'`
  have hCpts : (Subscheme.ofClosed (⟨Hs, hHclosed⟩ :
      TopologicalSpace.Closeds t.X')).pts = Hs := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  refine ⟨Subscheme.ofClosed ⟨Hs, hHclosed⟩, ⟨?_, ?_, ?_⟩, hCpts⟩
  · exact ⟨_, hmax, rfl⟩
  · rw [hCpts, hFpts]
    obtain ⟨u, huG, huF⟩ := Set.not_subset.mp hG.2.1
    obtain ⟨u', hu'W, hfu'⟩ := hTL2 u (pts_subset_of_isContainedIn hGW huG)
    intro hsub
    have hu'H : u' ∈ Hs := ⟨hu'W, by rw [Set.mem_preimage, hfu']; exact huG⟩
    have := hf_sub _ u' (hsub hu'H)
    rw [hfu'] at this
    exact huF this
  · rw [hCpts, hFpts]
    obtain ⟨x, hxG, hxF⟩ := hG.2.2
    have hFW : (P.ℜ.prepF P.E₁ P.U).pts ⊆ P.ℜ.W.pts := fun y hy =>
      P.ℜ.pts_prepWStar_subset P.E₁ (Subscheme.mem_pts_inter_iff.mp
        (P.ℜ.pts_prepF_subset P.E₁ P.U hy)).1
    obtain ⟨x', hx'W, hfx'⟩ := hTL2 x (pts_subset_of_isContainedIn hGW hxG)
    refine ⟨x', ⟨hx'W, by rw [Set.mem_preimage, hfx']; exact hxG⟩, ?_⟩
    refine _root_.Hironaka.MonoidalTransformation.mem_of_forall_of_mem_closure t P.ℜ.W e he
      (A := (P.ℜ.prepF P.E₁ P.U).pts \ G.pts) (fun y hy => hFW hy.1)
      (P.pts_prepF_subset_closure_diff_of_mem_badComponents hG hxF)
      (Subscheme.strictTransform t (P.ℜ.prepF P.E₁ P.U)).support.isClosed ?_ hx'W hfx'
    intro z hz hfz
    have hzexc : z ∉ t.exceptional.pts := by
      rw [MonoidalTransformation.pts_exceptional]; exact hfz.2
    exact (MonoidalTransformation.mem_pts_strictTransform_iff_of_notMem t _ hzexc).mpr hfz.1

section PrepPhase21d

open IsLocalRing Classical

/-- `μ(W, E, G) = m`: the order of `E|_W` at the point of `W` over the generic point of `G` is `m`.
-/
def OrderIsAlong {Y : Scheme.{u}} (W E G : Subscheme Y) (m : ℕ) : Prop :=
  ∃ w : W.toScheme, IsGenericPoint (W.ι w) G.pts ∧ Subscheme.orderAt W E w = m

theorem OrderIsAlong.congr {Y : Scheme.{u}} {W W₂ E E₂ G : Subscheme Y} (hW : W = W₂)
    (hE : E = E₂) {m : ℕ} : OrderIsAlong W E G m ↔ OrderIsAlong W₂ E₂ G m := by
  subst hW hE; rfl

/-- `μ(P, G) = m` for the principal subscheme `W` and `E_1` of `P`. -/
def OrderIs (P : PrepSetting X) (G : Subscheme X) (m : ℕ) : Prop :=
  OrderIsAlong P.ℜ.W P.E₁ G m

/-- The hypotheses of the order-drop theorem
(`MonoidalTransformation.exists_orderAt_strictTransform_add_one`)
for a bad component `G` of `W_* ∩ E_1`, `W` and `E_1` of `P`, at the point `w` of `W` over the
generic point
of `G`. -/
theorem exists_orderAt_data_of_mem_badComponents [IsAlgebraicScheme X] (hXns : X.IsNonsingular)
    {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar) {G : Subscheme X}
    (hG : G ∈ P.badComponents) :
    ∃ w : P.ℜ.W.toScheme, IsGenericPoint (P.ℜ.W.ι w) G.pts ∧
      (Subscheme.totalTransform P.ℜ.W.ι G).IsInvertibleIdeal ∧
      G.stalkIdeal (P.ℜ.W.ι w) = maximalIdeal (X.presheaf.stalk (P.ℜ.W.ι w)) ∧
      (∃ e, P.E₁.stalkIdeal (P.ℜ.W.ι w) = Ideal.span {e}) ∧
      IsRegularLocalRing (X.presheaf.stalk (P.ℜ.W.ι w) ⧸ P.E₁.stalkIdeal (P.ℜ.W.ι w)) ∧
      P.ℜ.W.ι w ∈ P.E₁.pts ∧ (Subscheme.totalTransform P.ℜ.W.ι P.E₁).stalkIdeal w ≠ ⊥ := by
  classical
  have := isAlgebraicScheme_toScheme P.ℜ.W
  obtain ⟨hGns, hGirr, hGU, hGW⟩ := P.isNonsingular_and_isIrreducible_of_mem_badComponents h₃ hG
  have hGred : G.IsReduced := Subscheme.isReduced_of_isNonsingular hGns
  -- the generic point of `G`
  have : IrreducibleSpace G.toScheme := hGirr
  set ξ : G.toScheme := genericPoint G.toScheme with hξ
  have hξgen : IsGenericPoint ξ (Set.univ : Set G.toScheme) := genericPoint_spec G.toScheme
  have hγgen : IsGenericPoint (G.ι ξ) G.pts := by
    show closure {G.ι ξ} = G.pts
    have h1 := G.ι.isClosedEmbedding.closure_image_eq ({ξ} : Set G.toScheme)
    rw [Set.image_singleton] at h1
    rw [h1, hξgen.def, Set.image_univ, Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hγG : G.ι ξ ∈ G.pts := hγgen.mem
  have hγW : G.ι ξ ∈ P.ℜ.W.pts := pts_subset_of_isContainedIn hGW hγG
  obtain ⟨w, hw⟩ : ∃ w : P.ℜ.W.toScheme, P.ℜ.W.ι w = G.ι ξ := by
    have : G.ι ξ ∈ Set.range P.ℜ.W.ι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hγW
    exact this
  have hγD : G.ι ξ ∈ ((P.ℜ.prepWStar P.E₁).inter P.E₁).pts :=
    Subscheme.pts_subset_of_mem_irreducibleComponents hG.1 hγG
  have hγE : G.ι ξ ∈ P.E₁.pts := (Subscheme.mem_pts_inter_iff.mp hγD).2
  have hE1ns : P.E₁.IsNonsingular := by
    have hne : P.E₁ ≠ Subscheme.empty := fun h => by
      rw [h, DatumTransform.pts_empty] at hγE; exact hγE
    exact ((P.hE ⟨0, P.hα⟩).resolve_left hne).1
  refine ⟨w, hw ▸ hγgen, P.isInvertibleIdeal_totalTransform_of_mem_badComponents hXns h₂ h₃ hG, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [hw]
    refine stalkIdeal_eq_maximalIdeal_of_isReduced G hGred ξ ?_
    rw [hξgen.def]
    exact ⟨IrreducibleSpace.isIrreducible_univ _, fun s _ _ => Set.subset_univ s⟩
  · rw [hw]
    exact Subscheme.exists_stalkIdeal_eq_span_of_isNonsingularIrreducibleCodimOne hXns
      (P.hE ⟨0, P.hα⟩) hγE
  · rw [hw]; exact Subscheme.isRegular_stalk_quot P.E₁ hE1ns hγE
  · rw [hw]; exact hγE
  · intro hbot
    rw [stalkIdeal_totalTransform] at hbot
    -- `E_1` does not contain the branch of `W` through `G`
    obtain ⟨W₁, hW₁, hW₁E, hGW₁⟩ := P.exists_comp_of_mem_badComponents hG
    obtain ⟨Zw, hZw, rfl⟩ := id hW₁
    obtain ⟨ω, hω⟩ : ∃ ω, IsGenericPoint ω (Zw : Set X) := QuasiSober.sober hZw.1.1 Zw.isClosed
    have hZwpts : (Subscheme.ofClosed Zw).pts = Zw
        := Scheme.IdealSheafData.coe_support_vanishingIdeal Zw
    have hωx : ω ⤳ P.ℜ.W.ι w := by
      rw [specializes_iff_mem_closure, hω.def, hw]
      exact hZwpts ▸ hGW₁ hγG
    have hωW : ω ∈ P.ℜ.W.pts := hZw.1.2 hω.mem
    have hωE : ω ∉ P.E₁.pts := fun hωE => hW₁E (by
      refine Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced Zw) ?_
      rw [hZwpts, ← hω.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hωE) P.E₁.support.isClosed)
    -- `E_{1,x} ≤ W_x`
    have hle : P.E₁.stalkIdeal (P.ℜ.W.ι w) ≤ P.ℜ.W.stalkIdeal (P.ℜ.W.ι w) := by
      have hker : RingHom.ker (P.ℜ.W.ι.stalkMap w).hom = P.ℜ.W.stalkIdeal (P.ℜ.W.ι w) :=
        (stalkIdeal_eq_ker_stalkMap P.ℜ.W w).symm
      rw [← hker]
      exact (Ideal.map_eq_bot_iff_le_ker _).mp hbot
    have hWp : (P.ℜ.W.stalkIdeal (P.ℜ.W.ι w)).IsPrime := by
      obtain ⟨hWs, -, -⟩ := h₂.2.2.2 _ (hGU (hw ▸ hγG))
      exact Subscheme.isPrime_stalkIdeal_of_isSimpleAt hWs
    exact hωE (mem_pts_of_stalkIdeal_le_of_specializes hωx hωW hle)

end PrepPhase21d

section PrepPhase21e

open IsLocalRing Classical

/-- Every bad component has a finite order `μ(P, G)`. -/
theorem exists_orderIs_of_mem_badComponents [IsAlgebraicScheme X] (hXns : X.IsNonsingular)
    {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar) {G : Subscheme X}
    (hG : G ∈ P.badComponents) : ∃ m : ℕ, P.OrderIs G m := by
  classical
  obtain ⟨w, hwgen, -, -, -, -, -, hWE⟩ := P.exists_orderAt_data_of_mem_badComponents hXns h₂ h₃ hG
  have := isAlgebraicScheme_toScheme P.ℜ.W
  have := IsAlgebraicScheme.isNoetherian P.ℜ.W.toScheme
  have hfin : Subscheme.orderAt P.ℜ.W P.E₁ w ≠ ⊤ := (Subscheme.orderAt_ne_top_iff _ _ _).mpr hWE
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  exact ⟨m, w, hwgen, hm.symm⟩

/-- The drop of the order under one blow-up at a bad component `G` (p. 287, Lemma 5; p. 291): with
`μ = μ(P, G)`, `μ ≥ 1`; `H = W' ∩ f⁻¹(G)` lies in `E_1'` iff `μ ≥ 2`; and then `H` is a bad
component of
`Q` of order `μ - 1`. -/
theorem orderIs_drop_of_blowupTransform [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {N n : ℕ} (hX : IsAmbient X N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃ Ubar)
    {G : Subscheme X} (hG : G ∈ P.badComponents) (t : MonoidalTransformation X G)
    {Q : PrepSetting t.X'} (hY : IsAmbient t.X' N) (hBT : P.BlowupTransform t Q) {m : ℕ}
    (hm : P.OrderIs G m) :
    1 ≤ m ∧
      ((Subscheme.strictTransform t P.ℜ.W).pts ∩ t.f.base ⁻¹' G.pts ⊆ Q.E₁.pts ↔ 2 ≤ m) ∧
      (2 ≤ m → ∃ C ∈ Q.badComponents, Q.OrderIs C (m - 1)) := by
  classical
  have := hX.1
  have hXns := hX.2.1
  obtain ⟨w₀, hw₀gen, hinv, hGw, hEprin, hEreg, hEmem, hWE⟩ :=
    P.exists_orderAt_data_of_mem_badComponents hXns h₂ h₃ hG
  obtain ⟨w, hwgen, hwm⟩ := hm
  have hww : w = w₀ := by
    have : P.ℜ.W.ι w = P.ℜ.W.ι w₀ := hwgen.eq hw₀gen
    exact P.ℜ.W.ι.isClosedEmbedding.injective this
  subst hww
  obtain ⟨hs, hQ, -⟩ := id hBT
  obtain ⟨w', hw', huniq, hμ⟩ := MonoidalTransformation.exists_orderAt_strictTransform_add_one
    hXns t P.ℜ.W P.E₁ hinv w hGw hEprin hEreg hEmem hWE
  have hiff := MonoidalTransformation.mem_pts_strictTransform_iff_two_le_orderAt hXns t P.ℜ.W P.E₁
      hinv
    w hGw hEprin hEreg hEmem hWE w' hw'
  have h1m : 1 ≤ m := by
    have := (Subscheme.one_le_orderAt_iff P.ℜ.W P.E₁ w).mpr hEmem
    rw [hwm] at this
    exact_mod_cast this
  -- `H` is the closure of `ι' w'`
  obtain ⟨e, he⟩ := P.exists_iso_strictTransform_of_mem_badComponents hXns h₂ h₃ hG t
  obtain ⟨hTL1, hTL2⟩ :=
      _root_.Hironaka.MonoidalTransformation.specializes_and_surjective_of_iso_strictTransform
    t P.ℜ.W e he
  obtain ⟨y₀, hy₀, hfy₀, hcl⟩ :=
      _root_.Hironaka.MonoidalTransformation.exists_eq_closure_pts_inter_preimage
    t P.ℜ.W hTL1 hTL2 (S := G.pts) G.support.isClosed
    (pts_subset_of_isContainedIn (P.isNonsingular_and_isIrreducible_of_mem_badComponents h₃
        hG).2.2.2)
    hw₀gen
  have hy₀eq : y₀ = (Subscheme.strictTransform t P.ℜ.W).ι w' := by
    have : y₀ ∈ Set.range (Subscheme.strictTransform t P.ℜ.W).ι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hy₀
    obtain ⟨u, hu⟩ := this
    have := huniq u (by rw [hu, hfy₀])
    rw [← hu, this]
  have hE'pts : Q.E₁.pts = (Subscheme.strictTransform t P.E₁).pts := by rw [hQ.2.2]; rfl
  have hHcl : (Subscheme.strictTransform t P.ℜ.W).pts ∩ t.f.base ⁻¹' G.pts =
      closure {(Subscheme.strictTransform t P.ℜ.W).ι w'} := by rw [← hy₀eq]; exact hcl
  have hH_iff : (Subscheme.strictTransform t P.ℜ.W).pts ∩ t.f.base ⁻¹' G.pts ⊆ Q.E₁.pts ↔
      (Subscheme.strictTransform t P.ℜ.W).ι w' ∈ (Subscheme.strictTransform t P.E₁).pts := by
    constructor
    · intro h
      rw [← hE'pts]
      exact h (hHcl ▸ subset_closure rfl)
    · intro h
      rw [hHcl, hE'pts]
      exact closure_minimal (Set.singleton_subset_iff.mpr h)
        (Subscheme.strictTransform t P.E₁).support.isClosed
  have hiff' : (Subscheme.strictTransform t P.ℜ.W).ι w' ∈ (Subscheme.strictTransform t P.E₁).pts ↔
      2 ≤ m := by
    rw [hiff, hwm]; exact_mod_cast Iff.rfl
  refine ⟨h1m, hH_iff.trans hiff', fun h2 => ?_⟩
  have hH := hH_iff.mpr (hiff'.mpr h2)
  obtain ⟨C, hC, hCpts⟩ := P.exists_mem_badComponents_pts_eq_of_subset hX hP h₂ h₃ hG t hY
    hBT hH
  refine ⟨C, hC, ?_⟩
  have hWeq : Q.ℜ.W = Subscheme.strictTransform t P.ℜ.W := by rw [hQ.1]; rfl
  have hEeq : Q.E₁ = Subscheme.strictTransform t P.E₁ := hQ.2.2
  show OrderIsAlong Q.ℜ.W Q.E₁ C (m - 1)
  rw [OrderIsAlong.congr hWeq hEeq]
  refine ⟨w', ?_, ?_⟩
  · show closure {(Subscheme.strictTransform t P.ℜ.W).ι w'} = C.pts
    rw [hCpts, hHcl]
  · have hx : Subscheme.orderAt (Subscheme.strictTransform t P.ℜ.W) (Subscheme.strictTransform t
      P.E₁)
        w' + 1 = (m : ℕ∞) := hμ.trans hwm
    generalize Subscheme.orderAt (Subscheme.strictTransform t P.ℜ.W)
      (Subscheme.strictTransform t P.E₁) w' = x at hx ⊢
    induction x using ENat.recTopCoe with
    | top => simp at hx
    | coe k =>
      have : k + 1 = m := by exact_mod_cast hx
      subst this
      simp

end PrepPhase21e

section PrepPhase21f

/-- The transform `Q` of `P` under one blow-up at a bad component satisfies (1), (2), (3):
`Q.Stage₃` (p. 291: "the conditions (1), (2) and (3) remain to be satisfied if we replace `(ℜ, U)`
by `f*(ℜ, U)`"). -/
theorem stage₃_of_blowupTransform [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} (hX : IsAmbient X N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) (hS : P.Stage₃) {G : Subscheme X}
    (hG : G ∈ P.badComponents) (t : MonoidalTransformation X G)
    {Q : PrepSetting t.X'} (hY : IsAmbient t.X' N) (hBT : P.BlowupTransform t Q) :
    Q.Stage₃ := by
  obtain ⟨hC1, Ubar, h₂, h₃⟩ := hS
  obtain ⟨hs, hQ, J', hJ3, hJ', hG1, hexc, hα, hcs⟩ := id hBT
  refine ⟨P.cond₁_transform_of_mem_badComponents hX hC1 h₂ h₃ hG t hY hs hQ, _,
    P.cond₂_transform_of_tail hX hP hY hs hQ h₂ J' hJ3 hJ',
    P.cond₃_transform_of_mem_badComponents hX hP h₂ h₃ hG t hY hs hQ J' hJ3 hJ' hG1 hexc hα hcs⟩

/-- Monotonicity of `StepTo` in the target stage. -/
theorem StepTo.mono {N n : ℕ} {Stage₁ Stage₂ : ∀ Y : Scheme.{u}, PrepSetting Y → Prop}
    (h : P.StepTo N n Stage₁) (hmono : ∀ Y Q, Stage₁ Y Q → Stage₂ Y Q) : P.StepTo N n Stage₂ := by
  obtain ⟨Y, s, Q, hs, hT, hY, hn, hSt⟩ := h
  exact ⟨Y, s, Q, hs, hT, hY, hn, hmono Y Q hSt⟩

end PrepPhase21f

/-- The heart of step (3)* (p. 291, via Lemma 5): if there is a bad component `G` of `W_* ∩ E_1`
(not contained in `F`, meeting `F`), a permissible succession (the monoidal transformation with
center `G`, followed by the iteration of Lemma 5) leads to a transform again satisfying (1), (2),
(3), with strictly fewer bad components.

Status: proved, modulo the cited leaves only.  The iteration of Lemma 5 is realized as a
strong induction on the order `μ(P, G)` of `E_1|_W` along `G` (`OrderIs`; the drop
`MonoidalTransformation.exists_orderAt_strictTransform_add_one` of `Compat/BlowupOrderDrop.lean`):
each step is the blow-up at a bad component (`Cond₁`:
`cond₁_transform_of_mem_badComponents`; `Cond₂`:
`cond₂_transform_of_tail`; `Cond₃`: `cond₃_transform_of_mem_badComponents`; together
`stage₃_of_blowupTransform`).  By `orderIs_drop_of_blowupTransform`, `H = W' ∩ f⁻¹(G)` lies in
`E_1'`
iff `μ ≥ 2`, and then it is a bad component of `Q` of order `μ - 1`
(`exists_mem_badComponents_pts_eq_of_subset`).  The number of bad components never increases
(`ncard_badComponents_transform_le`, an injection `C ↦ closure f(C)` of the bad components of `Q`
into those of `P`) and decreases strictly at the last step, where `H ⊄ E_1'`
(`ncard_badComponents_transform_lt`).

Deviation from the paper (incomplete citation: Lemma 5's hypotheses fail globally; the paper's
measure is used): the termination measure is the paper's own `ν` from the proof of Lemma 5 (p. 288:
`P_0 + (y^ν)R_0` contains `w` but `P_0 + (y^{ν+1})R_0` does not), i.e. `orderAt`, which drops by one
at each step, so the iteration ends after `ν` steps.  What differs is that Lean iterates the blow-up
globally on `X`, instead of applying Lemma 5 on a non-singular irreducible open, because `W` need not
be irreducible or non-singular.  That the conditions (1)-(3) and the description of the components
are preserved at each step, and that the number of bad components drops, is tacit on p. 291.

Older notes.  Items 1 and 2: the permissibility of the
center `G` of a bad component: `isPermissible_of_mem_badComponents` (for `ℜ`),
`isPermissible_tail_of_mem_badComponents` (for the tail `(⋃_{i≥2} E_i; V; W)`) and
`isPermissibleOpen_of_mem_badComponents` (for `(ℜ, U)`).  Localization and extension:
`exists_localization_of_mem_badComponents` and `exists_localized_iteration_of_mem_badComponents`
(not
needed by the global induction). -/
theorem exists_stepTo_lt_badComponents [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} (hX : IsAmbient X N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) (h : P.Stage₃) (hbad : P.badComponents ≠ ∅) :
    P.StepTo N n (fun _ Q => Q.Stage₃ ∧ Q.badComponents.ncard < P.badComponents.ncard) := by
  classical
  -- strong induction on the order `μ(R, G)` of `E_1|_W` along the bad component `G`
  have key : ∀ m : ℕ, ∀ (Y : Scheme.{u}) (R : PrepSetting Y), IsAmbient Y N →
      R.ℜ.n ≤ (n : WithBot ℕ∞) → R.Stage₃ → ∀ G ∈ R.badComponents, R.OrderIs G m →
      R.StepTo N n (fun _ Q => Q.Stage₃ ∧ Q.badComponents.ncard < R.badComponents.ncard) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro Y R hY hR hS G hG hm
      have : IsAlgebraicScheme Y := hY.1
      obtain ⟨t, -⟩ := MonoidalTransformation.exists_isProper Y G
      obtain ⟨hC1, Ubar, h₂, h₃⟩ := id hS
      obtain ⟨Q, hBT, hQY, hQn⟩ := R.exists_blowupTransform_of_mem_badComponents hY hR h₂ h₃ hG t
      have hQS := R.stage₃_of_blowupTransform hY hR hS hG t hQY hBT
      obtain ⟨h1m, hiff, hnext⟩ := R.orderIs_drop_of_blowupTransform hY hR h₂ h₃ hG t hQY hBT hm
      have hle := R.ncard_badComponents_transform_le hY hR h₂ h₃ hG t hQY hBT
      obtain ⟨hs, hQ, -⟩ := id hBT
      by_cases h2 : 2 ≤ m
      · -- `H = W' ∩ f⁻¹(G) ⊆ E_1'` is a bad component of `Q` of order `m - 1`: blow it up next
        obtain ⟨C, hC, hCm⟩ := hnext h2
        refine StepTo.trans (Stage₁ := fun _ Q' => Q'.Stage₃ ∧
            Q'.badComponents.ncard ≤ R.badComponents.ncard ∧
            ∃ C ∈ Q'.badComponents, Q'.OrderIs C (m - 1))
          ⟨t.X', MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X'), Q, hs, hQ, hQY, hQn,
            hQS, hle, C, hC, hCm⟩ ?_
        rintro Y' Q' hY' hn' ⟨hS', hle', C', hC', hC'm⟩
        refine StepTo.mono Q' (ih (m - 1) (by omega) Y' Q' hY' hn' hS' C' hC' hC'm) ?_
        intro _ Q'' h
        exact ⟨h.1, lt_of_lt_of_le h.2 hle'⟩
      · have hH : ¬ (Subscheme.strictTransform t R.ℜ.W).pts ∩ t.f.base ⁻¹' G.pts ⊆ Q.E₁.pts :=
          fun h => h2 (hiff.mp h)
        exact ⟨t.X', MonoidalSuccession.cons G t (MonoidalSuccession.nil t.X'), Q, hs, hQ, hQY,
          hQn, hQS, R.ncard_badComponents_transform_lt hY hR h₂ h₃ hG t hQY hBT hH⟩
  obtain ⟨G, hG⟩ := Set.nonempty_iff_ne_empty.mpr hbad
  have := hX.1
  obtain ⟨hC1, Ubar, h₂, h₃⟩ := id h
  obtain ⟨m, hm⟩ := P.exists_orderIs_of_mem_badComponents hX.2.1 h₂ h₃ hG
  exact key m X P hX hP h G hG hm

/-- Step 4 (pp. 291): Lemma 5.  "If `G` is any reduced irreducible component of `W_* ∩ E_1` as
above, (2) and (3) imply immediately that the monoidal transformation `f : X' → X` with center
`G` is permissible for the resolution datum `(⋃_{i≥2} E_i; V_1, …, V_β; W)`, hence for
`(ℜ, U)`.  Moreover the conditions (1), (2) and (3) remain to be satisfied if we replace
`(ℜ, U)` by `f*(ℜ, U)`, and `Ū` by `f⁻¹(Ū) ∩` (the strict transform of `W`).  Therefore, by
Lemma 5, we may assume that (3)*".

Deviation from the paper (gap filled): that the centers `G` are permissible
and the preservation of (1), (2), (3) are asserted as "immediately"/"remain"; the finiteness of the
number of components and the iteration are tacit (Lemma 5:
`MonoidalTransformation.strictTransform_iso_and_inter_eq_unionFam_inducedPreimage`).

Status.  The induction on the number of bad components is assembled: `badComponents` and
`badComponents_finite`, `StepTo.trans` (composition of reductions), `stepTo_of_badComponents_eq_empty`
(no bad component: the empty succession), and the strong induction below (the one-step reduction
`exists_stepTo_lt_badComponents` is proved).  Proved about the center:
`isNonsingular_and_isIrreducible_of_mem_badComponents` (by (3) a bad `G` is non-singular, irreducible, in
`Ũ` and in `W`).

Gap noted (Lemma 5 is global): Lemma 5 (`strictTransform_iso_and_inter_eq_unionFam_inducedPreimage`) is
stated for a non-singular irreducible algebraic scheme `X`, a non-singular irreducible `W` and a
non-singular irreducible divisor `E` not containing `W`; in the application on p. 291 `W` is neither
irreducible nor non-singular.  The application therefore needs the localization to an open `O ⊇ G`
(where `W ∩ O` is the non-singular irreducible component through `G`) and the extension of the resulting
succession to `X` (`Hironaka/Compat/ExtendSuccession.lean`, as for step (5)); this is tacit in the paper.

Plan for `exists_stepTo_lt_badComponents` (it uses Condition (3) in the form of `cond₃_transform`).  (a) Induction on the
number `c(P)` of components `G` of `W_* ∩ E_1` not contained in `F` that meet `F` (finite by
`prepComps_finite`; `c = 0` is `Cond₃Star`).  (b) For such a `G`, `Cond₃` gives `G = W ∩ E_j` with
`j ≥ 2`, `G ⊆ Ũ`, `G` non-singular irreducible; the blow-up `f : X' → X` with center `G` is permissible
for the tail datum `(⋃_{i≥2} E_i; V; W)` (the tail is resolved on `Ũ ⊇ G`, `G = W ∩ E_j` has normal
crossings with `E`, `W` and the `V_k`), hence for `(ℜ, U)` since `G ∩ U = ∅`
(`isPermissibleIOpen_of_isPermissibleIOpen_extendBy`-type lemma for `ℜ`, `ℜ.extendBy G`).  (c) By
Lemma 5 (`strictTransform_iso_and_inter_eq_unionFam_inducedPreimage`) `f̃ : W' → W` is an isomorphism
and `W_*' ∩ E_1'` is the union of the induced preimages of the components, so the number of components
meeting `F'` but not in `F'` drops (those through `G` become components of `F'` or are separated).
(d) Conditions (1), (2) pass to the transform as in `cond₁_transform`, `cond₂_transform_resolvedSet`
with `Ũ' = f⁻¹(Ũ) ∩ W'` (the datum is resolved there by Lemma 4 and Corollary 2 of Theorem 5:
`tail_resolvedAt_transform`), and (3) as in `cond₃_transform`. -/
theorem stepTo_stage₃Star [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} (hX : IsAmbient X N) (hP : P.ℜ.n ≤ (n : WithBot ℕ∞))
    (h : P.Stage₃) : P.StepTo N n (fun _ Q => Q.Stage₃Star) := by
  classical
  have key : ∀ (k : ℕ) {Y : Scheme.{u}} (Q : PrepSetting Y), IsAmbient Y N →
      Q.ℜ.n ≤ (n : WithBot ℕ∞) → Q.Stage₃ → Q.badComponents.ncard = k →
      Q.StepTo N n (fun _ R => R.Stage₃Star) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro Y Q hY hQ hQ3 hk
      by_cases hbad : Q.badComponents = ∅
      · exact stepTo_of_badComponents_eq_empty Q hY hQ hQ3 hbad
      · refine (Q.exists_stepTo_lt_badComponents hY hQ hQ3 hbad).trans
          fun Z R hZ hR ⟨hR3, hlt⟩ => ih _ (hk ▸ hlt) R hZ hR hR3 rfl
  exact key _ P hX hP h rfl

/-- Step 5 (p. 291): "Then, by replacing `Ũ` by `Ũ − ((W_* ∩ E_1) − F)`, we may assume that
(3)** `Ũ ∩ W_* ∩ E_1 = F`, where `Ũ ∩ W_*` is an open dense subset of `W_*`." (The paper prints `W_*` here.  `Ū` in these docstrings is the
paper's `Ũ`.)  Lean removes the union `K` of the components of `W_* ∩ E_1` disjoint from `F`,
which by (3)* is `(W_* ∩ E_1) − F`.

Deviation from the paper (gap filled): that `K` is closed (finitely many components of a
closed subset of a noetherian space, `finite_setOf_maximal_isIrreducible_subset`), so that
`Ū − K` is open in `W`; that `U` and `F` are not affected (a component meeting `U` is contained in
`F`); and the density of `Ū ∩ W_*` in `W_*` (`DatumI.Raw.pts_prepWStar_subset_closure_inter`: a
non-empty open subset of an irreducible component of `W` is dense in it, and `U` is dense in `W`)
are tacit in the paper. -/
theorem stage₃SS_of_stage₃Star {N : ℕ} (hX : IsAmbient X N) (h : P.Stage₃Star) :
    P.Stage₃SS := by
  classical
  have : IsAlgebraicScheme X := hX.1
  have : TopologicalSpace.NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  obtain ⟨h₁, h₃, Ubar, h₂, -⟩ := h
  obtain ⟨⟨V, hV, hUbar⟩, hUU, hFU, hres⟩ := h₂
  have hFD := P.ℜ.pts_prepF_subset P.E₁ P.U
  have hfin := finite_setOf_maximal_isIrreducible_subset (X := X)
    ((P.ℜ.prepWStar P.E₁).inter P.E₁).support.isClosed
  -- the components of `W_* ∩ E_1` disjoint from `F`
  set K : Set X := ⋃ G ∈ {G ∈ ((P.ℜ.prepWStar P.E₁).inter P.E₁).irreducibleComponents |
    G.pts ∩ (P.ℜ.prepF P.E₁ P.U).pts = ∅}, G.pts with hK
  have hKcl : IsClosed K := by
    refine Set.Finite.isClosed_biUnion ?_ fun G _ => G.support.isClosed
    refine (hfin.image Subscheme.ofClosed).subset ?_
    rintro G ⟨⟨Z, hZ, rfl⟩, -⟩
    exact ⟨Z, hZ, rfl⟩
  have hKF : ∀ x ∈ K, x ∉ (P.ℜ.prepF P.E₁ P.U).pts := by
    intro x hxK hxF
    obtain ⟨G, ⟨-, hGF⟩, hxG⟩ := Set.mem_iUnion₂.mp hxK
    exact (Set.eq_empty_iff_forall_notMem.mp hGF) x ⟨hxG, hxF⟩
  have hKU : ∀ x ∈ K, x ∉ P.U := by
    intro x hxK hxU
    obtain ⟨G, ⟨hG, hGF⟩, hxG⟩ := Set.mem_iUnion₂.mp hxK
    exact (Set.eq_empty_iff_forall_notMem.mp hGF) x
      ⟨hxG, P.ℜ.pts_subset_pts_prepF P.E₁ P.U hG ⟨x, hxG, hxU⟩ hxG⟩
  refine ⟨h₁, Ubar \ K, ⟨⟨V \ K, hV.sdiff hKcl, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hUbar]; ext x; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
  · exact fun x hx => ⟨hUU hx, fun hxK => hKU x hxK hx⟩
  · exact fun x hx => ⟨hFU hx, fun hxK => hKF x hxK hx⟩
  · exact fun x hx => hres x hx.1
  · -- `Ū' ∩ W_* ∩ E_1 = F`
    apply Set.Subset.antisymm
    · rintro x ⟨⟨⟨hxU, hxK⟩, hxW⟩, hxE⟩
      obtain ⟨G, hG, hxG⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_pts
        ((P.ℜ.prepWStar P.E₁).inter P.E₁) (Subscheme.mem_pts_inter_iff.mpr ⟨hxW, hxE⟩)
      rcases h₃ G hG with hsub | hempty
      · exact hsub hxG
      · exact absurd (Set.mem_iUnion₂.mpr ⟨G, ⟨hG, hempty⟩, hxG⟩) hxK
    · intro x hx
      have := Subscheme.mem_pts_inter_iff.mp (hFD hx)
      exact ⟨⟨⟨hFU hx, fun hxK => hKF x hxK hx⟩, this.1⟩, this.2⟩
  · -- density
    obtain ⟨U₀, hU₀, hUeq⟩ := P.hU.1
    have hd := P.ℜ.pts_prepWStar_subset_closure_inter P.E₁ hU₀
      (by rw [← hUeq]; exact P.hU.2.1)
    refine hd.trans (closure_mono ?_)
    rintro v ⟨hv0, hvW⟩
    have hvU : v ∈ P.U := by rw [hUeq]; exact ⟨hv0, P.ℜ.pts_prepWStar_subset P.E₁ hvW⟩
    exact ⟨⟨hUU hvU, fun hvK => hKU v hvK hvU⟩, hvW⟩

/-- "`ℜ` is resolved at every generic point of `F`" (p. 291, the parenthetical remark in step (4)):
a generic point `η` of `F` (a point with `closure {η}` an irreducible component of `F`) lies in the
open restriction `U`, on which `ℜ` is resolved.

Deviation from the paper (gap filled): the paper uses this fact without comment.  `F` is the union of
the components `F_j` of `W_* ∩ E_1` meeting `U = U₀ ∩ W`, so `η` is the generic point of some `F_j`;
the non-empty open subset `F_j ∩ U₀` of the irreducible `F_j` contains `η`, hence `η ∈ U`. -/
theorem resolvedAt_of_isGenericPoint_prepF [IsAlgebraicScheme X] {η : X}
    (h : Maximal (fun S : Set X => _root_.IsIrreducible S ∧ S ⊆ (P.ℜ.prepF P.E₁ P.U).pts)
      (closure {η})) : P.ℜ.ResolvedAt η :=
  P.hU.2.2 η (P.mem_U_of_isGenericPoint_prepF h)

/-- Step 6 (p. 291) at a point `x` of `F`: "It follows from (1), (2) and (3)**, with help of Lemma 3,
that (4) `ℜ` is resolved at every point of `Ū ∩ W_*`.  (Here, we must use the fact that `ℜ` is
resolved at every generic point of `F`.)"  Here `hnc` is the second part of (1) and `hgen` the fact
that `ℜ` is resolved at every generic point of `F` (`resolvedAt_of_isGenericPoint_prepF`).

Proof.  The ideal `J = W_x + E_{1,x}` has `F_x` as its radical (every component of `W ∩ E_1`
through `x` has its generic point in `Ū ∩ W_* ∩ E_1 = F` by (3)**), and `F_x` is a minimal prime of
`J`, the stalk at `x` of a component of `W ∩ E_1` whose generic point `η` is a generic point of
`F`.  At `η`, `ℜ` is resolved, so the maximal ideal of `O_η = (O_x)_{F_x}` is generated by the
generators of `W_η` and `E_{1,η}`, i.e. `J` becomes `F_x` after localization.  Hence
`F_x = W_x + E_{1,x}` (transversality of `E_1` and `W` at `x`;
`eq_sup_span_of_radical_of_loc`), and Lemma 3 in the transversal form
(`Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_of_transversal`) gives the normal crossings of `E`
with `W` at `x`.

Deviation from the paper (gap filled; incomplete citation): Lemma 3 as stated does not apply at
`x ∈ F` (its hypothesis (iii) fails for `E_1`); the paper's parenthetical remark supplies the
missing transversality, and this is what is proved here.  The fact "resolved at every generic point
of `F`", which the paper uses in this parenthesis, follows from the hypothesis that `ℜ` is resolved on
`U` (`resolvedAt_of_isGenericPoint_prepF`). -/
theorem resolvedAt_of_mem_prepF [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) {Ubar : Set X}
    (hnc : P.ℜ.E.HasOnlyNormalCrossingsWith (P.ℜ.prepF P.E₁ P.U))
    (hgen : ∀ η : X, Maximal (fun S : Set X =>
      _root_.IsIrreducible S ∧ S ⊆ (P.ℜ.prepF P.E₁ P.U).pts) (closure {η}) → P.ℜ.ResolvedAt η)
    (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃SS Ubar) {x : X}
    (hxF : x ∈ (P.ℜ.prepF P.E₁ P.U).pts) : P.ℜ.ResolvedAt x := by
  have : TopologicalSpace.NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  set F := P.ℜ.prepF P.E₁ P.U with hFdef
  set Wst := P.ℜ.prepWStar P.E₁ with hWstdef
  set W := P.ℜ.W with hWdef
  set i₀ : Fin P.α := ⟨0, P.hα⟩ with hi₀
  obtain ⟨⟨V, hV, hUbar⟩, hUU, hFU, hres⟩ := h₂
  have hFsub : ∀ y ∈ F.pts, y ∈ Wst.pts ∧ y ∈ P.E₁.pts := fun y hy =>
    Subscheme.mem_pts_inter_iff.mp (P.ℜ.pts_prepF_subset P.E₁ P.U hy)
  have hFW : F.pts ⊆ W.pts := fun y hy => P.ℜ.pts_prepWStar_subset P.E₁ (hFsub y hy).1
  have hxUbar : x ∈ Ubar := hFU hxF
  obtain ⟨hWs, hVf, hrest⟩ := hres x hxUbar
  have hxW : x ∈ W.pts := hWs.1
  have hFred : F.IsReduced := Subscheme.ofClosed_isReduced _
  have hWred : W.IsReduced := P.hℜ.2.2.2.1
  have hQF : W.stalkIdeal x ≤ F.stalkIdeal x :=
    Subscheme.stalkIdeal_mono (fun U => Subscheme.isContainedIn_of_pts_subset hFred hFW U) x
  have hEF : P.E₁.stalkIdeal x ≤ F.stalkIdeal x :=
    Subscheme.stalkIdeal_mono (fun U => Subscheme.isContainedIn_of_pts_subset hFred
      (fun y hy => (hFsub y hy).2) U) x
  -- the normal crossings of `E` with `F` at `x`
  have hiF : (Subscheme.unionFam P.E).HasOnlyNormalCrossingsWithAt F x := P.hEunion ▸ hnc x hxF
  obtain ⟨ZE, hZE, ⟨tF, htF, hFt⟩, hEZE⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    P.E P.hE (fun i => iInf_le _ i) hiF
  obtain ⟨z, hzZ, hzE⟩ : ∃ z ∈ ZE, P.E₁.stalkIdeal x = Ideal.span {z} := by
    rcases hEZE i₀ with h | h
    · exfalso
      have h1 := Subscheme.stalkIdeal_le_maximalIdeal P.E₁ (hFsub x hxF).2
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ h1))
    · exact h
  have hzm : z ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := hZE.1 ▸ Ideal.subset_span hzZ
  have hext : ExtendsToRSOP (X.presheaf.stalk x) tF := ⟨ZE, htF, hZE⟩
  have hFprime : (F.stalkIdeal x).IsPrime := by rw [hFt]; exact hext.isPrime_span
  have hFreg : IsRegularLocalRing (X.presheaf.stalk x ⧸ F.stalkIdeal x) := by
    rw [hFt]; exact hext.isRegularLocalRing_quotient
  have hQreg : IsRegularLocalRing (X.presheaf.stalk x ⧸ W.stalkIdeal x) := hWs.2
  have hQprime : (W.stalkIdeal x).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
  -- the unique component `C₀` of `W` through `x`; it is not contained in `E₁`
  obtain ⟨C₀, hC₀, hC₀E, hxC₀⟩ :=
    DatumI.Raw.exists_mem_irreducibleComponents_of_mem_pts_prepWStar P.ℜ P.E₁ (hFsub x hxF).1
  have hminQ : ∀ C ∈ W.irreducibleComponents, x ∈ C.pts → C.stalkIdeal x = W.stalkIdeal x := by
    intro C hC hxC
    have hq := Subscheme.stalkIdeal_mem_minimalPrimes hC hxC
    exact le_antisymm (hq.2 ⟨hQprime, le_rfl⟩ hq.1.2) hq.1.2
  have hC₀Q : C₀.stalkIdeal x = W.stalkIdeal x := hminQ C₀ hC₀ hxC₀
  have hC₀Wst : C₀.pts ⊆ Wst.pts := by
    obtain ⟨Z, -, hZeq⟩ := id hC₀
    intro y hy
    rw [DatumI.Raw.pts_prepWStar]
    exact subset_closure ⟨_, ⟨C₀.support, ⟨_, hC₀, hC₀E, rfl⟩, rfl⟩, hy⟩
  -- the ideal `J = W_x + E_{1,x}` and the subscheme `D = W ∩ E₁`
  set D := W.inter P.E₁ with hD
  set J := W.stalkIdeal x ⊔ P.E₁.stalkIdeal x with hJ
  have hDx : D.stalkIdeal x = J := Subscheme.stalkIdeal_sup_eq _ _ x
  have hDpts : D.pts ⊆ W.pts ∩ P.E₁.pts := fun y hy => Subscheme.mem_pts_inter_iff.mp hy
  have hFD : F.pts ⊆ D.pts := fun y hy =>
    Subscheme.mem_pts_inter_iff.mpr ⟨hFW hy, (hFsub y hy).2⟩
  -- every component of `D` through `x` lies in `F`
  have hcompF : ∀ G ∈ D.irreducibleComponents, x ∈ G.pts → G.pts ⊆ F.pts := by
    intro G hG hxG
    obtain ⟨Z, hZmax, rfl⟩ := id hG
    have hZpts : (Subscheme.ofClosed Z).pts = Z := Scheme.IdealSheafData.coe_support_vanishingIdeal Z
    have hxZ : x ∈ (Z : Set X) := by rwa [hZpts] at hxG
    obtain ⟨g, hg⟩ : ∃ g, IsGenericPoint g (Z : Set X) := QuasiSober.sober hZmax.1.1 Z.isClosed
    have hgx : g ⤳ x := hg.specializes hxZ
    have hgD : g ∈ D.pts := hZmax.1.2 hg.mem
    have hgW : g ∈ W.pts := (hDpts hgD).1
    have hgE : g ∈ P.E₁.pts := (hDpts hgD).2
    have hxV : x ∈ V := by
      have := hxUbar; rw [hUbar] at this; exact this.1
    have hgUbar : g ∈ Ubar := by
      rw [hUbar]; exact ⟨hgx.mem_open hV hxV, hgW⟩
    obtain ⟨C', hC', hgC'⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_pts W hgW
    have hxC' : x ∈ C'.pts := by
      obtain ⟨Z', -, rfl⟩ := hC'
      have h1 : g ∈ (Z' : Set X) := by
        rwa [show (Subscheme.ofClosed Z').pts = Z' from
          Scheme.IdealSheafData.coe_support_vanishingIdeal Z'] at hgC'
      have h2 : x ∈ closure {g} := specializes_iff_mem_closure.mp hgx
      rw [show (Subscheme.ofClosed Z').pts = Z' from
          Scheme.IdealSheafData.coe_support_vanishingIdeal Z']
      exact closure_minimal (Set.singleton_subset_iff.mpr h1) Z'.isClosed h2
    have hC'eq : C' = C₀ :=
      Subscheme.eq_of_stalkIdeal_eq hC' hC₀ hxC' hxC₀ ((hminQ C' hC' hxC').trans hC₀Q.symm)
    have hgC₀ : g ∈ C₀.pts := hC'eq ▸ hgC'
    have hgF : g ∈ F.pts := by
      rw [← h₃.1]
      exact ⟨⟨hgUbar, hC₀Wst hgC₀⟩, hgE⟩
    have : (Z : Set X) ⊆ F.pts := by
      rw [← hg.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hgF) F.support.isClosed
    rwa [hZpts]
  have hJp : J ≤ F.stalkIdeal x := sup_le hQF hEF
  have hmin : ∀ q ∈ J.minimalPrimes, F.stalkIdeal x ≤ q := by
    intro q hq
    obtain ⟨G, hG, hxG, hGq⟩ :=
      Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes D x (hDx ▸ hq)
    have hGred : G.IsReduced := by
      obtain ⟨Z, -, rfl⟩ := hG
      exact Subscheme.ofClosed_isReduced Z
    rw [← hGq]
    exact Subscheme.stalkIdeal_mono (fun U => Subscheme.isContainedIn_of_pts_subset hGred
      (hcompF G hG hxG) U) x
  have hrad : F.stalkIdeal x = J.radical := by
    refine le_antisymm ?_ ?_
    · rw [← Ideal.sInf_minimalPrimes]
      exact le_sInf fun q hq => hmin q hq
    · exact (Ideal.radical_mono hJp).trans (Ideal.IsPrime.radical hFprime).le
  -- `F_x` is a minimal prime of `J`
  have hFmin : F.stalkIdeal x ∈ J.minimalPrimes := by
    obtain ⟨q₀, hq₀, hq₀p⟩ := Ideal.exists_minimalPrimes_le hJp
    have := le_antisymm (hmin q₀ hq₀) hq₀p
    exact this ▸ hq₀
  -- the component `G₀` of `D` with stalk `F_x`, and its generic point `η`
  obtain ⟨G₀, hG₀, hxG₀, hG₀p⟩ :=
    Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes D x (hDx ▸ hFmin)
  obtain ⟨Z₀, hZ₀max, hZ₀eq⟩ := id hG₀
  have hZ₀pts : G₀.pts = Z₀ := by
    rw [hZ₀eq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z₀
  have hxZ₀ : x ∈ (Z₀ : Set X) := by rwa [hZ₀pts] at hxG₀
  obtain ⟨η, hη⟩ : ∃ η, IsGenericPoint η (Z₀ : Set X) :=
    QuasiSober.sober hZ₀max.1.1 Z₀.isClosed
  have hηx : η ⤳ x := hη.specializes hxZ₀
  have hZ₀F : (Z₀ : Set X) ⊆ F.pts := hZ₀pts ▸ hcompF G₀ hG₀ hxG₀
  have hηF : η ∈ F.pts := hZ₀F hη.mem
  have hmax : Maximal (fun S : Set X => _root_.IsIrreducible S ∧ S ⊆ F.pts) (closure {η}) := by
    have hcl : closure {η} = (Z₀ : Set X) := hη.def
    rw [hcl]
    refine ⟨⟨hZ₀max.1.1, hZ₀F⟩, fun S hS hle => ?_⟩
    obtain ⟨hSirr, hSF⟩ := hS
    have hcS : closure S ⊆ F.pts := closure_minimal hSF F.support.isClosed
    have hT := hZ₀max.2 (y := ⟨closure S, isClosed_closure⟩) ⟨hSirr.closure, (hcS.trans hFD)⟩
      (hle.trans subset_closure)
    exact subset_closure.trans hT
  have hηres := hgen η hmax
  -- `z ∉ W_x`: otherwise `C₀` would be a component of `W ∩ E₁`, hence contained in `E₁`
  have hzQ : z ∉ W.stalkIdeal x := by
    intro hzQ
    have hJQ : J = W.stalkIdeal x := by
      rw [hJ, hzE]
      exact sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hzQ)
    have hQmin : W.stalkIdeal x ∈ J.minimalPrimes := by
      rw [hJQ]
      exact ⟨⟨hQprime, le_rfl⟩, fun q hq _ => hq.2⟩
    obtain ⟨G, hG, hxG, hGq⟩ :=
      Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes D x (hDx ▸ hQmin)
    have hGC : G = C₀ := Subscheme.eq_of_stalkIdeal_eq_of_mem_irreducibleComponents hG hC₀ hxG
      hxC₀ (hGq.trans hC₀Q.symm)
    have hC₀red : C₀.IsReduced := by
      obtain ⟨Z, -, hZ⟩ := hC₀
      rw [hZ]; exact Subscheme.ofClosed_isReduced Z
    apply hC₀E
    refine Subscheme.isContainedIn_of_pts_subset hC₀red fun y hy => ?_
    have : y ∈ G.pts := hGC ▸ hy
    obtain ⟨Z, hZmax, hZ⟩ := hG
    have hy' : y ∈ D.pts := by
      have h2 : y ∈ (Z : Set X) := by
        rw [hZ] at this
        rwa [show (Subscheme.ofClosed Z).pts = Z from
          Scheme.IdealSheafData.coe_support_vanishingIdeal Z] at this
      exact hZmax.1.2 h2
    exact (hDpts hy').2
  -- the algebra at the generic point `η`
  have : IsRegularLocalRing (X.presheaf.stalk η) := hX η
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk η) :=
    (X.presheaf.stalkSpecializes hηx).hom.toAlgebra
  have hloc := isLocalization_stalkSpecializes_of_specializes hηx
  have hcomap : (IsLocalRing.maximalIdeal (X.presheaf.stalk η)).comap (X.presheaf.stalkSpecializes hηx).hom =
      F.stalkIdeal x := by
    have hG₀η : G₀.stalkIdeal η = IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
      rw [hZ₀eq]
      have : Z₀ = ⟨closure {η}, isClosed_closure⟩ := by
        apply SetLike.coe_injective
        exact hη.def.symm
      rw [this]
      exact stalkIdeal_ofClosed_closure_self' η
    have : (G₀.stalkIdeal x).IsPrime := hG₀p ▸ hFprime
    rw [Subscheme.comap_maximalIdeal_stalkSpecializes_eq G₀ hηx hG₀η, hG₀p]
  have hsub : ((IsLocalRing.maximalIdeal (X.presheaf.stalk η)).comap
      (X.presheaf.stalkSpecializes hηx).hom).primeCompl = (F.stalkIdeal x).primeCompl := by
    ext a
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hcomap]
  have : IsLocalization (F.stalkIdeal x).primeCompl (X.presheaf.stalk η) := by
    rw [← hsub]
    exact hloc
  have : IsLocalization.AtPrime (X.presheaf.stalk η) (F.stalkIdeal x) := this
  -- normal crossings of `E` with `W` at `η`
  have hηnc : (Subscheme.unionFam P.E).HasOnlyNormalCrossingsWithAt W η := P.hEunion ▸ hηres.2.2
  obtain ⟨Zη, hZη, ⟨tη, htη, hWt⟩, hEη⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt
    P.E P.hE (fun i => iInf_le _ i) hηnc
  have hmapE : ∀ D' : Subscheme X,
      D'.stalkIdeal η = (D'.stalkIdeal x).map (algebraMap (X.presheaf.stalk x) (X.presheaf.stalk η)) := fun D' =>
    Subscheme.stalkIdeal_eq_map_stalkSpecializes D' hηx
  obtain ⟨a, haZ, haE⟩ : ∃ a ∈ Zη, P.E₁.stalkIdeal η = Ideal.span {a} := by
    rcases hEη i₀ with h | h
    · exfalso
      have h1 := Subscheme.stalkIdeal_le_maximalIdeal P.E₁ (hFsub η hηF).2
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ h1))
    · exact h
  have hzB : (Ideal.span {z}).map (algebraMap (X.presheaf.stalk x) (X.presheaf.stalk η)) = Ideal.span {a} := by
    rw [← hzE, ← hmapE]; exact haE
  have hQB : (W.stalkIdeal x).map (algebraMap (X.presheaf.stalk x) (X.presheaf.stalk η)) = Ideal.span (tη : Set (X.presheaf.stalk η)) := by
    rw [← hmapE]; exact hWt
  have hzprime : (Ideal.span {z}).IsPrime :=
    (ExtendsToRSOP.of_isRegularSystemOfParameters hZE).isPrime_span_singleton hzZ
  have hzp : z ∈ F.stalkIdeal x := hEF (hzE ▸ Ideal.mem_span_singleton_self z)
  have hrad' : F.stalkIdeal x = (W.stalkIdeal x ⊔ Ideal.span {z}).radical := by
    rw [hrad, hJ, hzE]
  obtain ⟨hlocal, hdD⟩ := localization_facts_of_isRegularSystemOfParameters (F.stalkIdeal x)
    (W.stalkIdeal x) hQF hzprime hzp hrad' hZη htη hQB haZ hzB
  have hT : F.stalkIdeal x = W.stalkIdeal x ⊔ Ideal.span {z} :=
    eq_sup_span_of_radical_of_loc (W.stalkIdeal x) (F.stalkIdeal x) hQF hzQ hzm hrad' hlocal
  have hred : (Subscheme.unionFam P.E).IsReduced := P.hEunion ▸ P.hℜ.1
  refine ⟨hWs, hVf, ?_⟩
  rw [P.hEunion]
  refine Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_of_transversal hX P.E P.hE i₀ hred hxF
    hiF hrest hQF (fun h => hzQ ((Ideal.span_singleton_le_iff_mem _).mp (hzE ▸ h))) ?_ ?_
  · show F.stalkIdeal x = W.stalkIdeal x ⊔ P.E₁.stalkIdeal x
    rw [hzE]; exact hT
  · intro j hj hle
    have hxj : x ∈ (P.E j).pts := by
      refine Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr fun h => ?_
      have h1 := Subscheme.stalkIdeal_le_maximalIdeal F hxF
      rw [h] at hle
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (top_le_iff.mp hle ▸ h1))
    have hne : P.E j ≠ Subscheme.empty := by
      intro h
      rw [h, DatumTransform.pts_empty] at hxj
      exact hxj
    obtain ⟨hns, -, -⟩ := (P.hE j).resolve_left hne
    have : ((P.E j).stalkIdeal x).IsPrime :=
      Subscheme.isPrime_stalkIdeal_of_isNonsingular_of_mem_pts _ hns hxj
    obtain ⟨b, hb, hbE⟩ : ∃ b ∈ Zη, (P.E j).stalkIdeal η = Ideal.span {b} := by
      rcases hEη j with h | h
      · exfalso
        have h1 : ((P.E j).stalkIdeal x).map (algebraMap (X.presheaf.stalk x) (X.presheaf.stalk η)) ≤ (F.stalkIdeal x).map (algebraMap (X.presheaf.stalk x) (X.presheaf.stalk η)) :=
          Ideal.map_mono hle
        rw [IsLocalization.AtPrime.map_eq_maximalIdeal (F.stalkIdeal x) (X.presheaf.stalk η), ← hmapE, h] at h1
        exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp h1)
      · exact h
    rcases hdD ((P.E j).stalkIdeal x) hle b hb (by rw [← hmapE]; exact hbE) with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hzE.symm)

/-- Step 6 (p. 291): "It follows from (1), (2) and (3)**, with help of Lemma 3, that (4) `ℜ` is
resolved at every point of `Ū ∩ W_*`.  (Here, we must use the fact that `ℜ` is resolved at every
generic point of `F`.)"

At a point `x ∈ Ū ∩ W_*` outside `E_1` the sets `E` and `⋃_{i≥2} E_i` agree near `x` and the claim
is (2); at a point of `Ū ∩ W_* ∩ E_1 = F` (by (3)**) it is `resolvedAt_of_mem_prepF`.

Deviation from the paper (gap filled; incomplete citation): see `resolvedAt_of_mem_prepF` (Lemma 3
does not cover `E_1`, the transversality of `E_1` and `W` along `F` is obtained from the resolvedness
at the generic points of `F`, `resolvedAt_of_isGenericPoint_prepF`). -/
theorem cond₄_of_cond₃SS {N : ℕ} (hX : IsAmbient X N) {Ubar : Set X} (h₁ : P.Cond₁)
    (h₂ : P.Cond₂ Ubar) (h₃ : P.Cond₃SS Ubar) : P.Cond₄ Ubar := by
  classical
  have : IsAlgebraicScheme X := hX.1
  intro x hx
  by_cases hxE : x ∈ P.E₁.pts
  · have hxF : x ∈ (P.ℜ.prepF P.E₁ P.U).pts := by
      rw [← h₃.1]; exact ⟨hx, hxE⟩
    exact P.resolvedAt_of_mem_prepF hX.2.1 h₁.2.2
      (fun η hη => P.resolvedAt_of_isGenericPoint_prepF hη) h₂ h₃ hxF
  · obtain ⟨hWs, hVf, hrest⟩ := h₂.2.2.2 x hx.1
    refine ⟨hWs, hVf, ?_⟩
    rw [P.hEunion]
    exact Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_of_stalkIdeal_eq_top hX.2.1 P.E P.hE
      ⟨0, P.hα⟩ (P.hEunion ▸ P.hℜ.1) hrest (Subscheme.stalkIdeal_eq_top_of_notMem_pts hxE)

/-- (3)** and the conditions (1), (2) give (4): `Stage₃SS → Stage₄` (`cond₄_of_cond₃SS`). -/
theorem stage₄_of_stage₃SS {N : ℕ} (hX : IsAmbient X N) (h : P.Stage₃SS) : P.Stage₄ := by
  obtain ⟨h₁, Ubar, h₂, h₃⟩ := h
  exact ⟨h₁, Ubar, h₂, h₃, P.cond₄_of_cond₃SS hX h₁ h₂ h₃⟩

/-! ### step 7 (p. 291), the datum on `X − F` -/

section PrepPhase22a

open IsLocalRing Classical

theorem _root_.Hironaka.Subscheme.totalTransform_bot_eq {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    Subscheme.totalTransform g (⊥ : Subscheme Y) = ⊥ := by
  refine le_antisymm (Subscheme.le_iff_stalkIdeal_le.mpr fun y => ?_) bot_le
  rw [Hironaka.stalkIdeal_totalTransform, Subscheme.stalkIdeal_bot_eq,
    Subscheme.stalkIdeal_bot_eq, Ideal.map_bot]

/-- The restriction of a closed restriction to an open subscheme is a closed restriction
(`(E_1 − F)` for the datum `ℜ_{X−F}`, p. 291). -/
theorem _root_.Hironaka.DatumI.Raw.isClosedRestriction_pullback_of_isOpenImmersion
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) [IsOpenImmersion g] {ℜ : DatumI.Raw Y} {F : Subscheme Y}
    (h : ℜ.IsClosedRestriction F) :
    (ℜ.pullback g).IsClosedRestriction (Subscheme.totalTransform g F) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨FlatPreimm.isNonsingularIrreducibleCodimOne_totalTransform g F h1, fun z => ?_, ?_⟩
  · rw [DatumI.Raw.pullback_E, ← FlatPreimm.totalTransform_union]
    show (Subscheme.totalTransform g (ℜ.E.union F)).HasOnlyNormalCrossingsWithAt ⊥ z
    rw [← Subscheme.totalTransform_bot_eq g]
    exact (FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff g _ _ z).mpr (h2 (g z))
  · rw [DatumI.Raw.pullback_W, FlatPreimm.pts_totalTransform, FlatPreimm.pts_totalTransform]
    have : g.base ⁻¹' ℜ.W.pts \ g.base ⁻¹' F.pts = g.base ⁻¹' (ℜ.W.pts \ F.pts) := rfl
    rw [this, ← g.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      g.base.hom.continuous]
    exact Set.preimage_mono h3

/-- The tail `⋃_{E_i ≠ E_1} E_i` together with `E_1` is the whole boundary `⋃ E_i`. -/
theorem prepERest_union_E₁ : (prepERest P.E ⟨0, P.hα⟩).union P.E₁ = Subscheme.unionFam P.E := by
  apply le_antisymm
  · refine le_iInf fun i => ?_
    by_cases h : P.E i = P.E ⟨0, P.hα⟩
    · rw [h]; exact inf_le_right
    · exact inf_le_left.trans (iInf_le (fun i : {i : Fin P.α // P.E i ≠ P.E ⟨0, P.hα⟩} => P.E i)
        ⟨i, h⟩)
  · exact le_inf (le_iInf fun i => iInf_le _ i.1) (iInf_le P.E (⟨0, P.hα⟩ : Fin P.α))

/-- The datum `ℜ^{N*,n*}_I` of step 7, before restriction to `X − F`:
`(⋃_{i≥2} E_i; V_1, …, V_β, W; W_*)` (p. 291). -/
noncomputable def datumStar : DatumI.Raw X :=
  { P.ℜ.extendBy P.ℜ.W with E := prepERest P.E ⟨0, P.hα⟩, W := P.ℜ.prepWStar P.E₁ }

theorem datumStar_E : P.datumStar.E = prepERest P.E ⟨0, P.hα⟩ := rfl

theorem datumStar_W : P.datumStar.W = P.ℜ.prepWStar P.E₁ := rfl

theorem isDatum_datumStar (hXns : X.IsNonsingular) : P.datumStar.IsDatum := by
  have hrest := P.isDatum_rest hXns
  have hWsub : (P.ℜ.prepWStar P.E₁).IsContainedIn P.ℜ.W :=
    Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced _)
      (P.ℜ.pts_prepWStar_subset P.E₁)
  refine ⟨hrest.1, hrest.2.1, hrest.2.2.1, Subscheme.ofClosed_isReduced _, fun j => ?_⟩
  induction j using Fin.lastCases with
  | last => simpa only [datumStar, DatumI.Raw.extendBy, Fin.snoc_last] using hWsub
  | cast j =>
    simp only [datumStar, DatumI.Raw.extendBy, Fin.snoc_castSucc]
    exact fun U => (P.hℜ.2.2.2.2 j U).trans (hWsub U)

/-- `(E; W_*)` with the restriction `E_1` is a closed restriction for `datumStar` (p. 291: the
closed
restriction `E_1` of `ℜ^{N*,n*}_I` before removing `F`). -/
theorem isClosedRestriction_datumStar_E₁ [IsAlgebraicScheme X] :
    P.datumStar.IsClosedRestriction P.E₁ := by
  have : NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  have hE1 := P.hE ⟨0, P.hα⟩
  refine ⟨hE1, ?_, ?_⟩
  · intro x
    rw [datumStar_E, prepERest_union_E₁, ← P.hEunion]
    exact P.hℜ.2.2.1 x
  · rw [datumStar_W, DatumI.Raw.pts_prepWStar_eq]
    have hcl := prepWStarT_eq_closure_diff (W := P.ℜ.W.pts) (E := P.E₁.pts)
      P.ℜ.W.support.isClosed P.E₁.support.isClosed
    rw [hcl]
    refine closure_minimal (fun y hy => subset_closure ⟨subset_closure hy, hy.2⟩) isClosed_closure
  
end PrepPhase22a

/-! ### step 7, permissibility of the induced succession -/

section PrepPhase23a

open IsLocalRing Classical

/-- Lemma 3 (p. 286) for a union `T ∪ E_1` with `E_1` non-singular at `x` (presentation-free form of
`hasOnlyNormalCrossingsWithAt_unionFam_of_stalkIdeal_le`): if `T ∪ E_1` has only normal crossings at
`x`,
`T` has only normal crossings with `B` at `x`, and `E_{1,x} ⊆ B_x`, then `T ∪ E_1` has only normal
crossings with `B` at `x`.  The components of `T ∪ E_1` through `x` are those of `T` and `E_1`
(whose
generator lies in `B_x`, so needs no partner in the system adapted to `B`). -/
theorem Subscheme.hasOnlyNormalCrossingsWithAt_union_of_stalkIdeal_le
    {X : Scheme.{u}} (hX : X.IsNonsingular) {T E₁ B : Subscheme X} {x : X} (hxB : x ∈ B.pts)
    (hred : (T.union E₁).IsReduced) (hp : (E₁.stalkIdeal x).IsPrime)
    (hi : (T.union E₁).HasOnlyNormalCrossingsAt x) (hT : T.HasOnlyNormalCrossingsWithAt B x)
    (hz : E₁.stalkIdeal x ≤ B.stalkIdeal x) : (T.union E₁).HasOnlyNormalCrossingsWithAt B x := by
  classical
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  obtain ⟨ZE, hZE, ⟨JE, hJEZ, hEJ⟩, -⟩ :=
    (Subscheme.hasOnlyNormalCrossingsWithAt_iff hred (hX x)).mp hi
  obtain ⟨ZW, hZW, hcompT, tW, htWZ, hBt⟩ := hT
  have hJEext := (ExtendsToRSOP.of_isRegularSystemOfParameters hZE).mono hJEZ
  have hQP : B.stalkIdeal x ≤ maximalIdeal (X.presheaf.stalk x) :=
    Subscheme.stalkIdeal_le_maximalIdeal B hxB
  have hEx : (T.union E₁).stalkIdeal x = T.stalkIdeal x ⊓ E₁.stalkIdeal x :=
    Subscheme.stalkIdeal_inf_eq T E₁ x
  obtain ⟨Z, hZ, hCZ, tP, htPZ, hPt, tQ, htQ, hQt⟩ :=
    exists_rsop_adapted_to_flag (B.stalkIdeal x) (maximalIdeal (X.presheaf.stalk x)) hQP ZE ZE ZW tW
      JE hZE (Finset.Subset.refl _) hZE.1.symm hZW htWZ hBt hJEZ (by
        intro c hc hcB
        have hpc : (Ideal.span {c}).IsPrime := hJEext.isPrime_span_singleton hc
        have hmin : Ideal.span {c} ∈ ((T.union E₁).stalkIdeal x).minimalPrimes := by
          rw [hEJ, hJEext.minimalPrimes_span_prod]
          exact ⟨c, hc, rfl⟩
        have hle : T.stalkIdeal x ⊓ E₁.stalkIdeal x ≤ Ideal.span {c} := by
          rw [← hEx]; exact hmin.1.2
        rcases (Ideal.IsPrime.inf_le hpc).mp hle with hTc | hEc
        · -- `span{c}` is minimal over `T_x`
          have hminT : Ideal.span {c} ∈ (T.stalkIdeal x).minimalPrimes := by
            refine ⟨⟨hpc, hTc⟩, fun q hq hqc => ?_⟩
            have hqE : (T.union E₁).stalkIdeal x ≤ q := by
              rw [hEx]; exact inf_le_left.trans hq.2
            exact hmin.2 ⟨hq.1, hqE⟩ hqc
          obtain ⟨C, hC, hxC, hCc⟩ :=
            Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes T x hminT
          obtain ⟨a, haZ, haC⟩ := hcompT C hC hxC
          exact ⟨a, haZ, hCc.symm.trans haC⟩
        · -- `span{c} = E_{1,x}`, which lies in `B_x`
          exfalso
          have hEE : E₁.stalkIdeal x = Ideal.span {c} := by
            have hq : (T.union E₁).stalkIdeal x ≤ E₁.stalkIdeal x := by rw [hEx]; exact inf_le_right
            exact le_antisymm hEc (hmin.2 ⟨hp, hq⟩ hEc)
          exact hcB (hz (hEE ▸ Ideal.mem_span_singleton_self c)))
  exact (Subscheme.hasOnlyNormalCrossingsWithAt_iff hred (hX x)).mpr
    ⟨Z, hZ, ⟨JE, hCZ, hEJ⟩, ⟨tQ, htQ.trans htPZ, hQt⟩⟩

end PrepPhase23a

section PrepPhase23b

open IsLocalRing Classical

variable {Y : Scheme.{u}}

/-- The datum `(T; V_1, …, V_β, W; W₁)` attached to `ℜ = (E; V; W)`: the datum `ℜ^{N*,n*}_I` of step
7
(p. 291) is `starDatum P.ℜ (⋃_{i≥2} E_i) W_*`. -/
noncomputable def starDatum (ℜ : DatumI.Raw Y) (T W₁ : Subscheme Y) : DatumI.Raw Y :=
  { ℜ.extendBy ℜ.W with E := T, W := W₁ }

theorem starDatum_transform (ℜ : DatumI.Raw Y) (T W₁ : Subscheme Y) {C : Subscheme Y}
    (t : MonoidalTransformation Y C) :
    (starDatum ℜ T W₁).transform t = starDatum (ℜ.transform t)
      ((Subscheme.strictTransform t T).union t.exceptional) (Subscheme.strictTransform t W₁) := by
  refine DatumI.Raw.mk_eq_mk rfl (fun j => ?_) rfl
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [starDatum, DatumI.Raw.extendBy, DatumI.Raw.transform, Fin.snoc_last]
  · simp [starDatum, DatumI.Raw.extendBy, DatumI.Raw.transform, Fin.snoc_castSucc]

/-- `⋃_{i∈J} E_i ∪ E_{i₀} = ⋃ E_i` when every index is in `J` or has `E_i = E_{i₀}`. -/
theorem unionFam_eq_union_of_forall {α : ℕ} (E : Fin α → Subscheme Y) (J : Set (Fin α))
    (i₀ : Fin α) (hJ : ∀ i, i ∈ J ∨ E i = E i₀) :
    Subscheme.unionFam E = (Subscheme.unionFam (fun i : J => E i)).union (E i₀) := by
  apply le_antisymm
  · exact le_inf (le_iInf fun i => iInf_le _ i.1) (iInf_le _ i₀)
  · refine le_iInf fun i => ?_
    rcases hJ i with h | h
    · exact inf_le_left.trans (iInf_le (fun i : J => E i) ⟨i, h⟩)
    · rw [h]; exact inf_le_right

/-- Step 7, "canonically induced": one center, permissible for `ℜ₁ = (T; V, W; W₁)` with closed
restriction
`E_1` (where `ℜ.E = T ∪ E_1`, `W₁ ⊆ W`), is permissible for `ℜ` (Lemma 3 for the boundary).

Deviation from the paper (gap filled): "any permissible monoidal transformation for
`(ℜ^{N*,n*}_I, E_1 − F)` is canonically induced by a permissible monoidal transformation for
`(ℜ, U)`"
(p. 291): the part about the datum `ℜ` is this lemma; the normal crossings of the whole boundary
`E_1 ∪ ⋃_{i≥2} E_i` with the center, which lies in `E_1`, is Lemma 3
(`hasOnlyNormalCrossingsWithAt_union_of_stalkIdeal_le`), the flatness conditions are among those of
`ℜ₁`
(the list of `ℜ₁` is that of `ℜ` followed by `W`). -/
theorem isPermissible_of_isPermissibleClosed_starDatum [IsAlgebraicScheme Y]
    (hXns : Y.IsNonsingular) {α : ℕ} (hα : 0 < α) (E : Fin α → Subscheme Y)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) (J : Set (Fin α))
    (hJ : ∀ i, i ∈ J ∨ E i = E ⟨0, hα⟩) {ℜ : DatumI.Raw Y} (hℜ : ℜ.IsDatum)
    (hEunion : ℜ.E = Subscheme.unionFam E) {W₁ : Subscheme Y} (hW₁ : W₁.IsContainedIn ℜ.W)
    {B : Subscheme Y}
    (hB : (starDatum ℜ (Subscheme.unionFam fun i : J => E i) W₁).IsPermissibleClosed
      (E ⟨0, hα⟩) B) : ℜ.IsPermissible B := by
  classical
  obtain ⟨⟨hBc, -, hres⟩, hBsub⟩ := hB
  have hBred : B.IsReduced := Subscheme.IsCenter.isReduced hBc
  have hBW : B.pts ⊆ ℜ.W.pts := (hBsub.trans Set.inter_subset_left).trans
    (pts_subset_of_isContainedIn hW₁)
  have hdec := unionFam_eq_union_of_forall E J ⟨0, hα⟩ hJ
  refine ⟨hBc, DatumI.Raw.isDatum_extendBy hℜ hBred hBW, fun x hx => ?_⟩
  obtain ⟨hs, hnf, hnc⟩ := hres x hx
  refine ⟨hs, fun j => ?_, ?_⟩
  · have h1 : ((starDatum ℜ (Subscheme.unionFam fun i : J => E i) W₁).extendBy B).V j.castSucc =
        (ℜ.extendBy B).V j := Fin.snoc_castSucc (α := fun _ => Subscheme Y) _ _ _
    rw [← h1]; exact hnf j.castSucc
  · have hE1pts : x ∈ (E ⟨0, hα⟩).pts := (hBsub hx).2
    have hE1ns : (E ⟨0, hα⟩).IsNonsingular := by
      have hne : E ⟨0, hα⟩ ≠ Subscheme.empty := fun h => by
        rw [h, DatumTransform.pts_empty] at hE1pts; exact hE1pts
      exact ((hE _).resolve_left hne).1
    have hprime := Subscheme.isPrime_stalkIdeal_of_isNonsingular_of_mem_pts _ hE1ns hE1pts
    have hle : (E ⟨0, hα⟩).stalkIdeal x ≤ B.stalkIdeal x :=
      Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn
        (Subscheme.isContainedIn_of_pts_subset hBred fun y hy => (hBsub hy).2) x
    have hi : (Subscheme.unionFam fun i : J => E i).union (E ⟨0, hα⟩) |>.HasOnlyNormalCrossingsAt x
        := by
      rw [← hdec, ← hEunion]; exact hℜ.2.2.1 x
    have hred : ((Subscheme.unionFam fun i : J => E i).union (E ⟨0, hα⟩)).IsReduced := by
      rw [← hdec, ← hEunion]; exact hℜ.1
    have := Subscheme.hasOnlyNormalCrossingsWithAt_union_of_stalkIdeal_le hXns hx hred hprime hi hnc
        hle
    show ℜ.E.HasOnlyNormalCrossingsWithAt B x
    rw [hEunion, hdec]; exact this

end PrepPhase23b

section PrepPhase23c

open IsLocalRing Classical

/-- Step 7, "canonically induced" (p. 291): a succession permissible for `ℜ₁ = (T; V, W; W₁)` with
closed
restriction `E_1`, where `ℜ.E = ⋃_{i∈J} E_i ∪ E_1` is presented by non-singular irreducible
divisors,
`W₁ ⊆ W`, whose centers lie in the complement of `U`, is permissible for `(ℜ, U)`.  Induction on the
succession; the data are carried along by `exists_presentation_transform`, `transform_tail_E` and
`starDatum_transform`.  See `isPermissible_of_isPermissibleClosed_starDatum`. -/
theorem _root_.Hironaka.MonoidalSuccession.isPermissibleIOpen_of_isPermissibleIClosed_starDatum [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}]
    {Y Y' : Scheme.{u}} (s : MonoidalSuccession Y Y') :
    ∀ [IsAlgebraicScheme Y], Y.IsNonsingular → ∀ {α : ℕ} (hα : 0 < α) (E : Fin α → Subscheme Y),
      (∀ i, (E i).IsNonsingularIrreducibleCodimOne) → ∀ (J : Set (Fin α)),
      (∀ i, i ∈ J ∨ E i = E ⟨0, hα⟩) → ∀ {ℜ : DatumI.Raw Y}, ℜ.IsDatum →
      ℜ.E = Subscheme.unionFam E → ∀ {W₁ : Subscheme Y}, W₁.IsContainedIn ℜ.W →
      ∀ (U R : Set Y), U ⊆ R →
      (starDatum ℜ (Subscheme.unionFam fun i : J => E i) W₁).IsDatum →
      s.IsPermissibleIClosed (starDatum ℜ (Subscheme.unionFam fun i : J => E i) W₁)
        (E ⟨0, hα⟩) → s.CentersAvoid R → s.IsPermissibleIOpen ℜ U := by
  induction s with
  | nil Y => intros; trivial
  | cons B t rest ih =>
    intro hXa hXns α hα E hE J hJ ℜ hℜ hEunion W₁ hW₁ U R hUR hℜ₁ hperm hav
    obtain ⟨hB, hrest⟩ := hperm
    obtain ⟨hBav, hrestav⟩ := hav
    have hBperm : ℜ.IsPermissible B :=
      isPermissible_of_isPermissibleClosed_starDatum hXns hα E hE J hJ hℜ hEunion hW₁ hB
    have hBW : B.pts ⊆ ℜ.W.pts :=
      (hB.2.trans Set.inter_subset_left).trans (pts_subset_of_isContainedIn hW₁)
    refine ⟨⟨hBperm, fun y hy => ⟨hBW hy, fun hyU => hBav y hy (hUR hyU)⟩⟩, ?_⟩
    obtain ⟨E', hE', hEq', hcs, hlast⟩ :=
      DatumI.Raw.exists_presentation_transform hXns E hE ℜ hℜ hEunion t hBperm
    have hT' := DatumI.Raw.transform_tail_E hXns E hE hℜ hEunion t hBperm E' hcs hlast J
    have hstar : (starDatum ℜ (Subscheme.unionFam fun i : J => E i) W₁).transform t =
        starDatum (ℜ.transform t)
          (Subscheme.unionFam fun j : ↥(Fin.castSucc '' J ∪ {Fin.last α}) => E' j)
          (Subscheme.strictTransform t W₁) := by
      rw [starDatum_transform]
      congr 2
    have hdat' := (DatumI.Raw.transform_isDatum hXns ℜ hℜ t hBperm).1
    have hℜ₁' := (DatumI.Raw.transform_isDatum hXns _ hℜ₁ t hB.1).1
    rw [hstar] at hℜ₁'
    have hE0 : E' ⟨0, Nat.succ_pos α⟩ = Subscheme.strictTransform t (E ⟨0, hα⟩) := hcs ⟨0, hα⟩
    have hrest' : rest.IsPermissibleIClosed
        (starDatum (ℜ.transform t)
          (Subscheme.unionFam fun j : ↥(Fin.castSucc '' J ∪ {Fin.last α}) => E' j)
          (Subscheme.strictTransform t W₁)) (E' ⟨0, Nat.succ_pos α⟩) := by
      rw [hE0, ← hstar]; exact hrest
    have hJ' : ∀ i : Fin (α + 1),
        i ∈ (Fin.castSucc '' J ∪ {Fin.last α} : Set (Fin (α + 1))) ∨
          E' i = E' ⟨0, Nat.succ_pos α⟩ := by
      intro i
      refine Fin.lastCases ?_ (fun i₀ => ?_) i
      · exact Or.inl (Or.inr rfl)
      · rcases hJ i₀ with h | h
        · exact Or.inl (Or.inl ⟨i₀, h, rfl⟩)
        · right
          rw [hE0, hcs i₀, h]
    have hW₁' : (Subscheme.strictTransform t W₁).IsContainedIn (ℜ.transform t).W :=
      MonoidalTransformation.isContainedIn_strictTransform t hW₁
    have hXa' : IsAlgebraicScheme t.X' := t.isAlgebraicScheme
    exact ih (t.isNonsingular_and_isNonsingular_exceptional hXns hBperm.1.isNonsingular).1
      (Nat.succ_pos α) E' hE' _ hJ' hdat' hEq' hW₁' (t.f.base ⁻¹' U) (t.f.base ⁻¹' R)
      (Set.preimage_mono hUR) hℜ₁' hrest' hrestav

end PrepPhase23c

section PrepPhase22ext

open CategoryTheory CategoryTheory.Limits

open _root_.Hironaka.MonoidalSuccession

variable {Z Z' : Scheme.{u}}

/-- `MonoidalSuccession.exists_extension` with the additional information that the centers of the
induced
succession lie over `C` (`sY.CentersAvoid Cᶜ`); same proof (the centers are the closures of the
images, `BY.pts = j(B)`).  Used in step 7 (p. 291) to see that the centers miss `F`. -/
theorem _root_.Hironaka.MonoidalSuccession.exists_extension_centersAvoid [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}]
    (s : MonoidalSuccession Z Z') :
    ∀ {Y : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] (C : Set Y), IsClosed C →
      C ⊆ Set.range j.base → s.CentersClosedIn j C →
      ∃ (Y' : Scheme.{u}) (sY : MonoidalSuccession Y Y') (j' : Z' ⟶ Y'), Flat j' ∧
        IsPreimmersion j' ∧ sY.CentersAvoid Cᶜ ∧ sY.length = s.length ∧
        j' ≫ sY.composite = s.composite ≫ j ∧
        Set.range j'.base = sY.composite.base ⁻¹' Set.range j.base ∧
        (∀ V, Subscheme.totalTransform j' (sY.strictTransform V) =
          s.strictTransform (Subscheme.totalTransform j V)) ∧
        (∀ ℜ : DatumI.Raw Y, (sY.transformI ℜ).pullback j' = s.transformI (ℜ.pullback j)) ∧
        (IsAlgebraicScheme Y → Y.IsNonsingular → ∀ ℜ : DatumI.Raw Y, ℜ.IsDatum →
          (s.IsPermissibleI (ℜ.pullback j) → sY.IsPermissibleI ℜ) ∧
          (∀ F : Subscheme Y, s.IsPermissibleIClosed (ℜ.pullback j)
              (Subscheme.totalTransform j F) → sY.IsPermissibleIClosed ℜ F) ∧
          (∀ U : Set Y, s.IsPermissibleIOpen (ℜ.pullback j) (j.base ⁻¹' U) →
              sY.IsPermissibleIOpen ℜ U)) := by
  induction s with
  | nil Z =>
    intro Y j _ _ C _ _ _
    exact ⟨Y, nil Y, j, inferInstance, inferInstance, trivial, rfl, by simp, by simp, fun V => rfl,
      fun ℜ => rfl, fun _ _ ℜ _ => ⟨fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩⟩
  | cons B ts rest ih =>
    intro Y j _ _ C hC hCj hs
    obtain ⟨hBred, hBC, hrest⟩ := hs
    have hcl : IsClosed (j.base '' B.pts) := by
      have h1 : closure (j.base '' B.pts) ⊆ C := closure_minimal hBC hC
      have h2 := FlatPreimm.pts_closureLift_inter_range j B
      rw [FlatPreimm.pts_closureLift] at h2
      rw [← h2, Set.inter_eq_left.mpr (h1.trans hCj)]
      exact isClosed_closure
    obtain ⟨BY, tY, j', hfl, hpre, hBY, hpts, htt, hsq, hrange, hexc, hst⟩ :=
      MonoidalTransformation.exists_extend_step j hBred hcl ts
    obtain ⟨Y', sY, j'', hfl', hpre', hav, hlen, hcomp, hrange', hst', htr, hperm⟩ :=
      ih j' (tY.f.base ⁻¹' C) (hC.preimage tY.f.continuous)
        (fun y hy => by rw [hrange]; exact hCj hy)
        ((centersClosedIn_comp rest j' tY.f C).mp (by rw [hsq]; exact hrest))
    refine ⟨Y', cons BY tY sY, j'', hfl', hpre', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun y hy hyC => hyC ?_, ?_⟩
      · rw [hpts] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        exact hBC ⟨z, hz, rfl⟩
      · rw [Set.preimage_compl]; exact hav
    · simp [length_cons, hlen]
    · rw [composite_cons, composite_cons, ← Category.assoc, hcomp, Category.assoc, hsq,
        Category.assoc]
    · rw [hrange', composite_cons, hrange]
      rfl
    · intro V
      rw [strictTransform_cons, strictTransform_cons, hst', hst]
    · intro ℜ
      rw [transformI_cons, transformI_cons, htr,
        DatumI.Raw.pullback_transform_of_lift tY j ts j' hexc hst]
    · intro hYa hYns ℜ hℜ
      have hrng : BY.pts ⊆ Set.range j.base := by
        rw [hpts]; rintro _ ⟨z, -, rfl⟩; exact ⟨z, rfl⟩
      have htr1 : (ℜ.transform tY).pullback j' = (ℜ.pullback j).transform ts :=
        DatumI.Raw.pullback_transform_of_lift tY j ts j' hexc hst ℜ
      -- the datum and ambient hypotheses for the next step, given permissibility of `BY`
      have key : ℜ.IsPermissible BY → IsAlgebraicScheme tY.X' ∧ tY.X'.IsNonsingular ∧
          (ℜ.transform tY).IsDatum := fun hp => by
        have := hYa
        exact ⟨tY.isAlgebraicScheme,
          (tY.isNonsingular_and_isNonsingular_exceptional hYns hp.1.isNonsingular).1,
          (DatumI.Raw.transform_isDatum hYns ℜ hℜ tY hp).1⟩
      refine ⟨fun hs => ?_, fun F hs => ?_, fun U hs => ?_⟩
      · have hp := DatumI.Raw.isPermissible_of_isPermissible_pullback j hℜ hBY htt hrng hs.1
        obtain ⟨h1, h2, h3⟩ := key hp
        refine ⟨hp, (hperm h1 h2 _ h3).1 ?_⟩
        rw [htr1]; exact hs.2
      · have hp := DatumI.Raw.isPermissible_of_isPermissible_pullback j hℜ hBY htt hrng hs.1.1
        obtain ⟨h1, h2, h3⟩ := key hp
        refine ⟨⟨hp, ?_⟩, (hperm h1 h2 _ h3).2.1 (Subscheme.strictTransform tY F) ?_⟩
        · rw [hpts]
          rintro _ ⟨z, hz, rfl⟩
          have := hs.1.2 hz
          rw [DatumI.Raw.pullback_W, FlatPreimm.pts_totalTransform,
            FlatPreimm.pts_totalTransform] at this
          exact this
        · rw [htr1, hst]; exact hs.2
      · have hp := DatumI.Raw.isPermissible_of_isPermissible_pullback j hℜ hBY htt hrng hs.1.1
        obtain ⟨h1, h2, h3⟩ := key hp
        refine ⟨⟨hp, ?_⟩, (hperm h1 h2 _ h3).2.2 (DatumI.Raw.transformOpen tY U) ?_⟩
        · rw [hpts]
          rintro _ ⟨z, hz, rfl⟩
          have := hs.1.2 hz
          rw [DatumI.Raw.pullback_W, FlatPreimm.pts_totalTransform] at this
          exact this
        · rw [htr1]
          have e : j'.base ⁻¹' DatumI.Raw.transformOpen tY U = DatumI.Raw.transformOpen ts
              (j.base ⁻¹' U) := by
            show j'.base ⁻¹' (tY.f.base ⁻¹' U) = ts.f.base ⁻¹' (j.base ⁻¹' U)
            have := congrArg (fun g : ts.X' ⟶ Y => g.base ⁻¹' U) hsq
            simpa [Scheme.Hom.comp_base, Set.preimage_comp] using this
          rw [e]; exact hs.2

end PrepPhase22ext

section PrepPhase22b

open IsLocalRing Classical

/-- `X − F`, the open subscheme on which the datum of step 7 lives (p. 291). -/
def complF : X.Opens :=
  ⟨(P.ℜ.prepF P.E₁ P.U).ptsᶜ, (P.ℜ.prepF P.E₁ P.U).support.isClosed.isOpen_compl⟩

/-- `W_* ∩ E_1 ⊆ F` gives (5)* for `P` itself (p. 291: (3)** and (4) hold, `W_* ∩ E_1 = F ⊆ Ū`). -/
theorem cond₅_of_subset {Ubar : Set X} (h₂ : P.Cond₂ Ubar)
    (hd : (P.ℜ.prepWStar P.E₁).pts ∩ P.E₁.pts ⊆ (P.ℜ.prepF P.E₁ P.U).pts) : P.Cond₅ Ubar := by
  refine ⟨Set.Subset.antisymm ?_ ?_, h₂.2.2.1⟩
  · intro x hx; exact hd ⟨hx.2, hx.1⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := Subscheme.mem_pts_inter_iff.mp (P.ℜ.pts_prepF_subset P.E₁ P.U hx)
    exact ⟨h2, h1⟩

/-- Dimensions of step 7 (p. 291, "with `N* = dim (X − F)` and `n* = dim (W_* − F)`"): if
`(W_* ∩ E_1) − F ≠ ∅` and `n < N`, then `X − F` is a non-singular irreducible algebraic scheme of
dimension `N* ≤ N`, and `W_* − F` is non-empty of dimension `n* ≤ n` with `n* < N*`.

Truth check: `n* < N*` needs `n < N` (for `W = X` and `E_1` missing `U` it fails), which is the
paper's
`N > n` (p. 288); `N*` can be smaller than `N` for a local `X`. -/
theorem exists_dims_complF {N n : ℕ} (hX : IsAmbient X N) (hnN : n < N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞))
    (hd : ¬ (P.ℜ.prepWStar P.E₁).pts ∩ P.E₁.pts ⊆ (P.ℜ.prepF P.E₁ P.U).pts) :
    ∃ (N' n' : ℕ), n' < N' ∧ N' ≤ N ∧ n' ≤ n ∧ IsAmbient P.complF.toScheme N' ∧
      (Subscheme.totalTransform P.complF.ι (P.ℜ.prepWStar P.E₁)).dim = (n' : WithBot ℕ∞) := by
  classical
  have := hX.1
  obtain ⟨hXa, hXns, hXirr, hXdim⟩ := hX
  obtain ⟨u, ⟨huW, huE⟩, huF⟩ := Set.not_subset.mp hd
  have hne : Nonempty P.complF.toScheme := ⟨⟨u, huF⟩⟩
  obtain ⟨N', hN'N, hamb⟩ := exists_isAmbient_of_isOpenImmersion ⟨hXa, hXns, hXirr, hXdim⟩
    P.complF.ι
  set D := Subscheme.totalTransform P.complF.ι (P.ℜ.prepWStar P.E₁) with hDdef
  have hDpts : D.pts = P.complF.ι.base ⁻¹' (P.ℜ.prepWStar P.E₁).pts :=
    FlatPreimm.pts_totalTransform _ _
  have hDne : D.pts.Nonempty := ⟨⟨u, huF⟩, by rw [hDpts]; exact huW⟩
  have hWsub : (P.ℜ.prepWStar P.E₁).pts ⊆ P.ℜ.W.pts := P.ℜ.pts_prepWStar_subset P.E₁
  -- `W_*` is not everything: otherwise `dim W = dim X = N > n`
  have hDne' : D.pts ≠ Set.univ := by
    intro hDu
    have hOW : (P.complF : Set X) ⊆ (P.ℜ.prepWStar P.E₁).pts := by
      intro x hx
      have : (⟨x, hx⟩ : P.complF.toScheme) ∈ D.pts := by rw [hDu]; trivial
      rw [hDpts] at this
      exact this
    have hdense : Dense (P.complF : Set X) := IsOpen.dense P.complF.isOpen ⟨u, huF⟩
    have hWtop : (P.ℜ.prepWStar P.E₁).pts = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← hdense.closure_eq]
      exact closure_minimal hOW (P.ℜ.prepWStar P.E₁).support.isClosed
    have hWuniv : P.ℜ.W.pts = Set.univ := Set.eq_univ_of_univ_subset (hWtop ▸ hWsub)
    have hdimW : P.ℜ.n = (N : WithBot ℕ∞) := by
      show P.ℜ.W.dim = _
      rw [Subscheme.dim_eq_topologicalKrullDim, hWuniv, LocSucc.topologicalKrullDim_univ,
        ← Scheme.dim_eq_topologicalKrullDim, hXdim]
    rw [hdimW] at hP
    exact absurd (by exact_mod_cast hP : N ≤ n) (by omega)
  obtain ⟨hOa, hOns, hOirr, hOdim⟩ := hamb
  have hDne1 : D.dim ≠ ⊥ := Subscheme.dim_ne_bot hDne
  have hlt : D.dim + 1 ≤ (N' : WithBot ℕ∞) := by
    rw [← hOdim]
    exact LocSucc.dim_add_one_le_of_pts_ne_univ hDne' hDne
  obtain ⟨m, hm, hmN'⟩ := LocSucc.exists_nat_of_add_one_le hDne1 hlt
  refine ⟨N', m, hmN', hN'N, ?_, ⟨hOa, hOns, hOirr, hOdim⟩, hm⟩
  -- `m = dim D ≤ dim W_* ≤ dim W ≤ n`
  have h1 : D.dim ≤ (P.ℜ.prepWStar P.E₁).dim := LocSucc.dim_totalTransform_le P.complF.ι _
  have h2 : (P.ℜ.prepWStar P.E₁).dim ≤ P.ℜ.W.dim := by
    rw [Subscheme.dim_eq_topologicalKrullDim, Subscheme.dim_eq_topologicalKrullDim]
    exact (Topology.IsEmbedding.inclusion hWsub).isInducing.topologicalKrullDim_le
  have h3 : (m : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
    rw [← hm]; exact h1.trans (h2.trans hP)
  exact_mod_cast h3

end PrepPhase22b

/-- The closed subset `(W_* ∩ E_1) − F = W_* ∩ E_1 ∩ (X − V)` of `X` containing the centers
(`Ū = V ∩ W`; by (3)** a point of `W_* ∩ E_1` lies in `F` iff it lies in `V`). -/
def centerSet (V : Set X) : Set X := (P.ℜ.prepWStar P.E₁).pts ∩ P.E₁.pts ∩ Vᶜ

/-- Step 7, "canonically induced by a permissible monoidal transformation for `(ℜ, U)`" (p. 291): a
succession `s_X` of `X` permissible for `(ℜ^{N*,n*}_I, E_1)` whose centers lie over the closed set
`(W_* ∩ E_1) − F` is permissible for `(ℜ, U)`.

Proof.  Induction on `s_X`
(`MonoidalSuccession.isPermissibleIOpen_of_isPermissibleIClosed_starDatum`),
with `ℜ.E = ⋃_{i∈J} E_i ∪ E_1`: a center `B` permissible for `ℜ₁ = (⋃_{i≥2} E_i; V, W; W_*)` with
closed
restriction `E_1` is permissible for `ℜ` (`isPermissible_of_isPermissibleClosed_starDatum`: the list
of the
`V`'s of `ℜ₁` is that of `ℜ` followed by `W`, and the normal crossings of the whole boundary with
`B ⊆ E_1`
follow from those of the tail by Lemma 3, `hasOnlyNormalCrossingsWithAt_union_of_stalkIdeal_le`); it
misses
`U'` because it lies over `(W_* ∩ E_1) − F`, disjoint from `Ū ⊇ U`; the data are carried to the next
stage
by `exists_presentation_transform`, `transform_tail_E` and `starDatum_transform`.

Deviation from the paper (gap filled): "canonically induced by a permissible monoidal transformation
for
`(ℜ, U)`" (p. 291) is tacit; Lemma 3 is used in a presentation-free form for `T ∪ E_1`. -/
theorem isPermissibleIOpen_of_extension [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {N : ℕ} (hX : IsAmbient X N) (_h : P.Stage₄) {V : Set X}
    {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (hUbar : Ubar = V ∩ P.ℜ.W.pts)
    {Y'' : Scheme.{u}} (sX : MonoidalSuccession X Y'')
    (hperm : sX.IsPermissibleIClosed P.datumStar P.E₁)
    (hav : sX.CentersAvoid (P.centerSet V)ᶜ) : sX.IsPermissibleIOpen P.ℜ P.U := by
  classical
  have := hX.1
  have hXns := hX.2.1
  have hW₁ : (P.ℜ.prepWStar P.E₁).IsContainedIn P.ℜ.W :=
    Subscheme.isContainedIn_of_pts_subset (Subscheme.ofClosed_isReduced _)
      (P.ℜ.pts_prepWStar_subset P.E₁)
  have hUR : P.U ⊆ (P.centerSet V)ᶜ := by
    intro y hy hyC
    have : y ∈ Ubar := h₂.2.1 hy
    rw [hUbar] at this
    exact hyC.2 this.1
  exact MonoidalSuccession.isPermissibleIOpen_of_isPermissibleIClosed_starDatum sX hXns P.hα P.E
    P.hE {i | P.E i ≠ P.E ⟨0, P.hα⟩}
    (fun i => by by_cases hi : P.E i = P.E ⟨0, P.hα⟩ <;> simp [hi]) P.hℜ P.hEunion hW₁ P.U _ hUR
    (P.isDatum_datumStar hXns) hperm hav

/-- Over the part of `Y` where a succession is an isomorphism (a lift `j₁` of an open immersion
`j₀`), a
point lies on the strict transform of `V` iff its image lies on `V`. -/
theorem _root_.Hironaka.MonoidalSuccession.mem_pts_strictTransform_iff_of_lift
    {X Y Z : Scheme.{u}} (s : MonoidalSuccession X Y) (j₀ : Z ⟶ X) (j₁ : Z ⟶ Y)
    [Flat j₁] [IsPreimmersion j₁]
    (hst : ∀ V, Subscheme.totalTransform j₁ (s.strictTransform V) = Subscheme.totalTransform j₀ V)
    [Flat j₀] [IsPreimmersion j₀] (V : Subscheme X) (z : Z) :
    j₁.base z ∈ (s.strictTransform V).pts ↔ j₀.base z ∈ V.pts := by
  have h1 := FlatPreimm.pts_totalTransform j₁ (s.strictTransform V)
  have h2 := FlatPreimm.pts_totalTransform j₀ V
  rw [hst V] at h1
  have := congrArg (fun S : Set Z => z ∈ S) (h2.symm.trans h1)
  exact this.symm.to_iff

/-- Step 7, "this permissible monoidal transformation for `(ℜ, U)` does not affect the properties
(1), (2),
(3)** and (4)", and the result (5) (p. 291): for the transform `Q` of `P` under a succession `s_X`
as in
`isPermissibleIOpen_of_extension`, with `W_*' ∩ E_1' ⊆ f⁻¹(F)`, the conditions (1), (2), (4), (5)*
hold.

Proof.  The centers lie over the closed set `C = (W_* ∩ E_1) − F`, so `f` is an isomorphism over the
open set
`X − C ⊇ Ū ∪ F ∪ U`: `exists_lift_of_centersAvoid` gives a lift `j₁` of `X − C → X` through `f`
which
pulls the transform of `ℜ` and the strict transforms back to the plain pull-backs.  (1): `F'` is
simple and
`E'` has normal crossings with it at the points of `F'`, which lie over `F ⊆ X − C`
(`cond₁_transform_of_pointwise`).  (2): `cond₂_transform_of_tail`, with `Ū' =` the set where the
tail is
resolved.  (5)*: a point of `E_1' ∩ W_*'` lies on the strict transform of `W_*` (a point of
`W' − E_1'` is
a limit of points over `X − C`, where it lies over `W − E_1`), hence over `F` by the hypothesis,
hence on
`F'`.  (3)** follows from (5)* and the density of `Ū' ∩ W_*'` in `W_*'`, and (4) from (1), (2),
(3)** as on
p. 291 (`cond₄_of_cond₃SS`).

Deviation from the paper (gap filled): "this does not affect the properties (1), (2), (3)** and (4)"
(p. 291) is proved as above; (4) and (3)** for the transform are obtained from (1), (2), (5)*, not
transported. -/
theorem stage₅_of_extension [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} (hX : IsAmbient X N) (hP : P.ℜ.n ≤ (n : WithBot ℕ∞))
    (h : P.Stage₄) {V : Set X} (hV : IsOpen V) {Ubar : Set X} (h₂ : P.Cond₂ Ubar)
    (hUbar : Ubar = V ∩ P.ℜ.W.pts) {Y'' : Scheme.{u}} (sX : MonoidalSuccession X Y'')
    (_hperm : sX.IsPermissibleIClosed P.datumStar P.E₁)
    (hav : sX.CentersAvoid (P.centerSet V)ᶜ)
    (hempty : (sX.transformI P.datumStar).W.pts ∩ (sX.strictTransform P.E₁).pts ⊆
      sX.composite.base ⁻¹' (P.ℜ.prepF P.E₁ P.U).pts)
    (hs : sX.IsPermissibleIOpen P.ℜ P.U) {Q : PrepSetting Y''} (hQ : P.IsTransform sX Q)
    (hY : IsAmbient Y'' N) (J' : Set (Fin Q.α))
    (hJ3 : (sX.transformI ({ P.ℜ with E := prepERest P.E ⟨0, P.hα⟩ } : DatumI.Raw X)).E =
      Subscheme.unionFam (fun j : J' => Q.E j))
    (hJ' : ∀ j, Q.E j ≠ Q.E ⟨0, Q.hα⟩ → j ∈ J') :
    Q.Stage₅ := by
  classical
  have := hX.1
  have := hY.1
  have hXns := hX.2.1
  have hYns := hY.2.1
  obtain ⟨hC1, -⟩ := h
  set F := P.ℜ.prepF P.E₁ P.U with hFdef
  set f := sX.composite with hfdef
  set Cs := P.centerSet V with hCsdef
  have hCsc : IsClosed Cs :=
    ((P.ℜ.prepWStar P.E₁).support.isClosed.inter P.E₁.support.isClosed).inter hV.isClosed_compl
  have hVO : V ⊆ Csᶜ := fun x hx hxC => hxC.2 hx
  have hFV : F.pts ⊆ V := fun x hx => by
    have := h₂.2.2.1 hx
    rw [hUbar] at this; exact this.1
  let O' : X.Opens := ⟨Csᶜ, hCsc.isOpen_compl⟩
  have hrange₀ : Set.range O'.ι.base = Csᶜ := Scheme.Opens.range_ι O'
  obtain ⟨j₁, hfl, hpre, hcomp, hrange₁, hst, hℜ⟩ :=
    sX.exists_lift_of_centersAvoid O'.ι (by rw [hrange₀]; exact hav)
  have := hfl
  have := hpre
  have hF_O : ∀ x ∈ F.pts, x ∈ Csᶜ := fun x hx => hVO (hFV hx)
  have hfj : ∀ z, f.base (j₁.base z) = O'.ι.base z := fun z => by
    have := congrArg (fun g => g.base z) hcomp
    simpa using this
  have hrange_iff : ∀ y, y ∈ Set.range j₁.base ↔ f.base y ∈ Csᶜ := fun y => by
    rw [hrange₁, Set.mem_preimage, hrange₀]
  -- over `X − C` the strict transform of `A` is the preimage of `A`
  have htr' : ∀ (A : Subscheme X) (y : Y''), f.base y ∈ Csᶜ →
      (y ∈ (sX.strictTransform A).pts ↔ f.base y ∈ A.pts) := by
    intro A y hy
    obtain ⟨z, rfl⟩ := (hrange_iff y).mpr hy
    rw [MonoidalSuccession.mem_pts_strictTransform_iff_of_lift sX O'.ι j₁ hst, hfj]
  -- (1)
  have hres' : ∀ y ∈ (sX.strictTransform F).pts, (sX.strictTransform F).IsSimpleAt y ∧
      (sX.transformI P.ℜ).E.HasOnlyNormalCrossingsWithAt (sX.strictTransform F) y := by
    intro y hy
    have hfy : f.base y ∈ F.pts := MonoidalSuccession.pts_strictTransform_subset sX F hy
    obtain ⟨z, rfl⟩ := (hrange_iff y).mpr (hF_O _ hfy)
    have hjz : O'.ι.base z ∈ F.pts := by rw [← hfj]; exact hfy
    have hNC : (sX.transformI P.ℜ).E.HasOnlyNormalCrossingsWithAt (sX.strictTransform F)
        (j₁.base z) := by
      rw [← FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff j₁]
      have e1 : Subscheme.totalTransform j₁ (sX.transformI P.ℜ).E =
          Subscheme.totalTransform O'.ι P.ℜ.E := congrArg DatumI.Raw.E (hℜ P.ℜ)
      rw [e1, hst F]
      exact (FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff O'.ι _ _ z).mpr
        (hC1.2.2 _ hjz)
    exact ⟨Subscheme.IsSimpleAt.of_hasOnlyNormalCrossingsWithAt (hYns _) hy hNC, hNC⟩
  have hC1Q : Q.Cond₁ := P.cond₁_transform_of_pointwise hXns hs hQ hres'
  -- (2)
  have hC2Q := P.cond₂_transform_of_tail hX hP hY hs hQ h₂ J' hJ3 hJ'
  -- `W'_*` lies on the strict transform of `W_*`
  have hNoeX : NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  have hNoeY : NoetherianSpace Y'' := IsAlgebraicScheme.noetherianSpace Y''
  have hWpts : Q.ℜ.W.pts = (sX.strictTransform P.ℜ.W).pts := by
    rw [hQ.1, MonoidalSuccession.transformI_W]
  have hE1pts : Q.E₁.pts = (sX.strictTransform P.E₁).pts := by rw [hQ.2.2]
  have hW'cl : IsClosed (sX.strictTransform P.ℜ.W).pts :=
    (sX.strictTransform P.ℜ.W).support.isClosed
  have hE'cl : IsClosed (sX.strictTransform P.E₁).pts := (sX.strictTransform P.E₁).support.isClosed
  have hWstar_cl : IsClosed (sX.strictTransform (P.ℜ.prepWStar P.E₁)).pts :=
    (sX.strictTransform (P.ℜ.prepWStar P.E₁)).support.isClosed
  have hWdense : P.ℜ.W.pts ⊆ closure (P.ℜ.W.pts ∩ Csᶜ) := by
    refine P.hU.2.1.trans (closure_mono fun x hx => ?_)
    have : x ∈ Ubar := h₂.2.1 hx
    rw [hUbar] at this
    exact ⟨this.2, hVO this.1⟩
  have hW'dense := sX.pts_strictTransform_subset_closure_inter P.ℜ.W Csᶜ hWdense
  have hdiff : (sX.strictTransform P.ℜ.W).pts \ (sX.strictTransform P.E₁).pts ⊆
      (sX.strictTransform (P.ℜ.prepWStar P.E₁)).pts := by
    intro w ⟨hwW, hwE⟩
    -- `w` is a limit of points over `X − C` of `W' − E_1'`
    have hw : w ∈ closure (((sX.strictTransform P.ℜ.W).pts ∩ f.base ⁻¹' Csᶜ) \
        (sX.strictTransform P.E₁).pts) := by
      rw [mem_closure_iff]
      intro o ho hwo
      have := mem_closure_iff.mp (hW'dense hwW) (o ∩ (sX.strictTransform P.E₁).ptsᶜ)
        (ho.inter hE'cl.isOpen_compl) ⟨hwo, hwE⟩
      obtain ⟨a, ⟨hao, haE⟩, haW⟩ := this
      exact ⟨a, hao, haW, haE⟩
    refine closure_minimal ?_ hWstar_cl hw
    rintro y ⟨⟨hyW, hyC⟩, hyE⟩
    have hfyW : f.base y ∈ P.ℜ.W.pts := MonoidalSuccession.pts_strictTransform_subset sX _ hyW
    have hfyE : f.base y ∉ P.E₁.pts := fun h => hyE ((htr' P.E₁ y hyC).mpr h)
    have hcl := prepWStarT_eq_closure_diff (W := P.ℜ.W.pts) (E := P.E₁.pts)
      P.ℜ.W.support.isClosed P.E₁.support.isClosed
    rw [htr' _ y hyC, DatumI.Raw.pts_prepWStar_eq, hcl]
    exact subset_closure ⟨hfyW, hfyE⟩
  have hW'star : (Q.ℜ.prepWStar Q.E₁).pts ⊆ (sX.strictTransform (P.ℜ.prepWStar P.E₁)).pts := by
    rw [DatumI.Raw.pts_prepWStar_eq, hWpts, hE1pts,
      prepWStarT_eq_closure_diff hW'cl hE'cl]
    exact closure_minimal hdiff hWstar_cl
  have hFQ := P.prepF_transform_pts_eq hXns hs hQ
  have key : ∀ Ubar' : Set Y'', Q.Cond₂ Ubar' → Q.Stage₅ := by
    intro Ubar' hC2Q
    -- (5)*
    have hC5 : Q.Cond₅ Ubar' := by
      refine ⟨Set.Subset.antisymm ?_ ?_, hC2Q.2.2.1⟩
      · rintro y ⟨hyE, hyW⟩
        have hyWs := hW'star hyW
        have hyE' : y ∈ (sX.strictTransform P.E₁).pts := hE1pts ▸ hyE
        have hyW0 : y ∈ (sX.transformI P.datumStar).W.pts := by
          rw [MonoidalSuccession.transformI_W]; exact hyWs
        have hfyF : f.base y ∈ F.pts := hempty ⟨hyW0, hyE'⟩
        rw [hFQ]
        exact (htr' F y (hF_O _ hfyF)).mpr hfyF
      · intro y hy
        obtain ⟨h1, h2⟩ := Subscheme.mem_pts_inter_iff.mp (Q.ℜ.pts_prepF_subset Q.E₁ Q.U hy)
        exact ⟨h2, h1⟩
    -- (3)**
    have hC3 : Q.Cond₃SS Ubar' := by
      refine ⟨Set.Subset.antisymm ?_ ?_, ?_⟩
      · rintro y ⟨⟨-, hyW⟩, hyE⟩
        exact hC5.1.subset ⟨hyE, hyW⟩
      · intro y hy
        have hyD := hC5.1.symm.subset hy
        exact ⟨⟨hC5.2 hy, hyD.2⟩, hyD.1⟩
      · obtain ⟨U₀, hU₀, hUeq⟩ := hC2Q.1
        have hdense : Q.ℜ.W.pts ⊆ closure (U₀ ∩ Q.ℜ.W.pts) := by
          refine Q.hU.2.1.trans (closure_mono fun x hx => ?_)
          have := hC2Q.2.1 hx
          rw [hUeq] at this
          exact this
        have hd := Q.ℜ.pts_prepWStar_subset_closure_inter Q.E₁ hU₀ hdense
        have hsub : Ubar' ∩ (Q.ℜ.prepWStar Q.E₁).pts = U₀ ∩ (Q.ℜ.prepWStar Q.E₁).pts := by
          rw [hUeq]
          ext x
          exact ⟨fun hx => ⟨hx.1.1, hx.2⟩,
            fun hx => ⟨⟨hx.1, Q.ℜ.pts_prepWStar_subset Q.E₁ hx.2⟩, hx.2⟩⟩
        rw [hsub]; exact hd
    exact ⟨hC1Q, Ubar', hC2Q, Q.cond₄_of_cond₃SS hY hC1Q hC2Q hC3, hC5⟩
  exact key _ hC2Q

/-- Step 7, after the extension (p. 291): a succession `s_X` of `X`, permissible for
`(ℜ^{N*,n*}_I, E_1)`, whose centers lie over the closed set `(W_* ∩ E_1) − F`, such that
`W_*' ∩ E_1' ⊆ f⁻¹(F)`, is permissible for `(ℜ, U)` (`isPermissibleIOpen_of_extension`) and its
transform
satisfies (1), (2), (4), (5)* (`stage₅_of_extension`); the presentation of the transform and the
ambient
data are as in the earlier steps. -/
theorem stepTo_stage₅_of_extension [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} (hX : IsAmbient X N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) (h : P.Stage₄) {V : Set X}
    (hV : IsOpen V) {Ubar : Set X} (h₂ : P.Cond₂ Ubar) (hUbar : Ubar = V ∩ P.ℜ.W.pts)
    {Y'' : Scheme.{u}} (sX : MonoidalSuccession X Y'')
    (hperm : sX.IsPermissibleIClosed P.datumStar P.E₁)
    (hav : sX.CentersAvoid (P.centerSet V)ᶜ)
    (hempty : (sX.transformI P.datumStar).W.pts ∩ (sX.strictTransform P.E₁).pts ⊆
      sX.composite.base ⁻¹' (P.ℜ.prepF P.E₁ P.U).pts) :
    P.StepTo N n (fun _ Q => Q.Stage₅) := by
  classical
  have := hX.1
  have hs : sX.IsPermissibleIOpen P.ℜ P.U :=
    P.isPermissibleIOpen_of_extension hX h h₂ hUbar sX hperm hav
  obtain ⟨⟨hY, hdat, hdim⟩, hopen⟩ := IsGoodDatumI.succession_open sX ⟨hX, P.hℜ, hP⟩ P.hU hs
  obtain ⟨α', hα', E', hE', hEq', hcs, J', hJ1, hJ2, hJ3, -, -, -, -⟩ :=
    sX.exists_presentation_transformI_tail hX.1 hX.2.1 P.E P.hE P.ℜ P.hℜ P.hEunion
      hs.isPermissibleI {i | P.E i ≠ P.E ⟨0, P.hα⟩}
  have := hY.1
  let Q : PrepSetting Y'' := ⟨α', P.hα.trans_le hα', E', hE', sX.transformI P.ℜ, hdat, hEq',
    sX.transformOpen P.U, hopen⟩
  have hQ : P.IsTransform sX Q := ⟨rfl, rfl, hcs ⟨0, P.hα⟩⟩
  have hJ' : ∀ j : Fin α', Q.E j ≠ Q.E ⟨0, Q.hα⟩ → j ∈ J' := by
    intro j hj
    by_cases hjα : P.α ≤ j.val
    · exact hJ2 j hjα
    · have hlt : j.val < P.α := by omega
      have hji : j = Fin.castLE hα' ⟨j.val, hlt⟩ := Fin.ext rfl
      rw [hji, hJ1]
      intro hi
      apply hj
      have hi' : P.E ⟨j.val, hlt⟩ = P.E ⟨0, P.hα⟩ := by simpa using hi
      show E' j = E' ⟨0, _⟩
      rw [hji]
      have h0 : (⟨0, P.hα.trans_le hα'⟩ : Fin α') = Fin.castLE hα' ⟨0, P.hα⟩ := Fin.ext rfl
      rw [h0, hcs, hcs, hi']
  exact ⟨Y'', sX, Q, hs, hQ, hY, hdim,
    P.stage₅_of_extension hX hP h hV h₂ hUbar sX hperm hav hempty hs hQ hY J' hJ3 hJ'⟩

/-- Step 7, after Theorem I₁ (p. 291): a succession `s` of `X − F`, permissible for
`(ℜ^{N*,n*}_I, E_1 − F)` with `(W_*' ∩ (E_1 − F)') = ∅`, is "canonically induced" by a succession of
`X`
permissible for `(ℜ^{N*,n*}_I, E_1)` (`MonoidalSuccession.exists_extension_centersAvoid`: the
centers are
the closures of the images, which lie in the closed set `(W_* ∩ E_1) − F`); then
`stepTo_stage₅_of_extension` applies.

Deviation from the paper (gap filled): "is canonically induced by a permissible monoidal
transformation for
`(ℜ, U)`" (p. 291) is proved by `exists_extension_centersAvoid`, the closedness of the centers in
`X`
(`centersClosedIn_of_isPermissibleIClosed`, which uses (3)**: `(W_* ∩ E_1) − F = (W_* ∩ E_1) − V`),
and
the emptiness `W_*' ∩ E_1' ⊆ f⁻¹(F)` is obtained from that on `X − F` since `f` is an isomorphism
over `F`. -/
theorem stepTo_stage₅_of_succession [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} (hX : IsAmbient X N) (_hnN : n < N)
    (hP : P.ℜ.n ≤ (n : WithBot ℕ∞)) (h : P.Stage₄)
    (_hd : ¬ (P.ℜ.prepWStar P.E₁).pts ∩ P.E₁.pts ⊆ (P.ℜ.prepF P.E₁ P.U).pts)
    {Y' : Scheme.{u}} (s : MonoidalSuccession P.complF.toScheme Y')
    (hperm : s.IsPermissibleIClosed (P.datumStar.pullback P.complF.ι)
      (Subscheme.totalTransform P.complF.ι P.E₁))
    (hempty : (s.transformI (P.datumStar.pullback P.complF.ι)).principal.pts ∩
      (s.strictTransform (Subscheme.totalTransform P.complF.ι P.E₁)).pts = ∅) :
    P.StepTo N n (fun _ Q => Q.Stage₅) := by
  classical
  have := hX.1
  have hXns := hX.2.1
  obtain ⟨hC1, Ubar, h₂, h₃, h₄⟩ := id h
  obtain ⟨V, hVo, hUbar⟩ := h₂.1
  set j := P.complF.ι with hjdef
  have hrj : Set.range j.base = (P.ℜ.prepF P.E₁ P.U).ptsᶜ := Scheme.Opens.range_ι P.complF
  -- membership of `W_* ∩ E_1` in `F` is membership in `V` (by (3)**)
  have hFV : ∀ x ∈ (P.ℜ.prepWStar P.E₁).pts ∩ P.E₁.pts,
      x ∈ (P.ℜ.prepF P.E₁ P.U).pts ↔ x ∈ V := by
    intro x hx
    constructor
    · intro hxF
      have : x ∈ Ubar := h₂.2.2.1 hxF
      rw [hUbar] at this; exact this.1
    · intro hxV
      have hxW : x ∈ P.ℜ.W.pts := P.ℜ.pts_prepWStar_subset P.E₁ hx.1
      have : x ∈ Ubar := by rw [hUbar]; exact ⟨hxV, hxW⟩
      rw [← h₃.1]; exact ⟨⟨this, hx.1⟩, hx.2⟩
  have hCclosed : IsClosed (P.centerSet V) :=
    ((P.ℜ.prepWStar P.E₁).support.isClosed.inter P.E₁.support.isClosed).inter hVo.isClosed_compl
  have hCrange : P.centerSet V ⊆ Set.range j.base := by
    intro x hx
    rw [hrj]
    intro hxF
    exact hx.2 ((hFV x ⟨hx.1.1, hx.1.2⟩).mp hxF)
  have hcenters : s.CentersClosedIn j (P.centerSet V) := by
    refine MonoidalSuccession.centersClosedIn_of_isPermissibleIClosed hperm j _ ?_
    rintro _ ⟨z, ⟨hzW, hzF⟩, rfl⟩
    rw [DatumI.Raw.pullback_W, FlatPreimm.pts_totalTransform] at hzW
    rw [FlatPreimm.pts_totalTransform] at hzF
    refine ⟨⟨hzW, hzF⟩, fun hxV => ?_⟩
    have hz : j.base z ∈ Set.range j.base := Set.mem_range_self z
    rw [hrj] at hz
    exact hz ((hFV _ ⟨hzW, hzF⟩).mpr hxV)
  obtain ⟨Y'', sX, j', hfl, hpre, hav, -, -, hrange, hst, htr, hpermX⟩ :=
    MonoidalSuccession.exists_extension_centersAvoid s j _ hCclosed hCrange hcenters
  obtain ⟨-, hclosed, -⟩ := hpermX hX.1 hXns P.datumStar (P.isDatum_datumStar hXns)
  have hpermX1 : sX.IsPermissibleIClosed P.datumStar P.E₁ := hclosed P.E₁ hperm
  refine P.stepTo_stage₅_of_extension hX hP h hVo h₂ hUbar sX hpermX1 hav ?_
  -- `W_*' ∩ E_1' ⊆ f⁻¹(F)`: over `X − F` this is the hypothesis on `s`
  intro y ⟨hyW, hyE⟩
  by_contra hyF
  have hyr : y ∈ Set.range j'.base := by
    rw [hrange, Set.mem_preimage, hrj]; exact hyF
  obtain ⟨z, rfl⟩ := hyr
  have h1 : z ∈ (s.transformI (P.datumStar.pullback j)).principal.pts := by
    rw [show (s.transformI (P.datumStar.pullback j)).principal =
        ((sX.transformI P.datumStar).pullback j').W from
        (congrArg (fun r => r.W) (htr P.datumStar)).symm, DatumI.Raw.pullback_W,
      FlatPreimm.pts_totalTransform]
    exact hyW
  have h2 : z ∈ (s.strictTransform (Subscheme.totalTransform j P.E₁)).pts := by
    rw [← hst P.E₁, FlatPreimm.pts_totalTransform]; exact hyE
  exact (Set.eq_empty_iff_forall_notMem.mp hempty) z ⟨h1, h2⟩

/-- Step 7 (p. 291): "Now, let us consider the following resolution datum on the non-singular
irreducible algebraic scheme `X − F`, with `N* = dim (X − F)` and `n* = dim (W_* − F)`:
`ℜ^{N*,n*}_I = (⋃_{i≥2}(E_i − F); V_1 − F, …, V_β − F, W − F; W_* − F)` with closed restriction
`E_1 − F`.  Note that `(E_1 − F) ∩ (W_* − F)` is entirely contained in `W_* − Ū` while `F` is
entirely contained in `Ū`.  Therefore the center of any permissible monoidal transformation for
`(ℜ^{N*,n*}_I, E_1 − F)` is contained in `W_* − Ū` and closed not only in `W_* − F` but also in
`W_*`.  It follows that any permissible monoidal transformation for `(ℜ^{N*,n*}_I, E_1 − F)` is
canonically induced by a permissible monoidal transformation for `(ℜ, U)`, and that this does not
affect the properties (1), (2), (3)** and (4).  Thus, by Theorem I₁^{N*,n*}, we may assume that
(5) `E_1 − F` and `W_* − F` have empty intersection".

Status: proved, modulo the cited leaves only.  The application of Theorem I₁^{N*,n*}
(`exists_dims_complF`, `datumStar`, `isDatum_datumStar`, `isClosedRestriction_datumStar_E₁`,
`DatumI.Raw.isClosedRestriction_pullback_of_isOpenImmersion`), the extension of the succession to
`X`
(`stepTo_stage₅_of_succession`, `MonoidalSuccession.exists_extension_centersAvoid`), its
permissibility
for `(ℜ, U)` (`isPermissibleIOpen_of_extension`) and the properties of the transform
(`stage₅_of_extension`) are all proved; the case `W_* ∩ E_1 ⊆ F` is trivial (`cond₅_of_subset`).

Deviation from the paper (gap filled; hypothesis made explicit): the hypothesis `n < N` of
Proposition 5 (p. 288, "where `N > n`") is added; without it `n* < N*` can fail (for `W = X` and
`E_1`
missing `U`).  The verification that `N* ≤ N`, `n* < N*`, `n* ≤ n` (needed to use the induction
hypothesis `hI₁`), that `X − F` is a non-singular irreducible algebraic scheme, that the displayed
tuple
is a datum with closed restriction, and the canonical lifting of the succession to `X` are tacit in
the
paper.  The case `(W_* ∩ E_1) − F = ∅` (then (5) holds with the empty succession) is not
distinguished
in the paper. -/
theorem stepTo_stage₅ [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ} (hX : IsAmbient X N) (hnN : n < N) (hP : P.ℜ.n ≤ (n : WithBot ℕ∞))
    (hI₁ : ∀ N' n' : ℕ, n' < N' → N' ≤ N → n' ≤ n → FundamentalTheorem.I₁.{u} N' n')
    (h : P.Stage₄) : P.StepTo N n (fun _ Q => Q.Stage₅) := by
  classical
  have := hX.1
  by_cases hd : (P.ℜ.prepWStar P.E₁).pts ∩ P.E₁.pts ⊆ (P.ℜ.prepF P.E₁ P.U).pts
  · obtain ⟨hC1, Ubar, h₂, h₃, h₄⟩ := h
    exact ⟨X, MonoidalSuccession.nil X, P, trivial, ⟨rfl, rfl, rfl⟩, hX, hP, hC1, Ubar, h₂, h₄,
      P.cond₅_of_subset h₂ hd⟩
  · obtain ⟨N', n', hlt, hN'N, hn'n, hamb, hdimD⟩ := P.exists_dims_complF hX hnN hP hd
    have hI := hI₁ N' n' hlt hN'N hn'n
    let ℜ' : DatumI P.complF.toScheme :=
      ⟨P.datumStar.pullback P.complF.ι,
        DatumI.Raw.isDatum_pullback _ (P.isDatum_datumStar hX.2.1)⟩
    have hcr : (ℜ' : DatumI.Raw P.complF.toScheme).IsClosedRestriction
        (Subscheme.totalTransform P.complF.ι P.E₁) :=
      DatumI.Raw.isClosedRestriction_pullback_of_isOpenImmersion _
        P.isClosedRestriction_datumStar_E₁
    have hn : (ℜ' : DatumI.Raw P.complF.toScheme).n = (n' : WithBot ℕ∞) := hdimD
    obtain ⟨Y', s, hperm, hempty⟩ := hI P.complF.toScheme hamb ℜ' _ hcr hn
    exact P.stepTo_stage₅_of_succession hX hnN hP h hd s hperm hempty

/-- Step 8 (p. 291): "By (1), (2) and (4), `ℜ` is resolved at every point of `Ū` (`Ū` is an open
subset of `W` containing `U`)": at the points of `Ū ∩ W_*` this is (4); at the other points of `Ū`
only components of `W` contained in `E_1` pass.

Deviation from the paper (gap filled; no argument is printed at the points of `Ū − W_*`, where (4) does
not apply, so there is no printed route to follow): at a point `x ∈ Ū − W_*` the component `C` of `W` through
`x` (unique, `W_x` being prime as `x` is a simple point) is contained in `E_1`, hence
`E_{1,x} ⊆ W_x`, and `(⋃_{i≥2} E_i)` has only normal crossings with `W` at `x` by (2); Lemma 3
in the form `Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_of_stalkIdeal_le` (a regular system of
parameters adapted to the `E_i` and to `W_x`, by the flag lemma with the maximal ideal in the place
of `B_x`) gives that `⋃_{i≥1} E_i` has only normal crossings with `W` at `x`.  Condition (1) is
not needed. -/
theorem resolvedAt_of_cond₂_cond₄ (hX : X.IsNonsingular) {Ubar : Set X} (h₂ : P.Cond₂ Ubar)
    (h₄ : P.Cond₄ Ubar) : ∀ x ∈ Ubar, P.ℜ.ResolvedAt x := by
  classical
  intro x hx
  by_cases hxW : x ∈ (P.ℜ.prepWStar P.E₁).pts
  · exact h₄ x ⟨hx, hxW⟩
  obtain ⟨hWs, hVf, hrest⟩ := h₂.2.2.2 x hx
  have hxWpts : x ∈ P.ℜ.W.pts := hWs.1
  refine ⟨hWs, hVf, ?_⟩
  -- the component of `W` through `x` is contained in `E_1`, so `E_{1,x} ⊆ W_x`
  have : IsRegularLocalRing (X.presheaf.stalk x ⧸ P.ℜ.W.stalkIdeal x) := hWs.2
  have hWp : (P.ℜ.W.stalkIdeal x).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
  have hmin : P.ℜ.W.stalkIdeal x ∈ (P.ℜ.W.stalkIdeal x).minimalPrimes :=
    ⟨⟨hWp, le_rfl⟩, fun q hq _ => hq.2⟩
  obtain ⟨C, hC, hxC, hCq⟩ :=
    Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes P.ℜ.W x hmin
  have hCE : C.IsContainedIn P.E₁ := by
    by_contra hn
    apply hxW
    rw [DatumI.Raw.pts_prepWStar]
    exact subset_closure ⟨_, ⟨C.support, ⟨C, hC, hn, rfl⟩, rfl⟩, hxC⟩
  have hz : P.E₁.stalkIdeal x ≤ P.ℜ.W.stalkIdeal x := by
    have := Subscheme.stalkIdeal_mono (fun U => hCE U) x
    rwa [hCq] at this
  have hred : (Subscheme.unionFam P.E).IsReduced := P.hEunion ▸ P.hℜ.1
  have hi : (Subscheme.unionFam P.E).HasOnlyNormalCrossingsAt x := P.hEunion ▸ P.hℜ.2.2.1 x
  rw [P.hEunion]
  exact Subscheme.hasOnlyNormalCrossingsWithAt_unionFam_of_stalkIdeal_le hX P.E P.hE ⟨0, P.hα⟩
    hred hxWpts hi hrest hz

/-- End of the proof (p. 291–292): by (1) and (5)*, "every irreducible component `W_1` of `W` is
either contained in `E_1` or such that `E_1 ∩ W_1 ⊆ Ū`".

Deviation from the paper (gap filled): the two lines closing the proof are proved (with
`resolvedAt_of_cond₂_cond₄` for the resolvedness at `Ū`), including that an irreducible
component of `W` not contained in `E_1` lies in `W_*`. -/
theorem Goal.of_stage₅ (hX : X.IsNonsingular) (h : P.Stage₅) : P.Goal := by
  obtain ⟨-, Ubar, h₂, h₄, h₅⟩ := h
  refine ⟨X, MonoidalSuccession.nil X, trivial, Ubar, h₂.1, h₂.2.1, ?_, ?_⟩
  · exact P.resolvedAt_of_cond₂_cond₄ hX h₂ h₄
  · intro W₁ hW₁
    by_cases hW : W₁.IsContainedIn P.E₁
    · exact Or.inl hW
    · right
      obtain ⟨Z, hZ, rfl⟩ := id hW₁
      have hsub : (Subscheme.ofClosed Z).pts ⊆ (P.ℜ.prepWStar P.E₁).pts := by
        have hle : (Subscheme.ofClosed Z).support ≤ sSup {Z' : TopologicalSpace.Closeds X |
            ∃ W₂ ∈ P.ℜ.W.irreducibleComponents, ¬ W₂.IsContainedIn P.E₁ ∧ Z' = W₂.support} :=
          le_sSup ⟨_, hW₁, hW, rfl⟩
        intro x hx
        have hx' := hle hx
        show x ∈ (((Subscheme.ofClosed (sSup {Z' : TopologicalSpace.Closeds X |
            ∃ W₂ ∈ P.ℜ.W.irreducibleComponents, ¬ W₂.IsContainedIn P.E₁ ∧
              Z' = W₂.support})).support : TopologicalSpace.Closeds X) : Set X)
        rw [Subscheme.ofClosed, Scheme.IdealSheafData.coe_support_vanishingIdeal]
        exact hx'
      intro x hx
      obtain ⟨hx1, hx2⟩ := Subscheme.mem_pts_inter_iff.mp hx
      have : x ∈ P.E₁.pts ∩ (P.ℜ.prepWStar P.E₁).pts := ⟨hx2, hsub hx1⟩
      rw [h₅.1] at this
      exact h₅.2 this

end PrepSetting

end PrepProposition

/-- **Proposition 5** (preparation theorem on `(ℜ^{N,n}_I, U)`, pp. 288–292).

Condition (ii) is stated as the paper prints it (pp. 288–289): "either `E₁′ ⊇ W₁′` or
`E₁′ ∩ W₁′ ⊆ Ũ′`", i.e. `W₁.IsContainedIn … ∨ …`, without a negation; the end of the proof (p. 292:
"every irreducible component `W₁` of `W` is either contained in `E₁` or such that `E₁ ∩ W₁ ⊆ Ū`") and
the use of (ii) for `[(2)]` on p. 307 (`AB.PrepHyp`) confirm this reading. -/
@[blueprint "prop:IV.2-5"
  (statement := /-- \textbf{Proposition 5} (Preparation theorem on
    $(\mathfrak R^{N,n}_{\mathrm I},U)$). Let $(\mathfrak R^{N,n}_{\mathrm I},U)$ be a
    resolution datum of the type $\mathfrak R^{N,n}_{\mathrm I}$ with open restriction $U$ on
    a non-singular irreducible algebraic scheme $X$, where $N>n\ge0$. Let
    $\mathfrak R^{N,n}_{\mathrm I}=(\bigcup_{i=1}^\alpha E_i;V_1,\dots,V_\beta;W)$ and let us
    assume that $\alpha\ge1$. Suppose that Theorems $\mathrm I_1^{N',n'}$ with $n'<N'\le N$
    and $n'\le n$, and Theorems $\mathrm I_2^{N,n''}$ with $n''<n$, are verified
    (\cref{thm:I.2-I1}, \cref{thm:I.2-I2}). Then there exists a permissible succession of
    monoidal transformations $f\colon X'\to X$ for $(\mathfrak R^{N,n}_{\mathrm I},U)$ such
    that the transform $f^*(\mathfrak R^{N,n}_{\mathrm I},U)
    =(f^*(\mathfrak R^{N,n}_{\mathrm I}),U')$ with
    $f^*(\mathfrak R^{N,n}_{\mathrm I})=(\bigcup_iE_i';V_1',\dots,V_\beta';W')$ has the
    following property: there exists an open subset $U''$ of $W'$ such that
    \begin{enumerate}
      \item[(i)] $U''\supseteq U'$ and $f^*(\mathfrak R^{N,n}_{\mathrm I})$ is resolved at
        every point of $U''$, and
      \item[(ii)] if $W_1'$ is any irreducible component of $W'$, either
        $E_1'\supseteq W_1'$ or $E_1'\cap W_1'\subseteq U''$, where $E_1'$ denotes the
        strict transform of $E_1$ on $X'$.
    \end{enumerate}
    (pp.~288--289; the paper writes $\tilde U'$ for $U''$.)

    (Condition (ii) is stated as the paper prints it, $E_1'\supseteq W_1'$ or
    $E_1'\cap W_1'\subseteq U''$, without a negation; the end of the proof on p.~292 and the use of
    (ii) for [(2)] on p.~307 confirm this reading.)

    (Formalization notes. (a) \emph{Index conditions} are transcribed verbatim from the
    printed page: ``Theorems $\mathrm I_1^{N',n'}$ with $n'<N'\le N$ and $n'\le n$, and
    Theorems $\mathrm I_2^{N,n''}$ with $n''<n$'' (p.~288; the
    condition on $n'$ is $\le$, consistently with the implication (B) of \S2, Ch.~I, p.~172,
    which assumes $\mathrm I_1^{N^*,n^*}$ for $n^*<N^*\le N$ and $n^*\le n$, and with the
    proof, which applies $\mathrm I_1^{N^*,n^*}$ to the datum on $X-F$ with principal
    subscheme $W_*-F$, where $n^*$ may equal $n$). (b) (Encoding.) The boundary of
    $f^*(\mathfrak R)$ is a single subscheme in
    \texttt{DatumI.Raw}, namely the union of the strict transforms of the $E_i$ and of all
    the exceptional divisors introduced by $f$ (Definition 7, p.~168); $E_1'$ is the strict
    transform of $E_1$ along the succession. (c) (Encoding.) ``$U''$ is an open subset of $W'$'' is
    rendered, as in Definition 5 (I.2), as $U''=V\cap W'$ for some open $V$ of $X'$.) -/)
  (proof := /-- Let $W_1,\dots,W_a$ be those irreducible components of $W$ which are not
    contained in $E_1$, and $W_{a+1},\dots,W_c$ those irreducible components of $W$ which are
    contained in $E_1$. Let $W_*=W_1\cup\dots\cup W_a$. Let $F_1,\dots,F_\delta$ be those
    reduced irreducible components of $W_*\cap E_1$ which have non-empty intersection with
    $U$, and let $F=\bigcup_{i=1}^\delta F_i$. Since $\mathfrak R^{N,n}_{\mathrm I}$ is
    resolved at every point of $U$, $U$ consists of only simple points of $W$ and in
    particular it does not contain any common point of any two irreducible components of $W$.
    Moreover, the resolution datum on $X$
    \[\bar{\mathfrak R}^{N,\bar n}_{\mathrm I}
      =\Big(\bigcup_{j=1}^\alpha E_j;V_1,\dots,V_\beta,W;F\Big),\qquad\bar n=\dim F,\]
    is resolved at every point of $F\cap U$ (Corollary 1 of Proposition 1, \S1, Ch.~II), and
    $F\cap U$ is an open dense subset of $F$. We consider
    $(\bar{\mathfrak R}^{N,\bar n}_{\mathrm I},F\cap U)$ on $X$ with open restriction
    $F\cap U$; as is easily seen, a permissible succession for
    $(\bar{\mathfrak R}^{N,\bar n}_{\mathrm I},F\cap U)$ is such a succession for
    $(\mathfrak R^{N,n}_{\mathrm I},U)$. Since $\bar n<n$, Theorem $\mathrm I_2^{N,\bar n}$
    gives a permissible succession $f\colon X'\to X$ for
    $(\bar{\mathfrak R}^{N,\bar n}_{\mathrm I},F\cap U)$ such that
    $f^*(\bar{\mathfrak R}^{N,\bar n}_{\mathrm I})$ is resolved at every point of the strict
    transform $F'$ of $F$. Then $F'$ is non-singular and $V_1',\dots,V_\beta',W'$ are all
    normally flat along $F'$; in particular every point of $F'$ is a simple point of $W'$
    (Corollary 4 of Proposition 1, \S1, Ch.~II), and all the $V_j'$ are normally flat along
    $W'$ at every point of $F'$ (Corollary of Theorem 3, \S3, Ch.~II). On the other hand,
    since $\mathfrak R^{N,n}_{\mathrm I}$ is resolved at every point of $U$, for $i\ge2$ any
    $E_i$ containing some $F_j$ must contain the unique irreducible component of $W$
    containing $F_j$; since $f$ induces an isomorphism of $X'-f^{-1}(W-U)$ onto $X-(W-U)$, it
    follows that for $i\ge2$ any $E_i'$ containing an irreducible component $F_j'$ of $F'$
    must contain the unique irreducible component of $W'$ containing $F_j'$. In virtue of
    \cref{lem:IV.2-3}, the resolution datum
    $(\bigcup_{i\ge2}E_i';V_1',\dots,V_\beta';W')$ on $X'$ must be resolved at every point of
    $F'$.

    Thus we may assume, without any loss of generality, that the given resolution datum
    $(\mathfrak R^{N,n}_{\mathrm I},U)$ is such that
    \begin{enumerate}
      \item[(1)] if $W_*$ is the union of those irreducible components of $W$ which are not
        contained in $E_1$ and if $F_1,\dots,F_\delta$ are those reduced irreducible
        components of $W_*\cap E_1$ which have non-empty intersection with $U$, then
        $F=F_1\cup\dots\cup F_\delta$ is a disjoint union of non-singular schemes
        $F_1,\dots,F_\delta$ and $\bigcup_iE_i$ has only normal crossings with $F$;
      \item[(2)] there exists an open subset $\tilde U$ of $W$ which contains $U$ and $F$ and
        such that the resolution datum $(\bigcup_{i\ge2}E_i;V_1,\dots,V_\beta;W)$ is resolved
        at every point of $\tilde U$.
    \end{enumerate}

    Let us consider the resolution datum $\bar{\mathfrak R}^{N,\bar n}_{\mathrm I}
    =\big(\bigcup_{i=1}^\alpha E_i;V_1,\dots,V_\beta,W,W_*\cap E_1;F\big)$ with open
    restriction $\tilde U\cap F$ on $X$. By Theorem $\mathrm I_2^{N,\bar n}$ we have a
    permissible succession $f\colon X'\to X$ for
    $(\bar{\mathfrak R}^{N,\bar n}_{\mathrm I},\tilde U\cap F)$ such that
    $f^*(\bar{\mathfrak R}^{N,\bar n}_{\mathrm I})$ is resolved at every point of the strict
    transform $F'$ of $F$; it is clear that $f$ is permissible for
    $(\mathfrak R^{N,n}_{\mathrm I},U)$. Write
    $f^*(\mathfrak R^{N,n}_{\mathrm I})=(\bigcup_{i=1}^{\alpha'}E_i';V_1',\dots,V_\beta';W')$
    and $f^*(\mathfrak R^{N,n}_{\mathrm I},U)=(f^*(\mathfrak R^{N,n}_{\mathrm I}),U')$, and
    let $(W_*\cap E_1)'$ be the strict transform of $W_*\cap E_1$, so that
    $f^*(\bar{\mathfrak R}^{N,\bar n}_{\mathrm I})
    =(\bigcup_{i=1}^{\alpha'}E_i';V_1',\dots,V_\beta',W',(W_*\cap E_1)';F')$. Let $\tilde U'$ be
    the open subset $f^{-1}(\tilde U)\cap W'$ of $W'$. Then, in view of \cref{lem:IV.2-4} and
    Corollary 2 of Theorem 5, \S6, Ch.~III, the resolution datum
    $(\bigcup_{i\ge2}E_i';V_1',\dots,V_\beta';W')$ is resolved at every point of $\tilde U'$.
    Moreover, if $W_*'$ denotes the union of those irreducible components of $W'$ which are
    not contained in $E_1'$, then $W_*'\cap E_1'\supseteq(W_*\cap E_1)'$ and every reduced
    irreducible component of $W_*'\cap E_1'$ is either contained in $(W_*\cap E_1)'$ or
    contained in $W'\cap E_j'$ with $j$ such that $\alpha<j\le\alpha'$. Since
    $f^*(\bar{\mathfrak R}^{N,\bar n}_{\mathrm I})$ is resolved at every point of $F'$,
    $(W_*\cap E_1)'$ is normally flat along $F'$, hence every component of $(W_*\cap E_1)'$ is
    either in $F'$ or has empty intersection with $F'$. Therefore every irreducible component
    of $W_*'\cap E_1'$ having non-empty intersection with $F'$ is either a reduced irreducible
    component of $F'$ or such of $W'\cap E_j'$ with $\alpha<j\le\alpha'$; and one proves that
    the $W'\cap E_j'$ for $\alpha<j\le\alpha'$ are non-singular irreducible subschemes of $X'$
    contained in $\tilde U'$.

    Thus, without any loss of generality, we may assume that $(\mathfrak R^{N,n}_{\mathrm I},
    U)$ has the following property, in addition to (1) and (2):
    \begin{enumerate}
      \item[(3)] if $G$ is any reduced irreducible component of $W_*\cap E_1$ which is not in
        $F$ and has non-empty intersection with $F$, then $G$ is contained in $\tilde U$ and of
        the form $W\cap E_j$ with $j\ge2$, hence non-singular.
    \end{enumerate}
    If $G$ is such a component, (2) and (3) imply immediately that the monoidal
    transformation $f\colon X'\to X$ with center $G$ is permissible for the resolution datum
    $(\bigcup_{i\ge2}E_i;V_1,\dots,V_\beta;W)$, hence for $(\mathfrak R^{N,n}_{\mathrm I},U)$;
    and (1), (2), (3) remain satisfied if we replace $(\mathfrak R^{N,n}_{\mathrm I},U)$ by
    $f^*(\mathfrak R^{N,n}_{\mathrm I},U)$ and $\tilde U$ by $f^{-1}(\tilde U)\cap W'$. Therefore,
    by \cref{lem:IV.2-5}, we may assume that
    \begin{enumerate}
      \item[(3)$^*$] every reduced irreducible component of $W_*\cap E_1$ is either contained
        in $F$ (hence is one of the $F_j$) or has empty intersection with $F$.
    \end{enumerate}
    Then, by replacing $\tilde U$ by $\tilde U-((W_*\cap E_1)-F)$, we may assume that
    \begin{enumerate}
      \item[(3)$^{**}$] $\tilde U\cap W_*\cap E_1=F$, where $\tilde U\cap W_*$ is an open dense
        subset of $W_*$.
    \end{enumerate}
    It follows from (1), (2) and (3)$^{**}$, with the help of \cref{lem:IV.2-3}, that
    \begin{enumerate}
      \item[(4)] $\mathfrak R^{N,n}_{\mathrm I}=(\bigcup_{i=1}^\alpha E_i;V_1,\dots,V_\beta;W)$
        is resolved at every point of $\tilde U\cap W_*$.
    \end{enumerate}
    (Here we must use the fact that $\mathfrak R^{N,n}_{\mathrm I}$ is resolved at every
    generic point of $F$.)

    Now let us consider the following resolution datum on the non-singular irreducible
    algebraic scheme $X-F$, with $N^*=\dim(X-F)$ and $n^*=\dim(W_*-F)$:
    \[\mathfrak R^{N^*,n^*}_{\mathrm I}=\Big(\bigcup_{i\ge2}(E_i-F);V_1-F,\dots,V_\beta-F,
      W-F;W_*-F\Big)\]
    with closed restriction $E_1-F$. Note that $(E_1-F)\cap(W_*-F)$ is entirely contained in
    $W_*-\tilde U$ while $F$ is entirely contained in $\tilde U$. Therefore the center of any
    permissible monoidal transformation for $(\mathfrak R^{N^*,n^*}_{\mathrm I},E_1-F)$ is
    contained in $W_*-\tilde U$ and closed not only in $W_*-F$ but also in $W_*$. It follows
    that any permissible monoidal transformation for
    $(\mathfrak R^{N^*,n^*}_{\mathrm I},E_1-F)$ is canonically induced by a permissible
    monoidal transformation for $(\mathfrak R^{N,n}_{\mathrm I},U)$, and that this permissible
    monoidal transformation for $(\mathfrak R^{N,n}_{\mathrm I},U)$ does not affect the
    properties (1), (2), (3)$^{**}$ and (4). Thus, by Theorem $\mathrm I_1^{N^*,n^*}$, we may
    assume that
    \begin{enumerate}
      \item[(5)] $E_1-F$ and $W_*-F$ have empty intersection,
    \end{enumerate}
    hence
    \begin{enumerate}
      \item[(5)$^*$] $E_1\cap W_*=F\subseteq\tilde U$.
    \end{enumerate}
    By (1), (2) and (4), $\mathfrak R^{N,n}_{\mathrm I}$ is resolved at every point of
    $\tilde U$ ($\tilde U$ is an open subset of $W$ containing $U$), and by (1) and (5)$^*$ every
    irreducible component $W_1$ of $W$ is either contained in $E_1$ or such that
    $E_1\cap W_1\subseteq\tilde U$. \textsc{q.e.d.}

    \textbf{Deviation from the paper (gap filled).} The repeated ``we may assume'' (the
    replacement of $(\mathfrak R^{N,n}_{\mathrm I},U)$ by its transform under a permissible
    succession, with the open restriction $U'$, the presentation of the transformed boundary and
    the strict transform of $E_1$) is made explicit: the goal for a transform gives the goal for
    the datum (composition of successions), and each reduction is a separate statement in the
    Lean file (conditions (1), (2), (3), (3)*, (3)**, (4), (5)*). The closing two lines of the
    proof are proved. All the steps are proved (modulo the cited results).

    \textbf{Deviation from the paper (gap filled).} For (3)$^{**}$: that $(W_*\cap E_1)-F$ is
    closed (finitely many components, by (3)$^*$), that $U$ and $F$ are not affected by its removal,
    and that $\tilde U\cap W_*$ is open and dense in $W_*$ are tacit in the paper and are proved.

    \textbf{Deviation from the paper (gap filled; no argument printed).} ``By (1), (2) and (4),
    $\mathfrak R$ is resolved at every point of $\tilde U$'' is stated without argument at the
    points of $\tilde U-W_*$ (where (4) does not apply); Lean supplies one: at a point of $\tilde U-W_*$ the unique component of $W$
    through the point is contained in $E_1$, so $E_{1,x}\subseteq W_x$, and Lemma~3, in the form of
    a regular system of parameters adapted at once to the $E_i$ and to $W_x$, gives the normal
    crossings of $E_1\cup\dots\cup E_\alpha$ with $W$ at $x$ (condition (1) is not used).

    \textbf{Deviation from the paper (gap filled; incomplete citation).} For (4): Lemma~3 as
    stated does not apply at a point $x$ of $F$, because its hypothesis (iii) (any $E_j$
    containing $F$ contains $W$) fails for $E_1$, which contains $F=W_*\cap E_1$ but not $W$. The
    parenthetical remark ``here we must use the fact that $\mathfrak R^{N,n}_{\mathrm I}$ is resolved
    at every generic point of $F$'' supplies the missing transversality: if $\eta$ is a generic
    point of $F$ with $x\in F_\eta$, $R=\mathcal O_{X,x}$, $\mathfrak p=F_x$, $Q=W_x$ and $E_{1,x}=(z)$,
    then $\mathfrak p=\sqrt{Q+(z)}$ by (3)$^{**}$ (every component of $W\cap E_1$ through $x$ has its
    generic point in $\tilde U\cap W_*\cap E_1=F$), and at $\eta$ the maximal ideal of
    $R_{\mathfrak p}=\mathcal O_{X,\eta}$ is generated by the generators of $W_\eta$ and
    $E_{1,\eta}$, which are part of a regular system of parameters; hence $Q+(z)$ and
    $\mathfrak p$ agree after localization at $\mathfrak p$, and since $R/Q$ is a regular local
    ring with $\dim R/\mathfrak p=\dim R/Q-1$, the prime $\mathfrak p/Q$ is principal, and
    Krull's principal ideal theorem shows that it is generated by the image of $z$; thus
    $F_x=W_x+E_{1,x}$. A regular system of parameters
    adapted to $E_1,\dots,E_\alpha$, to $F$ and to $W$ is then built from the flag lemma and an
    exchange of one parameter (Nakayama's lemma), which gives the normal crossings of
    $\bigcup_iE_i$ with $W$ at $x$. At the points of $\tilde U\cap W_*$ outside $E_1$,
    $\bigcup_iE_i$ and $\bigcup_{i\ge2}E_i$ agree near $x$.

    \textbf{Deviation from the paper (gap filled).} The presentation of the transformed boundary by
    the strict transforms $E_1',\dots,E_\alpha'$ of the $E_i$ followed by the exceptional divisor
    (Definition~7), which the paper uses without comment in $f^*(\mathfrak R)=(\bigcup_{i=1}^{\alpha'}
    E_i';\dots)$ and for the strict transform $E_1'$ of $E_1$, is proved: the strict transform of
    $E_1\cup\dots\cup E_\alpha$ is $E_1'\cup\dots\cup E_\alpha'$ (chart computation of
    Remark~1), the $E_i'$ and the exceptional divisor are non-singular irreducible of codimension
    one, and this passes to successions (induction on the succession).

    \textbf{Deviation from the paper (gap filled).} First reduction (p.~289). That
    $\bar{\mathfrak R}=(\bigcup E_j;V_1,\dots,V_\beta,W;F)$ is a resolution datum ($F$ reduced,
    $F\subseteq W\subseteq V_j$), that $F\cap U$ is an open dense subset of $F$, that $\dim F<\dim W$
    (each irreducible subset of $F$ lies in a component of $W$ not contained in $E_1$ whose generic
    point is not in $F$), that $\bar{\mathfrak R}$ is resolved on $F\cap U$ (at $x\in F\cap U$:
    $F_x=W_x+E_{1,x}$ is generated by part of a regular system of parameters adapted to $E$ and $W$,
    and Corollary~1 of Proposition~1, Ch.~II, is used pointwise), and that a succession permissible
    for $(\bar{\mathfrak R},F\cap U)$ is permissible for $(\mathfrak R,U)$ (``as is easily seen'')
    are tacit in the paper and are proved. The case $F=\emptyset$ is handled by the empty
    succession. In the conclusion, condition (1) for the transform is deduced from the resolvedness
    of $f^*\bar{\mathfrak R}$ on $F'$ (components of $F'$ are non-singular and disjoint); the
    identification of the $F$ of the transformed datum with the strict transform $F'$ (the centres
    avoid $U_0$, $U=U_0\cap W$, so $f$ is an isomorphism over $U_0$, and components of $W_*'\cap E_1'$
    meeting $U'$ are closures of components over $U_0$) is tacit in the paper ($f^*\bar{\mathfrak R}
    =(\bigcup E_j';V';W';F')$) and is proved. Condition (2) for the transform is proved as follows: the
    set $\tilde U'$ of points of $W'$ at which $(\bigcup_{E_i\ne E_1}E_i';V';W')$ is resolved is open
    in $W'$ (Lemma~1 of Ch.~IV \S1), it contains $U'$, and contains $F'$: $W'$ is simple at the points
    of $F'$ and the $V_j'$ are normally flat along $W'$ there (Corollary~4 of Proposition~1 and the
    Corollary of Theorem~3, Ch.~II, applied to the non-singular irreducible components of $F'$ and read
    in the schemes $V_j'$), and the normal crossings of the tail with $W'$ at a point of $F'$ follow
    from Lemma~3 in its pointwise form (see \cref{lem:IV.2-3}).

    \textbf{Gap filled.} In condition (2) for the transform, the two sentences ``since
    $\mathfrak R^{N,n}_{\mathrm I}$ is resolved at every point of $U$, for $i\ge2$ and $j$, $E_i$
    containing $F_j$ must contain the unique irreducible component of $W$ containing $F_j$. Since
    the above morphism $f$ induces an isomorphism of $X'-f^{-1}(W-U)$ onto $X-(W-U)$, it follows that
    for $i\ge2$, $E'_i$ containing an irreducible component $F'_j$ of $F'$ must contain the unique
    irreducible component of $W'$ containing $F'_j$'' (p.~289) are proved in this order, in the
    stalk form at the generic point. First, on $X$ at a point $\eta\in U$ of $F$ with $F_\eta=M_\eta$
    (the generic point of a component $F_j$): $\mathfrak R$ is resolved at $\eta$, $W_\eta+E_{1,\eta}$
    is the maximal ideal since $F_j$ is a component of $W_*\cap E_1$, so every $E_{i,\eta}\ne E_{1,\eta}$
    through $\eta$ lies in $W_\eta$. Then on $X'$, by transport along the isomorphism over
    $U_0=X-(W-U)$ (the centres of $f$ lie in $W-U$): the generic point $\eta'$ of $F_j'$ lies in
    $U'=f^{-1}(U)$, the strict transforms $E'_i$ ($i\le\alpha$), $W'$, $F'$ correspond to $E_i$, $W$,
    $F$ at $\eta=f(\eta')$ and the stalk ideals correspond, so $E'_{i,\eta'}\subseteq W'_{\eta'}$; the
    exceptional components $E'_j$, $j>\alpha$, lie over the centres, hence do not pass through $\eta'$
    ($f(\eta')\in U$). The conclusion at a point of $F'_j$ follows by contraction (the local ring at
    $\eta'$ is the localization at the prime $F'_y$). The unique-component statement itself, tacit in
    the paper, is used in this stalk form.

    \textbf{Deviation from the paper (slip; statement modified).} In condition (2) the tail
    $\bigcup_{i=2}^\alpha E_i$ is read as the union of the $E_i$ different from $E_1$. The convention
    of p.~274 (``We do not require that $E_i$ differ from $E_j$ if $i\ne j$'') allows $E_i=E_1$ for
    some $i\ge2$; for such an $i$ the paper's ``$E_i$ containing $F_j$ must contain the unique
    irreducible component of $W$ containing $F_j$'' (p.~289) fails ($E_1\supseteq F_j$ but not the
    component of $W_*$ through it), Lemma~3 does not apply, and the printed (2) would require the
    normal crossings of $E_1$ with $W$ along $F$, which (4) proves only later. With the copies of
    $E_1$ excluded the argument goes through, and the later uses of (2) are unaffected.

    \textbf{Deviation from the paper (statement modified).} Corollary~4 of Proposition~1 and the
    Corollary of Theorem~3 (Ch.~II), used on p.~289 for the $V_j'$, $W'$ and the components of $F'$,
    are applied in a form for the $V_j$ of a resolution datum (normal flatness read in the scheme
    $V_j$); this is proved in Lean as
    \texttt{Subscheme.isSimpleAt\_and\_isNormallyFlatAlongAt'\_of\_chain}.

    \textbf{Deviation from the paper (gap filled).} The fact used in (4), that
    $\mathfrak R^{N,n}_{\mathrm I}$ is resolved at every generic point of $F$, follows from the
    hypothesis that $\mathfrak R^{N,n}_{\mathrm I}$ is resolved on $U$: each $F_j$ meets the open
    restriction $U=U_0\cap W$, so the non-empty open subset $F_j\cap U_0$ of the irreducible $F_j$
    contains its generic point.

    \textbf{Deviation from the paper (gap filled).} Step 3 (p.~290): ``Then in view of Lemma~4 of
    this section and Corollary~2 of Theorem~5, \S6, Ch.~III, the resolution datum
    $(\bigcup_{i\ge2}E_i';V_1',\dots,V_\beta';W')$ is resolved at every point of $\tilde U'$''
    ($\tilde U'=f^{-1}(\tilde U)\cap W'$). The two cited results do not suffice by themselves; the
    following are tacit and are proved. (a) Corollary~2 requires $W-B$ dense in $W$, which holds
    because $U\cap W$ is dense in $W$ and misses the center $B$; it requires $B$ non-singular and
    irreducible, which holds because $B\ni f(y)$ is a non-empty center, and $W$ simple at $f(y)$,
    which holds because the datum is resolved there. (b) Off the exceptional divisor $f$ is a local
    isomorphism, so resolvedness is transported; over the center, simplicity of $W'$ follows from the
    normal crossings of $E'$ with $W'$ given by Lemma~4 (\cref{lem:IV.2-4}), applied on an open
    neighbourhood of the point on which its hypotheses hold. (c) The tail $(\bigcup_{i\ge2}E_i;V;W)$ is a resolution datum, $U$
    is an open restriction for it and the succession is permissible for it, because normal crossings
    with $B$ and with $W$ pass to sub-unions of the components of the boundary. (d) The boundary of
    $f^*$ of the tail is the sub-union of the $E_j'$ over a set of indices containing all $j>\alpha$
    and all $j\le\alpha$ with $E_j\ne E_1$ (the strict transform of a sub-union of the components is
    the sub-union of the strict transforms), which contains the tail of the presentation of
    $f^*(\mathfrak R)$. Moreover, the printed relation $W_*'\cap E_1'\supseteq(W_*\cap E_1)'$ on
    this page carries a doubled-bar $\supseteq$, not an equality. The
    sentences about the components of $W_*'\cap E_1'$ ((3) for the transform) are proved as follows.
    (i) $W_*'\cap E_1'\supseteq(W_*\cap E_1)'$: over $X-F$ the transformation is an isomorphism (the
    centres lie over $F$), and over $F$ the strict transform of $(W_*\cap E_1)$ lies in
    $F'\cup$(strict transform of the closure of $(W_*\cap E_1)-F$). (ii) A component of $W_*'\cap E_1'$
    through a point over $X-F$ is the strict transform of a component of $W_*\cap E_1$; one over $F$
    lies in $F'$ or in an exceptional divisor $E_j'$ ($j>\alpha$), since $f^{-1}(F)=F'\cup\bigcup_jE_j'$.
    (iii) ``Since $f^*(\bar{\mathfrak R})$ is resolved at every point of $F'$, $(W_*\cap E_1)'$ is
    normally flat along $F'$, hence every component of $(W_*\cap E_1)'$ is either in $F'$ or has empty
    intersection with $F'$'' is the Ch.~II type fact that a scheme normally flat along one of its
    components has no other component through the point; Lean proves it in the hypersurface situation
    $W'\cap E_1'$ of the regular local ring $\mathcal O_{X',x}$: the prime $F'_x$ of $\mathcal
    O_{W',x}$ is minimal over $(\bar z)$, $E_1'=(z)$, hence of height one, hence principal $(\pi)$, and a
    graded-piece argument (the pieces $P^n/P^{n+1}$ of $\mathcal O_{W',x}/J$ are cyclic and free over the
    domain $\mathcal O_{W',x}/P$, hence torsion free) shows that $J=((W_*\cap E_1)')_x$ contains a power
    of $\pi$ (alternative proof, gap filled). (iv) ``We can prove that $W'\cap E_j'$ are non-singular
    irreducible subschemes of $X'$ and contained in $\tilde U'$'': non-singular, because the tail datum is
    resolved at the points of $W'\cap E_j'$ and $W'\not\subseteq E_j'$ (the exceptional divisors lie over
    $F$, the strict transform of $W$ is dense over $X-F$); contained in $\tilde U'$ since the exceptional
    divisors lie over the centres, which lie in $F\subseteq\tilde U$; the irreducibility is true under
    the standing hypotheses (at the centres $W$ is simple, so one component of $W$ passes through the
    connected centre $B_k$, along which $W^{(k)}\cap\mathrm{Exc}_k$ is the projective bundle
    $\mathbb P(N_{B_k/C})$; the later steps replace it by its strict transform, because at the centres the
    tail datum is resolved, so the equations of $W'$, $E_j'$ and of the new exceptional divisor lie in one
    regular system of parameters) and is reduced, by induction on the succession, to the
    first-step statement that $W_1\cap\mathrm{Exc}_1$ is irreducible, which is proved
    (no counterexample: the counterexample to Lemma (AB.4), \cref{lem:IV.AB-4-componentwise}, needs a centre meeting two branches of $W$). The ``or such of $W'\cap E_j'$'' is the equality of the component with
    $W'\cap E_j'$ (height one over $W'_x$ and irreducibility). Finally $E_j'\neq E_1'$ for $j>\alpha$ when
    $E_1\not\subseteq F$ (and if $E_1\subseteq F$ every component lies in $F'$), which puts $E_j'$ into the
    tail.

    \textbf{Deviation from the paper (gap filled).} For the blow-up with center a component $G$ of
    $W_*\cap E_1$ which is not in $F$ but meets it (p.~291: ``the conditions (1), (2) and (3)
    remain to be satisfied if we replace $(\mathfrak R,U)$ by $f^*(\mathfrak R,U)$''), condition
    (1) is proved. The paper gives no argument. Lemma~4 of \S2 does not apply directly to the
    strict transform $F'$ of $F$: its hypotheses are $B\subseteq W$ and normal crossings of $E$ with
    $W$, whereas here $G\not\subseteq F$ and $E_1$ need not have normal crossings with $W$ at the
    points of $G\cap F$ (it can be tangent to $W$ along $G$; e.g.\ $W=\{z=0\}$, $E_2=\{y=0\}$,
    $E_1=\{z=xy\}$ in $\mathbb A^3$, $F$ the $y$-axis, $G$ the $x$-axis). Lean proceeds by a local
    computation in one adapted regular system of parameters at $x\in G\cap F$. A flag lemma (for
    $W_x\subseteq F_x$ and the components of $E_i$, $i\ge2$, which have normal crossings with $F$
    by (1) and with $W$ by (2)) gives a regular system $Z$ in which $W_x$, $F_x$ and $G_x=W_x+(z_j)$
    are generated by subsets and the tail components by members; the generator of $E_1$, which lies
    in $F_x\cap G_x$ and is independent of the other components modulo $\mathfrak m^2$, replaces a
    generator of $W_x$ (one with a unit coefficient and not a component generator), so that $E$,
    $F$ and $G$ are all adapted to one system. The chart $R'=R[G/z_t]$ then gives $E'$, the
    exceptional divisor and $F'$ as products, resp.\ subsets, of one set extending to a regular
    system of parameters of $R'$. For this one needs the \emph{chart formula for the strict
    transform of a subscheme not contained in the center}: if $V_x$ is generated by $S\subseteq Z$
    (not only $S\subseteq T$, the generators of the center), then $V'_y$ is $(1)$ if $z_t\in S$ and
    $(z'_s:s\in S)$ otherwise, where $z'_s=z_s$ for $s\notin T$; the saturation computation of
    p.~169 is extended accordingly.

    \textbf{Deviation from the paper (gap filled).} Condition (3) after the same blow-up (p.~291,
    ``the conditions (1), (2) and (3) remain to be satisfied'') is proved. The proof of (3) after the
    succession of p.~290 (centers in $F$) is not available: it uses that the centers lie in $F$. Here
    the centers lie in $W-U$ over $G\subseteq\tilde U$. The strict transform $W'$ of $W$ is
    isomorphic to $W$ (first assertion of Lemma~5; Lean proves it for $W$ only simple along $G$,
    the ideal of $G$ in $\mathcal O_{W,x}$ being generated by the non-zero image of the equation of
    $E_j$, hence invertible). A component $C$ of $W_*'\cap E_1'$ not in $F'$ and meeting $F'$ is then
    either contained in $W'\cap f^{-1}(G)$, which corresponds to $G$ under $W'\cong W$, hence is
    irreducible, or the strict transform of a component of $W_*\cap E_1$ other than $G$ which is not
    in $F$ and meets $F$, i.e.\ a bad component $W\cap E_i$, and is contained in the irreducible
    $W'\cap E_i'$. In both cases $C$ equals $W'\cap E'_k$, which is non-singular and lies in
    $\tilde U'$: Krull's principal ideal theorem in the regular local domain $\mathcal O_{W',x}$
    ($G_x$ and $(W'\cap E_k')_x$ are primes of height one over $W'_x$, one containing the other),
    the simplicity of $W'\cap E_k'$ from the resolvedness of the tail datum on $\tilde U'$.

    \textbf{Deviation from the paper (incomplete citation: Lemma~5's hypotheses fail globally; the
    paper's measure is used).} For (3)$^*$
    (``Therefore, by Lemma~5, we may assume that (3)$^*$'', p.~291): Lemma~5 is applied on a
    non-singular irreducible scheme and its termination is proved by a local computation
    (p.~288: $P_0+(y^\nu)R_0$ contains $w$ but $P_0+(y^{\nu+1})R_0$ does not); here $W$ is neither
    irreducible nor non-singular. Lean iterates the blow-up on the scheme $X$ itself, with the paper's
    own $\nu$ as the termination measure: it is the order $\mu(G)=\nu$ of $E_1|_W$ along the bad
    component $G$ at its generic point (a discrete valuation ring, $G$ being a Cartier divisor in $W$ because $W$ is simple
    along $G\subseteq\tilde U$): after the blow-up of $G$, with $H=W'\cap f^{-1}(G)\cong G$, the order
    of $E_1'|_{W'}$ along $H$ is $\mu(G)-1$ (so $H\subseteq E_1'$ iff $\mu(G)\ge2$), which is the
    termination of Lemma~5. If $\mu\ge2$, $H$ is again a component of $W_*'\cap E_1'$, not in $F'$ and
    meeting $F'$ (a bad component: $W'\cong W$ and $F\subseteq\overline{F-G}$), and one blows it up
    next. The components of $W_*'\cap E_1'$ which are not in $F'$ and meet $F'$ are $H$ or the strict
    transforms of the bad components $\ne G$ (the ones met by the generic point of $W'$ over their
    generic point); so the number of bad components does not increase and, at the last step
    ($H\not\subseteq E_1'$), decreases by one. The conditions (1), (2), (3) are preserved at each
    step.

    \textbf{Deviation from the paper (gap filled; hypothesis made explicit).} For (5) (p.~291:
    ``Now, let us consider the following resolution datum on the non-singular irreducible algebraic
    scheme $X-F$, with $N^*=\dim(X-F)$ and $n^*=\dim(W_*-F)$''): the hypothesis $N>n$ of
    Proposition~5 (p.~288) is used, in Lean as the hypothesis $n<N$ of this step; without it
    $n^*<N^*$ can fail (for $W=X$ and $E_1$ missing $U$ one has $n^*=N^*$ and $F=\emptyset$). Lean
    verifies what the paper leaves tacit: if $(W_*\cap E_1)-F=\emptyset$ then (5) already holds (empty
    succession); otherwise $X-F$ is a non-empty open subscheme of $X$, hence a non-singular
    irreducible algebraic scheme of dimension $N^*\le N$ (the dimension of an open subset of a local
    scheme can drop), $W_*-F$ is non-empty of dimension $n^*\le n$, and $n^*<N^*$ because $W_*-F$ is a
    proper closed subset of $X-F$ (otherwise $W_*=X$ and $\dim W=N>n$) and a proper closed subset of
    an irreducible scheme has smaller dimension. The displayed tuple is the pull-back to $X-F$ of
    $(\bigcup_{i\ge2}E_i;V_1,\dots,V_\beta,W;W_*)$, a datum, with closed restriction $E_1-F$ (the
    pull-back of $E_1$, a non-singular irreducible divisor or empty; $E$ has only normal crossings;
    $W_*-F$ is dense off $E_1$ because $W_*=\overline{W_*-E_1}$). The centers of a permissible
    succession for it lie in $W_*\cap E_1-F=(W_*\cap E_1)\cap(X-V)$ (here $\tilde U=V\cap W$ and
    $\tilde U\cap W_*\cap E_1=F$ by (3)$^{**}$), a closed subset of $X$, so the succession is induced by
    a succession of $X$ whose centers are the closures of the images (the extension lemma), and
    $W_*'\cap E_1'\subseteq f^{-1}(F)$ follows from the emptiness on $X-F$. That this induced
    succession is permissible for $(\mathfrak R,U)$ is proved by induction along it: a center $B$
    permissible for $(\bigcup_{i\ge2}E_i;V_1,\dots,V_\beta,W;W_*)$ with closed restriction $E_1$ is
    permissible for $\mathfrak R$, because the list of the $V$'s of the former is that of $\mathfrak R$
    followed by $W$, and the whole boundary $E_1\cup\bigcup_{i\ge2}E_i$ has only normal crossings with
    $B\subseteq E_1$ by Lemma~3 (applied to $T\cup E_1$ with $E_1$ non-singular, in a form not using a
    presentation of $T$); $B$ misses $U$ because it lies over $(W_*\cap E_1)-F$, disjoint from
    $\tilde U\supseteq U$; the strict transforms of the union and the exceptional divisors are tracked by
    the presentation of the transformed boundary (Lean: \texttt{isPermissibleIOpen\_of\_extension}). That the
    transform satisfies (1), (2), (4) and (5)$^*$ (``this does not affect the properties (1), (2),
        (3)$^{**}$
    and (4)'', p.~291) is proved as follows (Lean: \texttt{stage₅\_of\_extension}). The centers lie
        over the
    closed set $C=(W_*\cap E_1)-F$, so $f$ is an isomorphism over the open set $X-C\supseteq\tilde
        U\cup F\cup U$;
    a lift of $X-C\to X$ through $f$ pulls the transform of $\mathfrak R$ and the strict transforms
        back to the
    plain pull-backs. (1): at the points of $F'$, which lie over $F\subseteq X-C$, $F'$ is simple
        and $E'$ has
    only normal crossings with it, by the pull-back. (2) is the corresponding statement of the
        earlier steps
    (the tail datum of $f^*(\mathfrak R)$ is resolved over $\tilde U$). (5)$^*$: a point of
        $E_1'\cap W_*'$ lies on
    the strict transform of $W_*$ (a point of $W'-E_1'$ is a limit of points over $X-C$, where it
        lies over
    $W-E_1$), so lies over $F$ by the emptiness on $X-F$, hence on $F'$. (3)$^{**}$ then follows
        from (5)$^*$ and
    the density of $\tilde U'\cap W_*'$ in $W_*'$, and (4) from (1), (2), (3)$^{**}$ as in the
        preceding steps. -/)
  (latexEnv := "proposition")]
theorem exists_isPermissibleIOpen_isOpen_resolvedAt_of_unionFam [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {X : Scheme.{u}} (N n : ℕ) (hX :
    IsAmbient X N) (hNn : n < N)
    (hI₁ : ∀ N' n' : ℕ, n' < N' → N' ≤ N → n' ≤ n → FundamentalTheorem.I₁.{u} N' n')
    (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'')
    (α : ℕ) (hα : 0 < α) (E : Fin α → Subscheme X)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne)
    (ℜ : DatumI.Raw X) (hℜ : ℜ.IsDatum) (hEunion : ℜ.E = Subscheme.unionFam E)
    (hn : ℜ.n = (n : WithBot ℕ∞)) (U : Set X) (hU : ℜ.IsOpenRestriction U) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
      s.IsPermissibleIOpen ℜ U ∧
      ∃ U'' : Set Y,
        (∃ V : Set Y, IsOpen V ∧ U'' = V ∩ (s.transformI ℜ).W.pts) ∧
        s.transformOpen U ⊆ U'' ∧
        (∀ x ∈ U'', (s.transformI ℜ).ResolvedAt x) ∧
        ∀ W₁ ∈ (s.transformI ℜ).W.irreducibleComponents,
          W₁.IsContainedIn (s.strictTransform (E ⟨0, hα⟩)) ∨
            (W₁.inter (s.strictTransform (E ⟨0, hα⟩))).pts ⊆ U'' := by
  let P : PrepSetting X := ⟨α, hα, E, hE, ℜ, hℜ, hEunion, U, hU⟩
  have hnle : P.ℜ.n ≤ (n : WithBot ℕ∞) := hn.le
  have hgoal : P.Goal := by
    refine PrepSetting.Goal.of_stepTo (P.stepTo_stage₁₂ hX hnle hI₂) ?_
    intro Y₁ Q₁ hY₁ hn₁ h₁
    refine PrepSetting.Goal.of_stepTo (Q₁.stepTo_stage₃ hY₁ hn₁ hI₂ h₁) ?_
    intro Y₂ Q₂ hY₂ hn₂ h₂
    refine PrepSetting.Goal.of_stepTo (Q₂.stepTo_stage₃Star hY₂ hn₂ h₂) ?_
    intro Y₃ Q₃ hY₃ hn₃ h₃
    have h₄ := Q₃.stage₄_of_stage₃SS hY₃ (Q₃.stage₃SS_of_stage₃Star hY₃ h₃)
    refine PrepSetting.Goal.of_stepTo (Q₃.stepTo_stage₅ hY₃ hNn hn₃ hI₁ h₄) ?_
    intro Y₄ Q₄ hY₄ hn₄ h₅
    exact PrepSetting.Goal.of_stage₅ Q₄ hY₄.2.1 h₅
  exact hgoal

end

end Hironaka

