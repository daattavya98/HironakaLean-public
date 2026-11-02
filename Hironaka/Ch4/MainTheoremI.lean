/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Architect
public import Hironaka.Compat.MainISystem
public import Hironaka.Compat.MonoidalSuccessionBaseChange
public import Hironaka.Compat.CompletionResolved
public import Hironaka.Compat.CompletionEmbedding
public import Hironaka.Compat.CompletionFibreGeneral
public import Hironaka.Ch4.MainIAmbient
public import Hironaka.Ch4.Conclusion
public import Hironaka.Ch4.LiftingOpen
public import Hironaka.Ch4.MainIStepIso
public import Hironaka.Statements

/-!
# Main Theorem I(n) (Ch. I §3, pp. 174–176)

> MAIN THEOREM I(n). Let `V₀` be an arbitrary algebraic scheme, `V_j` (1 ≤ j ≤ β) a finite number of subschemes of `V₀`,
> and `W` a reduced subscheme of `V₀` of dimension `n` which is contained in `⋂_{j=1}^β V_j`.  Then there exists a
> finite succession of monoidal transformations `{f_i : V₀(i+1) → V₀(i)}` with centers `B_i` in `V₀(i)` for
> `0 ≤ i < r`, where `V₀(0) = V₀`, such that if `{V_j(i+1) → V_j(i)}` and `{W(i+1) → W(i)}` are the monoidal
> transformations induced by `f_i`, where `V_j(0) = V_j` and `W(0) = W`, then (1) … (4).
>
> The proof is accomplished by induction on `n`.  If `n = 0`, then we take the empty succession which obviously will
> do.  Assume that the theorem is proved for all `n′ < n` where `n` is any fixed positive integer.  …  (p. 174)
> … Main theorem I(n) is now established.  (p. 176)

Contents: the base case, the one-step lemma (the added monoidal transformation
`ĝ`, the center `C`, the application of I(n′), the induced succession with empty centers, (1)–(3) for the new
prolongation), the induction on the length of the prolongation of `{f̂_i}` (`Reach4`), the improvement lemma
(`S̄(r′) ⊂ S̄(r)`), the descending chain and the induction on `n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

/-! ### Generic points of closed sets, points of the completion over `x` -/

/-- A nonempty closed subset of an algebraic scheme has a generic point of an irreducible component (p. 174: "take
a generic point `x` of `S̄(r)`"): finitely many irreducible closed sets cover it, take one that is maximal. -/
theorem exists_isGenericPointOfComponent {X : Scheme.{u}} [IsAlgebraicScheme X] {S : Set X}
    (hS : IsClosed S) (hne : S.Nonempty) : ∃ x, IsGenericPointOfComponent S x := by
  classical
  have := IsAlgebraicScheme.noetherianSpace X
  obtain ⟨F, hFirr, hFeq⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible
    (⟨S, hS⟩ : TopologicalSpace.Closeds X)
  have hcover : S = ⋃ K ∈ F, (K : Set X) := by
    have := congrArg (fun T : TopologicalSpace.Closeds X => (T : Set X)) hFeq
    simpa [TopologicalSpace.Closeds.coe_finset_sup] using this
  obtain ⟨z, hz⟩ := hne
  have hzK : ∃ K ∈ F, z ∈ (K : Set X) := by
    have : z ∈ ⋃ K ∈ F, (K : Set X) := hcover ▸ hz
    simpa using this
  obtain ⟨K₀, hK₀, -⟩ := hzK
  obtain ⟨K, hK, hKmax⟩ : ∃ K ∈ F, ∀ K' ∈ F, K ≤ K' → K' ≤ K := by
    have hFne : F.Nonempty := ⟨K₀, hK₀⟩
    obtain ⟨K, hK⟩ := F.exists_maximal hFne
    exact ⟨K, hK.1, fun K' hK' hle => hK.2 hK' hle⟩
  have hKirr : IsIrreducible (K : Set X) := hFirr ⟨K, hK⟩
  obtain ⟨x, hx⟩ : ∃ x, IsGenericPoint x (K : Set X) := QuasiSober.sober hKirr K.isClosed
  refine ⟨x, ?_⟩
  have hcl : closure {x} = (K : Set X) := hx.def
  have hKS : (K : Set X) ⊆ S := by
    rw [hcover]
    exact Set.subset_biUnion_of_mem (u := fun K : TopologicalSpace.Closeds X => (K : Set X)) hK
  refine ⟨⟨by rw [hcl]; exact hKirr, by rw [hcl]; exact hKS⟩, fun T hT hle => ?_⟩
  rw [hcl] at hle ⊢
  obtain ⟨hTirr, hTS⟩ := hT
  have hTcover : (T : Set X) ⊆ ⋃₀ ((fun K : TopologicalSpace.Closeds X => (K : Set X)) '' (F : Set _)) := by
    intro t ht
    have : t ∈ ⋃ K ∈ F, (K : Set X) := hcover ▸ hTS ht
    simpa using this
  obtain ⟨Z, hZ, hTZ⟩ := (isIrreducible_iff_sUnion_isClosed.mp hTirr)
    (F.image fun K : TopologicalSpace.Closeds X => (K : Set X))
    (by intro Z hZ; obtain ⟨K', -, rfl⟩ := Finset.mem_image.mp hZ; exact K'.isClosed)
    (by simpa using hTcover)
  obtain ⟨K', hK'F, rfl⟩ := Finset.mem_image.mp hZ
  have h1 : K ≤ K' := hle.trans hTZ
  exact hTZ.trans (hKmax K' hK'F h1)

/-- The completion `Spec(Ô_{X,x}) → X` hits `x` (the closed point; `S → Ŝ` is faithfully flat). -/
theorem exists_c0_eq [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X] (x : X) :
    ∃ p, (AB.c0 X x).base p = x := by
  have := isHironakaBase_stalk X x
  refine ⟨IsLocalRing.closedPoint (AB.Shat X x), ?_⟩
  show X.fromSpecStalk x (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
    (AB.Shat X x))) (IsLocalRing.closedPoint (AB.Shat X x))) = x
  have hloc : IsLocalHom (algebraMap (X.presheaf.stalk x) (AB.Shat X x)) := inferInstance
  have : IsLocalHom (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (AB.Shat X x))).hom :=
    hloc
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- A pull-back square is surjective on pairs of points with equal image. -/
theorem exists_eq_of_isPullback {P X₁ X₂ Z : Scheme.{u}} {fst : P ⟶ X₁} {snd : P ⟶ X₂} {f : X₁ ⟶ Z}
    {g : X₂ ⟶ Z} (H : IsPullback fst snd f g) (x₁ : X₁) (x₂ : X₂) (h : f.base x₁ = g.base x₂) :
    ∃ p : P, fst.base p = x₁ ∧ snd.base p = x₂ := by
  obtain ⟨a, ha1, ha2⟩ := Scheme.Pullback.exists_preimage_pullback x₁ x₂ h
  refine ⟨H.isoPullback.inv.base a, ?_, ?_⟩
  · have h1 : fst.base (H.isoPullback.inv.base a) = (H.isoPullback.inv ≫ fst).base a := rfl
    rw [h1, H.isoPullback_inv_fst]
    exact ha1
  · have h1 : snd.base (H.isoPullback.inv.base a) = (H.isoPullback.inv ≫ snd).base a := rfl
    rw [h1, H.isoPullback_inv_snd]
    exact ha2

/-! ### Along the succession from I(n′): the data of `C` and of `(V, W)` -/

section AlongC

variable {Y : Scheme.{u}} {β : ℕ}

/-- One step of "`C(k) ⊆ S(r+k)`" (p. 176: "We can easily see that … satisfying (1), (2) and (3)"): the strict transform
of a subscheme `C ⊆ W` contained in the unresolved set `S` of `(U; W)` is contained in the unresolved set of the strict
transforms.  Every point `p` of `C'` is a specialization of a point `q` of `C'` off the exceptional divisor
(`exists_generization_notMem_exceptional`); `f(q) ∈ C ⊆ S` is unresolved, `f` is a local isomorphism at `q`, so `q` is
unresolved; `S` is closed. -/
@[blueprint "lem:I.3-C-in-S-step"
  (statement := /-- One step of ``$C(k)\subseteq S(r+k)$'' (p.~176: ``We can easily see that $\{f_i,0\le i<r'\}$ is a prolongation of the $\{f_i,0\le i<r\}$ satisfying (1), (2) and (3)''). Let $C\subseteq W$ be a subscheme all of whose points lie in $S$ (\cref{def:I.3-main-S}) and $f$ a monoidal transformation. Then the points of the strict transform $C'$ lie in the set $S'$ of the strict transforms of the data. -/)
  (proof := /-- Every point $p$ of $C'$ is a specialization of a point $q$ of $C'$ off the exceptional divisor; $f(q)\in C\subseteq S$ is not resolved and $f$ is a local isomorphism at $q$ (\cref{lem:I.3-resolved-off-exceptional}), so $q\in S'$; and $S'$ is closed (\cref{lem:I.3-S-closed}). -/)
  (latexEnv := "lemma")]
theorem pts_strictTransform_subset_mainUnresolved_step [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme Y] {B : Subscheme Y}
    (t : MonoidalTransformation Y B) (U : Fin (β + 1) → Subscheme Y) (W : Subscheme Y)
    (hWU : ∀ j, W.IsContainedIn (U j)) (C : Subscheme Y) (hCW : C.IsContainedIn W)
    (hC : C.pts ⊆ Subscheme.mainUnresolved U W) :
    (Subscheme.strictTransform t C).pts ⊆ Subscheme.mainUnresolved
      (fun j => Subscheme.strictTransform t (U j)) (Subscheme.strictTransform t W) := by
  have := t.isAlgebraicScheme
  intro p hp
  obtain ⟨q, hq, hqE, hqp⟩ := t.exists_generization_notMem_exceptional C hp
  have hqW : q ∈ (Subscheme.strictTransform t W).pts :=
    pts_subset_of_isContainedIn (Subscheme.IsContainedIn.strictTransform t hCW) hq
  have hfq : t.f.base q ∈ Subscheme.mainUnresolved U W :=
    hC (MonoidalTransformation.pts_strictTransform_subset t C hq)
  have hqS : q ∈ Subscheme.mainUnresolved (fun j => Subscheme.strictTransform t (U j))
      (Subscheme.strictTransform t W) :=
    ⟨hqW, fun hres => hfq.2
      ((Subscheme.isMainResolvedAt_strictTransform_iff_of_notMem_exceptional t U W hWU hqE).mp hres)⟩
  have hcl := Subscheme.isClosed_mainUnresolved (fun j => Subscheme.strictTransform t (U j))
    (Subscheme.strictTransform t W) (fun j => Subscheme.IsContainedIn.strictTransform t (hWU j))
  exact closure_minimal (Set.singleton_subset_iff.mpr hqS) hcl (specializes_iff_mem_closure.mp hqp)

/-- `C(k) ⊆ S(r+k)` for all `k` (iterating the step). -/
@[blueprint "lem:I.3-C-in-S"
  (statement := /-- $C(k)\subseteq S(r+k)$ for all $k$ (p.~176: ``let $C(i+1)\to C(i)$ for $r\le i<r'-1$ be the succession of monoidal transformations induced by $f_i$, where $C(r)=C$''; the property $C\subseteq S(r)$ is p.~175: ``We have $C\subseteq S(r)$''): along a succession, the strict transform of a subscheme $C\subseteq W$ contained in $S$ is contained in the set $S$ of the strict transforms of the data. -/)
  (proof := /-- Iterate \cref{lem:I.3-C-in-S-step} along the succession. -/)
  (latexEnv := "lemma")]
theorem MonoidalSuccession.pts_strictTransform_subset_mainUnresolved [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme Y] {Y' : Scheme.{u}}
    (s' : MonoidalSuccession Y Y') (U : Fin (β + 1) → Subscheme Y) (W : Subscheme Y)
    (hWU : ∀ j, W.IsContainedIn (U j)) (C : Subscheme Y) (hCW : C.IsContainedIn W)
    (hC : C.pts ⊆ Subscheme.mainUnresolved U W) :
    (s'.strictTransform C).pts ⊆ Subscheme.mainUnresolved (fun j => s'.strictTransform (U j))
      (s'.strictTransform W) := by
  revert U W C
  revert ‹IsAlgebraicScheme Y›
  induction s' with
  | nil X =>
    intro _ U W hWU C hCW hC
    exact hC
  | cons B t rest ih =>
    intro hY U W hWU C hCW hC
    have := t.isAlgebraicScheme
    exact ih _ _ (fun j => Subscheme.IsContainedIn.strictTransform t (hWU j)) _
      (Subscheme.IsContainedIn.strictTransform t hCW)
      (pts_strictTransform_subset_mainUnresolved_step t U W hWU C hCW hC)

/-- (1), (2), (3) for the data `(U; W)` from (1′), (2′), (3′) of I(n′) for the system `(U, W)` with principal `C ⊆ S`
(p. 176, "We can easily see that {f_i} is a prolongation … satisfying (1), (2) and (3)"): `B_k ⊆ C(k) ⊆ W(r+k)`; `B_k`
contains no resolved point of `W(r+k)` because `C(k) ⊆ S(r+k)`; the `V_j(r+k)` and `W(r+k)` are normally flat along `B_k`
by (3′), `W(r)` being one of the `V′_j` (the last one). -/
@[blueprint "lem:I.3-main-123-of-snoc"
  (statement := /-- (1), (2), (3) for the data $(V_0(r),V_1(r),\dots,V_\beta(r);W(r))$ from (1$'$), (2$'$), (3$'$) of Main Theorem~I($n'$) for the system $(V_0(r),\dots,V_\beta(r),W(r))$ with principal subscheme $C\subseteq S(r)$ (p.~176: ``We can easily see that $\{f_i,0\le i<r'\}$ is a prolongation of the $\{f_i,0\le i<r\}$ satisfying (1), (2) and (3)''): the centers $B_k\subseteq C(k)\subseteq W(r+k)$ contain no resolved point of $W(r+k)$ because $C(k)\subseteq S(r+k)$, and the $V_j(r+k)$ and $W(r+k)$ are normally flat along $B_k$, $W(r)$ being the last member of the system. -/)
  (proof := /-- Induction on the succession: $B_k\subseteq C(k)\subseteq W(r+k)$, (2) from $C(k)\subseteq S(r+k)$ (\cref{lem:I.3-C-in-S-step}) and (3) from (3) for the system containing $W(r)$. -/)
  (latexEnv := "lemma")]
theorem MonoidalSuccession.isMain123_of_snoc [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme Y] {Y' : Scheme.{u}}
    (s' : MonoidalSuccession Y Y') (U : Fin (β + 1) → Subscheme Y) (W : Subscheme Y)
    (hWU : ∀ j, W.IsContainedIn (U j)) (C : Subscheme Y) (hCW : C.IsContainedIn W)
    (hC : C.pts ⊆ Subscheme.mainUnresolved U W)
    (hs : s'.IsMain123 (Fin.snoc (α := fun _ => Subscheme Y) U W) C) : s'.IsMain123 U W := by
  revert U W C
  revert ‹IsAlgebraicScheme Y›
  induction s' with
  | nil X =>
    intro _ U W hWU C hCW hC hs
    trivial
  | cons B t rest ih =>
    intro hY U W hWU C hCW hC hs
    have := t.isAlgebraicScheme
    obtain ⟨⟨⟨hBc, hBC⟩, h2, h3⟩, hrest⟩ := hs
    refine ⟨⟨⟨hBc, hBC.trans hCW⟩, fun x hx => (hC (pts_subset_of_isContainedIn hBC hx)).2,
      fun x hx => ⟨fun j => ?_, ?_⟩⟩, ?_⟩
    · simpa using (h3 x hx).1 (Fin.castSucc j)
    · simpa using (h3 x hx).1 (Fin.last _)
    · have hfun : (fun j => Subscheme.strictTransform t
          ((Fin.snoc (α := fun _ => Subscheme _) U W : Fin (β + 1 + 1) → Subscheme _) j)) =
          Fin.snoc (α := fun _ => Subscheme t.X') (fun j => Subscheme.strictTransform t (U j))
            (Subscheme.strictTransform t W) := by
        funext j
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
      rw [hfun] at hrest
      exact ih _ _ (fun j => Subscheme.IsContainedIn.strictTransform t (hWU j)) _
        (Subscheme.IsContainedIn.strictTransform t hCW)
        (pts_strictTransform_subset_mainUnresolved_step t U W hWU C hCW hC) hrest

/-- p. 176: the strict transforms `C(k)` of the reduced irreducible `C` stay reduced and irreducible along a succession
satisfying (2): `C(k)` has a generic point, at which the data of `C` are resolved (reduced), so by (2) it is not on the
center `B_k`, and the strict transform of an irreducible scheme by a center not containing it is irreducible. -/
@[blueprint "lem:I.3-C-strict-transform-irreducible"
  (statement := /-- Let $s'$ satisfy (1), (2), (3) for the system $V'$ and the principal subscheme $C$, with $C$ reduced and irreducible. Then the strict transforms $C(k)$ of $C$ are reduced and irreducible (p.~176: ``$C(r)=C$'', $C(i+1)\to C(i)$ ``the succession of monoidal transformations induced by $f_i$'', and the monoidal transformation $f_{r'-1}$ ``with center $C(r'-1)$''). -/)
  (proof := /-- The generic point of $C(k)$ is resolved (the resolved points of a reduced scheme are dense, \cref{lem:I.3-resolved-generization}), hence by (2) it is not on the center $B_k$, and the strict transform of an irreducible scheme by a center not containing it is irreducible; reducedness is preserved by strict transforms. -/)
  (latexEnv := "lemma")]
theorem MonoidalSuccession.isReduced_and_isIrreducible_strictTransform [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme Y] {Y' : Scheme.{u}}
    (s' : MonoidalSuccession Y Y') (V' : Fin (β + 1) → Subscheme Y) (C : Subscheme Y)
    (hCV : ∀ j, C.IsContainedIn (V' j)) (hCred : C.IsReduced) (hCirr : C.IsIrreducible)
    (hs : s'.IsMain123 V' C) :
    (s'.strictTransform C).IsReduced ∧ (s'.strictTransform C).IsIrreducible := by
  revert V' C
  revert ‹IsAlgebraicScheme Y›
  induction s' with
  | nil X =>
    intro _ V' C hCV hCred hCirr hs
    exact ⟨hCred, hCirr⟩
  | cons B t rest ih =>
    intro hY V' C hCV hCred hCirr hs
    have := t.isAlgebraicScheme
    obtain ⟨⟨⟨hBc, hBC⟩, h2, h3⟩, hrest⟩ := hs
    -- the generic point of `C` is resolved, hence not on `B`
    have hirr := Subscheme.isIrreducible_pts C hCirr
    set η := hirr.genericPoint
    have hCcl : IsClosed C.pts := C.support.isClosed
    have hηcl : closure {η} = C.pts := by
      rw [hirr.isGenericPoint_genericPoint_closure.def]
      exact hCcl.closure_eq
    have hηC : η ∈ C.pts := by rw [← hηcl]; exact subset_closure rfl
    obtain ⟨η', hη'η, hη'⟩ := Subscheme.exists_specializes_isMainResolvedAt V' C hCred hCV hηC
    have hη'C : η' ∈ C.pts := hη'.1.1
    have hηη' : η ⤳ η' := specializes_iff_mem_closure.mpr (by rw [hηcl]; exact hη'C)
    have hηres : Subscheme.IsMainResolvedAt V' C η := (hη'η.antisymm hηη').eq ▸ hη'
    have hnot : ¬ C.pts ⊆ B.pts := fun h => h2 η (h hηC) hηres
    exact ih _ _ (fun j => Subscheme.IsContainedIn.strictTransform t (hCV j))
      (t.isReduced_strictTransform_of_isReduced C hCred)
      (MonoidalTransformation.strictTransform_isIrreducible t C hCirr hnot) hrest

/-- The strict transform of the whole scheme by a succession is the whole scheme (`V_0(r) = V₀(r)`). -/
theorem MonoidalSuccession.strictTransform_bot' {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) :
    s.strictTransform (⊥ : Subscheme X) = ⊥ := by
  induction s with
  | nil X => rfl
  | cons B t rest ih =>
    rw [MonoidalSuccession.strictTransform_cons, MonoidalTransformation.strictTransform_bot]
    exact ih

/-- The system `(V_0(r), V_1(r), …, V_β(r))` is the strict transform of the system. -/
theorem mainSystem_strictTransform_succession {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {β : ℕ}
    (V : Fin β → Subscheme X) :
    (fun j => s.strictTransform (mainSystem V j)) = mainSystem (fun j => s.strictTransform (V j)) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [mainSystem, Fin.cons_zero]
    exact s.strictTransform_bot'
  · simp [mainSystem]

end AlongC

namespace MainTheorem

/-- p. 174: "If `n = 0`, then we take the empty succession which obviously will do": a reduced subscheme of dimension
`0` is non-singular and every `V_j` is normally flat along it (the ideal of `W` in `O_{V_j,x}` is the maximal ideal,
the quotient a field). -/
@[blueprint "lem:I.3-main-I-zero"
  (statement := /-- Main Theorem~I($0$) (p.~174): ``The proof is accomplished by induction on $n$. If $n=0$, then we take the empty succession which obviously will do.'' A reduced subscheme $W$ of dimension $0$ is non-singular and all the $V_j$ ($0\le j\le\beta$) are normally flat along it. -/)
  (proof := /-- The ``obvious'' fact is proved: if a point $x$ of $W$ were not resolved, the resolved generization $\eta\ne x$ of $x$ (\cref{lem:I.3-resolved-generization}) would give $\operatorname{height}x+1\le\operatorname{height}\eta\le\dim W=0$. Hence $S$ is empty, i.e.\ (4) holds for the empty succession (\cref{lem:I.3-main-4-iff-S-empty}). -/)
  (latexEnv := "lemma")]
theorem I_zero : MainTheorem.I.{u} 0 := by
  intro V₀ _ β V W hW hWn hWV
  refine ⟨V₀, MonoidalSuccession.nil V₀, trivial, ?_⟩
  rw [MonoidalSuccession.isMain4_iff_mainUnresolvedAt_eq_empty]
  refine Set.eq_empty_of_forall_notMem fun x hxS => ?_
  obtain ⟨hx, hn⟩ : x ∈ W.pts ∧ ¬ Subscheme.IsMainResolvedAt (mainSystem V) W x := hxS
  obtain ⟨η, hηx, hη⟩ := Subscheme.exists_specializes_isMainResolvedAt (mainSystem V) W hW
    (mainSystem_isContainedIn V W hWV) hx
  by_cases hxη : x = η
  · exact hn (hxη ▸ hη)
  · have hlt : x < η := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hηx) fun h =>
      hxη ((Scheme.le_iff_specializes.mp h).antisymm hηx).eq
    have h1 : Order.height x + 1 ≤ Order.height η := Order.height_add_one_le hlt
    have h2 : (Order.height η : WithBot ℕ∞) ≤ W.dim := StrictDim.height_le_dim W hη.1.1
    rw [hWn] at h2
    have h3 : Order.height η ≤ (0 : ℕ∞) := by exact_mod_cast h2
    have h4 : Order.height x + 1 ≤ 0 := h1.trans h3
    simp at h4

section Step

variable {V₀ : Scheme.{u}} [IsAlgebraicScheme V₀] {β : ℕ} (V : Fin β → Subscheme V₀) (W : Subscheme V₀)

/-- **The step of pp. 175–176.**  Let `s` be a succession satisfying (1), (2), (3), `x` a generic point of a closed set
`T ⊇ S̄(r)`, and `ĝ` a monoidal transformation of the completed scheme `V̂₀(r)` with center `Ĉ` satisfying (1), (2), (3)
for the completed data.  Then there is a prolongation `t` of `s` satisfying (1), (2), (3), with `S̄(r′) ⊆ S̄(r)`, whose
completion is `ĝ` up to the empty centers inserted before it: there is an isomorphism
`(s.append t).baseChangeTarget ≅ gh.X'` carrying the strict transform of the completed data by `ĝ` to the completed data
of `s.append t`.

Printed route: "Let `Ĉ` be the center of `ĝ`.  Then `Ĉ` is a reduced irreducible subscheme of `V̂₀(r)`, which is contained in
`Ŝ(r)`.  Since the point `x` is a generic point of `S̄(r)`, the image of `Ŝ(r)` in `V̂₀` is the unique closed point.
Therefore, we can find a reduced irreducible subscheme `C` of `V₀(r)` such that `Ĉ = c_r⁻¹(C)`.  In fact, we take the
smallest subscheme `C` of `V₀(r)` such that `Ĉ = c_r⁻¹(C)`.  We have `C ⊆ S(r)`.  Hence `dim(C) = n′ < n`.  We apply
theorem I(n′) to `V₀(r)`, `V₁(r)`, …, `V_β(r)`, `W(r)`, and `C`. … Let `{f_i, 0 ≤ i < r′ − 1}` be the prolongation of the
`{f_i, 0 ≤ i < r}` obtained by adding a succession in the above application of theorem I(n′), and let `C(i+1) → C(i)` for
`r ≤ i < r′ − 1` be the succession of monoidal transformations induced by `f_i`, where `C(r) = C`.  Let
`f_{r′−1} : V₀(r′) → V₀(r′ − 1)` be the monoidal transformation with center `C(r′ − 1)`.  We can easily see that
`{f_i, 0 ≤ i < r′}` is a prolongation of the `{f_i, 0 ≤ i < r}` satisfying (1), (2) and (3), and that it induces the
prolongation of the `{f̂_i}` by `ĝ` except for the `(r′ − r − 1)` monoidal transformations with empty centers which
should precede `ĝ`." -/
@[blueprint "lem:I.3-main-I-step"
  (statement := /-- The step of pp.~175--176. Let $\{f_i\}_{0\le i<r}$ be a succession satisfying (1), (2), (3), $x$ a generic point of a closed set containing $\bar S(r)$, and $\hat g$ a monoidal transformation of $\hat V_0(r)$ with center $\hat C$ satisfying (1), (2), (3) for the completed data. Then there is a prolongation of $\{f_i\}$ satisfying (1), (2), (3) with $\bar S(r')\subseteq\bar S(r)$ which induces the prolongation of the $\{\hat f_i\}$ by $\hat g$ up to monoidal transformations with empty centers: ``Let $\hat C$ be the center of $\hat g$. Then $\hat C$ is a reduced irreducible subscheme of $\hat V_0(r)$, which is contained in $\hat S(r)$. Since the point $x$ is a generic point of $\bar S(r)$, the image of $\hat S(r)$ in $\hat V_0$ is the unique closed point. Therefore, we can find a reduced irreducible subscheme $C$ of $V_0(r)$ such that $\hat C=c_r^{-1}(C)$. In fact, we take the smallest subscheme $C$ of $V_0(r)$ such that $\hat C=c_r^{-1}(C)$. We have $C\subseteq S(r)$. Hence $\dim(C)=n'<n$. We apply theorem I($n'$) to $V_0(r),V_1(r),\cdots,V_\beta(r),W(r)$, and $C$. Since $\hat C$ is non-singular and all the $\hat V_j(r)$ and $\hat W(r)$ are normally flat along $\hat C$, any succession of monoidal transformations which appears in the application of theorem I($n'$) induces in $\hat V_0(r)$ a succession of monoidal transformations with empty centers. Let $\{f_i,0\le i<r'-1\}$ be the prolongation of the $\{f_i,0\le i<r\}$ obtained by adding a succession in the above application of theorem I($n'$), and let $C(i+1)\to C(i)$ for $r\le i<r'-1$ be the succession of monoidal transformations induced by $f_i$, where $C(r)=C$. Let $f_{r'-1}\colon V_0(r')\to V_0(r'-1)$ be the monoidal transformation with center $C(r'-1)$. We can easily see that $\{f_i,0\le i<r'\}$ is a prolongation of the $\{f_i,0\le i<r\}$ satisfying (1), (2) and (3), and that it induces the prolongation of the $\{\hat f_i\}$ by $\hat g$ except for the $(r'-r-1)$ monoidal transformations with empty centers which should precede $\hat g$.'' (pp.~175--176.) -/)
  (proof := /-- In the printed order: $\hat C\subseteq\hat S(r)=c_r^{-1}(S(r))$; the points of $\hat S(r)$ lie over $x$ (\cref{lem:I.3-fibre-over-generic-point}); $C$ is the smallest subscheme with $\hat C=c_r^{-1}(C)$, reduced irreducible, $C\subseteq S(r)$ and $\dim C=n'<n$ (\cref{lem:I.3-dim-C-lt-n}); Main Theorem~I($n'$) applied to $(V_0(r),\dots,V_\beta(r),W(r);C)$; the centers of the resulting succession avoid the range of $c_r$ (\cref{lem:I.3-centers-avoid}); $C(k)\subseteq S(r+k)$ and the last center $C(r'-1)$ (\cref{lem:I.3-C-in-S}, \cref{lem:I.3-C-strict-transform-irreducible}); the new prolongation satisfies (1), (2), (3) (\cref{lem:I.3-main-123-of-snoc}) and induces $\hat g$ up to empty centers (the comparison of two monoidal transformations of $\hat V_0(r)$ with the same center, by the universal property). -/)
  (latexEnv := "lemma")]
theorem exists_prolongation_step [Hironaka.HironakaCitedResults.{u}] {n : ℕ} (hlt : ∀ n' < n, MainTheorem.I.{u} n') (hW : W.IsReduced)
    (hWn : W.dim = (n : WithBot ℕ∞)) (hWV : ∀ j, W.IsContainedIn (V j)) (x : V₀) (T : Set V₀) (hT : IsClosed T)
    (hx : IsGenericPointOfComponent T x) {Y : Scheme.{u}} (s : MonoidalSuccession V₀ Y)
    (hs : s.IsMain123 (mainSystem V) W) (hsT : s.mainImage (mainSystem V) W ⊆ T)
    (Bh : Subscheme (s.baseChangeTarget (AB.c0 V₀ x)))
    (gh : MonoidalTransformation (s.baseChangeTarget (AB.c0 V₀ x)) Bh)
    (hstep : Subscheme.IsMainStep
      (fun j => Subscheme.totalTransform (s.baseChangeMap (AB.c0 V₀ x)) (s.strictTransform (mainSystem V j)))
      (Subscheme.totalTransform (s.baseChangeMap (AB.c0 V₀ x)) (s.strictTransform W)) Bh) :
    ∃ (Y' : Scheme.{u}) (t : MonoidalSuccession Y Y'),
      (s.append t).IsMain123 (mainSystem V) W ∧
      (s.append t).mainImage (mainSystem V) W ⊆ s.mainImage (mainSystem V) W ∧
      ∃ e : (s.append t).baseChangeTarget (AB.c0 V₀ x) ≅ gh.X',
        (∀ j, Subscheme.totalTransform ((s.append t).baseChangeMap (AB.c0 V₀ x))
            ((s.append t).strictTransform (mainSystem V j)) =
          Subscheme.totalTransform e.hom (Subscheme.strictTransform gh
            (Subscheme.totalTransform (s.baseChangeMap (AB.c0 V₀ x)) (s.strictTransform (mainSystem V j))))) ∧
        Subscheme.totalTransform ((s.append t).baseChangeMap (AB.c0 V₀ x)) ((s.append t).strictTransform W) =
          Subscheme.totalTransform e.hom (Subscheme.strictTransform gh
            (Subscheme.totalTransform (s.baseChangeMap (AB.c0 V₀ x)) (s.strictTransform W))) := by
  classical
  have hWV' := mainSystem_isContainedIn V W hWV
  have hYalg : IsAlgebraicScheme Y := s.isAlgebraicScheme_target
  have hnoe := IsAlgebraicScheme.isNoetherian V₀
  have hprop := s.isProper_composite
  have hH := s.isPullback_baseChange (AB.c0 V₀ x)
  set ĉ := s.baseChangeMap (AB.c0 V₀ x) with hĉ
  set ĝ' := (s.baseChangeSucc (AB.c0 V₀ x)).composite with hĝ'
  let U : Fin (β + 1) → Subscheme Y := fun j => s.strictTransform (mainSystem V j)
  let W₁ : Subscheme Y := s.strictTransform W
  have hWU : ∀ j, W₁.IsContainedIn (U j) := fun j =>
    MonoidalSuccession.isContainedIn_strictTransform s (hWV' j)
  by_cases hBe : Bh = Subscheme.empty
  · -- an empty center: the prolongation is empty
    obtain ⟨e, he⟩ := exists_iso_step_of_eq_empty x s Bh gh hBe
    refine ⟨Y, MonoidalSuccession.nil Y, ?_, ?_, e, fun j => ?_, ?_⟩
    · rw [AB.succession_append_nil]; exact hs
    · rw [AB.succession_append_nil]
    · rw [MonoidalSuccession.strictTransform_append]; exact he _
    · rw [MonoidalSuccession.strictTransform_append]; exact he _
  · obtain ⟨⟨hBc, hBW⟩, h2, h3⟩ := hstep
    rcases hBc with hBem | ⟨hns, hirr⟩
    · exact absurd hBem hBe
    have hred : Bh.IsReduced := Subscheme.isReduced_of_isNonsingular hns
    -- "Ĉ is contained in Ŝ(r)"
    have hmuT := Subscheme.mainUnresolved_totalTransform_of_isPullback_completion x s.composite ĉ ĝ' hH U W₁ hWU
    have hSub : ∀ ŷ ∈ Bh.pts, ĉ.base ŷ ∈ Subscheme.mainUnresolved U W₁ := by
      intro ŷ hŷ
      have hmem : ŷ ∈ Subscheme.mainUnresolved (fun j => Subscheme.totalTransform ĉ (U j))
          (Subscheme.totalTransform ĉ W₁) := ⟨pts_subset_of_isContainedIn hBW hŷ, h2 ŷ hŷ⟩
      rw [hmuT] at hmem
      exact hmem
    -- "the image of Ŝ(r) in V̂₀ is the unique closed point"
    have hfib : ∀ ŷ ∈ Bh.pts, s.composite.base (ĉ.base ŷ) = x := fun ŷ hŷ =>
      g_eq_of_mem_preimage x s.composite ĉ ĝ' hH.w (s.mainUnresolvedAt (mainSystem V) W) T hT hx hsT
        (hSub ŷ hŷ)
    -- "we take the smallest subscheme C of V₀(r) such that Ĉ = c_r⁻¹(C)"
    obtain ⟨C, hCred, hCirr, hCtt, hCpts, -⟩ :=
      exists_reduced_irreducible_totalTransform_eq x s.composite ĉ ĝ' hH Bh hred hirr hfib
    have hBne : Bh.pts.Nonempty := by
      by_contra h
      exact hBe (Subscheme.eq_empty_of_pts_eq_empty (Set.not_nonempty_iff_eq_empty.mp h))
    have hCne : C.pts.Nonempty := by
      rw [hCpts]
      exact (hBne.image _).mono subset_closure
    have hSclosed := Subscheme.isClosed_mainUnresolved U W₁ hWU
    have hCS : C.pts ⊆ Subscheme.mainUnresolved U W₁ := by
      rw [hCpts]
      exact closure_minimal (fun y ⟨ŷ, hŷ, hy⟩ => hy ▸ hSub ŷ hŷ) hSclosed
    have hCW : C.IsContainedIn W₁ := Subscheme.isContainedIn_of_pts_subset hCred (fun y hy => (hCS hy).1)
    -- "We have C ⊆ S(r). Hence dim(C) = n' < n."
    obtain ⟨n', hn'dim, hn'lt⟩ := s.exists_dim_eq_lt_of_pts_subset_mainUnresolvedAt (mainSystem V) W hW
      hWV' hWn C hCne hCS
    -- "We apply theorem I(n') to V₀(r), V₁(r), …, V_β(r), W(r), and C."
    let Vs : Fin β → Subscheme Y := fun j => s.strictTransform (V j)
    let V' : Fin (β + 1) → Subscheme Y := Fin.snoc (α := fun _ => Subscheme Y) Vs W₁
    have hsys : mainSystem V' = (Fin.snoc (α := fun _ => Subscheme Y) U W₁ : Fin (β + 1 + 1) → Subscheme Y) := by
      have hU : U = mainSystem Vs := mainSystem_strictTransform_succession s V
      rw [hU]
      exact Fin.cons_snoc_eq_snoc_cons _ _ _
    have hCV'' : ∀ j, C.IsContainedIn
        ((Fin.snoc (α := fun _ => Subscheme Y) U W₁ : Fin (β + 1 + 1) → Subscheme Y) j) := by
      intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa using hCW
      · simpa using hCW.trans (hWU i)
    have hCV : ∀ j, C.IsContainedIn (V' j) := by
      intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa [V'] using hCW
      · have := hCW.trans (MonoidalSuccession.isContainedIn_strictTransform s (hWV i))
        simpa [V', Vs] using this
    obtain ⟨Y', s', hs'⟩ := hlt n' hn'lt Y (β + 1) V' C hCred hn'dim hCV
    have h123 := hs'.1
    have h4 := hs'.2
    unfold MonoidalSuccession.IsMain4 at h4
    rw [hsys] at h123 h4
    -- the centers of s' avoid the range of c_r
    have hRes : ∀ y ∈ C.pts, y ∈ Set.range ĉ.base →
        Subscheme.IsMainResolvedAt (Fin.snoc (α := fun _ => Subscheme Y) U W₁ : Fin (β + 1 + 1) → Subscheme Y) C y := by
      rintro y hy ⟨ŷ, rfl⟩
      have hŷ : ŷ ∈ Bh.pts := by
        rw [← hCtt, FlatPreimm.pts_totalTransform]; exact hy
      refine ⟨?_, fun j => ?_⟩
      · refine (Subscheme.isSimpleAt_totalTransform_iff_of_isPullback_completion x s.composite ĉ ĝ' hH
          C ŷ).mp ?_
        rw [hCtt]
        exact ⟨hŷ, Subscheme.isRegular_stalk_quot Bh hns hŷ⟩
      · refine (Subscheme.isNormallyFlatAlongAt'_totalTransform_iff_of_isPullback_completion x s.composite
          ĉ ĝ' hH _ C (hCV'' j) ŷ).mp ?_
        rw [hCtt]
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa using (h3 ŷ hŷ).2
        · simpa using (h3 ŷ hŷ).1 i
    have hAvoid : s'.CentersAvoid (Set.range ĉ.base) :=
      MonoidalSuccession.centersAvoid_of_isMain123 s' _ C hCV'' h123 _ hRes
    -- the final center C(r' - 1)
    have hirr' := MonoidalSuccession.isReduced_and_isIrreducible_strictTransform s' _ C hCV'' hCred hCirr h123
    obtain ⟨hCfns, hCfnf⟩ := h4
    obtain ⟨tfin⟩ : Nonempty (MonoidalTransformation Y' (s'.strictTransform C)) :=
      ⟨(MonoidalTransformation.exists_isProper Y' (s'.strictTransform C)).choose⟩
    have hCfS := MonoidalSuccession.pts_strictTransform_subset_mainUnresolved s' U W₁ hWU C hCW hCS
    have hstepf : Subscheme.IsMainStep (fun j => s'.strictTransform (U j)) (s'.strictTransform W₁)
        (s'.strictTransform C) := by
      refine ⟨⟨Or.inr ⟨hCfns, hirr'.2⟩, MonoidalSuccession.isContainedIn_strictTransform s' hCW⟩,
        fun y hy => (hCfS hy).2, fun y hy => ⟨fun j => ?_, ?_⟩⟩
      · simpa using hCfnf (Fin.castSucc j) y hy
      · simpa using hCfnf (Fin.last _) y hy
    -- the prolongation t = s' followed by the monoidal transformation with center C(r'-1)
    have ht123 : (s'.append (MonoidalSuccession.cons (s'.strictTransform C) tfin
        (MonoidalSuccession.nil tfin.X'))).IsMain123 U W₁ := by
      refine (MonoidalSuccession.isMain123With_append _ s' _ U W₁).mpr
        ⟨MonoidalSuccession.isMain123_of_snoc s' U W₁ hWU C hCW hCS h123, ?_⟩
      exact ⟨hstepf, trivial⟩
    have hsapp := (MonoidalSuccession.isMain123With_append _ s
      (s'.append (MonoidalSuccession.cons (s'.strictTransform C) tfin (MonoidalSuccession.nil tfin.X')))
      (mainSystem V) W).mpr ⟨hs, ht123⟩
    obtain ⟨e, he⟩ := exists_iso_step_of_centersAvoid x s s' hAvoid C Bh hCtt gh tfin
    refine ⟨tfin.X', _, hsapp, MonoidalSuccession.mainImage_append_subset s _ (mainSystem V) W hWV' ht123,
      e, fun j => ?_, ?_⟩
    · rw [MonoidalSuccession.strictTransform_append]; exact he _
    · rw [MonoidalSuccession.strictTransform_append]; exact he _

/-- p. 175: "Therefore, we have only to show that any prolongation of `{f̂_i}` satisfying (1), (2) and (3) can be induced
(possibly when we modify it by adding a suitable number of monoidal transformations with empty centers before each of
the given monoidal transformations) by a prolongation of `{f_i}` satisfying (1), (2) and (3).  It suffices to consider
the case in which the prolongation of `{f̂_i}` is obtained by adding a single monoidal transformation": induction on the
length `ℓ` of the prolongation of `{f̂_i}` (`Reach4 ℓ`) using `exists_prolongation_step`; for `ℓ = 0`, `Ŝ = ∅`, i.e.
`x ∉ S̄`. -/
@[blueprint "lem:I.3-main-I-reach4"
  (statement := /-- p.~175: ``Therefore, we have only to show that any prolongation of $\{\hat f_i\}$ satisfying (1), (2) and (3) can be induced (possibly when we modify it by adding a suitable number of monoidal transformations with empty centers before each of the given monoidal transformations) by a prolongation of $\{f_i\}$ satisfying (1), (2) and (3). It suffices to consider the case in which the prolongation of $\{\hat f_i\}$ is obtained by adding a single monoidal transformation.'' Precisely: if the completed data reach (4) after $\ell$ monoidal transformations (\cref{def:I.3-reach4}), then there is a prolongation of $\{f_i\}$ satisfying (1), (2), (3) with $\bar S(r')\subseteq\bar S(r)$ and $x\notin\bar S(r')$. -/)
  (proof := /-- Induction on $\ell$ using the step (\cref{lem:I.3-main-I-step}), transporting the rest of the prolongation of $\{\hat f_i\}$ along the isomorphism of the step (\cref{lem:I.3-reach4-of-iso}); for $\ell=0$ the completed $\hat S(r)$ is empty, i.e.\ $x\notin\bar S(r)$. -/)
  (latexEnv := "lemma")]
theorem exists_not_mem_mainImage_of_reach4 [Hironaka.HironakaCitedResults.{u}] {n : ℕ} (hlt : ∀ n' < n, MainTheorem.I.{u} n') (hW : W.IsReduced)
    (hWn : W.dim = (n : WithBot ℕ∞)) (hWV : ∀ j, W.IsContainedIn (V j)) (x : V₀) (T : Set V₀) (hT : IsClosed T)
    (hx : IsGenericPointOfComponent T x) (ℓ : ℕ) :
    ∀ {Y : Scheme.{u}} (s : MonoidalSuccession V₀ Y), s.IsMain123 (mainSystem V) W →
      s.mainImage (mainSystem V) W ⊆ T →
      Reach4 ℓ (s.baseChangeTarget (AB.c0 V₀ x))
        (fun j => Subscheme.totalTransform (s.baseChangeMap (AB.c0 V₀ x)) (s.strictTransform (mainSystem V j)))
        (Subscheme.totalTransform (s.baseChangeMap (AB.c0 V₀ x)) (s.strictTransform W)) →
      ∃ (Y' : Scheme.{u}) (t : MonoidalSuccession Y Y'), (s.append t).IsMain123 (mainSystem V) W ∧
        (s.append t).mainImage (mainSystem V) W ⊆ s.mainImage (mainSystem V) W ∧
        x ∉ (s.append t).mainImage (mainSystem V) W := by
  have hWV' := mainSystem_isContainedIn V W hWV
  induction ℓ with
  | zero =>
    intro Y s hs hsT hreach
    refine ⟨Y, MonoidalSuccession.nil Y, ?_, ?_, ?_⟩
    · rw [AB.succession_append_nil]; exact hs
    · rw [AB.succession_append_nil]
    · rw [AB.succession_append_nil]
      rintro ⟨z, hz, hzx⟩
      have hcloc := IsAlgebraicScheme.isNoetherian V₀
      have := s.isProper_composite
      have h4 : Subscheme.IsMain4Data
          (fun j => Subscheme.totalTransform (s.baseChangeMap (AB.c0 V₀ x)) (s.strictTransform (mainSystem V j)))
          (Subscheme.totalTransform (s.baseChangeMap (AB.c0 V₀ x)) (s.strictTransform W)) := hreach
      rw [Subscheme.isMain4Data_iff_mainUnresolved_eq_empty,
        Subscheme.mainUnresolved_totalTransform_of_isPullback_completion x s.composite _
          (s.baseChangeSucc (AB.c0 V₀ x)).composite (s.isPullback_baseChange (AB.c0 V₀ x))
          (fun j => s.strictTransform (mainSystem V j)) (s.strictTransform W)
          (fun j => MonoidalSuccession.isContainedIn_strictTransform s (hWV' j))] at h4
      obtain ⟨p, hp⟩ := exists_c0_eq V₀ x
      obtain ⟨ŷ, hŷ, -⟩ := exists_eq_of_isPullback (s.isPullback_baseChange (AB.c0 V₀ x)) z p
        (by rw [hzx, hp])
      have hmem : ŷ ∈ (s.baseChangeMap (AB.c0 V₀ x)).base ⁻¹' Subscheme.mainUnresolved
          (fun j => s.strictTransform (mainSystem V j)) (s.strictTransform W) := by
        rw [Set.mem_preimage, hŷ]
        exact hz
      rw [h4] at hmem
      exact hmem
  | succ ℓ ih =>
    intro Y s hs hsT hreach
    obtain ⟨Bh, gh, hstep, hrest⟩ := hreach
    obtain ⟨Y', t, ht, htimg, e, hV, hW'⟩ := exists_prolongation_step V W hlt hW hWn hWV x T hT hx s hs hsT
      Bh gh hstep
    have hsub : ∀ j, (Subscheme.totalTransform (s.baseChangeMap (AB.c0 V₀ x)) (s.strictTransform W)).IsContainedIn
        (Subscheme.totalTransform (s.baseChangeMap (AB.c0 V₀ x)) (s.strictTransform (mainSystem V j))) :=
      fun j U => FlatPreimm.totalTransform_mono _ (fun U => MonoidalSuccession.isContainedIn_strictTransform s (hWV' j) U) U
    have hrest' := Reach4.of_iso ℓ e _ _ _ _
      (fun j => Subscheme.IsContainedIn.strictTransform gh (hsub j)) hV hW' hrest
    obtain ⟨Y'', t₂, h1, h2, h3⟩ := ih (s.append t) ht (htimg.trans hsT) hrest'
    refine ⟨Y'', t.append t₂, ?_, ?_, ?_⟩
    · rw [← AB.succession_append_assoc]; exact h1
    · rw [← AB.succession_append_assoc]; exact h2.trans htimg
    · rw [← AB.succession_append_assoc]; exact h3

/-- **(P)** (p. 174): the improvement of a succession satisfying (1), (2), (3) with `S(r) ≠ ∅`: "the image of `S(r′)` in
`V₀` is different from (but always contained in) that of `S(r)`".  Take a generic point `x` of `S̄(r)` (closed, p. 174),
`V̂₀ = Spec(Ô_{V₀,x})`; the completed data satisfy (1̂), (2), (3) and `Ŝ(r) = c_r⁻¹(S(r))` (`CompletionResolved`); `V̂₀` is
embedded in a non-singular ambient scheme and the previous result gives a prolongation of `{f̂_i}` reaching (4)
(`exists_reach4_of_hat`); `exists_not_mem_mainImage_of_reach4` induces it. -/
@[blueprint "lem:I.3-main-I-prolongation"
  (statement := /-- The assertion (P) of p.~174: ``if $f_i\colon V_0(i+1)\to V_0(i)$ for $0\le i<r$ is any succession of monoidal transformations with centers $B_i$ in $V_0(i)$, where $V_0(0)=V_0$, which satisfy the conditions (1), (2) and (3) for all $i$; and if $S(r)$ denotes the closed subset of $W(r)$ complementary to the set of those simple points of $W(r)$ at which all the $V_j(r)$ for $0\le j\le\beta$ are normally flat along $W(r)$, then we can find a prolongation of the succession, say $f_i\colon V_0(i+1)\to V_0(i)$ for $0\le i\le r'$ for some $r'$ ($>r$), such that the image of $S(r')$ in $V_0$ is different from (but always contained in) that of $S(r)$, provided $S(r)$ is not empty.'' (Assuming Main Theorem~I($n'$) for $n'<n$.) -/)
  (proof := /-- Take a generic point $x$ of $\bar S(r)$ (closed, \cref{lem:I.3-main-image-closed}) and $\hat V_0=\operatorname{Spec}\hat{\mathcal O}_{V_0,x}$; the completed data satisfy (1), (2), (3) and $\hat S(r)=c_r^{-1}(S(r))$ (property (ii) of the class $\mathfrak B$, flat base change); $\hat V_0$ embeds in a non-singular scheme (footnote 37), so the previous result (\cref{def:I.3-main-I-ambient-statement}) gives a prolongation of $\{\hat f_i\}$ reaching (4) (\cref{def:I.3-reach4}); \cref{lem:I.3-main-I-reach4} induces it, so $x\notin\bar S(r')\subseteq\bar S(r)$. -/)
  (latexEnv := "lemma")]
theorem exists_prolongation [Hironaka.HironakaCitedResults.{u}] {n : ℕ} (hlt : ∀ n' < n, MainTheorem.I.{u} n') (hW : W.IsReduced)
    (hWn : W.dim = (n : WithBot ℕ∞)) (hWV : ∀ j, W.IsContainedIn (V j)) {Y : Scheme.{u}}
    (s : MonoidalSuccession V₀ Y) (hs : s.IsMain123 (mainSystem V) W)
    (hne : (s.mainUnresolvedAt (mainSystem V) W).Nonempty) :
    ∃ (Y' : Scheme.{u}) (t : MonoidalSuccession Y Y'), (s.append t).IsMain123 (mainSystem V) W ∧
      (s.append t).mainImage (mainSystem V) W ⊂ s.mainImage (mainSystem V) W := by
  have hWV' := mainSystem_isContainedIn V W hWV
  obtain ⟨hSc, hSW⟩ := MonoidalSuccession.isClosed_mainImage s (mainSystem V) W hWV'
  have hSne : (s.mainImage (mainSystem V) W).Nonempty := hne.image _
  obtain ⟨x, hx⟩ := exists_isGenericPointOfComponent hSc hSne
  have hxS : x ∈ s.mainImage (mainSystem V) W := hx.1.2 (subset_closure rfl)
  -- the completed data and the previous result (footnote 37)
  have hWred : (Subscheme.totalTransform (AB.c0 V₀ x) W).IsReduced := by
    exact (MonoidalSuccession.nil V₀).isReduced_strictTransform_baseChangeSucc x W hW
  obtain ⟨ℓ, hℓ⟩ := exists_reach4_of_hat (fun N n h => IAmbient_of_lt h) x (s.baseChangeSucc (AB.c0 V₀ x))
    (fun j => Subscheme.totalTransform (AB.c0 V₀ x) (mainSystem V j))
    (Subscheme.totalTransform (AB.c0 V₀ x) W) hWred
    (fun j U => FlatPreimm.totalTransform_mono _ (fun U => hWV' j U) U)
    (MonoidalSuccession.isMain123Hat_baseChangeSucc x s (mainSystem V) W hWV' hs)
  simp only [MonoidalSuccession.strictTransform_baseChangeSucc] at hℓ
  obtain ⟨Y', t, h1, h2, h3⟩ := exists_not_mem_mainImage_of_reach4 V W hlt hW hWn hWV x _ hSc hx ℓ s hs
    subset_rfl hℓ
  exact ⟨Y', t, h1, h2, fun h => h3 (h hxS)⟩

end Step

/-- **Main Theorem I(n)** for all `n` (pp. 174–176): induction on `n`; `n = 0` is the empty succession
(`I_zero`); the induction step is (P) (`exists_prolongation`) and the descending chain of closed subsets of `V₀`
(`exists_isMainI_of_improve`). -/
@[blueprint "thm:I.3-main-I"
  (statement := /-- \textbf{Main Theorem I($n$).} Let $V_0$ be an arbitrary algebraic scheme, $V_j$ ($1\le j\le\beta$)
    a finite number of subschemes of $V_0$, and $W$ a reduced subscheme of $V_0$ of dimension $n$ which is contained in
    $\bigcap_{j=1}^\beta V_j$. Then there exists a finite succession of monoidal transformations
    $\{f_i\colon V_0(i+1)\to V_0(i)\}$ with centers $B_i$ in $V_0(i)$ for $0\le i<r$, where $V_0(0)=V_0$, such that if
    $\{V_j(i+1)\to V_j(i)\}$ and $\{W(i+1)\to W(i)\}$ are the monoidal transformations induced by $f_i$, where
    $V_j(0)=V_j$ and $W(0)=W$, then (1) $B_i$ is a non-singular irreducible subscheme of $W(i)$; (2) $B_i$ does not contain
    any simple point of $W(i)$ at which all the $V_j(i)$ for $0\le j\le\beta$ are normally flat along $W(i)$; (3) all
    the $V_j(i)$ ($0\le j\le\beta$) and $W(i)$ are normally flat along $B_i$; and finally (4) $W(r)$ is non-singular and
    all the $V_j(r)$ for $0\le j\le\beta$ are normally flat along $W(r)$. (p.~174.) -/)
  (proof := /-- Induction on $n$. For $n=0$ the empty succession does. For $n>0$ it suffices to show that any succession
    satisfying (1), (2), (3) with $S(r)\neq\emptyset$ has a prolongation satisfying (1), (2), (3) whose image
    $\bar S(r')$ is strictly contained in $\bar S(r)$; then the descending chain of closed subsets of $V_0$ ends with
    $S(r)=\emptyset$, i.e.\ (4). Take a generic point $x$ of $\bar S(r)$ and the completion $\hat V_0=\operatorname{Spec}
    \hat{\mathcal O}_{V_0,x}$; by the property (ii) of the class $\mathfrak B$ the completed data satisfy $\hat S(r)=
    c_r^{-1}(S(r))$ and (1), (2), (3); $\hat V_0$ embeds in a non-singular scheme (footnote 37) so that the previous result
    gives a prolongation of $\{\hat f_i\}$ reaching (4); it is induced by a prolongation of $\{f_i\}$, one monoidal
    transformation $\hat g$ at a time, by applying I($n'$) to the smallest $C\subseteq S(r)$ with $\hat C=c_r^{-1}(C)$. -/)
  (latexEnv := "theorem")]
theorem I_all [Hironaka.HironakaCitedResults.{u}] (n : ℕ) : MainTheorem.I.{u} n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact I_zero
    · intro V₀ _ β V W hW hWn hWV
      exact exists_isMainI_of_improve V W hWV fun Y s hs hne =>
        exists_prolongation V W ih hW hWn hWV s hs hne

end MainTheorem

end Hironaka
