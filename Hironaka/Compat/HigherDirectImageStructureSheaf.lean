/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Architect
public import Hironaka.Ch1.ResolutionData
public import Hironaka.Compat.FunctionFieldMap
public import Hironaka.Compat.LocalizeSuccession
public import Hironaka.Compat.NowhereDenseCenters
public import Hironaka.Compat.StalkPrimitive
public import Hironaka.Compat.LerayEdgeSchemes
public import Hironaka.Statements

/-!
# Higher direct images of the structure sheaf (Ch. 0 §5, consequence (2) of Corollary 1, p. 145)

> (2) Let us suppose that `(X₁, θ₁)` dominates `(X₂, θ₂)` and that both `X₁` and `X₂` are non-singular.  Let `f` be the
> rational application of `(X₁, θ₁)` to `(X₂, θ₂)`, which is a morphism of `X₁` to `X₂`.  Then the direct images
> `Rⁱf(O_{X₁})` of `O_{X₁}` by `f` are zero sheaves on `X₂` except `R⁰f(O_{X₁})` which is `O_{X₂}`.  (In fact, it follows
> from the same result for a monoidal transformation of a non-singular algebraic `B`-scheme with non-singular center,
> and from (1) applied twice.)  (p. 145)

This module holds the part of the argument that is independent of the function-field pairs:

* the vocabulary: `Rⁱf_*(O_X)` is the `i`-th right derived functor of `f_* : X.Modules ⥤ Y.Modules` at `O_X`
  (`higherDirectImageStructure`), and `O_Y → f_*O_X` is the comorphism of `f` (`structureUnit`);
* **one cited leaf**, stated by the paper without proof or citation (assumed, as in the paper): the single blow-up case
  (`MonoidalTransformation.higherDirectImage_structureSheaf`);
* **one gap filled (tacit in the paper), proved**: the derived-functor facts that the argument uses tacitly, packaged as
  the existence of Leray edge maps with three properties (`exists_lerayEdge`). The paper does not state them, so they are
  proved, not assumed: general homological algebra (flasque modules, `Hironaka.Compat.FlasqueModules`; abstract edge
  maps of the Grothendieck spectral sequence, `Hironaka.Compat.LerayEdgeAbstract`; their instance for direct images,
  `Hironaka.Compat.LerayEdgeSchemes`);
* the extension of the single blow-up case to a succession of monoidal transformations (induction using the edge maps);
* the retract argument "from (1) applied twice" (`higherDirectImage_structureSheaf_of_dominating`), written against two
  successions as explicit arguments, so that (1) can be imported later.

Nothing is stated about the pairs `(X, θ)` here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}



theorem Hom.structureUnit_app (f : X ⟶ Y) (U : Y.Opens) (x : Γ(Y, U)) :
    ((f.structureUnit).app U) x = f.app U x := rfl

/-- The comorphisms are functorial: `O_Z → (f ≫ g)_*O_X` is `O_Z → g_*O_Y → g_*f_*O_X`. -/
theorem Hom.structureUnit_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).structureUnit = g.structureUnit ≫ (Modules.pushforward g).map f.structureUnit ≫
      (Modules.pushforwardComp f g).hom.app X.structureModule := by
  refine Modules.hom_ext _ _ fun U => ?_
  ext x
  rfl

end AlgebraicGeometry.Scheme

namespace Hironaka

section Vocabulary

variable {X Y Z : Scheme.{u}}


/-- The higher derived functors of the identity (direct image along `𝟙 X`) vanish in positive degrees. -/
theorem isZero_rightDerived_pushforward_id (F : X.Modules) {i : ℕ} (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward (𝟙 X)).rightDerived i).obj F) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  let I := InjectiveResolution.of F
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj (Scheme.Modules.pushforward (𝟙 X)) (n + 1))
  have e := (NatIso.mapHomologicalComplex (Scheme.Modules.pushforwardId X)
    (ComplexShape.up ℕ)).app I.cocomplex
  exact (HomologicalComplex.ExactAt.of_iso (I.cocomplex_exactAt_succ n) e.symm).isZero_homology

end Vocabulary

section Cited

variable {X : Scheme.{u}}


/-- **Cited: the single blow-up case of consequence (2), p. 145** (used without proof or citation; assumed, as in the
paper).  Let `B` be a field of characteristic zero, `X` a non-singular algebraic `B`-scheme (`p : X ⟶ Spec B` of finite
type) and `π : X' → X` a monoidal transformation of `X` with non-singular center `D` that is nowhere dense in `X`.  Then `Rⁱπ_*O_{X'} = 0` for `i > 0`, and `π_*O_{X'} = O_X`, i.e. the comorphism
`O_X → π_*O_{X'}` is an isomorphism (so that `R⁰π_*O_{X'} = O_X`).

Paper: "(In fact, it follows from the same result for a monoidal transformation of a non-singular algebraic
`B`-scheme with non-singular center, and from (1) applied twice.)" (p. 145).  The hypothesis "nowhere dense" is the
hypothesis of p. 144 under which monoidal transformations of pairs `(X, θ)` are considered ("a monoidal transformation
with center nowhere dense in `X`"). -/
@[blueprint "thm:0.5-direct-image-monoidal-transformation"
  (statement := /-- Let $B$ be a field of characteristic zero, $X$ a non-singular algebraic $B$-scheme and
    $f\colon X'\to X$ a monoidal transformation of $X$ with non-singular center $D$ nowhere dense in $X$.  Then $R^i f_*(\mathcal O_{X'})=0$ for $i>0$ and
    $f_*\mathcal O_{X'}=\mathcal O_X$.  (p.~145.) -/)
  (proof := /-- Cited, not proved in the paper: ``it follows from the same result for a monoidal transformation of a
    non-singular algebraic $B$-scheme with non-singular center'' (p.~145).  Used without proof or citation; assumed,
    as in the paper. -/)
  (latexEnv := "theorem")]
theorem MonoidalTransformation.higherDirectImage_structureSheaf [Hironaka.Cited.MonoidalTransformationHigherDirectImageStructureSheaf.{u}] :
    ∀ {B : Type u} [Field B] [CharZero B]
    (p : X ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType p] [QuasiCompact p] (hX : X.IsNonsingular) {D : Subscheme X} (hD : D.IsNonsingular) (hnd : interior D.pts = ∅)
    (t : MonoidalTransformation X D),
    (∀ i, 0 < i → IsZero (higherDirectImageStructure t.f i)) ∧ IsIso t.f.structureUnit :=
  @Hironaka.Cited.MonoidalTransformationHigherDirectImageStructureSheaf.higherDirectImage_structureSheaf _ X

/-- **Leray edge maps: gap filled (tacit in the paper), proved** (the derived-functor facts tacitly used by "(1) applied
twice", p. 145).  The paper does not state them; they are a gap filled by a proof, not an assumption.  For morphisms
`f : X ⟶ Y`, `g : Y ⟶ Z` and an `O_X`-module `F` there are the edge maps of the Leray spectral
sequence `E₂^{p,q} = Rᵖg_*(R^q f_* F) ⇒ R^{p+q}(f ≫ g)_* F`,
`ε f g F i : Rⁱg_*(f_*F) ⟶ Rⁱ(f ≫ g)_*F`, with the three properties used:

* naturality in `F`;
* `ε f g F i` is an isomorphism for all `i` when `R^q f_*F = 0` for all `q > 0` (the spectral sequence degenerates);
* compatibility with composition: for `f₁, f₂, f₃` the two ways of passing from `R^i f₃_*((f₁ ≫ f₂)_*F)` to
  `R^i(f₁ ≫ f₂ ≫ f₃)_*F` agree.

Proof: `ε f g F i` is `Scheme.Modules.pushforwardLerayEdge`, the abstract edge map `Functor.lerayEdge` for `f_*`, `g_*`
transported along `f_* ⋙ g_* ≅ (f ≫ g)_*`.  With `I` an injective resolution of `F`, `J` one of `f_*F`, and a
monomorphic quasi-isomorphism `β : f_*I ⟶ K` to a complex of injectives, `ε` is `Hⁱ(g_*α) ≫ Hⁱ(g_*β)⁻¹` for the unique
(up to homotopy) `α : J ⟶ K` compatible with the augmentations; `Hⁱ(g_*β)` is invertible because injective modules
are flasque, `f_*` preserves flasque modules and flasque modules are `g_*`-acyclic (Hartshorne III.2.4, II Ex. 1.16).
Nothing stronger is used.  (Hartshorne, III, Ex. 8.1; Godement; Grothendieck, Tôhoku.) -/
@[blueprint "thm:0.5-leray-edge-maps"
  (statement := /-- Leray edge maps $\varepsilon_{f,g,F}\colon R^ig_*(f_*F)\to R^i(g\circ f)_*F$ exist, natural in
    $F$, compatible with composition of three morphisms, and are isomorphisms for all $i$ when $R^qf_*F=0$ for $q>0$. -/)
  (proof := /-- Gap filled (tacit in the paper), proved.  Used tacitly in ``(1) applied twice'' (p.~145) and not
    stated in the paper.  With $I$ an injective resolution of $F$, $J$ one of $f_*F$ and a monomorphic
    quasi-isomorphism $\beta\colon f_*I\to K$ to a complex of injectives, $\varepsilon=H^i(g_*\alpha)\circ
    H^i(g_*\beta)^{-1}$ for the map $\alpha\colon J\to K$, unique up to homotopy, compatible with the
    augmentations; $H^i(g_*\beta)$ is invertible since injective modules are flasque, $f_*$ preserves flasque modules
    and flasque modules are $g_*$-acyclic.  The three properties follow from the uniqueness of $\alpha$. -/)
  (latexEnv := "theorem")]
theorem exists_lerayEdge :
    ∃ ε : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Modules) (i : ℕ),
        ((Scheme.Modules.pushforward g).rightDerived i).obj ((Scheme.Modules.pushforward f).obj F) ⟶
          ((Scheme.Modules.pushforward (f ≫ g)).rightDerived i).obj F,
      (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {F F' : X.Modules} (φ : F ⟶ F') (i : ℕ),
        ((Scheme.Modules.pushforward g).rightDerived i).map ((Scheme.Modules.pushforward f).map φ) ≫
            ε f g F' i =
          ε f g F i ≫ ((Scheme.Modules.pushforward (f ≫ g)).rightDerived i).map φ) ∧
      (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Modules),
        (∀ q, 0 < q → IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj F)) →
          ∀ i, IsIso (ε f g F i)) ∧
      (∀ {X Y Z T : Scheme.{u}} (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) (f₃ : Z ⟶ T) (F : X.Modules) (i : ℕ),
        ((Scheme.Modules.pushforward f₃).rightDerived i).map
            ((Scheme.Modules.pushforwardComp f₁ f₂).hom.app F) ≫ ε (f₁ ≫ f₂) f₃ F i =
          ε f₂ f₃ ((Scheme.Modules.pushforward f₁).obj F) i ≫ ε f₁ (f₂ ≫ f₃) F i) :=
  ⟨fun f g F i => Scheme.Modules.pushforwardLerayEdge f g F i,
    fun f g _ _ φ i => Scheme.Modules.pushforwardLerayEdge_naturality f g φ i,
    fun f g F hF i => Scheme.Modules.isIso_pushforwardLerayEdge f g F hF i,
    fun f₁ f₂ f₃ F i => Scheme.Modules.pushforwardLerayEdge_comp f₁ f₂ f₃ F i⟩

end Cited

section Units

variable {X Y : Scheme.{u}}

/-- The comorphism of the identity is an isomorphism. -/
instance isIso_structureUnit_id : IsIso (𝟙 X : X ⟶ X).structureUnit := by
  refine Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact Function.bijective_id

/-- For a morphism of integral schemes sending the generic point to the generic point, the comorphism
`O_Y → h_*O_X` is a monomorphism (sections of `O_Y` are determined by their germ at the generic point). -/
theorem mono_structureUnit [IsIntegral X] [IsIntegral Y] (h : X ⟶ Y)
    (hη : h (genericPoint X) = genericPoint Y) : Mono h.structureUnit := by
  refine Preadditive.mono_of_cancel_zero _ fun {Z} g hg => ?_
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  have hinj : Function.Injective (h.app U) := by
    by_cases hU : Nonempty U
    · have hmem : genericPoint Y ∈ U :=
        ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
      have key := germ_functionFieldMap h hη U hmem
      intro s s' hss'
      have hmap : functionFieldMap h hη (Y.presheaf.germ U (genericPoint Y) hmem s) =
          functionFieldMap h hη (Y.presheaf.germ U (genericPoint Y) hmem s') := by
        have e := congrArg (X.presheaf.germ (h ⁻¹ᵁ U) (genericPoint X)
          (show h (genericPoint X) ∈ U from hη ▸ hmem)) hss'
        exact (ConcreteCategory.congr_hom key s).trans
          (e.trans (ConcreteCategory.congr_hom key s').symm)
      exact germ_injective_of_isIntegral Y _ hmem
        ((functionFieldMap h hη).hom.injective hmap)
    · have := Scheme.subsingleton_sections_of_not_nonempty (X := Y) U hU
      exact fun s s' _ => Subsingleton.elim s s'
  ext x
  have h0 : h.app U ((g.app U) x) = 0 :=
    ConcreteCategory.congr_hom (congrArg (fun m => Scheme.Modules.Hom.app m U) hg) x
  exact hinj (h0.trans (map_zero _).symm)

end Units

section Succession

variable {X Y : Scheme.{u}}

/-- **Composition of the two conclusions.**  If `k : Y ⟶ X'` and `g : X' ⟶ X` both satisfy "`Rⁱ_*O = 0` for `i > 0`
and `O → _*O` is an isomorphism", then so does `k ≫ g` (Leray edge isomorphism for `k` and `g`). -/
theorem higherDirectImage_structureSheaf_comp {X' : Scheme.{u}} (k : Y ⟶ X') (g : X' ⟶ X)
    (hk : (∀ i, 0 < i → IsZero (higherDirectImageStructure k i)) ∧ IsIso k.structureUnit)
    (hg : (∀ i, 0 < i → IsZero (higherDirectImageStructure g i)) ∧ IsIso g.structureUnit) :
    (∀ i, 0 < i → IsZero (higherDirectImageStructure (k ≫ g) i)) ∧ IsIso (k ≫ g).structureUnit := by
  obtain ⟨ε, -, hε, -⟩ := exists_lerayEdge.{u}
  have hiso : ∀ i, IsIso (ε k g Y.structureModule i) := hε _ _ _ hk.1
  have := hk.2
  have := hg.2
  refine ⟨fun i hi => ?_, ?_⟩
  · have h1 : IsZero (((Scheme.Modules.pushforward g).rightDerived i).obj
        ((Scheme.Modules.pushforward k).obj Y.structureModule)) :=
      IsZero.of_iso (hg.1 i hi) (((Scheme.Modules.pushforward g).rightDerived i).mapIso
        (asIso k.structureUnit)).symm
    exact IsZero.of_iso h1 (asIso (ε k g Y.structureModule i)).symm
  · rw [Scheme.Hom.structureUnit_comp]
    infer_instance

/-- **The single blow-up case along a succession.**  For a succession of monoidal transformations with non-singular,
nowhere dense centers of a non-singular algebraic scheme, `Rⁱ(composite)_*O = 0` for `i > 0` and
`(composite)_*O = O` (induction on the length, using `higherDirectImage_structureSheaf_comp` and
`MonoidalTransformation.higherDirectImage_structureSheaf`). -/
theorem MonoidalSuccession.higherDirectImage_structureSheaf [Hironaka.HironakaCitedResults.{u}] [Hironaka.Cited.MonoidalTransformationHigherDirectImageStructureSheaf.{u}] {B : Type u} [Field B] [CharZero B]
    (s : MonoidalSuccession X Y) (p : X ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hX : X.IsNonsingular) (hs : s.HasNonsingularCenters) (hnd : s.NowhereDenseCenters) :
    (∀ i, 0 < i → IsZero (higherDirectImageStructure s.composite i)) ∧
      IsIso s.composite.structureUnit := by
  induction s with
  | nil X =>
    exact ⟨fun i hi => isZero_rightDerived_pushforward_id _ hi,
      (inferInstance : IsIso (𝟙 X : X ⟶ X).structureUnit)⟩
  | cons B' t rest ih =>
    have : IsLocallyNoetherian _ := LocallyOfFiniteType.isLocallyNoetherian p
    have := t.isProper
    have : LocallyOfFiniteType (t.f ≫ p) := inferInstance
    have : QuasiCompact (t.f ≫ p) := inferInstance
    obtain ⟨hX', -⟩ := t.isNonsingular_and_isNonsingular_exceptional hX hs.1
    rw [composite_cons]
    exact higherDirectImage_structureSheaf_comp _ _ (ih (t.f ≫ p) hX' hs.2 hnd.2)
      (t.higherDirectImage_structureSheaf p hX hs.1 hnd.1)

end Succession

section ZerothDirectImage

variable {X Y : Scheme.{u}}


/-- `R⁰f_*O_X = O_Y` (via the canonical map) iff `f_*O_X = O_Y`: the canonical map `f_*F → R⁰f_*F` is an isomorphism
for the left exact functor `f_*`. -/
theorem isIso_structureUnitR0_iff (f : X ⟶ Y) :
    IsIso (structureUnitR0 f) ↔ IsIso f.structureUnit := by
  have : IsIso ((Scheme.Modules.pushforward f).toRightDerivedZero.app X.structureModule) :=
    inferInstance
  constructor
  · intro h
    have h' : IsIso (f.structureUnit ≫
        (Scheme.Modules.pushforward f).toRightDerivedZero.app X.structureModule) := h
    exact IsIso.of_isIso_comp_right f.structureUnit
      ((Scheme.Modules.pushforward f).toRightDerivedZero.app X.structureModule)
  · intro h
    show IsIso (f.structureUnit ≫
        (Scheme.Modules.pushforward f).toRightDerivedZero.app X.structureModule)
    infer_instance

end ZerothDirectImage

section Retract

/-- **"(1) applied twice", p. 145: the retract argument.**  Let `f : X₁ ⟶ X₂` be a morphism of non-singular integral algebraic
`B`-schemes (`B` a field of characteristic zero; `p₁`, `p₂` are the structure morphisms, of finite type).  Suppose that `h : X' ⟶ X₁` is a morphism from a scheme `X'` obtained from `X₂` by a succession `s`
of monoidal transformations with non-singular, nowhere dense centers, with `h ≫ f = s.composite` (this is the first
application of (1): `X'` dominates `X₁`), and that `h' : X'' ⟶ X'` is a morphism from a scheme `X''` obtained from `X₁`
by such a succession `s'` with `h' ≫ h = s'.composite` (the second application of (1): `X''` dominates `X'`).  Then
`Rⁱf_*O_{X₁} = 0` for `i > 0` and `O_{X₂} → f_*O_{X₁}` is an isomorphism.

Proof (the printed argument): by the single blow-up case along successions, `O_{X₁}` is a retract of `Rh_*O_{X'}`
(the composite `O_{X₁} → Rh_*O_{X'} → Rk_*O_{X''}`, `k = h' ≫ h`, is an isomorphism); applying `Rf_*`, `Rf_*O_{X₁}` is a
retract of `R(h ≫ f)_*O_{X'} = Rg_*O_{X'}`, which is `O_{X₂}`.  In degree `0`, `O_{X₂} → f_*O_{X₁} → g_*O_{X'}` is the
isomorphism `O_{X₂} → g_*O_{X'}` and the second map is a monomorphism, because `X'` is integral and `h` is dominant.

Deviation from the paper (gap filled): the paper only says "it follows from the same result for a monoidal transformation
... and from (1) applied twice"; the retract argument, the use of the Leray edge maps and the monomorphism in degree `0`
are ours.  The hypotheses `hfh`, `hk` are the identifications of morphisms of `X'`-schemes that (1) provides (the two
rational applications agree). -/
@[blueprint "thm:0.5-direct-image-dominating"
  (statement := /-- Let $f\colon X_1\to X_2$ be a morphism of non-singular integral algebraic $B$-schemes, $B$ a field of characteristic zero, $h\colon X'\to X_1$
    a morphism from a scheme obtained from $X_2$ by a succession of monoidal transformations with non-singular
    nowhere dense centers with $f\circ h$ equal to the composite, and $h'\colon X''\to X'$ a morphism from a scheme
    obtained from $X_1$ by such a succession with $h\circ h'$ equal to the composite.  Then $R^if_*(\mathcal O_{X_1})=0$
    for $i>0$ and $f_*\mathcal O_{X_1}=\mathcal O_{X_2}$.  (p.~145.) -/)
  (proof := /-- Retract: $\mathcal O_{X_1}$ is a retract of $Rh_*\mathcal O_{X'}$, hence $Rf_*\mathcal O_{X_1}$ of
    $R(f\circ h)_*\mathcal O_{X'}=\mathcal O_{X_2}$, using the single blow-up case along successions
    (\cref{thm:0.5-direct-image-monoidal-transformation}) and the Leray edge maps
    (\cref{thm:0.5-leray-edge-maps}).  Gap filled: the paper only says ``from (1) applied twice''. -/)
  (proofUses := ["thm:0.5-direct-image-monoidal-transformation", "thm:0.5-leray-edge-maps"])
  (latexEnv := "theorem")]
theorem higherDirectImage_structureSheaf_of_dominating [Hironaka.HironakaCitedResults.{u}] [Hironaka.Cited.MonoidalTransformationHigherDirectImageStructureSheaf.{u}] {B : Type u} [Field B] [CharZero B]
    {X₁ X₂ X' X'' : Scheme.{u}} [IsIntegral X₁] [IsIntegral X']
    (p₁ : X₁ ⟶ Spec (CommRingCat.of B)) (p₂ : X₂ ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p₁] [QuasiCompact p₁] [LocallyOfFiniteType p₂] [QuasiCompact p₂]
    (f : X₁ ⟶ X₂) (h : X' ⟶ X₁) (h' : X'' ⟶ X')
    (s : MonoidalSuccession X₂ X') (s' : MonoidalSuccession X₁ X'')
    (hX₁ : X₁.IsNonsingular) (hX₂ : X₂.IsNonsingular)
    (hs : s.HasNonsingularCenters) (hsd : s.NowhereDenseCenters)
    (hs' : s'.HasNonsingularCenters) (hsd' : s'.NowhereDenseCenters)
    (hfh : h ≫ f = s.composite) (hk : h' ≫ h = s'.composite)
    (hη : h (genericPoint X') = genericPoint X₁) :
    (∀ i, 0 < i → IsZero (higherDirectImageStructure f i)) ∧ IsIso f.structureUnit := by
  obtain ⟨hg1, hg2⟩ := s.higherDirectImage_structureSheaf p₂ hX₂ hs hsd
  obtain ⟨hk1, hk2⟩ := s'.higherDirectImage_structureSheaf p₁ hX₁ hs' hsd'
  rw [← hfh] at hg1 hg2
  rw [← hk] at hk1 hk2
  obtain ⟨ε, hnat, hvan, hassoc⟩ := exists_lerayEdge.{u}
  have hmono := mono_structureUnit h hη
  refine ⟨fun i hi => ?_, ?_⟩
  · -- the chain `A → Z → W` is an isomorphism `A ≅ W` factoring through the zero object `Z`
    have HA := hassoc h' h f X''.structureModule i
    have HN := hnat h f h'.structureUnit i
    have hT : (((Scheme.Modules.pushforward f).rightDerived i).map h.structureUnit ≫
        ε h f X'.structureModule i ≫
        ((Scheme.Modules.pushforward (h ≫ f)).rightDerived i).map h'.structureUnit ≫
        ε h' (h ≫ f) X''.structureModule i) =
        ((Scheme.Modules.pushforward f).rightDerived i).map (h' ≫ h).structureUnit ≫
          ε (h' ≫ h) f X''.structureModule i := by
      rw [Scheme.Hom.structureUnit_comp h' h, Functor.map_comp, Functor.map_comp]
      calc _ = ((Scheme.Modules.pushforward f).rightDerived i).map h.structureUnit ≫
              ((ε h f X'.structureModule i ≫
                ((Scheme.Modules.pushforward (h ≫ f)).rightDerived i).map h'.structureUnit) ≫
                ε h' (h ≫ f) X''.structureModule i) := by simp
        _ = ((Scheme.Modules.pushforward f).rightDerived i).map h.structureUnit ≫
              ((((Scheme.Modules.pushforward f).rightDerived i).map
                ((Scheme.Modules.pushforward h).map h'.structureUnit) ≫
                ε h f ((Scheme.Modules.pushforward h').obj X''.structureModule) i) ≫
                ε h' (h ≫ f) X''.structureModule i) := by rw [HN]
        _ = ((Scheme.Modules.pushforward f).rightDerived i).map h.structureUnit ≫
              (((Scheme.Modules.pushforward f).rightDerived i).map
                ((Scheme.Modules.pushforward h).map h'.structureUnit) ≫
                (ε h f ((Scheme.Modules.pushforward h').obj X''.structureModule) i ≫
                ε h' (h ≫ f) X''.structureModule i)) := by simp
        _ = _ := by
          refine congrArg (fun z => ((Scheme.Modules.pushforward f).rightDerived i).map h.structureUnit ≫
            ((Scheme.Modules.pushforward f).rightDerived i).map
              ((Scheme.Modules.pushforward h).map h'.structureUnit) ≫ z) HA.symm |>.trans ?_
          rfl
    have hiso1 : IsIso (((Scheme.Modules.pushforward f).rightDerived i).map (h' ≫ h).structureUnit) := by
      have := hk2
      infer_instance
    have hiso2 : IsIso (ε (h' ≫ h) f X''.structureModule i) := hvan _ _ _ hk1 i
    have hTiso : IsIso (((Scheme.Modules.pushforward f).rightDerived i).map h.structureUnit ≫
        ε h f X'.structureModule i ≫
        ((Scheme.Modules.pushforward (h ≫ f)).rightDerived i).map h'.structureUnit ≫
        ε h' (h ≫ f) X''.structureModule i) := by
      rw [hT]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hiso1 hiso2
    have h0 : ((Scheme.Modules.pushforward f).rightDerived i).map h.structureUnit ≫
        ε h f X'.structureModule i = 0 := (hg1 i hi).eq_of_tgt _ _
    have hT0 : (((Scheme.Modules.pushforward f).rightDerived i).map h.structureUnit ≫
        ε h f X'.structureModule i ≫
        ((Scheme.Modules.pushforward (h ≫ f)).rightDerived i).map h'.structureUnit ≫
        ε h' (h ≫ f) X''.structureModule i) = 0 := by
      have e : (((Scheme.Modules.pushforward f).rightDerived i).map h.structureUnit ≫
          ε h f X'.structureModule i ≫
          ((Scheme.Modules.pushforward (h ≫ f)).rightDerived i).map h'.structureUnit ≫
          ε h' (h ≫ f) X''.structureModule i) =
          (((Scheme.Modules.pushforward f).rightDerived i).map h.structureUnit ≫
            ε h f X'.structureModule i) ≫
          (((Scheme.Modules.pushforward (h ≫ f)).rightDerived i).map h'.structureUnit ≫
            ε h' (h ≫ f) X''.structureModule i) := by simp only [Category.assoc]
      rw [e, h0, zero_comp]
    have hz : IsIso (0 : ((Scheme.Modules.pushforward f).rightDerived i).obj X₁.structureModule ⟶
        ((Scheme.Modules.pushforward (h' ≫ h ≫ f)).rightDerived i).obj X''.structureModule) := by
      rw [← hT0]
      exact hTiso
    refine (IsZero.iff_id_eq_zero _).mpr ?_
    show 𝟙 (((Scheme.Modules.pushforward f).rightDerived i).obj X₁.structureModule) = 0
    exact (IsIso.hom_inv_id (0 : ((Scheme.Modules.pushforward f).rightDerived i).obj X₁.structureModule ⟶
        ((Scheme.Modules.pushforward (h' ≫ h ≫ f)).rightDerived i).obj X''.structureModule)).symm.trans
      (zero_comp)
  · -- degree `0`
    have hcomp := Scheme.Hom.structureUnit_comp h f
    have hJ : IsIso (f.structureUnit ≫ (Scheme.Modules.pushforward f).map h.structureUnit ≫
        (Scheme.Modules.pushforwardComp h f).hom.app X'.structureModule) := by
      rw [← hcomp]
      exact hg2
    have : Mono ((Scheme.Modules.pushforward f).map h.structureUnit) := inferInstance
    have hm : Mono ((Scheme.Modules.pushforward f).map h.structureUnit ≫
        (Scheme.Modules.pushforwardComp h f).hom.app X'.structureModule) := mono_comp _ _
    have hsplit : IsSplitEpi ((Scheme.Modules.pushforward f).map h.structureUnit ≫
        (Scheme.Modules.pushforwardComp h f).hom.app X'.structureModule) :=
      ⟨⟨{ section_ := inv (f.structureUnit ≫ (Scheme.Modules.pushforward f).map h.structureUnit ≫
            (Scheme.Modules.pushforwardComp h f).hom.app X'.structureModule) ≫ f.structureUnit
          id := by rw [Category.assoc]; exact IsIso.inv_hom_id _ }⟩⟩
    have hmiso := isIso_of_mono_of_isSplitEpi ((Scheme.Modules.pushforward f).map h.structureUnit ≫
        (Scheme.Modules.pushforwardComp h f).hom.app X'.structureModule)
    exact IsIso.of_isIso_comp_right f.structureUnit
      ((Scheme.Modules.pushforward f).map h.structureUnit ≫
        (Scheme.Modules.pushforwardComp h f).hom.app X'.structureModule)

end Retract

end Hironaka
