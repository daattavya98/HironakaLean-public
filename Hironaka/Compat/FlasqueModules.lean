/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Topology.Sheaves.Flasque

/-!
# Flasque sheaves of modules on a scheme (gap filled for Ch. 0 §5, consequence (2), p. 145)

Consequence (2) of Corollary 1 (p. 145) is argued in the paper by "(1) applied twice", which tacitly uses the Leray edge
maps `Rⁱg_*(f_*F) → Rⁱ(f ≫ g)_*F` and their degeneration (`Hironaka.exists_lerayEdge`,
`Hironaka/Compat/HigherDirectImageStructureSheaf.lean`).  The paper does not state these facts; they are a gap filled
by a proof.  This module provides the sheaf-theoretic half of that proof: the class of *flasque* `O_X`-modules, which
contains the injective objects of `X.Modules`, is stable under direct images, is closed under cokernels of
monomorphisms between flasque modules, and on which every direct image functor `g_*` is exact (so that flasque
modules are `g_*`-acyclic).  Nothing here is an argument of the paper; it is general sheaf theory (Hartshorne II,
Ex. 1.16, and III, Lemma 2.4).

## Main results

* `AlgebraicGeometry.Scheme.Modules.IsFlasque`: all restriction maps `Γ(M, U) → Γ(M, V)`, `V ≤ U`, are surjective;
  `isFlasque_iff_presheaf_isFlasque` relates it to Mathlib's `TopCat.Presheaf.IsFlasque`.
* `AlgebraicGeometry.Scheme.Modules.isFlasque_of_injective`: an injective `O_X`-module is flasque (Hartshorne III,
  Lemma 2.4), via the "extension by zero" `j_!O_U` (`extendByZeroUnit`), the sheafification of the free presheaf of
  modules on the representable presheaf of `U`, which satisfies `Hom(j_!O_U, M) ≃ Γ(M, U)`.
* `AlgebraicGeometry.Scheme.Modules.IsFlasque.pushforward`: `f_*` of a flasque module is flasque.
* `AlgebraicGeometry.Scheme.Modules.IsFlasque.surjective_app_of_shortExact` and
  `AlgebraicGeometry.Scheme.Modules.IsFlasque.of_shortExact` (Hartshorne II, Ex. 1.16(b), (c)), deduced from the
  corresponding results for abelian sheaves in Mathlib through the forgetful functor
  `SheafOfModules.toSheaf`, which we show is exact (`SheafOfModules.preservesFiniteColimits_toSheaf`).
* `AlgebraicGeometry.Scheme.Modules.IsFlasque.shortExact_map_pushforward`: for a short exact sequence with flasque
  first term, its image under any `g_*` is short exact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-- The forgetful functor from sheaves of modules to sheaves of abelian groups preserves finite colimits: a colimit
of sheaves of modules is the sheafification of the colimit of the underlying presheaves of modules, and
sheafification commutes with forgetting the module structure. -/
instance preservesFiniteColimits_toSheaf : PreservesFiniteColimits (toSheaf.{u} R) where
  preservesFiniteColimits K _ _ := ⟨fun {F} => by
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
    let F' := F ⋙ (forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj))
    let e : F' ⋙ PresheafOfModules.sheafification (𝟙 R.obj) ≅ F :=
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ F.rightUnitor
    let H := PresheafOfModules.sheafification (𝟙 R.obj) ⋙ toSheaf R
    have : PreservesColimitsOfShape K H :=
      preservesColimitsOfShape_of_natIso (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
    have : PreservesColimit (F' ⋙ PresheafOfModules.sheafification (𝟙 R.obj)) (toSheaf R) :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 R.obj)) (colimit.isColimit F'))
        (isColimitOfPreserves H (colimit.isColimit F'))
    exact preservesColimit_of_iso_diagram _ e⟩

/-- The forgetful functor from sheaves of modules to sheaves of abelian groups preserves zero morphisms. -/
instance preservesZeroMorphisms_toSheaf : (toSheaf.{u} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

end SheafOfModules

namespace PresheafOfModules

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- Naturality of `freeYonedaEquiv` in the representing object: precomposing with the map
`free (yoneda V) ⟶ free (yoneda U)` induced by `f : V ⟶ U` corresponds to `M.map f.op`. -/
theorem freeYonedaEquiv_free_map_comp {M : PresheafOfModules.{u} R} {U V : C} (f : V ⟶ U)
    (c : (free R).obj (yoneda.obj U) ⟶ M) :
    freeYonedaEquiv ((free R).map (yoneda.map f) ≫ c) = M.map f.op (freeYonedaEquiv c) := by
  have h := (freeAdjunction R).homEquiv_naturality_left (yoneda.map f) c
  rw [freeAdjunction_homEquiv, freeAdjunction_homEquiv] at h
  exact (congrArg yonedaEquiv h).trans (yonedaEquiv_naturality _ _).symm

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

section Flasque

/-- An `O_X`-module `M` is *flasque* if all its restriction maps `Γ(M, U) → Γ(M, V)`, `V ≤ U`, are surjective. -/
def IsFlasque (M : X.Modules) : Prop :=
  ∀ ⦃U V : X.Opens⦄ (i : V ⟶ U), Function.Surjective (M.presheaf.map i.op)

/-- Flasqueness of an `O_X`-module is flasqueness (in the sense of Mathlib) of its underlying abelian presheaf. -/
theorem isFlasque_iff_presheaf_isFlasque (M : X.Modules) :
    M.IsFlasque ↔ TopCat.Presheaf.IsFlasque M.presheaf := by
  constructor
  · exact fun h => ⟨fun {_ _} i => (AddCommGrpCat.epi_iff_surjective _).2 (h i.unop)⟩
  · exact fun h _ _ i => (AddCommGrpCat.epi_iff_surjective _).1 (h.epi i.op)

/-- The direct image `f_*M` of a flasque `O_X`-module `M` is flasque. -/
theorem IsFlasque.pushforward {M : X.Modules} (hM : M.IsFlasque) (f : X ⟶ Y) :
    ((Modules.pushforward f).obj M).IsFlasque := fun _ _ i => by
  rw [pushforward_obj_presheaf_map]
  exact hM _

/-- Naturality of a morphism of `O_X`-modules with respect to restriction of sections. -/
theorem Hom.app_presheaf_map {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op s) = N.presheaf.map i.op (φ.app U s) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) s

/-- Flasqueness is invariant under isomorphism of `O_X`-modules. -/
theorem IsFlasque.of_iso {M N : X.Modules} (e : M ≅ N) (hM : M.IsFlasque) : N.IsFlasque := by
  intro U V i t
  obtain ⟨s, hs⟩ := hM i (e.inv.app V t)
  refine ⟨e.hom.app U s, ?_⟩
  rw [← Hom.app_presheaf_map, hs, ← ConcreteCategory.comp_apply, ← Hom.comp_app, e.inv_hom_id,
    Hom.id_app, ConcreteCategory.id_apply]

/-- The forgetful functor from `O_X`-modules to sheaves of abelian groups. -/
noncomputable abbrev toAbSheaf (X : Scheme.{u}) : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  SheafOfModules.toSheaf X.ringCatSheaf

/-- The forgetful functor from `O_X`-modules to sheaves of abelian groups preserves zero morphisms. -/
instance (X : Scheme.{u}) : (toAbSheaf X).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_toSheaf (J := Opens.grothendieckTopology X) X.ringCatSheaf

/-- The forgetful functor from `O_X`-modules to sheaves of abelian groups preserves finite limits. -/
instance (X : Scheme.{u}) : PreservesFiniteLimits (toAbSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf (J := Opens.grothendieckTopology X)
    X.ringCatSheaf))

/-- The forgetful functor from `O_X`-modules to sheaves of abelian groups preserves finite colimits. -/
instance (X : Scheme.{u}) : PreservesFiniteColimits (toAbSheaf X) :=
  SheafOfModules.preservesFiniteColimits_toSheaf (J := Opens.grothendieckTopology X) X.ringCatSheaf

/-- **Hartshorne II, Ex. 1.16(b).** If `0 → M₁ → M₂ → M₃ → 0` is a short exact sequence of `O_X`-modules with
`M₁` flasque, then `Γ(M₂, U) → Γ(M₃, U)` is surjective for every open `U`. -/
theorem IsFlasque.surjective_app_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : S.X₁.IsFlasque) (U : X.Opens) : Function.Surjective (S.g.app U) := by
  have hS' : (S.map (toAbSheaf X)).ShortExact := hS.map_of_exact _
  have : TopCat.Sheaf.IsFlasque (S.map (toAbSheaf X)).X₁ := (isFlasque_iff_presheaf_isFlasque _).1 h₁
  exact (AddCommGrpCat.epi_iff_surjective _).1 (TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) hS')

/-- **Hartshorne II, Ex. 1.16(c).** If `0 → M₁ → M₂ → M₃ → 0` is a short exact sequence of `O_X`-modules with
`M₁` and `M₂` flasque, then `M₃` is flasque. -/
theorem IsFlasque.of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) (h₁ : S.X₁.IsFlasque)
    (h₂ : S.X₂.IsFlasque) : S.X₃.IsFlasque := by
  intro U V i t
  obtain ⟨s, rfl⟩ := h₁.surjective_app_of_shortExact hS V t
  obtain ⟨s', rfl⟩ := h₂ i s
  exact ⟨S.g.app U s', (Hom.app_presheaf_map S.g i s').symm⟩

/-- A morphism of `O_X`-modules that is surjective on the sections over every open is an epimorphism. -/
theorem epi_of_surjective_app {M N : X.Modules} (φ : M ⟶ N) (h : ∀ U, Function.Surjective (φ.app U)) :
    Epi φ :=
  ⟨fun a b hab => hom_ext _ _ fun U => by
    ext x
    obtain ⟨y, rfl⟩ := h U x
    have := congr(($hab).app U)
    rw [Hom.comp_app, Hom.comp_app] at this
    exact ConcreteCategory.congr_hom this y⟩

/-- **Exactness of `g_*` on flasque kernels.** If `0 → M₁ → M₂ → M₃ → 0` is a short exact sequence of `O_X`-modules
with `M₁` flasque, then `0 → g_*M₁ → g_*M₂ → g_*M₃ → 0` is short exact, for every morphism of schemes `g : X ⟶ Y`. -/
theorem IsFlasque.shortExact_map_pushforward (g : X ⟶ Y) {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : S.X₁.IsFlasque) : (S.map (Modules.pushforward g)).ShortExact := by
  have := hS.mono_f
  have hexact : (S.map (Modules.pushforward g)).Exact :=
    hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance
  have hmono : Mono (S.map (Modules.pushforward g)).f := by
    dsimp
    infer_instance
  have hepi : Epi (S.map (Modules.pushforward g)).g :=
    epi_of_surjective_app _ fun U => h₁.surjective_app_of_shortExact hS _
  exact { exact := hexact, mono_f := hmono, epi_g := hepi }

end Flasque

section ExtensionByZero

variable (X) in
/-- The free presheaf of `O_X`-modules on the representable presheaf of an open `U`: its sections over `W` are
`Γ(X, W)` if `W ≤ U` and `0` otherwise. -/
noncomputable abbrev freeYonedaPresheaf (U : X.Opens) : X.PresheafOfModules :=
  (PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U)

variable (X) in
/-- The extension by zero `j_!O_U` of the structure sheaf of an open `U` (Hartshorne II, Ex. 1.19): the
sheafification of `freeYonedaPresheaf X U`. -/
noncomputable def extendByZeroUnit (U : X.Opens) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (freeYonedaPresheaf X U)

/-- The universal property of `j_!O_U`: `Hom(j_!O_U, M) ≃ Γ(M, U)`. -/
noncomputable def extendByZeroUnitHomEquiv (U : X.Opens) (M : X.Modules) :
    (extendByZeroUnit X U ⟶ M) ≃ Γ(M, U) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).trans
    PresheafOfModules.freeYonedaEquiv

/-- The map `j_!O_V ⟶ j_!O_U` induced by an inclusion of opens `V ≤ U`. -/
noncomputable def extendByZeroUnitMap {U V : X.Opens} (i : V ⟶ U) :
    extendByZeroUnit X V ⟶ extendByZeroUnit X U :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i))

/-- The map `j_!O_V ⟶ j_!O_U` is a monomorphism. -/
instance mono_extendByZeroUnitMap {U V : X.Opens} (i : V ⟶ U) : Mono (extendByZeroUnitMap i) := by
  have : Mono ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i)) := by
    refine PresheafOfModules.mono_of_injective fun W => ?_
    exact Finsupp.mapDomain_injective fun a b _ => Subsingleton.elim (α := W.unop ⟶ V) a b
  exact Functor.map_mono (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) _

/-- Under `Hom(j_!O_U, M) ≃ Γ(M, U)`, precomposition with `j_!O_V ⟶ j_!O_U` is restriction of sections. -/
theorem extendByZeroUnitHomEquiv_comp {U V : X.Opens} (i : V ⟶ U) {M : X.Modules}
    (b : extendByZeroUnit X U ⟶ M) :
    extendByZeroUnitHomEquiv V M (extendByZeroUnitMap i ≫ b) =
      M.presheaf.map i.op (extendByZeroUnitHomEquiv U M b) := by
  have h₁ : PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i)) ≫ b) =
      (PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i) ≫
        PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj) b :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_left _ _
  change PresheafOfModules.freeYonedaEquiv (PresheafOfModules.sheafificationHomEquiv
      (𝟙 X.ringCatSheaf.obj) ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i)) ≫ b)) =
    M.presheaf.map i.op (PresheafOfModules.freeYonedaEquiv
      (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj) b))
  rw [h₁, PresheafOfModules.freeYonedaEquiv_free_map_comp]
  rfl

/-- **Hartshorne III, Lemma 2.4.** An injective object of `X.Modules` is flasque. -/
theorem isFlasque_of_injective (M : X.Modules) [Injective M] : M.IsFlasque := by
  intro U V i s
  obtain ⟨b, hb⟩ := Injective.factors ((extendByZeroUnitHomEquiv V M).symm s) (extendByZeroUnitMap i)
  refine ⟨extendByZeroUnitHomEquiv U M b, ?_⟩
  rw [← extendByZeroUnitHomEquiv_comp, hb, Equiv.apply_symm_apply]

end ExtensionByZero

end AlgebraicGeometry.Scheme.Modules
