/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Hironaka.Compat.LerayEdgeAbstract
public import Hironaka.Compat.FlasqueModules

/-!
# Leray edge maps for direct images of `O_X`-modules

For morphisms of schemes `f : X ⟶ Y`, `g : Y ⟶ Z` and an `O_X`-module `F`, the edge maps of the Leray spectral
sequence `Rᵖg_*(R^q f_* F) ⇒ R^{p+q}(f ≫ g)_* F`,
`pushforwardLerayEdge f g F i : Rⁱg_*(f_* F) ⟶ Rⁱ(f ≫ g)_* F`,
are the abstract edge maps `Functor.lerayEdge` of `Hironaka.Compat.LerayEdgeAbstract` for `F = f_*`, `G = g_*`
(flasque modules form a class acyclic for every direct image functor, and `f_*` sends injective modules to flasque
modules: `Hironaka.Compat.FlasqueModules`), transported along `f_* ⋙ g_* ≅ (f ≫ g)_*`.  We prove the three properties
used in Ch. 0 §5, consequence (2) (p. 145): naturality, invertibility when `R^q f_* F = 0` for `q > 0`, and the
compatibility with a composite `f₁ ≫ f₂ ≫ f₃`.

Gap filled (tacit in the paper): proved, no cited result.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z T : Scheme.{u}}

/-- The class of flasque `O_X`-modules. -/
def flasque (X : Scheme.{u}) : ObjectProperty X.Modules := fun M => M.IsFlasque

/-- Flasque modules form a class acyclic for every direct image functor. -/
theorem isAcyclicClass_flasque (g : X ⟶ Y) : (pushforward g).IsAcyclicClass (flasque X) where
  injective M _ := isFlasque_of_injective M
  shortExact_map hS h₁ := IsFlasque.shortExact_map_pushforward g hS h₁
  of_shortExact hS h₁ h₂ := IsFlasque.of_shortExact hS h₁ h₂

/-- `f_*` sends injective modules into the class of flasque modules, acyclic for `g_*`. -/
theorem sendsInjectivesToAcyclic_pushforward (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pushforward f).SendsInjectivesToAcyclic (pushforward g) :=
  ⟨flasque Y, isAcyclicClass_flasque g, fun M _ => (isFlasque_of_injective M).pushforward f⟩

/-- `f_*` sends injective modules into the class of flasque modules, acyclic for `g_* ⋙ h_*`. -/
theorem sendsInjectivesToAcyclic_pushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (pushforward f).SendsInjectivesToAcyclic (pushforward g ⋙ pushforward h) :=
  ⟨flasque Y, (isAcyclicClass_flasque g).comp (isAcyclicClass_flasque h) (fun _ hM => hM.pushforward g),
    fun M _ => (isFlasque_of_injective M).pushforward f⟩

/-- `f_* ⋙ g_*` sends injective modules into the class of flasque modules, acyclic for `h_*`. -/
theorem sendsInjectivesToAcyclic_comp_pushforward (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (pushforward f ⋙ pushforward g).SendsInjectivesToAcyclic (pushforward h) :=
  ⟨flasque Z, isAcyclicClass_flasque h, fun M _ => ((isFlasque_of_injective M).pushforward f).pushforward g⟩

/-- The morphism of derived functors induced by a natural isomorphism is an isomorphism. -/
theorem isIso_rightDerived_app {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasInjectiveResolutions C] {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) (i : ℕ) (A : C) :
    IsIso ((NatTrans.rightDerived e.hom i).app A) :=
  ⟨(NatTrans.rightDerived e.inv i).app A,
    by rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id,
      NatTrans.id_app],
    by rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id,
      NatTrans.id_app]⟩

/-- **The Leray edge map** `Rⁱg_*(f_* F) ⟶ Rⁱ(f ≫ g)_* F`. -/
noncomputable def pushforwardLerayEdge (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Modules) (i : ℕ) :
    ((pushforward g).rightDerived i).obj ((pushforward f).obj F) ⟶
      ((pushforward (f ≫ g)).rightDerived i).obj F :=
  (pushforward f).lerayEdge (pushforward g) (sendsInjectivesToAcyclic_pushforward f g) F i ≫
    (NatTrans.rightDerived (pushforwardComp f g).hom i).app F

/-- Naturality of the Leray edge maps in the module. -/
theorem pushforwardLerayEdge_naturality (f : X ⟶ Y) (g : Y ⟶ Z) {F F' : X.Modules} (φ : F ⟶ F') (i : ℕ) :
    ((pushforward g).rightDerived i).map ((pushforward f).map φ) ≫ pushforwardLerayEdge f g F' i =
      pushforwardLerayEdge f g F i ≫ ((pushforward (f ≫ g)).rightDerived i).map φ := by
  simp only [pushforwardLerayEdge]
  rw [← Category.assoc, Functor.lerayEdge_naturality, Category.assoc, Category.assoc,
    (NatTrans.rightDerived (pushforwardComp f g).hom i).naturality φ]

/-- The Leray edge maps are isomorphisms when `R^q f_* F = 0` for all `q > 0`. -/
theorem isIso_pushforwardLerayEdge (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Modules)
    (hF : ∀ q, 0 < q → IsZero (((pushforward f).rightDerived q).obj F)) (i : ℕ) :
    IsIso (pushforwardLerayEdge f g F i) := by
  have := Functor.isIso_lerayEdge (pushforward f) (pushforward g) (sendsInjectivesToAcyclic_pushforward f g) F
    hF i
  have := isIso_rightDerived_app (pushforwardComp f g) i F
  dsimp only [pushforwardLerayEdge]
  infer_instance

/-- The coherence of the isomorphisms `pushforwardComp` for three morphisms. -/
theorem pushforwardComp_assoc (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) (f₃ : Z ⟶ T) :
    Functor.whiskerRight (pushforwardComp f₁ f₂).hom (pushforward f₃) ≫ (pushforwardComp (f₁ ≫ f₂) f₃).hom =
      Functor.whiskerLeft (pushforward f₁) (pushforwardComp f₂ f₃).hom ≫
        (pushforwardComp f₁ (f₂ ≫ f₃)).hom := by
  ext M : 2
  refine Modules.hom_ext _ _ fun U => ?_
  ext x
  rfl

/-- Compatibility of the Leray edge maps with a composite `f₁ ≫ f₂ ≫ f₃`. -/
theorem pushforwardLerayEdge_comp (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) (f₃ : Z ⟶ T) (F : X.Modules) (i : ℕ) :
    ((pushforward f₃).rightDerived i).map ((pushforwardComp f₁ f₂).hom.app F) ≫
        pushforwardLerayEdge (f₁ ≫ f₂) f₃ F i =
      pushforwardLerayEdge f₂ f₃ ((pushforward f₁).obj F) i ≫ pushforwardLerayEdge f₁ (f₂ ≫ f₃) F i := by
  have hL := Functor.lerayEdge_natTrans_left (pushforwardComp f₁ f₂).hom (pushforward f₃)
    (sendsInjectivesToAcyclic_comp_pushforward f₁ f₂ f₃) (sendsInjectivesToAcyclic_pushforward (f₁ ≫ f₂) f₃)
    F i
  have hR := Functor.lerayEdge_natTrans_right (pushforward f₁) (pushforwardComp f₂ f₃).hom
    (sendsInjectivesToAcyclic_pushforward_comp f₁ f₂ f₃) (sendsInjectivesToAcyclic_pushforward f₁ (f₂ ≫ f₃))
    F i
  have hC := Functor.lerayEdge_comp (pushforward f₁) (pushforward f₂) (pushforward f₃)
    (sendsInjectivesToAcyclic_pushforward f₂ f₃) (sendsInjectivesToAcyclic_pushforward_comp f₁ f₂ f₃)
    (sendsInjectivesToAcyclic_comp_pushforward f₁ f₂ f₃) F i
  have hN1 :
      (NatTrans.rightDerived (Functor.whiskerRight (pushforwardComp f₁ f₂).hom (pushforward f₃)) i).app F ≫
        (NatTrans.rightDerived (pushforwardComp (f₁ ≫ f₂) f₃).hom i).app F =
      (NatTrans.rightDerived (Functor.whiskerRight (pushforwardComp f₁ f₂).hom (pushforward f₃) ≫
        (pushforwardComp (f₁ ≫ f₂) f₃).hom) i).app F := by
    rw [NatTrans.rightDerived_comp, NatTrans.comp_app]
  have hN2 :
      (NatTrans.rightDerived (Functor.whiskerLeft (pushforward f₁) (pushforwardComp f₂ f₃).hom) i).app F ≫
        (NatTrans.rightDerived (pushforwardComp f₁ (f₂ ≫ f₃)).hom i).app F =
      (NatTrans.rightDerived (Functor.whiskerLeft (pushforward f₁) (pushforwardComp f₂ f₃).hom ≫
        (pushforwardComp f₁ (f₂ ≫ f₃)).hom) i).app F := by
    rw [NatTrans.rightDerived_comp, NatTrans.comp_app]
  have hN := hN1.trans ((congrArg (fun α => (NatTrans.rightDerived α i).app F)
    (pushforwardComp_assoc f₁ f₂ f₃)).trans hN2.symm)
  simp only [pushforwardLerayEdge]
  have s1 := (Category.assoc (((pushforward f₃).rightDerived i).map ((pushforwardComp f₁ f₂).hom.app F))
    ((pushforward (f₁ ≫ f₂)).lerayEdge (pushforward f₃) (sendsInjectivesToAcyclic_pushforward (f₁ ≫ f₂) f₃) F i)
    ((NatTrans.rightDerived (pushforwardComp (f₁ ≫ f₂) f₃).hom i).app F)).symm
  have s2 := congrArg (· ≫ (NatTrans.rightDerived (pushforwardComp (f₁ ≫ f₂) f₃).hom i).app F) hL
  have s3 := (Category.assoc ((pushforward f₁ ⋙ pushforward f₂).lerayEdge (pushforward f₃)
    (sendsInjectivesToAcyclic_comp_pushforward f₁ f₂ f₃) F i)
    ((NatTrans.rightDerived (Functor.whiskerRight (pushforwardComp f₁ f₂).hom (pushforward f₃)) i).app F)
    ((NatTrans.rightDerived (pushforwardComp (f₁ ≫ f₂) f₃).hom i).app F)).trans
    (congrArg ((pushforward f₁ ⋙ pushforward f₂).lerayEdge (pushforward f₃)
      (sendsInjectivesToAcyclic_comp_pushforward f₁ f₂ f₃) F i ≫ ·) hN)
  have s4 := congrArg (· ≫ ((NatTrans.rightDerived (Functor.whiskerLeft (pushforward f₁)
    (pushforwardComp f₂ f₃).hom) i).app F ≫ (NatTrans.rightDerived (pushforwardComp f₁ (f₂ ≫ f₃)).hom i).app F))
    hC.symm
  have s5 := congrArg ((pushforward f₂).lerayEdge (pushforward f₃) (sendsInjectivesToAcyclic_pushforward f₂ f₃)
    ((pushforward f₁).obj F) i ≫ · ≫ (NatTrans.rightDerived (pushforwardComp f₁ (f₂ ≫ f₃)).hom i).app F)
    hR.symm
  simp only [Category.assoc] at s4 s5 ⊢
  exact s1.trans (s2.trans (s3.trans (s4.trans s5)))

end AlgebraicGeometry.Scheme.Modules
