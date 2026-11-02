/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Compat.InjectiveReplacement

/-!
# Edge maps `RⁱG(F A) ⟶ Rⁱ(F ⋙ G)(A)` (abstract Leray / Grothendieck edge maps)

Let `F : C ⥤ D`, `G : D ⥤ E` be additive functors between abelian categories, `C`, `D` with enough injectives, and
suppose that `F` sends injective objects into a class `P` acyclic for `G` (`Functor.IsAcyclicClass`).  We construct the
edge maps of the Grothendieck spectral sequence `RᵖG(R^qF A) ⇒ R^{p+q}(F ⋙ G)(A)`,
`Functor.lerayEdge F G h A i : (G.rightDerived i).obj (F.obj A) ⟶ ((F ⋙ G).rightDerived i).obj A`,
and prove:

* naturality in `A` (`Functor.lerayEdge_naturality`), in `F` (`Functor.lerayEdge_natTrans_left`) and in `G`
  (`Functor.lerayEdge_natTrans_right`);
* `lerayEdge F G h A i` is an isomorphism for all `i` if `F` is left exact and `R^qF A = 0` for `q > 0`
  (`Functor.isIso_lerayEdge`);
* compatibility with three functors: `ε_{F₂,F₃}(F₁ A) ≫ ε_{F₁,F₂⋙F₃}(A) = ε_{F₁⋙F₂,F₃}(A)` (`Functor.lerayEdge_comp`).

Construction.  Let `I` be the chosen injective resolution of `A`, `J` that of `F A`, `M = F(I)` (a complex of objects
of `P`, coaugmented by `F A → F(I⁰)`), and `β : M ⟶ R` a chosen monomorphic quasi-isomorphism to a complex of
injectives (`CochainComplex.exists_mono_quasiIso_injective_nat`).  There is a unique map `α : J ⟶ R` in the homotopy
category compatible with the coaugmentations (`HomotopyCategory.bijective_quotient_map_comp`), and
`ε = Hⁱ(G α) ≫ Hⁱ(G β)⁻¹ : Hⁱ(G J) ⟶ Hⁱ(G F I)`; `Hⁱ(G β)` is invertible because `G` preserves monomorphic
quasi-isomorphisms between complexes of objects of `P` (`Functor.IsAcyclicClass.quasiIso_map_of_mono`).
All properties follow from the uniqueness of `α` and a general naturality lemma (`LerayEdge.edge_naturality`), so no
independence-of-choices argument is needed.

General homological algebra (a gap filled: the facts are used tacitly by the paper, Ch. 0 §5, consequence (2),
p. 145).
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex

namespace CategoryTheory

variable {C D E T : Type*} [Category* C] [Category* D] [Category* E] [Category* T]
  [Abelian C] [Abelian D] [Abelian E] [Abelian T]

namespace LerayEdge

section Replacement

variable [EnoughInjectives D]

/-- The chosen monomorphic injective replacement of an `ℕ`-indexed cochain complex. -/
noncomputable def rep (M : CochainComplex D ℕ) : CochainComplex D ℕ :=
  (CochainComplex.exists_mono_quasiIso_injective_nat M).choose

/-- The chosen monomorphic quasi-isomorphism `M ⟶ rep M`. -/
noncomputable def repι (M : CochainComplex D ℕ) : M ⟶ rep M :=
  (CochainComplex.exists_mono_quasiIso_injective_nat M).choose_spec.choose

instance (M : CochainComplex D ℕ) : Mono (repι M) :=
  (CochainComplex.exists_mono_quasiIso_injective_nat M).choose_spec.choose_spec.1

instance (M : CochainComplex D ℕ) : QuasiIso (repι M) :=
  (CochainComplex.exists_mono_quasiIso_injective_nat M).choose_spec.choose_spec.2.1

instance (M : CochainComplex D ℕ) (n : ℕ) : Injective ((rep M).X n) :=
  (CochainComplex.exists_mono_quasiIso_injective_nat M).choose_spec.choose_spec.2.2 n

end Replacement

/-- The quotient functor to the homotopy category of `ℕ`-indexed cochain complexes. -/
abbrev qt (D : Type*) [Category* D] [Abelian D] :
    CochainComplex D ℕ ⥤ HomotopyCategory D (ComplexShape.up ℕ) :=
  HomotopyCategory.quotient D (ComplexShape.up ℕ)

/-- The morphism `B[0] ⟶ M` given by a coaugmentation `v : B ⟶ M⁰` (`v ≫ d⁰ = 0`). -/
noncomputable def cs {B : D} {M : CochainComplex D ℕ} (v : B ⟶ M.X 0) (hv : v ≫ M.d 0 1 = 0) :
    (CochainComplex.single₀ D).obj B ⟶ M :=
  (CochainComplex.fromSingle₀Equiv M B).symm ⟨v, hv⟩

/-- The degree `0` component of `cs v hv` is `v`. -/
@[simp]
theorem cs_f_zero {B : D} {M : CochainComplex D ℕ} (v : B ⟶ M.X 0) (hv : v ≫ M.d 0 1 = 0) :
    (cs v hv).f 0 = v := by
  simp [cs]

/-- Postcomposition of `cs v hv` with a morphism of complexes. -/
theorem cs_comp {B : D} {M M' : CochainComplex D ℕ} (v : B ⟶ M.X 0) (hv : v ≫ M.d 0 1 = 0) (m : M ⟶ M') :
    cs v hv ≫ m = cs (v ≫ m.f 0) (by rw [Category.assoc, m.comm, reassoc_of% hv, zero_comp]) := by
  ext
  simp

/-- Precomposition of `cs v hv` with `b[0]`. -/
theorem single_map_cs {B B' : D} {M : CochainComplex D ℕ} (b : B' ⟶ B) (v : B ⟶ M.X 0)
    (hv : v ≫ M.d 0 1 = 0) :
    (CochainComplex.single₀ D).map b ≫ cs v hv = cs (b ≫ v) (by rw [Category.assoc, hv, comp_zero]) := by
  ext
  simp

/-- The augmentation of an injective resolution is `cs` of its degree `0` component. -/
theorem ι_eq_cs {B : D} (J : InjectiveResolution B) : J.ι = cs (J.ι.f 0) J.ι_f_zero_comp_complex_d := by
  ext
  exact (cs_f_zero _ _).symm

/-- Two morphisms out of `B[0]` that are equal in the homotopy category are equal. -/
theorem eq_of_qt_map_eq {B : D} {K : CochainComplex D ℕ} (f g : (CochainComplex.single₀ D).obj B ⟶ K)
    (h : (qt D).map f = (qt D).map g) : f = g := by
  have H := HomotopyCategory.homotopyOfEq f g h
  ext
  have := H.comm 0
  rw [Homotopy.prevD_zero_cochainComplex, Homotopy.dNext_cochainComplex] at this
  have h0 : ((CochainComplex.single₀ D).obj B).d 0 (0 + 1) = 0 :=
    (HomologicalComplex.isZero_single_obj_X _ 0 B 1 (by simp)).eq_of_tgt _ _
  rw [h0, zero_comp, add_zero, zero_add] at this
  exact this

section Edge

variable [EnoughInjectives D]

/-- The unique map `J ⟶ rep M` in the homotopy category compatible with the coaugmentations. -/
noncomputable def edgeHom {B : D} (J : InjectiveResolution B) (M : CochainComplex D ℕ) (v : B ⟶ M.X 0)
    (hv : v ≫ M.d 0 1 = 0) : (qt D).obj J.cocomplex ⟶ (qt D).obj (rep M) :=
  (Equiv.ofBijective _ (HomotopyCategory.bijective_quotient_map_comp J.ι)).symm
    ((qt D).map (cs v hv ≫ repι M))

/-- The defining property of `edgeHom`: it is compatible with the coaugmentations. -/
theorem edgeHom_spec {B : D} (J : InjectiveResolution B) (M : CochainComplex D ℕ) (v : B ⟶ M.X 0)
    (hv : v ≫ M.d 0 1 = 0) :
    (qt D).map J.ι ≫ edgeHom J M v hv = (qt D).map (cs v hv ≫ repι M) :=
  (Equiv.ofBijective _ (HomotopyCategory.bijective_quotient_map_comp J.ι)).apply_symm_apply _

/-- `edgeHom` is an isomorphism when the coaugmentation `B[0] ⟶ M` is a quasi-isomorphism. -/
theorem isIso_edgeHom {B : D} (J : InjectiveResolution B) (M : CochainComplex D ℕ) (v : B ⟶ M.X 0)
    (hv : v ≫ M.d 0 1 = 0) (hq : QuasiIso (cs v hv)) : IsIso (edgeHom J M v hv) := by
  have hb := HomotopyCategory.bijective_quotient_map_comp (cs v hv ≫ repι M) (K := J.cocomplex)
  obtain ⟨α', hα'⟩ := hb.2 ((qt D).map J.ι)
  refine ⟨α', ?_, ?_⟩
  · refine (HomotopyCategory.bijective_quotient_map_comp J.ι (K := J.cocomplex)).1 ?_
    simp only [← Category.assoc, edgeHom_spec]
    simpa using hα'
  · refine (HomotopyCategory.bijective_quotient_map_comp (cs v hv ≫ repι M) (K := rep M)).1 ?_
    simp only [← Category.assoc, hα', edgeHom_spec]
    simp

variable (G : D ⥤ E) [G.Additive]

/-- `Hⁱ(G -)` on the homotopy category. -/
noncomputable abbrev Φ (i : ℕ) : HomotopyCategory D (ComplexShape.up ℕ) ⥤ E :=
  G.mapHomotopyCategory (ComplexShape.up ℕ) ⋙ HomotopyCategory.homologyFunctor E (ComplexShape.up ℕ) i

/-- `Hⁱ(G -)` on the homotopy category, composed with the quotient functor, is `Hⁱ(G -)` on complexes. -/
noncomputable def ΦFactors (i : ℕ) :
    qt D ⋙ Φ G i ≅ G.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) i :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors _) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (HomotopyCategory.homologyFunctorFactors E _ i)

omit [EnoughInjectives D] in
/-- `Φ G i` of a morphism of complexes is invertible iff `Hⁱ(G -)` of it is. -/
theorem isIso_Φ_map_iff {M M' : CochainComplex D ℕ} (f : M ⟶ M') (i : ℕ) :
    IsIso ((Φ G i).map ((qt D).map f)) ↔ IsIso (homologyMap ((G.mapHomologicalComplex _).map f) i) :=
  NatIso.isIso_map_iff (ΦFactors G i) f

/-- `Hⁱ(G β)` is invertible for the chosen replacement `β : M ⟶ rep M` of a complex of `G`-acyclic objects. -/
theorem isIso_Φ_map_repι {M : CochainComplex D ℕ} (hM : ∃ P, G.IsAcyclicClass P ∧ ∀ n, P (M.X n)) (i : ℕ) :
    IsIso ((Φ G i).map ((qt D).map (repι M))) := by
  obtain ⟨P, hP, hPM⟩ := hM
  have hq := hP.quasiIso_map_of_mono (repι M) hPM (fun n => hP.injective _)
  exact (isIso_Φ_map_iff G _ i).2 ((quasiIsoAt_iff_isIso_homologyMap _ i).1 (hq.quasiIsoAt i))

/-- The edge map `Hⁱ(G J) ⟶ Hⁱ(G M)` attached to a coaugmented complex `M` of `G`-acyclic objects and an injective
resolution `J` of the coaugmenting object. -/
noncomputable def edge (i : ℕ) {B : D} (J : InjectiveResolution B) (M : CochainComplex D ℕ) (v : B ⟶ M.X 0)
    (hv : v ≫ M.d 0 1 = 0) (hM : ∃ P, G.IsAcyclicClass P ∧ ∀ n, P (M.X n)) :
    (Φ G i).obj ((qt D).obj J.cocomplex) ⟶ (Φ G i).obj ((qt D).obj M) :=
  have := isIso_Φ_map_repι G hM i
  (Φ G i).map (edgeHom J M v hv) ≫ inv ((Φ G i).map ((qt D).map (repι M)))

/-- **General naturality of the edge maps.** -/
theorem edge_naturality (i : ℕ) {B B' : D} (J : InjectiveResolution B) (J' : InjectiveResolution B')
    (b : B ⟶ B') (d : J.cocomplex ⟶ J'.cocomplex) (hd : J.ι ≫ d = (CochainComplex.single₀ D).map b ≫ J'.ι)
    (M M' : CochainComplex D ℕ) (v : B ⟶ M.X 0) (hv : v ≫ M.d 0 1 = 0) (v' : B' ⟶ M'.X 0)
    (hv' : v' ≫ M'.d 0 1 = 0) (m : M ⟶ M') (hm : v ≫ m.f 0 = b ≫ v')
    (hM : ∃ P, G.IsAcyclicClass P ∧ ∀ n, P (M.X n)) (hM' : ∃ P, G.IsAcyclicClass P ∧ ∀ n, P (M'.X n)) :
    (Φ G i).map ((qt D).map d) ≫ edge G i J' M' v' hv' hM' =
      edge G i J M v hv hM ≫ (Φ G i).map ((qt D).map m) := by
  have := isIso_Φ_map_repι G hM i
  have := isIso_Φ_map_repι G hM' i
  obtain ⟨γ, hγ⟩ := (HomotopyCategory.bijective_quotient_map_comp (repι M) (K := rep M')).2
    ((qt D).map (m ≫ repι M'))
  have hcs : cs v hv ≫ m = (CochainComplex.single₀ D).map b ≫ cs v' hv' := by
    rw [cs_comp, single_map_cs]
    congr 1
  have hγ' : (qt D).map (repι M) ≫ γ = (qt D).map (m ≫ repι M') := hγ
  have key1 : edgeHom J M v hv ≫ γ = (qt D).map d ≫ edgeHom J' M' v' hv' := by
    refine (HomotopyCategory.bijective_quotient_map_comp J.ι (K := rep M')).1 ?_
    dsimp only
    calc (qt D).map J.ι ≫ edgeHom J M v hv ≫ γ = ((qt D).map J.ι ≫ edgeHom J M v hv) ≫ γ :=
          (Category.assoc _ _ _).symm
      _ = (qt D).map (cs v hv) ≫ ((qt D).map (repι M) ≫ γ) := by
          rw [edgeHom_spec, Functor.map_comp, Category.assoc]
      _ = (qt D).map (cs v hv ≫ m ≫ repι M') := by rw [hγ', ← Functor.map_comp]
      _ = (qt D).map ((CochainComplex.single₀ D).map b ≫ cs v' hv' ≫ repι M') := by
          rw [← Category.assoc, hcs, Category.assoc]
      _ = (qt D).map ((CochainComplex.single₀ D).map b) ≫ ((qt D).map J'.ι ≫ edgeHom J' M' v' hv') := by
          rw [edgeHom_spec, ← Functor.map_comp]
      _ = (qt D).map (J.ι ≫ d) ≫ edgeHom J' M' v' hv' := by
          rw [hd, Functor.map_comp, Category.assoc]
      _ = (qt D).map J.ι ≫ (qt D).map d ≫ edgeHom J' M' v' hv' := by
          rw [Functor.map_comp, Category.assoc]
  have key2 : (Φ G i).map ((qt D).map (repι M)) ≫ (Φ G i).map γ =
      (Φ G i).map ((qt D).map m) ≫ (Φ G i).map ((qt D).map (repι M')) := by
    rw [← Functor.map_comp, hγ', Functor.map_comp, Functor.map_comp]
  have key3 : (Φ G i).map γ ≫ inv ((Φ G i).map ((qt D).map (repι M'))) =
      inv ((Φ G i).map ((qt D).map (repι M))) ≫ (Φ G i).map ((qt D).map m) := by
    rw [← cancel_epi ((Φ G i).map ((qt D).map (repι M))), IsIso.hom_inv_id_assoc, ← Category.assoc, key2,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  simp only [edge, Category.assoc]
  rw [← key3, ← Category.assoc ((Φ G i).map (edgeHom J M v hv)), ← Functor.map_comp, key1, Functor.map_comp,
    Category.assoc]

/-- The edge map is an isomorphism when the coaugmentation `B[0] ⟶ M` is a quasi-isomorphism. -/
theorem isIso_edge (i : ℕ) {B : D} (J : InjectiveResolution B) (M : CochainComplex D ℕ) (v : B ⟶ M.X 0)
    (hv : v ≫ M.d 0 1 = 0) (hM : ∃ P, G.IsAcyclicClass P ∧ ∀ n, P (M.X n)) (hq : QuasiIso (cs v hv)) :
    IsIso (edge G i J M v hv hM) := by
  have := isIso_Φ_map_repι G hM i
  have := isIso_edgeHom J M v hv hq
  dsimp only [edge]
  infer_instance

/-- Naturality of the edge maps in the functor `G`. -/
theorem edge_natTrans {G' : D ⥤ E} [G'.Additive] (σ : G ⟶ G') (i : ℕ) {B : D} (J : InjectiveResolution B)
    (M : CochainComplex D ℕ) (v : B ⟶ M.X 0) (hv : v ≫ M.d 0 1 = 0)
    (hM : ∃ P, G.IsAcyclicClass P ∧ ∀ n, P (M.X n)) (hM' : ∃ P, G'.IsAcyclicClass P ∧ ∀ n, P (M.X n)) :
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory σ (ComplexShape.up ℕ))
        (HomotopyCategory.homologyFunctor E (ComplexShape.up ℕ) i)).app ((qt D).obj J.cocomplex) ≫
        edge G' i J M v hv hM' =
      edge G i J M v hv hM ≫
        (Functor.whiskerRight (NatTrans.mapHomotopyCategory σ (ComplexShape.up ℕ))
          (HomotopyCategory.homologyFunctor E (ComplexShape.up ℕ) i)).app ((qt D).obj M) := by
  have := isIso_Φ_map_repι G hM i
  have := isIso_Φ_map_repι G' hM' i
  let S := Functor.whiskerRight (NatTrans.mapHomotopyCategory σ (ComplexShape.up ℕ))
    (HomotopyCategory.homologyFunctor E (ComplexShape.up ℕ) i)
  have n1 := S.naturality (edgeHom J M v hv)
  have n2 := S.naturality ((qt D).map (repι M))
  have n3 : inv ((Φ G i).map ((qt D).map (repι M))) ≫ S.app ((qt D).obj M) =
      S.app ((qt D).obj (rep M)) ≫ inv ((Φ G' i).map ((qt D).map (repι M))) := by
    rw [← cancel_epi ((Φ G i).map ((qt D).map (repι M))), IsIso.hom_inv_id_assoc]
    rw [← cancel_mono ((Φ G' i).map ((qt D).map (repι M))), Category.assoc, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id]
    exact n2.symm
  simp only [edge, Category.assoc]
  rw [n3]
  exact ((reassoc_of% n1) _).symm

end Edge

/-- The image of a coaugmentation under an additive functor is a coaugmentation. -/
theorem map_coaug (F : D ⥤ E) [F.Additive] {B : D} {M : CochainComplex D ℕ} (v : B ⟶ M.X 0)
    (hv : v ≫ M.d 0 1 = 0) : F.map v ≫ ((F.mapHomologicalComplex _).obj M).d 0 1 = 0 := by
  dsimp
  rw [← F.map_comp, hv, F.map_zero]

/-- A coaugmentation followed by a morphism of complexes is a coaugmentation. -/
theorem comp_coaug {B : D} {M M' : CochainComplex D ℕ} (v : B ⟶ M.X 0) (hv : v ≫ M.d 0 1 = 0)
    (m : M ⟶ M') : (v ≫ m.f 0) ≫ M'.d 0 1 = 0 := by
  rw [Category.assoc, m.comm, reassoc_of% hv, zero_comp]

end LerayEdge

open LerayEdge

namespace Functor

/-- `F` sends injective objects into a class of objects acyclic for `G`. -/
def SendsInjectivesToAcyclic (F : C ⥤ D) (G : D ⥤ E) [G.Additive] : Prop :=
  ∃ P : ObjectProperty D, G.IsAcyclicClass P ∧ ∀ X : C, Injective X → P (F.obj X)

/-- `F` applied to a complex of injectives is a complex of `G`-acyclic objects. -/
theorem SendsInjectivesToAcyclic.complex {F : C ⥤ D} [F.Additive] {G : D ⥤ E} [G.Additive]
    (h : F.SendsInjectivesToAcyclic G) (I : CochainComplex C ℕ) [∀ n, Injective (I.X n)] :
    ∃ P, G.IsAcyclicClass P ∧ ∀ n, P (((F.mapHomologicalComplex _).obj I).X n) :=
  let ⟨P, hP, hF⟩ := h
  ⟨P, hP, fun _ => hF _ inferInstance⟩

section

variable [EnoughInjectives C]

/-- The coaugmentation `A ⟶ I⁰` of the chosen injective resolution of `A`. -/
noncomputable def resCoaug (A : C) : A ⟶ (injectiveResolution A).cocomplex.X 0 :=
  (injectiveResolution A).ι.f 0

/-- `resCoaug A` is a coaugmentation. -/
theorem resCoaug_comp_d (A : C) : resCoaug A ≫ (injectiveResolution A).cocomplex.d 0 1 = 0 :=
  (injectiveResolution A).ι_f_zero_comp_complex_d

/-- `resCoaug` commutes with the descent of a morphism to injective resolutions. -/
theorem resCoaug_desc {A A' : C} (φ : A ⟶ A') :
    resCoaug A ≫ (InjectiveResolution.desc φ (injectiveResolution A') (injectiveResolution A)).f 0 =
      φ ≫ resCoaug A' :=
  InjectiveResolution.desc_commutes_zero φ _ _

/-- `F (resCoaug A)` is a coaugmentation of `F(I)`. -/
theorem coaug_comp (F : C ⥤ D) [F.Additive] (A : C) :
    F.map (resCoaug A) ≫ ((F.mapHomologicalComplex _).obj (injectiveResolution A).cocomplex).d 0 1 = 0 :=
  map_coaug F _ (resCoaug_comp_d A)

end

variable [EnoughInjectives C] [EnoughInjectives D]

/-- **The edge map** `RⁱG(F A) ⟶ Rⁱ(F ⋙ G)(A)` of the Grothendieck (Leray) spectral sequence, for additive functors
`F`, `G` such that `F` sends injective objects into a class acyclic for `G`. -/
noncomputable def lerayEdge (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive]
    (h : F.SendsInjectivesToAcyclic G) (A : C) (i : ℕ) :
    (G.rightDerived i).obj (F.obj A) ⟶ ((F ⋙ G).rightDerived i).obj A :=
  edge G i (injectiveResolution (F.obj A)) ((F.mapHomologicalComplex _).obj (injectiveResolution A).cocomplex)
    (F.map (resCoaug A)) (coaug_comp F A) (h.complex _)

/-- **Naturality of the edge maps in the object.** -/
theorem lerayEdge_naturality (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive]
    (h : F.SendsInjectivesToAcyclic G) {A A' : C} (φ : A ⟶ A') (i : ℕ) :
    (G.rightDerived i).map (F.map φ) ≫ lerayEdge F G h A' i =
      lerayEdge F G h A i ≫ ((F ⋙ G).rightDerived i).map φ :=
  edge_naturality G i (injectiveResolution (F.obj A)) (injectiveResolution (F.obj A')) (F.map φ)
    (InjectiveResolution.desc (F.map φ) _ _) (InjectiveResolution.desc_commutes _ _ _) _ _ _ _ _ _
    ((F.mapHomologicalComplex _).map (InjectiveResolution.desc φ _ _))
    ((F.map_comp _ _).symm.trans ((congrArg F.map (resCoaug_desc φ)).trans (F.map_comp _ _)))
    _ _

/-- **Naturality of the edge maps in the first functor.** -/
theorem lerayEdge_natTrans_left {F F' : C ⥤ D} [F.Additive] [F'.Additive] (τ : F ⟶ F') (G : D ⥤ E)
    [G.Additive] (h : F.SendsInjectivesToAcyclic G) (h' : F'.SendsInjectivesToAcyclic G) (A : C) (i : ℕ) :
    (G.rightDerived i).map (τ.app A) ≫ lerayEdge F' G h' A i =
      lerayEdge F G h A i ≫ (NatTrans.rightDerived (Functor.whiskerRight τ G) i).app A :=
  edge_naturality G i (injectiveResolution (F.obj A)) (injectiveResolution (F'.obj A)) (τ.app A)
    (InjectiveResolution.desc (τ.app A) _ _) (InjectiveResolution.desc_commutes _ _ _) _ _ _ _ _ _
    ((NatTrans.mapHomologicalComplex τ _).app (injectiveResolution A).cocomplex)
    (τ.naturality (resCoaug A)) _ _

/-- **Naturality of the edge maps in the second functor.** -/
theorem lerayEdge_natTrans_right (F : C ⥤ D) [F.Additive] {G G' : D ⥤ E} [G.Additive] [G'.Additive]
    (σ : G ⟶ G') (h : F.SendsInjectivesToAcyclic G) (h' : F.SendsInjectivesToAcyclic G') (A : C) (i : ℕ) :
    (NatTrans.rightDerived σ i).app (F.obj A) ≫ lerayEdge F G' h' A i =
      lerayEdge F G h A i ≫ (NatTrans.rightDerived (Functor.whiskerLeft F σ) i).app A :=
  edge_natTrans G σ i _ _ _ _ _ _

omit [EnoughInjectives D] in
/-- If `F` is left exact and `R^q F A = 0` for `q > 0`, the coaugmentation `F A ⟶ F(I)` is a quasi-isomorphism. -/
theorem quasiIso_cs_coaug (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (A : C)
    (hA : ∀ q, 0 < q → IsZero ((F.rightDerived q).obj A)) :
    QuasiIso (cs (B := F.obj A) (M := (F.mapHomologicalComplex _).obj (injectiveResolution A).cocomplex)
      (F.map (resCoaug A)) (coaug_comp F A)) := by
  let I := injectiveResolution A
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · let S := ShortComplex.mk (resCoaug A) (I.cocomplex.d 0 1) (resCoaug_comp_d A)
      have hS : S.Exact := I.exact₀
      have : Mono S.f := (inferInstance : Mono (I.ι.f 0))
      have key := (S.map F).exact_and_mono_f_iff_f_is_kernel.2 ⟨KernelFork.mapIsLimit _ hS.fIsKernel F⟩
      refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).1 key
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans ((cs_f_zero (B := F.obj A)
          (M := (F.mapHomologicalComplex _).obj I.cocomplex) _ (coaug_comp F A)).trans
          (Category.comp_id _).symm))
        ((Category.id_comp _).trans (Category.comp_id _).symm)
    all_goals first
      | exact ((CochainComplex.single₀ D).obj (F.obj A)).shape 0 0 (by simp)
      | exact ((F.mapHomologicalComplex _).obj I.cocomplex).shape 0 0 (by simp)
      | exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 (F.obj A) 1 (by simp)).eq_of_tgt
          ((CochainComplex.single₀ D).obj (F.obj A) |>.d 0 1) 0
  | succ n =>
    rw [quasiIsoAt_iff_isIso_homologyMap]
    refine isIso_of_isZero _ ?_ ?_
    · exact ShortComplex.isZero_homology_of_isZero_X₂ _
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 (F.obj A) (n + 1) (by simp))
    · exact IsZero.of_iso (hA (n + 1) (by lia)) (I.isoRightDerivedObj F (n + 1)).symm

/-- **The edge maps are isomorphisms when the spectral sequence degenerates**: if `F` is left exact and
`R^q F A = 0` for all `q > 0`, then `RⁱG(F A) ⟶ Rⁱ(F ⋙ G)(A)` is an isomorphism for every `i`. -/
theorem isIso_lerayEdge (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (G : D ⥤ E) [G.Additive]
    (h : F.SendsInjectivesToAcyclic G) (A : C) (hA : ∀ q, 0 < q → IsZero ((F.rightDerived q).obj A))
    (i : ℕ) : IsIso (lerayEdge F G h A i) :=
  isIso_edge G i _ _ _ _ _ (quasiIso_cs_coaug F A hA)

/-- **Compatibility of the edge maps with three functors**:
`ε_{F₂,F₃}(F₁ A) ≫ ε_{F₁,F₂⋙F₃}(A) = ε_{F₁⋙F₂,F₃}(A)`. -/
theorem lerayEdge_comp [EnoughInjectives E] (F₁ : C ⥤ D) (F₂ : D ⥤ E) (F₃ : E ⥤ T) [F₁.Additive]
    [F₂.Additive] [F₃.Additive] (h₂₃ : F₂.SendsInjectivesToAcyclic F₃)
    (h₁ : F₁.SendsInjectivesToAcyclic (F₂ ⋙ F₃)) (h₁₂ : (F₁ ⋙ F₂).SendsInjectivesToAcyclic F₃) (A : C)
    (i : ℕ) :
    lerayEdge F₂ F₃ h₂₃ (F₁.obj A) i ≫ lerayEdge F₁ (F₂ ⋙ F₃) h₁ A i = lerayEdge (F₁ ⋙ F₂) F₃ h₁₂ A i := by
  let I := injectiveResolution A
  let J := injectiveResolution (F₁.obj A)
  let L := injectiveResolution (F₂.obj (F₁.obj A))
  let M₁ := (F₁.mapHomologicalComplex _).obj I.cocomplex
  let v₁ : F₁.obj A ⟶ M₁.X 0 := F₁.map (resCoaug A)
  have hv₁ : v₁ ≫ M₁.d 0 1 = 0 := coaug_comp F₁ A
  obtain ⟨a₂, ha₂⟩ := (qt D).map_surjective (edgeHom J M₁ v₁ hv₁)
  have hspec := edgeHom_spec J M₁ v₁ hv₁
  rw [← ha₂, ← Functor.map_comp] at hspec
  have hdeg : resCoaug (F₁.obj A) ≫ a₂.f 0 = v₁ ≫ (repι M₁).f 0 := by
    have h0 := congrArg (fun f => f.f 0) (eq_of_qt_map_eq _ _ hspec)
    simp only [HomologicalComplex.comp_f] at h0
    exact h0.trans (congrArg (· ≫ (repι M₁).f 0) (cs_f_zero v₁ hv₁))
  have hR := h₂₃.complex (rep M₁)
  have hJ := h₂₃.complex J.cocomplex
  have hM := h₁₂.complex I.cocomplex
  have hiso : IsIso ((Φ F₃ i).map ((qt E).map ((F₂.mapHomologicalComplex _).map (repι M₁)))) :=
    isIso_Φ_map_repι (F₂ ⋙ F₃) (h₁.complex _) i
  have e2 : lerayEdge F₁ (F₂ ⋙ F₃) h₁ A i =
      (Φ F₃ i).map ((qt E).map ((F₂.mapHomologicalComplex _).map a₂)) ≫
        CategoryTheory.inv ((Φ F₃ i).map ((qt E).map ((F₂.mapHomologicalComplex _).map (repι M₁)))) := by
    show (Φ (F₂ ⋙ F₃) i).map (edgeHom J M₁ v₁ hv₁) ≫ _ = _
    rw [← ha₂]
    rfl
  have N1 := edge_naturality F₃ i L L (𝟙 _) (𝟙 _) (by simp) ((F₂.mapHomologicalComplex _).obj J.cocomplex)
    ((F₂.mapHomologicalComplex _).obj (rep M₁)) (F₂.map (resCoaug (F₁.obj A))) (coaug_comp F₂ (F₁.obj A))
    (F₂.map (v₁ ≫ (repι M₁).f 0)) (map_coaug F₂ _ (comp_coaug v₁ hv₁ (repι M₁)))
    ((F₂.mapHomologicalComplex _).map a₂)
    ((F₂.map_comp _ _).symm.trans ((congrArg F₂.map hdeg).trans (Category.id_comp _).symm)) hJ hR
  have N2 := edge_naturality F₃ i L L (𝟙 _) (𝟙 _) (by simp) ((F₂.mapHomologicalComplex _).obj M₁)
    ((F₂.mapHomologicalComplex _).obj (rep M₁)) (F₂.map v₁) (map_coaug F₂ _ hv₁)
    (F₂.map (v₁ ≫ (repι M₁).f 0)) (map_coaug F₂ _ (comp_coaug v₁ hv₁ (repι M₁)))
    ((F₂.mapHomologicalComplex _).map (repι M₁))
    ((F₂.map_comp _ _).symm.trans (Category.id_comp _).symm) hM hR
  simp only [Functor.map_id, Category.id_comp] at N1 N2
  rw [e2]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun x => x ≫ CategoryTheory.inv
    ((Φ F₃ i).map ((qt E).map ((F₂.mapHomologicalComplex _).map (repι M₁))))) (N1.symm.trans N2)).trans
    (by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]; rfl))

end Functor


end CategoryTheory
