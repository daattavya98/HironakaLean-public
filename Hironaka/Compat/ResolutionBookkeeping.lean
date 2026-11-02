/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Architect
public import Hironaka.Ch0.AlgebraicScheme
public import Hironaka.Compat.LocalizeSuccession
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Compat.BlowupLocalIso
public import Hironaka.Compat.IdealSheafStalk
public import Hironaka.Statements

/-!
# Bookkeeping for the Chapter 0 announcements of the main theorems (pp. 112, 132, 138, 151, 163)

> The maximum of `dim_x(V)` for all the points `x` of an algebraic scheme `V` is a non-negative integer, provided `V` is
> not empty.  (p. 163)
> We first remark that main theorems I, I*, II, stated in the preceding sections, remain verified if the field `B` is
> replaced by any local ring belonging to a certain class of local rings, which we shall specify in the beginning
> paragraph of Chapter I, and denote by `𝔅`.  (p. 151)

Contents:
* `IsAlgebraicScheme.of_field`: an algebraic `B`-scheme with a field `B` of characteristic zero (pp. 118-119, 132) is an
  algebraic scheme in the sense of p. 162 (fields of characteristic zero belong to `𝔅`, (a) of p. 161);
* `IsAlgebraicScheme.exists_dim_le`, `exists_nat_dim_eq`: the dimension of a (non-empty) algebraic scheme is a natural
  number (p. 163, stated without proof in the paper);
* `Subscheme.red` (the associated reduced scheme), its stalks, and `red(X')` is the strict transform of `red(X)` by a
  monoidal transformation and by a succession (used for `W(i) = red(X_i)` in Main Theorem I*, p. 138).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

/-- A field of characteristic zero belongs to 𝔅, so a scheme of finite type over it is an algebraic scheme. -/
theorem IsAlgebraicScheme.of_field {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType p] [QuasiCompact p] :
    IsAlgebraicScheme X :=
  ⟨⟨B, inferInstance, inferInstance, IsHironakaBase.of_field B, p, inferInstance, inferInstance⟩⟩

/-- A finitely generated algebra over a noetherian ring has Krull dimension at most that of the ring plus a
natural number (a quotient of a polynomial ring). -/
theorem exists_ringKrullDim_le_of_finiteType {R A : Type*} [CommRing R] [CommRing A] [IsNoetherianRing R]
    (f : R →+* A) (hf : f.FiniteType) : ∃ k : ℕ, ringKrullDim A ≤ ringKrullDim R + k := by
  let _ : Algebra R A := f.toAlgebra
  have : Algebra.FiniteType R A := hf
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType R A›
  refine ⟨n, ?_⟩
  calc ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin n) R) :=
        ringKrullDim_le_of_surjective g.toRingHom hg
    _ = ringKrullDim R + n := by simp

/-- Over an affine scheme `Z` of finite type over `Spec S`, `S` noetherian: the local dimensions are bounded. -/
theorem exists_dimAt_le_of_isAffine {S : Type u} [CommRing S] [IsNoetherianRing S] {Z : Scheme.{u}}
    [IsAffine Z] (g : Z ⟶ Spec (CommRingCat.of S)) [LocallyOfFiniteType g] :
    ∃ k : ℕ, ∀ z : Z, Z.dimAt z ≤ ringKrullDim S + k := by
  let ν : Z ≅ Spec Γ(Z, ⊤) := Scheme.isoSpec Z
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (ν.inv ≫ g)
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := by
      rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  obtain ⟨k, hk⟩ := exists_ringKrullDim_le_of_finiteType φ.hom hft
  refine ⟨k, fun z => ?_⟩
  have _ : (ν.hom z).asIdeal.IsPrime := (ν.hom z).isPrime
  have e1 : ringKrullDim ((Spec Γ(Z, ⊤)).presheaf.stalk (ν.hom z)) = Z.dimAt z :=
    ringKrullDim_eq_of_ringEquiv (asIso (ν.hom.stalkMap z)).commRingCatIsoToRingEquiv
  have e2 : ringKrullDim ((Spec Γ(Z, ⊤)).presheaf.stalk (ν.hom z)) =
      ((ν.hom z).asIdeal.height : WithBot ℕ∞) := by
    let _ : Algebra Γ(Z, ⊤) ((Spec Γ(Z, ⊤)).presheaf.stalk (ν.hom z)) :=
      StructureSheaf.stalkAlgebra Γ(Z, ⊤) (ν.hom z)
    have : IsLocalization.AtPrime ((Spec Γ(Z, ⊤)).presheaf.stalk (ν.hom z)) (ν.hom z).asIdeal :=
      StructureSheaf.IsLocalization.to_stalk Γ(Z, ⊤) (ν.hom z)
    exact IsLocalization.AtPrime.ringKrullDim_eq_height (ν.hom z).asIdeal _
  have e3 : ((ν.hom z).asIdeal.height : WithBot ℕ∞) ≤ ringKrullDim Γ(Z, ⊤) :=
    Ideal.height_le_ringKrullDim_of_ne_top (ν.hom z).isPrime.ne_top
  rw [← e1, e2]
  exact e3.trans hk

/-- p. 163: "The maximum of `dim_x(V)` for all the points `x` of an algebraic scheme `V` is a non-negative integer,
provided `V` is not empty": here the bound `dim V ≤ N`.

Deviation from the paper (gap filled): the paper states this without proof.  `X` is quasi-compact, so a finite
affine open cover; on a chart `Spec A`, `A` is of finite type over the noetherian local ring `S`, a quotient of a
polynomial ring `S[T₁, …, T_k]`, so `dim O_{X,x} = ht(p) ≤ dim A ≤ dim S + k` (`dim S < ∞`, Krull). -/
@[blueprint "lem:I.0-dimension-finite"
  (statement := /-- An algebraic scheme $V$ has $\dim(V)\le N$ for some natural number $N$ (and $\dim(V)$ is a
    natural number if $V$ is not empty). (p.~163.) -/)
  (proof := /-- $V$ is quasi-compact, hence covered by finitely many affine opens $\operatorname{Spec}A_i$ with
    $A_i$ of finite type over the noetherian local ring $S$, i.e.\ a quotient of $S[T_1,\dots,T_{k_i}]$ of
    dimension $\dim S+k_i$ (Krull). The local ring at a point is a localization of some $A_i$, so its dimension is
    at most $\dim A_i$. \textbf{Gap in the paper filled.} The paper states this without proof (p.~163). -/)
  (latexEnv := "lemma")]
theorem IsAlgebraicScheme.exists_dim_le (X : Scheme.{u}) [IsAlgebraicScheme X] :
    ∃ N : ℕ, X.dim ≤ (N : WithBot ℕ∞) := by
  obtain ⟨S, _, _, hS, p, hp, hq⟩ := IsAlgebraicScheme.exists_base (X := X)
  have : IsNoetherianRing S := inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim S = (m : WithBot ℕ∞) := by
    induction h : ringKrullDim S using WithBot.recBotCoe with
    | bot => exact absurd h ringKrullDim_ne_bot
    | coe a =>
      induction a using ENat.recTopCoe with
      | top => exact absurd h ringKrullDim_ne_top
      | coe n => exact ⟨n, rfl⟩
  let 𝒰 := X.affineCover.finiteSubcover
  have hk : ∀ i : 𝒰.I₀, ∃ k : ℕ, ∀ z : 𝒰.X i, (𝒰.X i).dimAt z ≤ ((m + k : ℕ) : WithBot ℕ∞) := by
    intro i
    obtain ⟨k, hk⟩ := exists_dimAt_le_of_isAffine (𝒰.f i ≫ p)
    refine ⟨k, fun z => (hk z).trans ?_⟩
    rw [hm]
    push_cast
    exact le_rfl
  choose K hK using hk
  refine ⟨m + Finset.univ.sup K, iSup_le fun x => ?_⟩
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  have e : ringKrullDim (X.presheaf.stalk (𝒰.f i y)) = (𝒰.X i).dimAt y :=
    ringKrullDim_eq_of_ringEquiv (asIso ((𝒰.f i).stalkMap y)).commRingCatIsoToRingEquiv
  have h1 : X.dimAt (𝒰.f i y) ≤ ((m + K i : ℕ) : WithBot ℕ∞) := e.le.trans (hK i y)
  refine h1.trans ?_
  exact_mod_cast Nat.add_le_add_left (Finset.le_sup (f := K) (Finset.mem_univ i)) m


/-- p. 163: a non-empty algebraic scheme has a natural number as dimension (see `IsAlgebraicScheme.exists_dim_le`). -/
theorem IsAlgebraicScheme.exists_nat_dim_eq (X : Scheme.{u}) [IsAlgebraicScheme X] [Nonempty X] :
    ∃ n : ℕ, X.dim = (n : WithBot ℕ∞) := by
  obtain ⟨N, hN⟩ := IsAlgebraicScheme.exists_dim_le X
  have hne : X.dim ≠ ⊥ := by
    obtain ⟨z⟩ := ‹Nonempty X›
    intro hb
    have h1 : X.dimAt z ≤ X.dim := LocSucc.dimAt_le_dim z
    have h2 : (0 : WithBot ℕ∞) ≤ X.dimAt z := ringKrullDim_nonneg_of_nontrivial
    rw [hb] at h1
    exact absurd (h2.trans h1) (by simp)
  obtain ⟨m, hm, -⟩ := LocSucc.exists_nat_of_le hne hN
  exact ⟨m, hm⟩


/-! ### The associated reduced scheme and strict transforms -/

namespace Subscheme

variable {X : Scheme.{u}}


/-- The associated reduced scheme is reduced. -/
theorem isReduced_red (D : Subscheme X) : (red D).IsReduced :=
  isReduced_of_radical_eq _ (Scheme.IdealSheafData.ext (funext fun _ => Ideal.radical_idem _))

/-- The stalk of `red(D)` is the radical of the stalk of `D` (radicals commute with localization). -/
theorem stalkIdeal_red (D : Subscheme X) (x : X) :
    (red D).stalkIdeal x = (D.stalkIdeal x).radical := by
  obtain ⟨W, hxW⟩ := exists_affineOpen_mem x
  have hW : IsAffineOpen (W : X.Opens) := W.2
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (U := W) ⟨x, hxW⟩
  have : IsLocalization (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl (X.presheaf.stalk x) :=
    hW.isLocalization_stalk ⟨x, hxW⟩
  rw [stalkIdeal_eq_map_germ_affine (red D) W hxW, stalkIdeal_eq_map_germ_affine D W hxW]
  exact IsLocalization.map_radical (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl (X.presheaf.stalk x)
    (D.ideal W)

/-- The stalk of `red(X)` is the nilradical of the local ring. -/
theorem stalkIdeal_red_bot (x : X) :
    (red (⊥ : Subscheme X)).stalkIdeal x = nilradical (X.presheaf.stalk x) := by
  rw [stalkIdeal_red, stalkIdeal_bot_eq]
  rfl

end Subscheme

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X}

/-- `red(X_{i+1})` is the strict transform of `red(X_i)`.  In the paper this identification is invisible: it is what
turns `W(i)`, the strict transforms of `W = red(X)` of Main Theorem I(n), into the schemes `red(X_i)` of Main
Theorem I* (p. 138).  `X'` is the scheme-theoretic closure of the complement of the exceptional divisor, where `f` is
a local isomorphism.

Deviation from the paper (gap filled): unprinted.  Proof on stalks: the strict transform of the nilradical consists of
nilpotents (`r g^n` nilpotent with `g` a non-zero-divisor), and conversely `red(X')` agrees with `f⁻¹(red X)` off `E`,
hence lies in the strict transform (the supremum of those). -/
theorem strictTransform_red_bot (t : MonoidalTransformation X B) :
    Subscheme.strictTransform t (Subscheme.red (⊥ : Subscheme X)) =
      Subscheme.red (⊥ : Subscheme t.X') := by
  refine Subscheme.ext_stalkIdeal fun y => ?_
  rw [Subscheme.stalkIdeal_red_bot]
  apply le_antisymm
  · rw [Subscheme.strictTransform_stalkIdeal]
    refine iSup_le fun n r hr => ?_
    obtain ⟨g, hg, hnzd⟩ := t.invertible.exists_stalkIdeal_eq_span y
    have hg' : t.exceptional.stalkIdeal y = Ideal.span {g} := hg
    have hmem := Submodule.mem_colon.mp hr (g ^ n)
      (by rw [hg', Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
    rw [stalkIdeal_totalTransform, Subscheme.stalkIdeal_red_bot] at hmem
    have hnil : r • g ^ n ∈ nilradical (t.X'.presheaf.stalk y) := by
      refine (Ideal.map_radical_le _).trans ?_ hmem
      rw [Ideal.zero_eq_bot, Ideal.map_bot]
      exact le_rfl
    obtain ⟨k, hk⟩ := hnil
    refine ⟨k, ?_⟩
    have h1 : (g ^ n) ^ k * r ^ k = 0 := by
      rw [mul_comm, ← mul_pow]; exact hk
    exact (mem_nonZeroDivisors_iff.mp (pow_mem (pow_mem hnzd n) k)).1 _ h1
  · have hmem : Subscheme.red (⊥ : Subscheme t.X') ∈
        {V' : Subscheme t.X' | ∀ x' : t.X', x' ∉ t.exceptional.pts →
          V'.stalkIdeal x' =
            (Subscheme.totalTransform t.f (Subscheme.red (⊥ : Subscheme X))).stalkIdeal x'} := by
      intro x' hx'
      have hfx : t.f.base x' ∉ B.pts := fun h => hx' (by rw [t.pts_exceptional]; exact h)
      have hbij := bijective_stalkMap_of_notMem_pts t x' hfx
      rw [Subscheme.stalkIdeal_red_bot, stalkIdeal_totalTransform, Subscheme.stalkIdeal_red_bot]
      have := Ideal.map_radical_of_surjective hbij.2
        (I := (⊥ : Ideal (X.presheaf.stalk (t.f.base x'))))
        (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hbij.1])
      rw [Ideal.map_bot] at this
      exact this.symm
    have hle : Subscheme.red (⊥ : Subscheme t.X') ≤
        Subscheme.strictTransform t (Subscheme.red (⊥ : Subscheme X)) := le_sSup hmem
    have h := Subscheme.le_iff_stalkIdeal_le.mp hle y
    rwa [Subscheme.stalkIdeal_red_bot] at h

end MonoidalTransformation

namespace MonoidalSuccession

/-- The strict transform of `red(X)` by a succession of monoidal transformations is `red(Y)`. -/
theorem strictTransform_red_bot {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) :
    s.strictTransform (Subscheme.red (⊥ : Subscheme X)) = Subscheme.red (⊥ : Subscheme Y) := by
  induction s with
  | nil X => rfl
  | cons B t rest ih =>
    rw [MonoidalSuccession.strictTransform_cons, MonoidalTransformation.strictTransform_red_bot]
    exact ih

end MonoidalSuccession

end Hironaka
