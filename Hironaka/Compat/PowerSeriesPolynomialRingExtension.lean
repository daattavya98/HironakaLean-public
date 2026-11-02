/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Architect
public import Hironaka.Compat.PowerSeriesPolynomialRing
public import Hironaka.Compat.DerivationExtension

/-!
# Compatibility layer: partial derivations of `k⟦t⟧[x,y]` along a base change of `x`

A step in the proof of property (c) of the class 𝔅 (p. 161).  Let
`T = k⟦t⟧[x₁..x_m]`, `T₁ = k⟦t⟧[x₁..x_m, y₁..y_l]` and let `τ : T → C` be a ring homomorphism to a
`k`-algebra `C` (in the application `C` is the completion of a localization `T_P`).  The ring
homomorphism `extensionHom τ : T₁ → C[y₁..y_l]` sends `k⟦t⟧` and the `x_i` through `τ` and `y_a` to
`y_a`.  If `d_j` are `k`-derivations of `C` compatible with the partial derivations of `T` along
`τ`, then every partial derivation `∂_J` of `T₁` extends along `extensionHom τ` to a derivation of
`C[y]`: `∂/∂t_j`, `∂/∂x_i` act coefficientwise by `d_j`, and `∂/∂y_a` is the formal derivative.
-/

@[expose] public section

open MvPowerSeries

noncomputable section

universe u

namespace Hironaka

namespace PowerSeriesPolynomialRing

section Generators

variable {k : Type*} [Field k] {n m : ℕ}

theorem pderivT_C (j : Fin n) (c : MvPowerSeries (Fin n) k) :
    pderivT k n m j (C c) = C (MvPowerSeries.pderiv j c : MvPowerSeries (Fin n) k) := by
  change mapCoeffsFun (Fin m) (MvPowerSeries.pderiv j :
    Derivation k (MvPowerSeries (Fin n) k) (MvPowerSeries (Fin n) k)) (MvPolynomial.C c) =
    MvPolynomial.C _
  ext s
  rw [coeff_mapCoeffsFun]
  simp only [MvPolynomial.coeff_C]
  split_ifs
  · rfl
  · simp

theorem pderivT_X (j : Fin n) (l : Fin m) : pderivT k n m j (X l) = 0 := by
  change mapCoeffsFun (Fin m) (MvPowerSeries.pderiv j :
    Derivation k (MvPowerSeries (Fin n) k) (MvPowerSeries (Fin n) k)) (MvPolynomial.X l) = 0
  ext s
  rw [coeff_mapCoeffsFun]
  simp only [MvPolynomial.coeff_X]
  split_ifs <;> simp

theorem pderivX_C (l : Fin m) (c : MvPowerSeries (Fin n) k) : pderivX k n m l (C c) = 0 := by
  show (MvPolynomial.pderiv l : Derivation (MvPowerSeries (Fin n) k)
    (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))
    (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) (MvPolynomial.C c) = 0
  exact MvPolynomial.pderiv_C

theorem pderivX_X (l l' : Fin m) :
    pderivX k n m l (X l') = if l' = l then 1 else 0 := by
  show (MvPolynomial.pderiv l : Derivation (MvPowerSeries (Fin n) k)
    (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))
    (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) (MvPolynomial.X l') = _
  rw [MvPolynomial.pderiv_X]
  exact Pi.single_apply _ _ _

/-- The partial derivation `∂/∂u_J` on a constant `c ∈ k⟦t⟧`. -/
theorem pderiv_apply_C (J : Fin (n + m)) (c : MvPowerSeries (Fin n) k) :
    pderiv k n m J (C c) =
      if h : J.val < n then C (MvPowerSeries.pderiv ⟨J.val, h⟩ c : MvPowerSeries (Fin n) k)
      else 0 := by
  induction J using Fin.addCases with
  | left j =>
    simp only [pderiv, Fin.addCases_left, Fin.val_castAdd, j.isLt, dite_true]
    exact pderivT_C j c
  | right l =>
    simp only [pderiv, Fin.addCases_right, Fin.val_natAdd]
    have hn : ¬ (n + l.val < n) := by omega
    simp only [hn, dite_false]
    exact pderivX_C l c

/-- The partial derivation `∂/∂u_J` on a polynomial variable. -/
theorem pderiv_apply_X (J : Fin (n + m)) (l : Fin m) :
    pderiv k n m J (X l) = if J.val = n + l.val then 1 else 0 := by
  induction J using Fin.addCases with
  | left j =>
    simp only [pderiv, Fin.addCases_left, Fin.val_castAdd]
    have hn : ¬ (j.val = n + l.val) := by omega
    simp only [hn, ite_false]
    exact pderivT_X j l
  | right l' =>
    simp only [pderiv, Fin.addCases_right, Fin.val_natAdd]
    rw [pderivX_X]
    by_cases h : l = l'
    · subst h; simp
    · have h' : ¬ (l'.val = l.val) := fun h'' => h (Fin.ext h''.symm)
      simp [h, h']

/-- Induction on `k⟦t⟧[x]`: constants, sums, multiplication by a variable. -/
theorem induction_on_C_X {P : PowerSeriesPolynomialRing k n m → Prop}
    (p : PowerSeriesPolynomialRing k n m) (hC : ∀ c, P (C c))
    (hadd : ∀ p q, P p → P q → P (p + q)) (hX : ∀ p l, P p → P (p * X l)) : P p :=
  MvPolynomial.induction_on (motive := P) p hC hadd hX

/-- Two "derivations along `ρ`" of `k⟦t⟧[x]` that agree on `C c` and `X l` are equal. -/
theorem funext_of_twisted_leibniz {N : Type*} [CommRing N]
    (ρ : PowerSeriesPolynomialRing k n m →+* N) (δ₁ δ₂ : PowerSeriesPolynomialRing k n m →+ N)
    (h₁ : ∀ a b, δ₁ (a * b) = ρ a * δ₁ b + ρ b * δ₁ a)
    (h₂ : ∀ a b, δ₂ (a * b) = ρ a * δ₂ b + ρ b * δ₂ a)
    (hC : ∀ c, δ₁ (C c) = δ₂ (C c)) (hX : ∀ l, δ₁ (X l) = δ₂ (X l))
    (p : PowerSeriesPolynomialRing k n m) : δ₁ p = δ₂ p := by
  refine induction_on_C_X (P := fun p => δ₁ p = δ₂ p) p hC (fun p q hp hq => ?_)
    (fun p l hp => ?_)
  · rw [map_add, map_add, hp, hq]
  · rw [h₁, h₂, hp, hX]

end Generators

end PowerSeriesPolynomialRing

section MapCoeffsGenerators

variable {k S σ : Type*} [CommRing k] [CommRing S] [Algebra k S]

theorem mapCoeffsDerivation_C_apply (d : Derivation k S S) (a : S) :
    mapCoeffsDerivation k σ d (MvPolynomial.C a) = MvPolynomial.C (d a) := by
  classical
  change mapCoeffsFun σ d (MvPolynomial.C a) = _
  ext s
  rw [coeff_mapCoeffsFun]
  simp only [MvPolynomial.coeff_C]
  split_ifs
  · rfl
  · simp

theorem mapCoeffsDerivation_X_apply (d : Derivation k S S) (i : σ) :
    mapCoeffsDerivation k σ d (MvPolynomial.X i) = 0 := by
  classical
  change mapCoeffsFun σ d (MvPolynomial.X i) = 0
  ext s
  rw [coeff_mapCoeffsFun]
  simp only [MvPolynomial.coeff_X]
  split_ifs <;> simp

end MapCoeffsGenerators

namespace PowerSeriesPolynomialRing

section Extension

variable {k : Type u} [Field k] {n m l : ℕ} {S : Type u} [CommRing S] [Algebra k S]

/-- The ring homomorphism `k⟦t⟧[x₁..x_m, y₁..y_l] → S[y₁..y_l]` induced by `τ : k⟦t⟧[x] → S`: it
sends `k⟦t⟧` and `x_i` through `τ`, and `y_a` to `y_a`. -/
def extensionHom (τ : PowerSeriesPolynomialRing k n m →+* S) :
    PowerSeriesPolynomialRing k n (m + l) →+* MvPolynomial (Fin l) S :=
  eval₂ (MvPolynomial.C.comp (τ.comp C))
    (Fin.addCases (motive := fun _ => MvPolynomial (Fin l) S)
      (fun i => MvPolynomial.C (τ (X i))) (fun a => MvPolynomial.X a))

omit [Algebra k S] in
theorem extensionHom_C (τ : PowerSeriesPolynomialRing k n m →+* S) (c : MvPowerSeries (Fin n) k) :
    extensionHom (l := l) τ (C c) = MvPolynomial.C (τ (C c)) := by
  simp [extensionHom]

omit [Algebra k S] in
theorem extensionHom_X_castAdd (τ : PowerSeriesPolynomialRing k n m →+* S) (i : Fin m) :
    extensionHom (l := l) τ (X (Fin.castAdd l i)) = MvPolynomial.C (τ (X i)) := by
  simp [extensionHom]

omit [Algebra k S] in
theorem extensionHom_X_natAdd (τ : PowerSeriesPolynomialRing k n m →+* S) (a : Fin l) :
    extensionHom (l := l) τ (X (Fin.natAdd m a)) = MvPolynomial.X a := by
  simp [extensionHom]

/-- The partial derivations of `S[y₁..y_l]` extending those of `k⟦t⟧[x,y]` along `extensionHom`:
for `J < n + m` (the variables `t` and `x`) the coefficientwise derivation `d_J`, and for the
variables `y_a` the formal derivative `∂/∂y_a`. -/
def extensionDerivation (d : Fin (n + m) → Derivation k S S) (J : Fin (n + (m + l))) :
    Derivation k (MvPolynomial (Fin l) S) (MvPolynomial (Fin l) S) :=
  if h : J.val < n + m then mapCoeffsDerivation k (Fin l) (d ⟨J.val, h⟩)
  else (MvPolynomial.pderiv (⟨J.val - (n + m), by omega⟩ : Fin l) :
    Derivation S (MvPolynomial (Fin l) S) (MvPolynomial (Fin l) S)).restrictScalars k

/-- **The partial derivations of `k⟦t⟧[x,y]` extend along `extensionHom`.**  If `d_j` are
`k`-derivations of `S` with `d_j(τ t) = τ(∂_j t)` for `t ∈ k⟦t⟧[x]`, then
`extensionDerivation d J (extensionHom τ F) = extensionHom τ (∂_J F)`. -/
@[blueprint "lem:extension-derivation-compat"
  (statement := /-- Let $S$ be a $k$-algebra, $\tau\colon k[[t]][x]\to S$ a ring homomorphism and
    $d_j$ ($j\le n+m$) $k$-derivations of $S$ with $d_j(\tau a)=\tau(\partial_ja)$. Extend the
    $d_j$ to $S[y_1,\dots,y_l]$ by $d_{n+m+a}=\partial/\partial y_a$. Then
    $d_J(\tau_1F)=\tau_1(\partial_JF)$ for every $F\in k[[t]][x,y]$, where
    $\tau_1\colon k[[t]][x,y]\to S[y]$ extends $\tau$ by $y_a\mapsto y_a$. -/)
  (proof := /-- Both sides are derivations in $F$ along $\tau_1$, and they agree on constants
    ($k[[t]][x]$, by hypothesis) and on the variables $y_a$ (both are the Kronecker delta), hence
    agree everywhere (induction on the form of $F$: constants, sums, products with a variable).
    -/)
  (latexEnv := "lemma")]
theorem extensionDerivation_extensionHom (τ : PowerSeriesPolynomialRing k n m →+* S)
    (d : Fin (n + m) → Derivation k S S)
    (hd : ∀ (j : Fin (n + m)) (t : PowerSeriesPolynomialRing k n m),
      d j (τ t) = τ (pderiv k n m j t))
    (J : Fin (n + (m + l))) (F : PowerSeriesPolynomialRing k n (m + l)) :
    extensionDerivation d J (extensionHom τ F) = extensionHom τ (pderiv k n (m + l) J F) := by
  let ρ := extensionHom (l := l) τ
  let δ₁ : PowerSeriesPolynomialRing k n (m + l) →+ MvPolynomial (Fin l) S :=
    (extensionDerivation d J).toLinearMap.toAddMonoidHom.comp ρ.toAddMonoidHom
  let δ₂ : PowerSeriesPolynomialRing k n (m + l) →+ MvPolynomial (Fin l) S :=
    ρ.toAddMonoidHom.comp (pderiv k n (m + l) J).toLinearMap.toAddMonoidHom
  refine funext_of_twisted_leibniz ρ δ₁ δ₂ ?_ ?_ ?_ ?_ F
  · intro a b
    show extensionDerivation d J (ρ (a * b)) = _
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    rfl
  · intro a b
    show ρ (pderiv k n (m + l) J (a * b)) = _
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
    rfl
  · intro c
    show extensionDerivation d J (ρ (C c)) = ρ (pderiv k n (m + l) J (C c))
    rw [extensionHom_C, pderiv_apply_C]
    by_cases h : J.val < n + m
    · have hd' := hd ⟨J.val, h⟩ (C c)
      rw [pderiv_apply_C] at hd'
      simp only [extensionDerivation, h, dite_true, mapCoeffsDerivation_C_apply]
      rw [hd']
      by_cases h' : J.val < n
      · simp only [h', dite_true]
        exact (extensionHom_C τ _).symm
      · simp [h']
    · have h' : ¬ J.val < n := by omega
      simp only [extensionDerivation, h, dite_false, h']
      simp
  · intro l'
    show extensionDerivation d J (ρ (X l')) = ρ (pderiv k n (m + l) J (X l'))
    rw [pderiv_apply_X]
    induction l' using Fin.addCases with
    | left i =>
      rw [extensionHom_X_castAdd]
      simp only [Fin.val_castAdd]
      by_cases h : J.val < n + m
      · have hd' := hd ⟨J.val, h⟩ (X i)
        rw [pderiv_apply_X] at hd'
        simp only [extensionDerivation, h, dite_true, mapCoeffsDerivation_C_apply]
        rw [hd']
        by_cases h' : J.val = n + i.val
        · simp [h']
        · simp [h']
      · have h' : ¬ J.val = n + i.val := by omega
        simp only [extensionDerivation, h, dite_false, h']
        simp
    | right a =>
      rw [extensionHom_X_natAdd]
      simp only [Fin.val_natAdd]
      by_cases h : J.val < n + m
      · have h' : ¬ J.val = n + (m + a.val) := by omega
        simp only [extensionDerivation, h, dite_true, mapCoeffsDerivation_X_apply, h']
        simp
      · simp only [extensionDerivation, h, dite_false]
        simp only [Derivation.restrictScalars_apply]
        rw [MvPolynomial.pderiv_X, Pi.single_apply]
        by_cases h' : J.val = n + (m + a.val)
        · have ha : a = ⟨J.val - (n + m), by omega⟩ := Fin.ext (by simp; omega)
          simp only [eq_true ha, eq_true h', ↓reduceIte, map_one]
        · have ha : ¬ a = ⟨J.val - (n + m), by omega⟩ := fun h'' => h' (by
            have := congrArg Fin.val h''
            simp at this
            omega)
          simp only [eq_false ha, eq_false h', ↓reduceIte, map_zero]

end Extension

end PowerSeriesPolynomialRing

end Hironaka
