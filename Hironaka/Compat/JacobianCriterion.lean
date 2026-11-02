/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.PowerSeriesPolynomialRing
public import Hironaka.Statements

/-!
# Compatibility layer: Cohen's theorem and the jacobian criterion of footnote 30 (cited facts)

Property (c) of the class 𝔅 (Ch. I, p. 161) and the closedness (iii) of the singular locus are
proved in the paper by reduction to the case of a complete base ring `S` and the jacobian
criterion.  Footnote 30 (p. 161):

> A proof of this fact can be obtained by reducing it (by virtue of (ii)) to the case in which S is
> complete, hence, it is a homomorphic image of a formal power series ring over a field of
> characteristic zero.  Namely, we have only to prove (iii) for the case in which A is a
> homomorphic image of a polynomial ring over such a formal power series ring.  For this case,
> will suffice the jacobian criterion for simplicity.  (cf. Nagata, [14], or Nagata, § 46, Ch. VII
> of [15].)  We can also make use of Theorem 1 (with its proof in § 1) of: *On the closedness of
> singular loci*, by M. Nagata, Publ. Math. de l'Inst. des Hautes Etudes Scientifiques, No. 2,
> 1959.

and footnote 31 (on (c)): "Reduce the proof to the case in which S is complete, and then apply the
jacobian criterion."  Two cited leaves:

* `exists_surjective_mvPowerSeries_of_isAdicComplete` (**L1**): the first half of footnote 30, a
  complete noetherian local ring with residue field of characteristic zero is a homomorphic image
  of a formal power series ring over a field of characteristic zero (Cohen's structure theorem).
  It duplicates in content the project's other Cohen leaves (`thm:cohen-structure`,
  `thm:cohen-coefficient-field`), which live downstream of Ch. 0 and cannot be imported here.
* `isRegularLocalRing_localization_iff_rank_jacobian_eq_height` (**L2**): the jacobian criterion
  for simplicity (Nagata [14]) for the ring `k⟦t₁,…,t_n⟧[x₁,…,x_m]` of footnote 30.

The ring `T = k⟦t₁,…,t_n⟧[x₁,…,x_m]` is `PowerSeriesPolynomialRing`, with its `n + m` partial
derivations `PowerSeriesPolynomialRing.pderiv` (`Hironaka/Compat/PowerSeriesPolynomialRing.lean`).
-/

@[expose] public section

open IsLocalRing

noncomputable section

namespace Hironaka

universe u


/-- **(L1)** (Cohen's structure theorem, in the form of footnote 30, p. 161.)  A complete noetherian
local ring `S` whose residue field has characteristic zero is a homomorphic image of a formal
power series ring `k⟦t₁,…,t_n⟧` over a field `k` of characteristic zero.

Cited, not proved in the paper: footnote 30, p. 161 ("... to the case in which S is complete,
hence, it is a homomorphic image of a formal power series ring over a field of characteristic
zero"); I. S. Cohen, *On the structure and ideal theory of complete local rings*, Trans. Amer. Math.
Soc. 59 (1946), 54–106; Matsumura, *Commutative Ring Theory*, §§28–29.

Encoding: "homomorphic image" is a surjective ring homomorphism.  The universe of `k` is that of
`S` (one may take `k = S/𝔪`).  This duplicates in content the cited Cohen theorems
`thm:cohen-structure` (`Ch2/AscendingChain.lean`) and Cohen's coefficient field
(`Compat/CoefficientField.lean`). -/
@[blueprint "lem:cohen-power-series-image"
  (statement := /-- Let $S$ be a complete noetherian local ring whose residue field has
    characteristic zero. Then $S$ is a homomorphic image of a formal power series ring
    $k[[t_1,\dots,t_n]]$ over a field $k$ of characteristic zero. (Footnote~30, p.~161.) -/)
  (proof := /-- Cited, not proved in the paper: footnote~30, p.~161 (``A proof of this fact can be
    obtained by reducing it (by virtue of (ii)) to the case in which S is complete, hence, it is
    a homomorphic image of a formal power series ring over a field of characteristic zero.'');
    I.~S.~Cohen, On the structure and ideal theory of complete local rings, Trans.\ Amer.\ Math.\
    Soc.\ 59 (1946); Matsumura, \emph{Commutative Ring Theory}, \S\S28--29. This duplicates in
    content the downstream Cohen leaves \cref{thm:cohen-structure} and
    \cref{thm:cohen-coefficient-field}. -/)
  (latexEnv := "theorem")]
theorem exists_surjective_mvPowerSeries_of_isAdicComplete [Hironaka.Cited.ExistsSurjectiveMvPowerSeriesOfIsAdicComplete.{u}] :
    ∀ (S : Type u) [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
    [CharZero (ResidueField S)],
    ∃ (n : ℕ) (k : Type u) (_ : Field k) (_ : CharZero k) (f : MvPowerSeries (Fin n) k →+* S),
      Function.Surjective f :=
  @Hironaka.Cited.ExistsSurjectiveMvPowerSeriesOfIsAdicComplete.exists_surjective_mvPowerSeries_of_isAdicComplete _


open PowerSeriesPolynomialRing in
/-- **(L2)** (The jacobian criterion for simplicity, footnote 30, p. 161, for
`T = k⟦t₁,…,t_n⟧[x₁,…,x_m]`.)  Let `k` be a field of characteristic zero, `𝔭 ⊆ 𝔮`
prime ideals of `T` (`𝔮` is given as the preimage of a prime `𝔮'` of `T/𝔭`), `R = T_𝔮`, and
`f₁,…,f_r` generators of `𝔭`.  Then `R/𝔭R = (T/𝔭)_{𝔮'}` is a regular local ring if and only if
`rank (J(f₁,…,f_r) modulo 𝔮) = rank 𝔭` (the height of `𝔭`), `J` being the matrix of partial
derivatives `(∂f_i/∂t_j, ∂f_i/∂x_l)`.

Cited, not proved in the paper: footnote 30, p. 161 ("For this case, will suffice the jacobian
criterion for simplicity.  (cf. Nagata, [14], or Nagata, § 46, Ch. VII of [15].)").  Nagata [14]
(M. Nagata, *A Jacobian criterion of simple points*, Illinois J. Math. 1 (1957), 427–432),
p. 429: "THEOREM.  Let A be the formal power series ring in indeterminates X₁, ⋯, Xₙ over a field
k, let 𝔭 ⊆ 𝔮 be prime ideals of A and set R = A_𝔮.  Furthermore, let {f₁, ⋯, f_r} be a set of
generators of 𝔭.  Then the following holds: (1) If A/𝔮 is separably generated over k, R/𝔭R is a
regular local ring if and only if rank (J(f₁, ⋯, f_r) modulo 𝔮) = rank 𝔭."  (Separable generation
is automatic in characteristic 0; (2) is the characteristic `p` case.)  Introduction of [14]:
"Although we shall treat the algebroid case, our proof is also valid for the algebraic case if
formal power series rings are replaced by polynomial rings."  Remark 3: "our proof can be applied
to another case, which may be called the analytic case" (convergent power series).

Encoding: `T` is `PowerSeriesPolynomialRing k n m` with its partial derivations
`PowerSeriesPolynomialRing.pderiv`; the prime `𝔮 ⊇ 𝔭` is given by the prime `𝔮'` of `T ⧸ 𝔭` with
`𝔮 = 𝔮'.comap (mk 𝔭)`, so `R/𝔭R` is `Localization.AtPrime 𝔮'`; "rank modulo 𝔮" is the rank of
the matrix over the fraction field of `T/𝔮` (`residueMap`), and "rank 𝔭" is `𝔭.height`. -/
@[blueprint "lem:jacobian-criterion"
  (statement := /-- Let $k$ be a field of characteristic zero, $T=k[[t_1,\dots,t_n]][x_1,\dots,
    x_m]$, $\mathfrak p\subseteq\mathfrak q$ prime ideals of $T$, $R=T_{\mathfrak q}$ and
    $f_1,\dots,f_r$ generators of $\mathfrak p$. Then $R/\mathfrak pR$ is a regular local ring
    if and only if
    $\operatorname{rank}(J(f_1,\dots,f_r)\bmod\mathfrak q)=\operatorname{rank}\mathfrak p$,
    where $J=(\partial f_i/\partial t_j,\partial f_i/\partial x_l)$ is the jacobian matrix of
    partial derivatives. (The jacobian criterion for simplicity, footnote~30, p.~161.) -/)
  (proof := /-- Cited, not proved in the paper: footnote~30, p.~161 (``For this case, will
    suffice the jacobian criterion for simplicity. (cf. Nagata, [14], or Nagata, \S~46, Ch.~VII
    of [15].)''). Nagata [14, p.~429]: ``Let A be the formal power series ring in indeterminates
    $X_1,\dots,X_n$ over a field k, let $\mathfrak p\subseteq\mathfrak q$ be prime ideals of A and
    set $R=A_{\mathfrak q}$. Furthermore, let $\{f_1,\dots,f_r\}$ be a set of generators of
    $\mathfrak p$. Then the following holds: (1) If $A/\mathfrak q$ is separably generated over k,
    $R/\mathfrak pR$ is a regular local ring if and only if rank$(J(f_1,\dots,f_r)$ modulo
    $\mathfrak q)$ = rank $\mathfrak p$.'' (Separable generation is automatic in characteristic
    0.) -/)
  (latexEnv := "theorem")]
theorem isRegularLocalRing_localization_iff_rank_jacobian_eq_height [Hironaka.Cited.IsRegularLocalRingLocalizationIffRankJacobianEqHeight.{u}] :
    ∀ (k : Type u) [Field k]
    [CharZero k] (n m : ℕ) (𝔭 : Ideal (PowerSeriesPolynomialRing k n m)) [𝔭.IsPrime]
    (𝔮' : Ideal (PowerSeriesPolynomialRing k n m ⧸ 𝔭)) [𝔮'.IsPrime] {r : ℕ}
    (f : Fin r → PowerSeriesPolynomialRing k n m) (hf : Ideal.span (Set.range f) = 𝔭),
    IsRegularLocalRing (Localization.AtPrime 𝔮') ↔
      (((jacobian f).map (residueMap (𝔮'.comap (Ideal.Quotient.mk 𝔭)))).rank : ℕ∞) =
        𝔭.height :=
  @Hironaka.Cited.IsRegularLocalRingLocalizationIffRankJacobianEqHeight.isRegularLocalRing_localization_iff_rank_jacobian_eq_height _

end Hironaka
