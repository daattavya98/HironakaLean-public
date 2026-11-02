/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Architect
public import Hironaka.Ch0.Blowup
public import Hironaka.Compat.BlowupCharts
public import Hironaka.Ch3.Transforms

/-!
# Ch. 0 §2 / §5 (pp. 142, 167): local structure of a monoidal transformation

The paper uses throughout that a monoidal transformation of a non-singular scheme with
non-singular center is again non-singular, together with its exceptional divisor (p. 142,
p. 167).  Locally this is the statement of Ch. III §2 (p. 209) that a monoidal transform
`R'` of a regular local ring `R` with regular center is regular, applied to the local rings of
`X'`, which are monoidal transforms of those of `X` by the chart description of the blow-up
(`Hironaka/Compat/BlowupCharts.lean`).

Formalization note: this module only fixes the position of the Ch. 0 statement after the
commutative algebra of Ch. III §2 (`Hironaka/Ch3/Transforms.lean`), on which its proof rests;
the statement is the one of Ch. 0 and the argument is the paper's local one.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X}

/-- If `X` and `B` are non-singular, then `X'` and `f⁻¹(B)` are non-singular (p. 142 and p. 167).
The paper's argument is local (p. 214): by the chart description of `X'`, every local ring
`R' = O_{X',y'}` is a monoidal transform of `R = O_{X,f(y')}` with center `P = B_{f(y')}`
(`compat:blowup-stalk-monoidal-transform`), which is regular by Ch. III §2 (p. 209); at points of
`E = f⁻¹(B)`, `O_{E,y'} = R'/PR' = R'/xR'` is the localization of a polynomial ring over the
regular ring `R/P` (p. 210).  Off `B`, `f` is a local isomorphism.

Deviation from the paper (gap filled): pp. 142 and 167 assert the statement without argument. -/
@[blueprint "lem:monoidal-transformation-nonsingular"
  (statement := /-- If $X$ and the center $B$ are non-singular, then $X'$ and $f^{-1}(B)$
    are non-singular. -/)
  (proof := /-- Let $y'\in X'$, $y=f(y')$, $R=\mathcal O_{X,y}$, $R'=\mathcal O_{X',y'}$ and
    $P=B_y$. If $y\notin B$, then $R\to R'$ is an isomorphism
    (\cref{compat:blowup-local-iso}). If $y\in B$, then $P$ is a non-zero prime with $R/P$
    regular (as $\mathcal O_{B,y}=R/P$), and $R'$ is a monoidal transform of $R$ with center $P$
    (\cref{compat:blowup-stalk-monoidal-transform}), hence regular
    (\cref{lem:III.2-monoidal-transform-regular}). The ideal of $f^{-1}(B)$ at $y'$ is
    $PR'=xR'$, and $R'/xR'$ is a localization of a polynomial ring over $R/P$, hence regular
    (pp.~209--210); so $\mathcal O_{f^{-1}(B),y'}=R'/xR'$ is regular.
    \textbf{Gap in the paper filled.} On p.~142 (``we know that $X'$ and $f^{-1}(D)$ are also
    non-singular'') and p.~167 (``necessarily non-singular'') the claim is made without
    argument; the proof above is the paper's own local argument of Ch.~III (pp.~209--210 and
    Remark~2, p.~214), transported to the local rings of $X'$ by the chart description of the
    blow-up, which the paper also asserts without proof (p.~214, ``we see''). -/)
  (latexEnv := "lemma")]
theorem isNonsingular_and_isNonsingular_exceptional (t : MonoidalTransformation X B) (hX : X.IsNonsingular)
    (hB : B.IsNonsingular) : t.X'.IsNonsingular ∧ t.exceptional.IsNonsingular :=
  t.isNonsingular_of_isNonsingular hX hB

end MonoidalTransformation

end Hironaka

