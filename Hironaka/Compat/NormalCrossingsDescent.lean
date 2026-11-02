/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.NormalCrossingsPullback
public import Hironaka.Compat.RSOPProducts
public import Hironaka.Compat.RegularQuotient

/-!
# Descent of normal crossings along a local homomorphism of regular local rings (Ch. IV §3, p. 309)

The paper (p. 309, Remark 4): "To show that ⋃_{i=1}^{α+s} E_i(s) has only normal crossings
with B_s at x, we note that if S_s (resp. Ŝ_s) is the local ring of X_s at x (resp. X̂_s at x̂) then
the canonical homomorphism S_s → Ŝ_s transforms a regular system of parameters of S_s into such a
system of parameters of Ŝ_s. (See Lemma (AB. 2).) For the case in which ℜ = (ℜ_I^{N,n}, F), the
permissibility of f_B̃ for ℜ_II^{N-1} implies that ⋃_{i=1}^{α+s} c_s^{-1}(E_i(s)) has only normal
crossings with B̃ at x̂. Therefore, by the above property of the homomorphism S_s → Ŝ_s, we can
conclude that ⋃_{i=1}^{α+s} E_i(s) has only normal crossings with B_s at x."

General statements, independent of the construction of `X̂_s`, `X̃`:

* `exists_isRegularSystemOfParameters_adapted_of_associated_rsop` (ring level): from a regular
  system of parameters of `R'` adapted to the prime `P'` and to the images of a part `K` of a
  regular system of parameters of `R`, one gets a regular system of parameters of `R` containing
  `K` and a part generating `P = P' ∩ R`;
* `Subscheme.hasOnlyNormalCrossingsWithAt_iInf_of_totalTransform` (stalk level, a finite family);
* `Subscheme.hasOnlyNormalCrossingsWithAt_iInf_of_totalTransform_of_flat` for a faithfully flat
  stalk map (the case `S_s → Ŝ_s`), where no transversality is needed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Hironaka

universe u

noncomputable section

section RingLevel

/-- Independence modulo `M²` descends along a local homomorphism: if the images of a family in `B`
are independent, so is the family in `A`. -/
theorem RSOPIndep.of_comp_isLocalHom {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] (ψ : A →+* B) [IsLocalHom ψ] {ι : Type*} {F : Finset ι} {v : ι → A}
    (h : RSOPIndep F (fun z => ψ (v z))) : RSOPIndep F v := by
  intro z hz
  obtain ⟨hm, hn⟩ := h z hz
  refine ⟨?_, fun hcon => hn ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).mp hm (hu.map ψ)
  · have h1 := Ideal.mem_map_of_mem ψ hcon
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_pow, Set.image_image] at h1
    exact (sup_le_sup (Ideal.span_mono Set.Subset.rfl)
      (Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le ψ) 2)) h1

open Classical in
/-- **Adapting a regular system of parameters to a prime and a family** (a copy of
`exists_isRegularSystemOfParameters_subset_and_span_eq_prime` of
`Compat/ExceptionalTransversal.lean`, which cannot be imported here since it depends on Ch. IV).
Let `P` be a prime of the regular local ring `R` with `R/P` regular, and `K` a part of a regular
system of parameters whose members outside `P` stay independent modulo `P`.  Then there is a regular
system of parameters `Z` containing `K`, and a part `T ⊆ Z` generating `P`. -/
theorem exists_isRegularSystemOfParameters_adapted_of_rsopIndep_quotient {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (P : Ideal R) [P.IsPrime] (hP : IsRegularLocalRing (R ⧸ P))
    (K : Finset R) (hK : ExtendsToRSOP R K)
    (hF : RSOPIndep (K.filter (· ∉ P)) (fun k : R => Ideal.Quotient.mk P k)) :
    ∃ Z T : Finset R, IsRegularSystemOfParameters R Z ∧ K ⊆ Z ∧ T ⊆ Z ∧
      Ideal.span (T : Set R) = P := by
  obtain ⟨S, T₁, hS, hScard, hT₁S, hT₁⟩ := exists_finset_span_eq_prime R P hP
  have hS' : IsRegularSystemOfParameters R S := by
    refine ⟨hS, ?_⟩
    rw [hScard, IsRegularLocalRing.spanFinrank_maximalIdeal]
  have key : ∀ J : Finset R, J ⊆ K.filter (· ∈ P) →
      ∃ Z T : Finset R, IsRegularSystemOfParameters R Z ∧ J ⊆ Z ∧ T ⊆ Z ∧
        Ideal.span (T : Set R) = P := by
    intro J
    induction J using Finset.induction_on with
    | empty => intro _; exact ⟨S, T₁, hS', Finset.empty_subset _, hT₁S, hT₁⟩
    | insert f J hfJ ih =>
      intro hJ
      obtain ⟨Z, T, hZ, hJZ, hTZ, hT⟩ := ih ((Finset.subset_insert f J).trans hJ)
      have hfK : f ∈ K.filter (· ∈ P) := hJ (Finset.mem_insert_self f J)
      have hfP : f ∈ Ideal.span (T : Set R) := by rw [hT]; exact (Finset.mem_filter.mp hfK).2
      have hJf : ExtendsToRSOP R (insert f J) := hK.mono (fun a ha => by
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact (Finset.mem_filter.mp hfK).1
        · exact (Finset.mem_filter.mp (hJ (Finset.mem_insert_of_mem ha))).1)
      obtain ⟨Z', T', hZ', hJZ', hfZ', hT'Z', hT'⟩ :=
        ExtendsToRSOP.exchange hZ hJZ hTZ hfP hfJ hJf
      exact ⟨Z', T', hZ', Finset.insert_subset hfZ' hJZ', hT'Z', by rw [hT', hT]⟩
  obtain ⟨Z₂, T₂, hZ₂, hKZ₂, hT₂Z₂, hT₂⟩ := key (K.filter (· ∈ P)) subset_rfl
  set G : Finset R := T₂ ∪ K.filter (· ∈ P) with hGdef
  have hGZ : G ⊆ Z₂ := Finset.union_subset hT₂Z₂ hKZ₂
  have hGind : RSOPIndep G (fun z : R => z) :=
    RSOPIndep.of_extends (fun a _ b _ h => h) (by
      rw [Finset.image_id']; exact ⟨Z₂, hGZ, hZ₂⟩)
  have hGP : Ideal.span (G : Set R) = P := by
    refine le_antisymm (Ideal.span_le.mpr fun a ha => ?_) ?_
    · rcases Finset.mem_union.mp (Finset.mem_coe.mp ha) with h | h
      · exact hT₂ ▸ Ideal.subset_span (Finset.mem_coe.mpr h)
      · exact (Finset.mem_filter.mp h).2
    · rw [← hT₂]
      exact Ideal.span_mono (by simp [hGdef])
  have hdisj : Disjoint G (K.filter (· ∉ P)) := by
    rw [Finset.disjoint_left]
    intro a haG haK
    have : a ∈ P := hGP ▸ Ideal.subset_span (Finset.mem_coe.mpr haG)
    exact (Finset.mem_filter.mp haK).2 this
  have hun := RSOPIndep.union_of_quotient hdisj hGind (J := P) (by simpa using hGP.symm) hF
  obtain ⟨-, hext⟩ := hun.injOn_and_extends
  obtain ⟨Z, hUZ, hZ⟩ := hext
  rw [Finset.image_id'] at hUZ
  refine ⟨Z, T₂, hZ, fun k hk => hUZ ?_, fun t ht => hUZ
    (Finset.mem_union_left _ (Finset.mem_union_left _ ht)), hT₂⟩
  by_cases hkP : k ∈ P
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, hkP⟩))
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, hkP⟩)

open Classical in
/-- The intersection of principal ideals generated by members of a part of a regular system of
parameters is generated by the product of the distinct generators (a copy of
`DatumTransform.exists_iInf_eq_span_prod_and_forall_mem` of
`Compat/ExceptionalTransversal.lean`). -/
theorem exists_iInf_eq_span_prod_of_forall_eq_top_or_eq_span {R : Type u} [CommRing R]
    [IsRegularLocalRing R] {ι : Type*} (D : ι → Ideal R) {K : Finset R} (hK : ExtendsToRSOP R K)
    (hD : ∀ i, D i = ⊤ ∨ ∃ k ∈ K, D i = Ideal.span {k}) :
    ∃ K₁ ⊆ K, (∀ k ∈ K₁, ∃ i, D i = Ideal.span {k}) ∧ ⨅ i, D i = Ideal.span {∏ k ∈ K₁, k} := by
  refine ⟨K.filter fun k => ∃ i, D i = Ideal.span {k}, Finset.filter_subset _ _,
    fun k hk => (Finset.mem_filter.mp hk).2, ?_⟩
  rw [← (hK.mono (Finset.filter_subset _ _)).iInf_span_singleton]
  apply le_antisymm
  · refine le_iInf₂ fun k hk => ?_
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hk).2
    exact (iInf_le D i).trans hi.le
  · refine le_iInf fun i => ?_
    rcases hD i with h | ⟨k, hk, h⟩
    · rw [h]; exact le_top
    · rw [h]; exact iInf₂_le k (Finset.mem_filter.mpr ⟨hk, i, h⟩)

/-- **Ring level.**  Let `φ : R → R'` be a local homomorphism of regular local rings, `P` a prime of
`R` with `R/P` regular, `Zt` a regular system of parameters of `R'` with a part `Tb` such that
`(Tb) ∩ R = P`, and `K` a part of a regular system of parameters of `R` such that the members of `K`
outside `P` have images generating, up to units, distinct members `β k` of `Zt`.  Then there is a
regular system of parameters of `R` containing `K`, with a part generating `P`.

Deviation from the paper (gap filled): the paper says only "we can conclude" (p. 309).  The
isomorphism `O_{X,x}/B_x ≃ O_{X̃,ỹ}/B̃` used in the descent of §4 Remark 1 (p. 322) is not needed:
independence of the classes modulo `M²` pulls back along the local map `R/P → R'/(Tb)`, and only
`(Tb) ∩ R = P` is used.
-/
@[blueprint "lem:IV.AB-rem4-nc-descent-ring"
  (statement := /-- Let $\varphi\colon R\to R'$ be a local homomorphism of regular local rings,
    $P$ a prime of $R$ with $R/P$ regular, $Z'$ a regular system of parameters of $R'$ with a
    part $T'$ such that $(T')\cap R=P$, and $K$ a part of a regular system of parameters of $R$.
    Suppose that for the members $k$ of $K$ outside $P$ the ideals $(\varphi(k))$ are generated
    by members $\beta(k)$ of $Z'$ and that $(\varphi(k))=(\varphi(k'))$ forces $k=k'$. Then there
    is a regular system of parameters of $R$ containing $K$, with a part generating $P$.
    (The algebra of p.~309, ``by the above property of the homomorphism $S_s\to\hat S_s$''.) -/)
  (proof := /-- The $\beta(k)$ lie in $Z'\setminus T'$, since $\beta(k)\in T'$ would give
    $k\in(T')\cap R=P$; they are distinct, so their classes are independent in the regular local
    ring $R'/(T')$, hence so are the classes of $\varphi(k)$ (associated). Independence pulls back
    along the local map $R/P\to R'/(T')$, so the classes of the $k\notin P$ are independent in
    $R/P$ and a regular system of parameters of $R$ containing $K$ with a part generating $P$
    exists.
    \textbf{Deviation from the paper (gap filled).} The paper says only ``we can conclude''
    (p.~309). -/)
  (latexEnv := "lemma")]
theorem exists_isRegularSystemOfParameters_adapted_of_associated_rsop {R R' : Type u} [CommRing R]
    [IsRegularLocalRing R] [CommRing R'] [IsRegularLocalRing R'] (φ : R →+* R') [IsLocalHom φ]
    (P : Ideal R) [P.IsPrime] (hP : IsRegularLocalRing (R ⧸ P)) {Zt Tb : Finset R'}
    (hZt : IsRegularSystemOfParameters R' Zt) (hTb : Tb ⊆ Zt)
    (hcomap : (Ideal.span (Tb : Set R')).comap φ = P) {K : Finset R} (hK : ExtendsToRSOP R K)
    (β : R → R') (hβZ : ∀ k ∈ K, k ∉ P → β k ∈ Zt)
    (hβ : ∀ k ∈ K, k ∉ P → Ideal.span {φ k} = Ideal.span {β k})
    (hinj : ∀ k ∈ K, k ∉ P → ∀ k' ∈ K, k' ∉ P → Ideal.span {φ k} = Ideal.span {φ k'} → k = k') :
    ∃ Z T : Finset R, IsRegularSystemOfParameters R Z ∧ K ⊆ Z ∧ T ⊆ Z ∧
      Ideal.span (T : Set R) = P := by
  classical
  refine exists_isRegularSystemOfParameters_adapted_of_rsopIndep_quotient P hP K hK ?_
  have hdom : IsDomain R' := Transforms.isDomain_of_isRegularLocalRing R'
  obtain ⟨hreg, hrs, hcard⟩ := rsop_quotient hZt hTb
  set mk' := Ideal.Quotient.mk (Ideal.span (Tb : Set R')) with hmk'
  have hinjZ : Set.InjOn mk' (Zt \ Tb : Finset R') := Finset.injOn_of_card_image_eq hcard
  have hβT : ∀ k ∈ K.filter (· ∉ P), β k ∉ Tb := by
    intro k hk hmem
    obtain ⟨hkK, hkP⟩ := Finset.mem_filter.mp hk
    have h1 : φ k ∈ Ideal.span (Tb : Set R') := by
      have : φ k ∈ Ideal.span {β k} := by
        rw [← hβ k hkK hkP]; exact Ideal.mem_span_singleton_self _
      exact Ideal.span_singleton_le_iff_mem _ |>.mpr (Ideal.subset_span (Finset.mem_coe.mpr hmem))
        this
    exact hkP (hcomap ▸ Ideal.mem_comap.mpr h1)
  have hmem : ∀ k ∈ K.filter (· ∉ P), β k ∈ Zt \ Tb := fun k hk =>
    Finset.mem_sdiff.mpr ⟨hβZ k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2,
      hβT k hk⟩
  have hβinj : ∀ a ∈ K.filter (· ∉ P), ∀ b ∈ K.filter (· ∉ P), β a = β b → a = b := by
    intro a ha b hb hab
    obtain ⟨haK, haP⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbK, hbP⟩ := Finset.mem_filter.mp hb
    refine hinj a haK haP b hbK hbP ?_
    rw [hβ a haK haP, hβ b hbK hbP, hab]
  have hind : RSOPIndep (K.filter (· ∉ P)) (fun k : R => mk' (β k)) := by
    refine RSOPIndep.of_extends (fun a ha b hb hab =>
      hβinj a ha b hb (hinjZ (hmem a ha) (hmem b hb) hab)) ?_
    have hsub : (K.filter (· ∉ P)).image (fun k => mk' (β k)) ⊆ (Zt \ Tb).image mk' := by
      intro y hy
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image_of_mem _ (hmem k hk)
    exact (ExtendsToRSOP.of_isRegularSystemOfParameters hrs).mono hsub
  have hassoc : ∀ k ∈ K.filter (· ∉ P), Associated (mk' (β k)) (mk' (φ k)) := by
    intro k hk
    obtain ⟨hkK, hkP⟩ := Finset.mem_filter.mp hk
    have : Associated (β k) (φ k) :=
      (Ideal.span_singleton_eq_span_singleton.mp (hβ k hkK hkP).symm)
    exact this.map mk'
  have hind' : RSOPIndep (K.filter (· ∉ P)) (fun k : R => mk' (φ k)) := hind.of_associated hassoc
  -- pull back along the local map `R/P → R'/(Tb)`
  have hle : P ≤ (Ideal.span (Tb : Set R')).comap φ := hcomap.ge
  let ψ : R ⧸ P →+* R' ⧸ Ideal.span (Tb : Set R') :=
    Ideal.quotientMap (Ideal.span (Tb : Set R')) φ hle
  have hψ : ∀ k, ψ (Ideal.Quotient.mk P k) = mk' (φ k) := fun k => rfl
  have : IsLocalRing (R ⧸ P) := hP.toIsLocalRing
  have : IsLocalRing (R' ⧸ Ideal.span (Tb : Set R')) := hreg.toIsLocalRing
  have hψloc : IsLocalHom ψ := isLocalHom_quotientMap_of_le_comap φ P (Ideal.span (Tb : Set R')) hle
  exact RSOPIndep.of_comp_isLocalHom ψ (by simpa only [hψ] using hind')

end RingLevel

namespace Subscheme

section StalkLevel

variable {Y' Y : Scheme.{u}}

/-- **Pointwise `exists_rsop_of_hasOnlyNormalCrossingsWithAt`**: the divisors `E i` need only be
simple of codimension one at `x` when they pass through it (no irreducibility). -/
theorem exists_rsop_of_hasOnlyNormalCrossingsWithAt_of_isSimpleAt {ι : Type*}
    (E : ι → Subscheme Y) {D₀ : Subscheme Y} (hD₀ : ∀ i, D₀ ≤ E i) {D : Subscheme Y} {x : Y}
    [IsRegularLocalRing (Y.presheaf.stalk x)]
    (hE : ∀ i, x ∈ (E i).pts → (E i).IsSimpleAt x ∧ (E i).codimAt x = 1)
    (h : D₀.HasOnlyNormalCrossingsWithAt D x) :
    ∃ Z : Finset (Y.presheaf.stalk x), IsRegularSystemOfParameters _ Z ∧
      (∃ T ⊆ Z, D.stalkIdeal x = Ideal.span (T : Set (Y.presheaf.stalk x))) ∧
      ∀ i, (E i).stalkIdeal x = ⊤ ∨ ∃ a ∈ Z, (E i).stalkIdeal x = Ideal.span {a} := by
  have := Transforms.isDomain_of_isRegularLocalRing (Y.presheaf.stalk x)
  obtain ⟨Z, hZ, hcomp, T, hTZ, hT⟩ := h
  refine ⟨Z, hZ, ⟨T, hTZ, hT⟩, fun i => ?_⟩
  by_cases hx : x ∈ (E i).pts
  swap
  · exact Or.inl (Subscheme.stalkIdeal_eq_top_of_notMem_pts hx)
  right
  obtain ⟨⟨-, hreg⟩, hcod⟩ := hE i hx
  have hp : ((E i).stalkIdeal x).IsPrime := by
    have := Transforms.isDomain_of_isRegularLocalRing (Y.presheaf.stalk x ⧸ (E i).stalkIdeal x)
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  have hp1 : ((E i).stalkIdeal x).height = 1 := hcod
  have hle : D₀.stalkIdeal x ≤ (E i).stalkIdeal x :=
    Subscheme.stalkIdeal_mono (hD₀ i) x
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hle
  obtain ⟨C, hC, hxC, hCq⟩ :=
    Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes _ x hq
  obtain ⟨a, ha, hCa⟩ := hcomp C hC hxC
  refine ⟨a, ha, ?_⟩
  have hqa : q = Ideal.span {a} := hCq.symm.trans hCa
  have hext : ExtendsToRSOP _ Z := ExtendsToRSOP.of_isRegularSystemOfParameters hZ
  have := hext.isPrime_span_singleton ha
  have ha0 : Ideal.span {a} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hext.ne_zero ha
  exact (DatumTransform.eq_of_le_of_height_eq_one (hqa ▸ hqp) ha0 hp1).symm

/-- **Descent of normal crossings at a point** (p. 309, "by the above property of the
homomorphism `S_s → Ŝ_s`"; also the descent from `X̃` in Remark 1, p. 322).  Let `g : Y' → Y` have
a local stalk map `φ : O_{Y,x} → O_{Y',y'}` of regular local rings, `x = g y'`.  Suppose the finite
family `E` has normal crossings at `x` (`hE`: its stalks are `⊤` or generated by members of one
regular system of parameters), `D` is non-singular at `x`, and the total transforms `g⁻¹E_i` have
normal crossings with `D'` at `y'` (`hE'`), where `D' ∩ O_{Y,x} = D` (`hcomap`) and `φ` does not
identify two different stalks of the `E_i` (`hinj`: equal stalks of the total transforms at `y'`
force equal stalks at `x`).  Then `⨅ E_i` has only normal crossings with `D` at `x`.

Deviation from the paper (gap filled): the paper writes "we can conclude" (p. 309); this is the
stalk-level descent.  It generalizes the descent from `X̃` to `X_s` of §4 Remark 1 (p. 322): there
`g` is not flat, and the hypotheses `hcomap`, `hinj` are what the transversality of the `Ê_j` to
`X̄_s` supplies.
-/
@[blueprint "lem:IV.AB-rem4-nc-descent-general"
  (statement := /-- Let $g\colon Y'\to Y$ be a morphism of schemes, $y'\in Y'$, $x=g(y')$, with
    $\mathcal O_{Y,x}$ and $\mathcal O_{Y',y'}$ regular and the stalk map local. Let $E_1,\dots,
    E_m$ be subschemes of $Y$ whose stalks at $x$ are $(1)$ or generated by members of one regular
    system of parameters, $D$ a subscheme non-singular at $x$, and $D'$ a subscheme of $Y'$ with
    $D'_{y'}\cap\mathcal O_{Y,x}=D_x$. Suppose the total transforms $g^{-1}E_i$ and $D'$ are
    adapted to one regular system of parameters of $\mathcal O_{Y',y'}$ (normal crossings of
    $\bigcup g^{-1}E_i$ with $D'$ at $y'$), and that equal stalks of $g^{-1}E_i$, $g^{-1}E_j$
    force equal stalks of $E_i$, $E_j$. Then $\bigcup E_i$ has only normal crossings with $D$
    at $x$. (p.~309, and the descent of p.~322.) -/)
  (proof := /-- Let $K_1\subseteq Z_0$ be the distinct generators of the stalks of the $E_i$ at
    $x$, so that $\bigcap E_{i,x}=(\prod K_1)$. Each $\varphi(k)$ generates the stalk of some
    $g^{-1}E_i$, a proper ideal as $\varphi$ is local, hence $(\varphi(k))=(\beta(k))$ with
    $\beta(k)$ in the regular system of parameters upstairs; the hypothesis on equal stalks gives
    injectivity. Apply \cref{lem:IV.AB-rem4-nc-descent-ring} to get a regular system of
    parameters adapted to $K_1$ and $D_x$. \textbf{Deviation from the paper (gap filled).} The
    paper says ``we can conclude''. -/)
  (proofUses := ["lem:IV.AB-rem4-nc-descent-ring"])
  (latexEnv := "lemma")]
theorem hasOnlyNormalCrossingsWithAt_iInf_of_totalTransform (g : Y' ⟶ Y) (y' : Y')
    [IsRegularLocalRing (Y.presheaf.stalk (g y'))] [IsRegularLocalRing (Y'.presheaf.stalk y')]
    [IsLocalHom (g.stalkMap y').hom] {ι : Type*} [Fintype ι] (E : ι → Subscheme Y)
    (D : Subscheme Y) (D' : Subscheme Y')
    (hDreg : IsRegularLocalRing (Y.presheaf.stalk (g y') ⧸ D.stalkIdeal (g y')))
    (hcomap : (D'.stalkIdeal y').comap (g.stalkMap y').hom = D.stalkIdeal (g y'))
    (hE : ∃ Z₀ : Finset (Y.presheaf.stalk (g y')), IsRegularSystemOfParameters _ Z₀ ∧
      ∀ i, (E i).stalkIdeal (g y') = ⊤ ∨ ∃ k ∈ Z₀, (E i).stalkIdeal (g y') = Ideal.span {k})
    (hE' : ∃ Zt : Finset (Y'.presheaf.stalk y'), IsRegularSystemOfParameters _ Zt ∧
      (∃ T ⊆ Zt, D'.stalkIdeal y' = Ideal.span (T : Set (Y'.presheaf.stalk y'))) ∧
      ∀ i, (totalTransform g (E i)).stalkIdeal y' = ⊤ ∨
        ∃ b ∈ Zt, (totalTransform g (E i)).stalkIdeal y' = Ideal.span {b})
    (hinj : ∀ i j, (E i).stalkIdeal (g y') ≠ ⊤ →
      (totalTransform g (E i)).stalkIdeal y' = (totalTransform g (E j)).stalkIdeal y' →
        (E i).stalkIdeal (g y') = (E j).stalkIdeal (g y')) :
    (⨅ i, E i).HasOnlyNormalCrossingsWithAt D (g y') := by
  classical
  obtain ⟨Z₀, hZ₀, hE0⟩ := hE
  have hZ₀ext : ExtendsToRSOP _ Z₀ := ExtendsToRSOP.of_isRegularSystemOfParameters hZ₀
  obtain ⟨K₁, hK₁Z, hK₁gen, hK₁⟩ := exists_iInf_eq_span_prod_of_forall_eq_top_or_eq_span
    (fun j => (E j).stalkIdeal (g y')) hZ₀ext hE0
  have hK₁ext : ExtendsToRSOP _ K₁ := hZ₀ext.mono hK₁Z
  have hmaxk : ∀ k ∈ K₁, k ∈ maximalIdeal _ := fun k hk => hZ₀ext.mem_maximalIdeal (hK₁Z hk)
  have hP : (D.stalkIdeal (g y')).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (Transforms.isDomain_of_isRegularLocalRing _)
  obtain ⟨Zt, hZt, ⟨Tb, hTbZ, hD'⟩, hEj⟩ := hE'
  have hTi : ∀ (i : ι) (k : Y.presheaf.stalk (g y')), (E i).stalkIdeal (g y') = Ideal.span {k} →
      (totalTransform g (E i)).stalkIdeal y' = Ideal.span {(g.stalkMap y').hom k} := by
    intro i k hk
    rw [stalkIdeal_totalTransform, hk, Ideal.map_span, Set.image_singleton]
  have hne : ∀ (i : ι) (k : Y.presheaf.stalk (g y')), k ∈ K₁ →
      (E i).stalkIdeal (g y') = Ideal.span {k} →
        (totalTransform g (E i)).stalkIdeal y' ≠ ⊤ := by
    intro i k hk hik
    rw [hTi i k hik, Ne, Ideal.span_singleton_eq_top]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).mp (hmaxk k hk) (IsLocalHom.map_nonunit _ hu)
  have hβex : ∀ k ∈ K₁, ∃ b ∈ Zt, Ideal.span {(g.stalkMap y').hom k} = Ideal.span {b} := by
    intro k hk
    obtain ⟨i, hi⟩ := hK₁gen k hk
    obtain ⟨b, hbZ, hb⟩ := (hEj i).resolve_left (hne i k hk hi)
    exact ⟨b, hbZ, (hTi i k hi).symm.trans hb⟩
  choose! β hβZ hβspan using hβex
  rw [hD'] at hcomap
  obtain ⟨Z, T, hZ, hKZ, hTZ, hT⟩ := exists_isRegularSystemOfParameters_adapted_of_associated_rsop
    (g.stalkMap y').hom (D.stalkIdeal (g y')) hDreg hZt hTbZ hcomap hK₁ext β
    (fun k hk _ => hβZ k hk) (fun k hk _ => hβspan k hk) (by
      intro k hk _ k' hk' _ hkk
      obtain ⟨i, hi⟩ := hK₁gen k hk
      obtain ⟨i', hi'⟩ := hK₁gen k' hk'
      have h1 := hinj i i' (by
        rw [hi, Ne, Ideal.span_singleton_eq_top]
        intro hu
        exact (IsLocalRing.mem_maximalIdeal _).mp (hmaxk k hk) hu)
        (by rw [hTi i k hi, hTi i' k' hi', hkk])
      exact hZ₀ext.span_singleton_injOn (Finset.mem_coe.mpr (hK₁Z hk))
        (Finset.mem_coe.mpr (hK₁Z hk')) (hi.symm.trans (h1.trans hi')))
  have hEst : (⨅ i, E i).stalkIdeal (g y') = Ideal.span {∏ k ∈ K₁, k} := by
    rw [DatumTransform.stalkIdeal_iInf_fintype]
    exact hK₁
  exact hasOnlyNormalCrossingsWithAt_of_stalkIdeal_eq hZ hKZ hTZ hEst hT.symm

/-- The case of a faithfully flat stalk map (`S_s → Ŝ_s`, p. 309): no transversality is needed.
`D' = g⁻¹D`, and the `g⁻¹E_i` need only be simple of codimension one at `y'` (when they pass through
it) with `⨅ g⁻¹E_i` having normal crossings with `g⁻¹D` at `y'`.

Paper (p. 309): "Therefore, by the above property of the homomorphism S_s → Ŝ_s, we can
conclude that ⋃_{i=1}^{α+s} E_i(s) has only normal crossings with B_s at x."

Deviation from the paper (gap filled): the "property" used is that `S_s → Ŝ_s` is faithfully flat
(a consequence of "transforms a regular system of parameters of S_s into such a system of
parameters of Ŝ_s", Lemma (AB.2)), in the form `(I Ŝ_s) ∩ S_s = I`; it makes distinct generators of
the `E_i(s)` stay distinct, so no transversality is needed.  The normal crossings of the `E_i(s)`
among themselves at `x` (they form a datum) and the simplicity of the `c_s⁻¹(E_i(s))` are used as
hypotheses.
-/
@[blueprint "lem:IV.AB-rem4-nc-descent"
  (statement := /-- \textbf{Descent of normal crossings.} Let $g\colon Y'\to Y$ have a local
    stalk map $S\to\hat S$ of regular local rings at $y'\mapsto x$ with $I\hat S\cap S=I$ for
    all ideals $I$ (e.g.\ faithfully flat), $E_1,\dots,E_m$ subschemes of $Y$ having normal
    crossings among themselves at $x$, $D$ non-singular at $x$. If each $g^{-1}E_i$ through $y'$ is
    non-singular of codimension one at $y'$ and $\bigcup g^{-1}E_i$ has only normal crossings with
    $g^{-1}D$ at $y'$, then $\bigcup E_i$ has only normal crossings with $D$ at $x$.
    (p.~309: ``Therefore, by the above property of the homomorphism $S_s\to\hat S_s$, we can
    conclude that $\bigcup_{i=1}^{\alpha+s}E_i(s)$ has only normal crossings with $B_s$ at
    $x$.'') -/)
  (proof := /-- The pointwise form of the adapted regular system of parameters upstairs gives the
    hypotheses of \cref{lem:IV.AB-rem4-nc-descent-general} with $D'=g^{-1}D$; the condition on
    ideals gives $D'_{y'}\cap S=D_x$ and that $E_{i,x}\ne E_{j,x}$ implies
    $(g^{-1}E_i)_{y'}\ne(g^{-1}E_j)_{y'}$. \textbf{Deviation from the paper (gap filled).} The
    paper uses only ``the above property of the homomorphism'' (p.~309). -/)
  (proofUses := ["lem:IV.AB-rem4-nc-descent-general"])
  (latexEnv := "lemma")]
theorem hasOnlyNormalCrossingsWithAt_iInf_of_totalTransform_of_flat (g : Y' ⟶ Y) (y' : Y')
    [IsRegularLocalRing (Y.presheaf.stalk (g y'))] [IsRegularLocalRing (Y'.presheaf.stalk y')]
    [IsLocalHom (g.stalkMap y').hom]
    (hflat : ∀ I : Ideal (Y.presheaf.stalk (g y')),
      (I.map (g.stalkMap y').hom).comap (g.stalkMap y').hom = I)
    {ι : Type*} [Fintype ι] (E : ι → Subscheme Y) (D : Subscheme Y)
    (hDreg : IsRegularLocalRing (Y.presheaf.stalk (g y') ⧸ D.stalkIdeal (g y')))
    (hE : ∃ Z₀ : Finset (Y.presheaf.stalk (g y')), IsRegularSystemOfParameters _ Z₀ ∧
      ∀ i, (E i).stalkIdeal (g y') = ⊤ ∨ ∃ k ∈ Z₀, (E i).stalkIdeal (g y') = Ideal.span {k})
    (hsimple : ∀ i, y' ∈ (totalTransform g (E i)).pts →
      (totalTransform g (E i)).IsSimpleAt y' ∧ (totalTransform g (E i)).codimAt y' = 1)
    (hNC : (⨅ i, totalTransform g (E i)).HasOnlyNormalCrossingsWithAt (totalTransform g D) y') :
    (⨅ i, E i).HasOnlyNormalCrossingsWithAt D (g y') := by
  obtain ⟨Zt, hZt, hD'T, hEj⟩ := exists_rsop_of_hasOnlyNormalCrossingsWithAt_of_isSimpleAt
    (fun i => totalTransform g (E i)) (D₀ := ⨅ i, totalTransform g (E i))
    (fun i => iInf_le _ i) hsimple hNC
  refine hasOnlyNormalCrossingsWithAt_iInf_of_totalTransform g y' E D (totalTransform g D) hDreg
    ?_ hE ⟨Zt, hZt, hD'T, hEj⟩ ?_
  · rw [stalkIdeal_totalTransform]
    exact hflat _
  · intro i j _ h
    rw [stalkIdeal_totalTransform, stalkIdeal_totalTransform] at h
    calc (E i).stalkIdeal (g y')
        = (((E i).stalkIdeal (g y')).map (g.stalkMap y').hom).comap (g.stalkMap y').hom :=
          (hflat _).symm
      _ = (((E j).stalkIdeal (g y')).map (g.stalkMap y').hom).comap (g.stalkMap y').hom := by
          rw [h]
      _ = (E j).stalkIdeal (g y') := hflat _

end StalkLevel

end Subscheme

end

end Hironaka
