/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Order.Antichain
public import Mathlib.Algebra.Module.SpanRank
import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber

/-!
# Coefficients at antichain generators of a monomial ideal

If the exponents generating a monomial ideal form an antichain for the
componentwise order, multiplication on the coefficient at any generating
exponent depends only on the multiplier's constant coefficient. Neither the
set of exponents nor the variable type needs to be finite, and the coefficient
semiring may be trivial.

The coefficient identity combines Mathlib's support criterion for monomial-ideal
membership with its coefficient convolution formula: below a generating exponent,
the only possible support exponent of an ideal member is that exponent itself.

Restricting coefficients to the generating antichain gives
`monomialIdealCoeffMap`, a semilinear map over `constantCoeff` from the stock
monomial ideal to finitely supported functions on the antichain. Finite support
is essential when the antichain is infinite. The map sends the monic monomial
generators to the corresponding single functions and is surjective, even over a
trivial semiring.

## References

* Mathlib, `Mathlib.RingTheory.MvPolynomial.Ideal`, by Eric Wieser, for
  `MvPolynomial.mem_ideal_span_monomial_image`.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Basic`, for coefficient convolution,
  `Finsupp.comapDomain` for coefficient restriction, and
  `Mathlib.Order.Antichain` for `IsAntichain`.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, October 21,
  2025 draft, Exercise 13.1.F(a), for the motivating minimum-three-generators
  problem for `(xy, xz, yz)` over a field. The coefficient identity and map here
  are ingredients formulated for arbitrary antichains, variable types, and
  commutative semirings, not a proof of that generator-count assertion.
-/

@[expose] public section

namespace MvPolynomial

universe u v

variable {R : Type u} {σ : Type v} [CommSemiring R]

/-- At an exponent in an antichain of monomial generators, multiplication of an
ideal member by `q` scales its coefficient by `q.coeff 0`. The antichain and
variable type may be infinite, and no nontriviality assumption on `R` is needed. -/
theorem coeff_mul_of_mem_ideal_span_monomial {S : Set (σ →₀ ℕ)}
    (hanti : IsAntichain (· ≤ ·) S) {p q : MvPolynomial σ R}
    (hp : p ∈ Ideal.span ((fun s => monomial s (1 : R)) '' S))
    {w : σ →₀ ℕ} (hw : w ∈ S) :
    (q * p).coeff w = q.coeff 0 * p.coeff w := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (0, w)]
  · rintro ⟨a, b⟩ hab hne
    simp only [Finset.mem_antidiagonal] at hab
    by_cases hb : p.coeff b = 0
    · rw [hb, mul_zero]
    · obtain ⟨s, hs, hsb⟩ := mem_ideal_span_monomial_image.mp hp b
        (mem_support_iff.mpr hb)
      have hbw : b ≤ w := by
        rw [← hab]
        exact le_add_left le_rfl
      have hsw : s = w := hanti.eq hs hw (hsb.trans hbw)
      have hbeq : b = w := le_antisymm hbw (hsw ▸ hsb)
      have hab' : a + w = 0 + w := by
        simpa only [hbeq, zero_add] using hab
      have ha : a = 0 := add_right_cancel hab'
      exact (hne (Prod.ext ha hbeq)).elim
  · simp

/-- Restrict the coefficients of an element of the monomial ideal to its
antichain of generating exponents. The source has its canonical module structure
over `MvPolynomial σ R`, and the target has its canonical `R`-module structure.
The scalar homomorphism is `constantCoeff`.

The antichain and variable type may be infinite. The codomain consists of
finitely supported functions, not all functions, and `R` may be trivial. -/
noncomputable def monomialIdealCoeffMap {S : Set (σ →₀ ℕ)}
    (hanti : IsAntichain (· ≤ ·) S) :
    (Ideal.span ((fun s => monomial s (1 : R)) '' S)) →ₛₗ[
      (constantCoeff : MvPolynomial σ R →+* R)] (S →₀ R) := by
  classical
  exact
    { toFun := fun p =>
        Finsupp.comapDomain
          (Function.Embedding.subtype (fun s : σ →₀ ℕ => s ∈ S))
          p.val.coeff
          (Function.Embedding.subtype (fun s : σ →₀ ℕ => s ∈ S)).injective.injOn
      map_add' := by
        intro p q
        ext w
        change (p.val + q.val).coeff w.val =
          p.val.coeff w.val + q.val.coeff w.val
        simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      map_smul' := by
        intro q p
        ext w
        change (q * p.val).coeff w.val = q.coeff 0 * p.val.coeff w.val
        exact coeff_mul_of_mem_ideal_span_monomial hanti p.property w.property }

/-- A coordinate of the restricted coefficient map is the original coefficient. -/
@[simp]
theorem monomialIdealCoeffMap_apply {S : Set (σ →₀ ℕ)}
    (hanti : IsAntichain (· ≤ ·) S)
    (p : Ideal.span ((fun s => monomial s (1 : R)) '' S)) (w : S) :
    monomialIdealCoeffMap hanti p w = p.val.coeff w.val := by
  rfl

/-- Each monic monomial generator maps to its corresponding single function. -/
@[simp]
theorem monomialIdealCoeffMap_monomial {S : Set (σ →₀ ℕ)}
    (hanti : IsAntichain (· ≤ ·) S) (w : S) :
    monomialIdealCoeffMap (R := R) hanti
      ⟨monomial w.val (1 : R), Ideal.subset_span ⟨w.val, w.property, rfl⟩⟩ =
        Finsupp.single w (1 : R) := by
  classical
  ext v
  rw [monomialIdealCoeffMap_apply]
  simpa only [coeff_monomial, Finsupp.single_apply] using
    Finsupp.single_apply_left Subtype.val_injective w v (1 : R)

/-- Every finitely supported family on the generating antichain is realized by
coefficients of an element of the monomial ideal. -/
theorem monomialIdealCoeffMap_surjective {S : Set (σ →₀ ℕ)}
    (hanti : IsAntichain (· ≤ ·) S) :
    Function.Surjective (monomialIdealCoeffMap (R := R) hanti) := by
  classical
  intro v
  refine Finsupp.induction v ?_ ?_
  · exact ⟨0, map_zero _⟩
  · intro w a v _ _ hv
    obtain ⟨p, hp⟩ := hv
    let g : Ideal.span ((fun s => monomial s (1 : R)) '' S) :=
      ⟨monomial w.val (1 : R), Ideal.subset_span ⟨w.val, w.property, rfl⟩⟩
    have hg : monomialIdealCoeffMap hanti g = Finsupp.single w (1 : R) :=
      monomialIdealCoeffMap_monomial hanti w
    -- A constant polynomial scales a monic generator to any prescribed coefficient.
    refine ⟨(C a : MvPolynomial σ R) • g + p, ?_⟩
    rw [map_add, map_smulₛₗ, constantCoeff_C, hg, hp]
    simp

/-!
## Minimum numbers of generators

For a finite antichain over a nontrivial coefficient semiring, the coefficient
surjection and Mathlib's basis-cardinality theorem compute the ideal's `spanFinrank`.
This counts generators over the polynomial semiring and bounds arbitrary polynomial
generating sets, not just monomial generating sets.

### Reference

Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, Exercise 13.1.F(a)
provides the example `(xy, xz, yz)`.
-/

variable [Nontrivial R]

/-- A finite antichain of monic monomials is a generating set of minimum cardinality
for its ideal, where generators may be arbitrary polynomials.

This generalizes the monomial-ideal example in Ravi Vakil, *The Rising Sea:
Foundations of Algebraic Geometry*, Exercise 13.1.F(a). The invariant is the minimum
number of generators over the polynomial semiring, not dimension over the coefficients. -/
theorem spanFinrank_ideal_span_monomial
    {S : Set (σ →₀ ℕ)} (hS : S.Finite)
    (hanti : IsAntichain (· ≤ ·) S) :
    (Ideal.span ((fun s => monomial s (1 : R)) '' S)).spanFinrank = S.ncard := by
  classical
  have hfg : (Ideal.span ((fun s => monomial s (1 : R)) '' S)).FG :=
    Submodule.fg_span (hS.image _)
  have : RingHomSurjective (constantCoeff : MvPolynomial σ R →+* R) :=
    ⟨fun r => ⟨C r, by simp⟩⟩
  -- The coefficient surjection forces at least one generator per antichain exponent.
  have hle := Submodule.spanRank_range_le (monomialIdealCoeffMap (R := R) hanti)
  rw [LinearMap.range_eq_top.mpr (monomialIdealCoeffMap_surjective hanti),
    Submodule.spanRank_top] at hle
  have hb : (⊤ : Submodule R (S →₀ R)).spanRank.toNat = S.ncard := by
    rw [← (Finsupp.basisSingleOne (ι := S) (R := R)).mk_eq_spanRank,
      ← Cardinal.toNat_toENat, Set.toENat_cardinalMk,
      (Finsupp.basisSingleOne (ι := S) (R := R)).injective.encard_range,
      ENat.card_coe_set_eq, ← Set.ncard_def]
  apply le_antisymm
  · exact (Submodule.spanFinrank_span_le_ncard_of_finite (hS.image _)).trans
      (Set.ncard_image_le hS)
  · calc
      S.ncard = (⊤ : Submodule R (S →₀ R)).spanRank.toNat := hb.symm
      _ ≤ (Ideal.span ((fun s => monomial s (1 : R)) '' S)).spanRank.toNat :=
        Cardinal.toNat_le_toNat hle (Submodule.spanRank_finite_iff_fg.mpr hfg)
      _ = (Ideal.span ((fun s => monomial s (1 : R)) '' S)).spanFinrank := rfl

/-- Every finite polynomial generating set of an ideal generated by a finite antichain
of monic monomials has at least as many elements as that antichain.

This is the arbitrary-generator lower bound underlying Ravi Vakil, *The Rising Sea:
Foundations of Algebraic Geometry*, Exercise 13.1.F(a). -/
theorem card_le_card_of_span_eq_ideal_span_monomial
    {S : Set (σ →₀ ℕ)} (hS : S.Finite)
    (hanti : IsAntichain (· ≤ ·) S)
    (T : Finset (MvPolynomial σ R))
    (hT : Ideal.span (↑T : Set (MvPolynomial σ R)) =
      Ideal.span ((fun s => monomial s (1 : R)) '' S)) :
    S.ncard ≤ T.card := by
  rw [← spanFinrank_ideal_span_monomial (R := R) hS hanti, ← hT]
  simpa only [Set.ncard_coe_finset] using
    Submodule.spanFinrank_span_le_ncard_of_finite T.finite_toSet

end MvPolynomial
