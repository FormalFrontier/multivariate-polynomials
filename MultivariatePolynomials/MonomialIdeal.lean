/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Order.Antichain

/-!
# Coefficients at antichain generators of a monomial ideal

If the exponents generating a monomial ideal form an antichain for the
componentwise order, multiplication on the coefficient at any generating
exponent depends only on the multiplier's constant coefficient. Neither the
set of exponents nor the variable type needs to be finite, and the coefficient
semiring may be trivial.

The proof combines Mathlib's support criterion for monomial-ideal membership
with its coefficient convolution formula: below a generating exponent, the
only possible support exponent of an ideal member is that exponent itself.

## References

* Mathlib, `Mathlib.RingTheory.MvPolynomial.Ideal`, by Eric Wieser, for
  `MvPolynomial.mem_ideal_span_monomial_image`.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Basic`, for coefficient convolution,
  and `Mathlib.Order.Antichain`, for `IsAntichain`.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, October 21,
  2025 draft, Exercise 13.1.F(a), for a motivating application to generators
  of monomial ideals. The coefficient identity here is a supporting lemma,
  rather than the generator-count assertion of that exercise.
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

end MvPolynomial
