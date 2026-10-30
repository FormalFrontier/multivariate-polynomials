/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Clearing negative Laurent exponents by a unit

Every Laurent polynomial over a semiring becomes a polynomial after left
multiplication by a unit. Coefficients need not commute: the Laurent monomials
are central because their coefficients are one.

## References

This uses Mathlib's Laurent-polynomial API: `LaurentPolynomial.exists_T_pow`,
`LaurentPolynomial.isUnit_T`, and `LaurentPolynomial.T_mul`.
-/

@[expose] public section

universe u

namespace LaurentPolynomial

/-- Left multiplication by a unit takes a Laurent polynomial into the image of
`Polynomial.toLaurent`. This holds for arbitrary semirings, including the zero semiring. -/
theorem exists_unit_mul_mem_range_toLaurent
    {R : Type u} [Semiring R] (f : LaurentPolynomial R) :
    ∃ v : (LaurentPolynomial R)ˣ,
      (v : LaurentPolynomial R) * f ∈
        Set.range (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R) := by
  obtain ⟨n, p, hp⟩ := exists_T_pow f
  obtain ⟨v, hv⟩ := isUnit_T (R := R) (n : ℤ)
  exact ⟨v, p, by simpa only [hv, T_mul] using hp⟩

end LaurentPolynomial
