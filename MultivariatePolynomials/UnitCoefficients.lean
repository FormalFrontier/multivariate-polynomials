/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Invertible

/-!
# Additive invertibility of coefficients of polynomial units

The nonconstant coefficients of a unit multivariate polynomial over a commutative
semiring are additive units. The coefficient of its product with an inverse is zero;
the finite-sum characterization of additive units isolates the relevant summand.
-/

@[expose] public section

universe u v

namespace MvPolynomial

variable {R : Type u} {σ : Type v} [CommSemiring R] {p : MvPolynomial σ R}

/-- Every nonconstant coefficient of a unit multivariate polynomial is an additive unit. -/
theorem isAddUnit_coeff_of_isUnit (hp : IsUnit p) {d : σ →₀ ℕ} (hd : d ≠ 0) :
    IsAddUnit (p.coeff d) := by
  classical
  obtain ⟨q, hpq, hqp⟩ := isUnit_iff_exists.mp hp
  have hsum : IsAddUnit (∑ x ∈ Finset.antidiagonal d, p.coeff x.1 * q.coeff x.2) := by
    rw [← coeff_mul, hpq, coeff_one, ite_eq_right (Ne.symm hd)]
    exact isAddUnit_zero
  have hterm : IsAddUnit (p.coeff d * q.coeff 0) :=
    IsAddUnit.sum_iff.mp hsum (d, 0) (by simp)
  have hconst : q.coeff 0 * p.coeff 0 = 1 := by
    simpa only [map_mul, constantCoeff_eq, map_one] using
      congrArg (constantCoeff : MvPolynomial σ R →+* R) hqp
  simpa only [mul_assoc, hconst, mul_one] using hterm.mul_right (p.coeff 0)

end MvPolynomial
