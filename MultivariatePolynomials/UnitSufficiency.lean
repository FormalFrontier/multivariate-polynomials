/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.ConstantTermNormalization
public import MultivariatePolynomials.ConstantUnits
public import MultivariatePolynomials.Nilpotent
public import MultivariatePolynomials.NilpotentAddUnits
import Mathlib.Algebra.Module.End

/-!
# Units with nilpotent, additively invertible nonconstant coefficients

Over a commutative semiring, a polynomial is a unit if its constant coefficient
is a unit and each nonconstant coefficient is both nilpotent and additively
invertible. The two conditions on the nonconstant coefficients are separate:
additive inverses need not exist for all elements of the coefficient semiring.

The proof uses
`MvPolynomial.exists_eq_C_mul_one_add_of_coeff_zero_mul_eq_one` to normalize the
constant coefficient, `MvPolynomial.isNilpotent_iff_coeff` for nilpotence of the
finite tail, and `IsNilpotent.isUnit_one_add_of_isAddUnit` for its geometric-series
inverse.
-/

@[expose] public section

universe u v

namespace MvPolynomial

variable {R : Type u} {σ : Type v} [CommSemiring R]

/-- A unit constant coefficient and nilpotent, additively invertible nonconstant
coefficients suffice for a multivariate polynomial over a commutative semiring
to be a unit. No finiteness assumption on the variables is needed. -/
theorem isUnit_of_coeff_isNilpotent_isAddUnit (p : MvPolynomial σ R)
    (hc : IsUnit (p.coeff (0 : σ →₀ ℕ)))
    (hn : ∀ d : σ →₀ ℕ, d ≠ 0 →
      IsNilpotent (p.coeff d) ∧ IsAddUnit (p.coeff d)) : IsUnit p := by
  classical
  obtain ⟨b, hb⟩ := hc.exists_right_inv
  obtain ⟨q, hq0, hpq, hqd⟩ :=
    exists_eq_C_mul_one_add_of_coeff_zero_mul_eq_one p b hb
  have hqn : IsNilpotent q := (isNilpotent_iff_coeff q).2 fun d => by
    by_cases hd : d = 0
    · subst d
      exact ⟨1, by simp [hq0]⟩
    · obtain ⟨n, hn'⟩ := (hn d hd).1
      exact ⟨n, by rw [hqd d hd, mul_pow, hn', mul_zero]⟩
  have hqa : IsAddUnit q := by
    rw [q.as_sum]
    apply IsAddUnit.sum_iff.mpr
    intro d hd
    have hd0 : d ≠ 0 := by
      intro h
      subst d
      exact (mem_support_iff.mp hd) hq0
    have hdau : IsAddUnit (q.coeff d) := by
      rw [hqd d hd0]
      exact (hn d hd0).2.smul_left b
    exact hdau.map (monomial d).toAddMonoidHom
  rw [hpq]
  exact (hc.map C).mul (hqn.isUnit_one_add_of_isAddUnit hqa)

end MvPolynomial
