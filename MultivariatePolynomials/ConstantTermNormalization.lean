/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Constant-term normalization

A polynomial whose constant coefficient has a specified multiplicative inverse
is a constant multiple of one plus a polynomial with zero constant coefficient.
The remaining coefficients of the normalized polynomial are specified explicitly.
-/

@[expose] public section

namespace MvPolynomial

universe u v

variable {R : Type u} {σ : Type v} [CommSemiring R]

/-- Normalize a polynomial by a specified inverse of its constant coefficient.
The normalized tail has zero constant coefficient, and each other coefficient is
multiplied by the specified inverse. -/
theorem exists_eq_C_mul_one_add_of_coeff_zero_mul_eq_one
    (p : MvPolynomial σ R) (b : R) (hb : p.coeff 0 * b = 1) :
    ∃ q : MvPolynomial σ R,
      q.coeff 0 = 0 ∧
      p = C (p.coeff 0) * (1 + q) ∧
      ∀ d : σ →₀ ℕ, d ≠ 0 → q.coeff d = b * p.coeff d := by
  classical
  let r : MvPolynomial σ R := p.erase 0
  have hr : C (p.coeff 0) + r = p := by
    apply MvPolynomial.ext
    intro d
    exact congrArg (fun f : (σ →₀ ℕ) →₀ R => f d)
      (Finsupp.single_add_erase 0 p.coeff)
  refine ⟨C b * r, ?_, ?_, ?_⟩
  · rw [coeff_C_mul]
    change b * (p.coeff.erase 0) 0 = 0
    rw [Finsupp.erase_same, mul_zero]
  · calc
      p = C (p.coeff 0) + r := hr.symm
      _ = C (p.coeff 0) * (1 + C b * r) := by
        rw [mul_add, mul_one, ← mul_assoc, ← map_mul, hb, map_one, one_mul]
  · intro d hd
    rw [coeff_C_mul]
    change b * (p.coeff.erase 0) d = b * p.coeff d
    rw [Finsupp.erase_ne hd]

end MvPolynomial

/- The public theorem recovers a nonzero tail over a semiring without subtraction. -/
example :
    ∃ q : MvPolynomial Unit ℕ,
      q = MvPolynomial.X () ∧ q.coeff 0 = 0 ∧ q.coeff (Finsupp.single () 1) = 1 := by
  obtain ⟨q, hzero, hfactor, hcoeff⟩ :=
    MvPolynomial.exists_eq_C_mul_one_add_of_coeff_zero_mul_eq_one
      (1 + MvPolynomial.X () : MvPolynomial Unit ℕ) 1 (by simp)
  have hsum : (1 : MvPolynomial Unit ℕ) + MvPolynomial.X () = 1 + q := by
    simpa using hfactor
  refine ⟨q, (add_left_cancel hsum).symm, hzero, ?_⟩
  have hdegree : (Finsupp.single () 1 : Unit →₀ ℕ) ≠ 0 := by simp
  have hone := MvPolynomial.coeff_C_of_ne_zero hdegree (1 : ℕ)
  simp only [map_one] at hone
  simpa [hone] using hcoeff (Finsupp.single () 1) hdegree
