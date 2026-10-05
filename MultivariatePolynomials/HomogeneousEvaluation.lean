/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Evaluation of homogeneous multivariate polynomials under variable scaling

Scaling each variable by a power of a common scalar scales the evaluation of a
weighted homogeneous polynomial by the corresponding power of that scalar.
The coefficient homomorphism remains unchanged, and the scalar need not be a unit.

## References

* Mathlib, `Mathlib.RingTheory.MvPolynomial.Homogeneous` (weighted homogeneous
  labels) and `Mathlib.Algebra.MvPolynomial.Eval` (monomial evaluation).
-/

set_option warningAsError true

public section

namespace MvPolynomial

variable {ι B R : Type*} [CommSemiring B] [CommSemiring R]

/-- Evaluating a weighted homogeneous polynomial after scaling variable `i` by
`a ^ w i` scales its value by `a ^ d`. Coefficients are evaluated by the same
unital homomorphism on both sides. -/
theorem IsWeightedHomogeneous.eval₂Hom_scaleVariables
    (w : ι → ℕ) (d : ℕ) (p : MvPolynomial ι B)
    (hp : p.IsWeightedHomogeneous w d) (σ : B →+* R) (v : ι → R) (a : R) :
    eval₂Hom σ (fun i => a ^ w i * v i) p = a ^ d * eval₂Hom σ v p := by
  classical
  have hprod (mon : ι →₀ ℕ) :
      mon.prod (fun i exponent => (a ^ w i * v i) ^ exponent) =
        a ^ Finsupp.weight w mon * mon.prod (fun i exponent => v i ^ exponent) := by
    simp_rw [mul_pow, ← pow_mul]
    rw [Finsupp.prod_mul]
    simp only [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply,
      Finsupp.sum, nsmul_eq_mul]
    congr 1
    exact congrArg (a ^ ·)
      (Finset.sum_congr rfl (fun i _ => mul_comm (w i) (mon i)))
  calc
    eval₂Hom σ (fun i => a ^ w i * v i) p =
        ∑ mon ∈ p.support, eval₂Hom σ (fun i => a ^ w i * v i)
          (monomial mon (p.coeff mon)) := by
            conv_lhs => rw [← p.support_sum_monomial_coeff]
            simp only [map_sum]
    _ = ∑ mon ∈ p.support, a ^ d * eval₂Hom σ v
          (monomial mon (p.coeff mon)) := by
            apply Finset.sum_congr rfl
            intro mon hmon
            rw [eval₂Hom_monomial, eval₂Hom_monomial, hprod mon,
              hp (mem_support_iff.mp hmon)]
            ac_rfl
    _ = a ^ d * eval₂Hom σ v p := by
          rw [← Finset.mul_sum, ← map_sum, p.support_sum_monomial_coeff]

/-- Ordinary homogeneous specialization: all variable values are multiplied by
the same scalar, with no invertibility or finiteness assumptions. -/
theorem IsHomogeneous.eval₂Hom_mul_left
    (d : ℕ) (p : MvPolynomial ι B) (hp : p.IsHomogeneous d)
    (σ : B →+* R) (v : ι → R) (a : R) :
    eval₂Hom σ (fun i => a * v i) p = a ^ d * eval₂Hom σ v p := by
  simpa using
    (IsWeightedHomogeneous.eval₂Hom_scaleVariables (1 : ι → ℕ) d p hp σ v a)

end MvPolynomial
