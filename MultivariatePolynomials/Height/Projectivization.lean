/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.NumberTheory.Height.Projectivization
public import MultivariatePolynomials.Height.Homogeneous
public import MultivariatePolynomials.Projectivization

/-!
# Height comparison for homogeneous polynomial maps on projective points

For a finite homogeneous polynomial family whose common zeros over an algebraic
closure are all zero, the induced map on projective points changes logarithmic
height by a bounded amount after scaling by the degree. Multiplicative height is
bounded above and below by constant multiples of the input height raised to that
degree.

Nonvanishing over the base field follows from the common-zero implication over
the algebraic closure and injectivity of the coefficient embedding. This step
requires neither homogeneity nor finite coordinate types. The height comparisons
use the tuple estimates and the computation of projective heights on a nonzero
representative. The degree may be zero, and either coordinate type may be empty.

## References

* `MultivariatePolynomials.Height.Homogeneous`: the logarithmic and multiplicative
  comparisons for evaluation on tuples.
* Mathlib, `Mathlib.NumberTheory.Height.Projectivization`: projective heights and
  their values on classes of nonzero tuples.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Eval`: `MvPolynomial.eval₂_comp` transfers
  evaluation along the coefficient embedding.
-/

public section

universe u v w

namespace Projectivization

/-- A homogeneous polynomial family with no nonzero common zero over an algebraic
closure induces a map whose logarithmic height is uniformly within a bounded
amount of the input height multiplied by the common degree. -/
theorem exists_logHeight_projectivize_sub_mul_bound
    {K : Type u} {I : Type v} {O : Type w}
    [Field K] [Height.AdmissibleAbsValues K] [Finite I] [Finite O]
    (p : O → MvPolynomial I K) (d : ℕ)
    (hp : ∀ o, (p o).IsHomogeneous d)
    (hzero : ∀ x : I → AlgebraicClosure K,
      (∀ o, MvPolynomial.eval₂ (algebraMap K (AlgebraicClosure K)) x (p o) = 0) →
        x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Projectivization K (I → K),
      |Projectivization.logHeight
          (MvPolynomial.projectivize p d hp (RingHom.id K)
            (MvPolynomial.eval_ne_zero_of_forall_eval₂_eq_zero p hzero) P) -
        (d : ℝ) * Projectivization.logHeight P| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := Height.exists_logHeight_eval_sub_mul_bound p d hp hzero
  refine ⟨C, hC, Projectivization.ind ?_⟩
  intro x hx
  simpa only [MvPolynomial.projectivize_mk, Projectivization.logHeight_mk,
    MvPolynomial.eval₂_id] using hbound x

/-- A homogeneous polynomial family with no nonzero common zero over an algebraic
closure induces a map whose multiplicative height is bounded above and below by
constant multiples of the input height raised to the common degree. The comparison
constant is at least one. -/
theorem exists_mulHeight_projectivize_bounds
    {K : Type u} {I : Type v} {O : Type w}
    [Field K] [Height.AdmissibleAbsValues K] [Finite I] [Finite O]
    (p : O → MvPolynomial I K) (d : ℕ)
    (hp : ∀ o, (p o).IsHomogeneous d)
    (hzero : ∀ x : I → AlgebraicClosure K,
      (∀ o, MvPolynomial.eval₂ (algebraMap K (AlgebraicClosure K)) x (p o) = 0) →
        x = 0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : Projectivization K (I → K),
      C⁻¹ * Projectivization.mulHeight P ^ d ≤
          Projectivization.mulHeight
            (MvPolynomial.projectivize p d hp (RingHom.id K)
              (MvPolynomial.eval_ne_zero_of_forall_eval₂_eq_zero p hzero) P) ∧
        Projectivization.mulHeight
            (MvPolynomial.projectivize p d hp (RingHom.id K)
              (MvPolynomial.eval_ne_zero_of_forall_eval₂_eq_zero p hzero) P) ≤
          C * Projectivization.mulHeight P ^ d := by
  obtain ⟨C, hC, hbound⟩ := Height.exists_mulHeight_eval_bounds p d hp hzero
  refine ⟨C, hC, Projectivization.ind ?_⟩
  intro x hx
  simpa only [MvPolynomial.projectivize_mk, Projectivization.mulHeight_mk,
    MvPolynomial.eval₂_id] using hbound x

end Projectivization
