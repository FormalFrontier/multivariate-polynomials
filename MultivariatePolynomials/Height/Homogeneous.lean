/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.NumberTheory.Height.MvPolynomial
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import Mathlib.Tactic.Linarith
import MultivariatePolynomials.HomogeneousCertificates

/-!
# Height comparison for homogeneous polynomial families

For a finite family of homogeneous polynomials of common degree whose common zeros over an
algebraic closure are all zero, evaluation changes logarithmic height by a bounded amount after
scaling by the degree. Equivalently, the multiplicative height of the evaluated tuple is bounded
above and below by positive constant multiples of the input height raised to that degree.

The comparisons hold for all input tuples, including the zero tuple. The index types may be empty,
and the common degree may be zero.

## References

* Michael Stoll, `Mathlib.NumberTheory.Height.MvPolynomial`: the upper and lower height estimates
  `Height.logHeight_eval_le'` and `Height.logHeight_eval_ge'`.
* `MultivariatePolynomials.HomogeneousCertificates`: homogeneous coordinate-power identities,
  constructed by `MvPolynomial.exists_homogeneous_sum_mul_eq_X_pow_of_forall_aeval_eq_zero`.
-/

@[expose] public section

universe u v w

namespace Height

/-- A homogeneous polynomial family whose common zeros over an algebraic closure are all zero
has logarithmic height uniformly within a bounded distance of the input height times its degree. -/
theorem exists_logHeight_eval_sub_mul_bound
    {K : Type u} {I : Type v} {O : Type w}
    [Field K] [Height.AdmissibleAbsValues K] [Finite I] [Finite O]
    (p : O → MvPolynomial I K) (d : ℕ)
    (hp : ∀ j, (p j).IsHomogeneous d)
    (hzero : ∀ x : I → AlgebraicClosure K,
      (∀ j, MvPolynomial.eval₂ (algebraMap K (AlgebraicClosure K)) x (p j) = 0) →
        x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : I → K,
      |Height.logHeight (fun j ↦ MvPolynomial.eval x (p j)) -
        (d : ℝ) * Height.logHeight x| ≤ C := by
  classical
  let : Fintype O := Fintype.ofFinite O
  obtain ⟨M, q, hq, hpow⟩ :=
    MvPolynomial.exists_homogeneous_sum_mul_eq_X_pow_of_forall_aeval_eq_zero p d hp
      (fun x hx ↦ hzero x fun j ↦ by
        simpa only [MvPolynomial.aeval_def] using hx j)
  obtain ⟨C₁, hupper⟩ := Height.logHeight_eval_le' hp
  obtain ⟨C₂, hlower⟩ := Height.logHeight_eval_ge' (N := d) hq
  refine ⟨max 0 (max C₁ (-C₂)), le_max_left _ _, ?_⟩
  intro x
  have heval : ∀ i, ∑ j, MvPolynomial.eval x (q (i, j)) * MvPolynomial.eval x (p j) =
      x i ^ (M + d) := by
    intro i
    simpa only [map_sum, map_mul, map_pow, MvPolynomial.eval_X] using
      congrArg (MvPolynomial.eval x) (hpow i)
  have hupperx := hupper x
  have hlowerx := hlower p heval
  have hC₁ : C₁ ≤ max 0 (max C₁ (-C₂)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hC₂ : -C₂ ≤ max 0 (max C₁ (-C₂)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  exact abs_le.mpr ⟨by linarith only [hlowerx, hC₂], by linarith only [hupperx, hC₁]⟩

/-- A homogeneous polynomial family whose common zeros over an algebraic closure are all zero
has multiplicative height bounded above and below by constant multiples of the input height
raised to its degree, with a comparison constant at least one. -/
theorem exists_mulHeight_eval_bounds
    {K : Type u} {I : Type v} {O : Type w}
    [Field K] [Height.AdmissibleAbsValues K] [Finite I] [Finite O]
    (p : O → MvPolynomial I K) (d : ℕ)
    (hp : ∀ j, (p j).IsHomogeneous d)
    (hzero : ∀ x : I → AlgebraicClosure K,
      (∀ j, MvPolynomial.eval₂ (algebraMap K (AlgebraicClosure K)) x (p j) = 0) →
        x = 0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : I → K,
      C⁻¹ * Height.mulHeight x ^ d ≤ Height.mulHeight (fun j ↦ MvPolynomial.eval x (p j)) ∧
        Height.mulHeight (fun j ↦ MvPolynomial.eval x (p j)) ≤ C * Height.mulHeight x ^ d := by
  obtain ⟨C, hC, hbound⟩ := Height.exists_logHeight_eval_sub_mul_bound p d hp hzero
  refine ⟨Real.exp C, Real.one_le_exp_iff.mpr hC, ?_⟩
  intro x
  have hx : Real.exp (Height.logHeight x) = Height.mulHeight x := by
    rw [Height.logHeight_eq_log_mulHeight, Real.exp_log (Height.mulHeight_pos x)]
  have hy : Real.exp (Height.logHeight (fun j ↦ MvPolynomial.eval x (p j))) =
      Height.mulHeight (fun j ↦ MvPolynomial.eval x (p j)) := by
    rw [Height.logHeight_eq_log_mulHeight, Real.exp_log (Height.mulHeight_pos _)]
  have hpow : Real.exp ((d : ℝ) * Height.logHeight x) = Height.mulHeight x ^ d := by
    rw [Real.exp_nat_mul, hx]
  obtain ⟨hlower, hupper⟩ := abs_le.mp (hbound x)
  constructor
  · calc
      (Real.exp C)⁻¹ * Height.mulHeight x ^ d =
          Real.exp (-C + (d : ℝ) * Height.logHeight x) := by
        rw [Real.exp_add, Real.exp_neg, hpow]
      _ ≤ Real.exp (Height.logHeight (fun j ↦ MvPolynomial.eval x (p j))) :=
        Real.exp_le_exp.mpr (by linarith only [hlower])
      _ = Height.mulHeight (fun j ↦ MvPolynomial.eval x (p j)) := hy
  · calc
      Height.mulHeight (fun j ↦ MvPolynomial.eval x (p j)) =
          Real.exp (Height.logHeight (fun j ↦ MvPolynomial.eval x (p j))) := hy.symm
      _ ≤ Real.exp (C + (d : ℝ) * Height.logHeight x) :=
        Real.exp_le_exp.mpr (by linarith only [hupper])
      _ = Real.exp C * Height.mulHeight x ^ d := by
        rw [Real.exp_add, hpow]

end Height
