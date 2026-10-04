/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.EvaluationIdeal
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Coordinate-difference ideal clients

These examples exercise the evaluation-ideal statements at a nonzero integer
point, in infinitely many or no variables, over rings with zero divisors or
only one element, and at a rational point.
-/

private theorem integerNonconstant :
    (MvPolynomial.X (3 : ℕ) ^ 2 - MvPolynomial.C (25 : ℤ)) ∈
      Ideal.span (Set.range (fun i : ℕ =>
        (MvPolynomial.X i : MvPolynomial ℕ ℤ) - MvPolynomial.C (5 : ℤ))) := by
  apply (MvPolynomial.mem_ideal_span_X_sub_C_iff (fun _ : ℕ => (5 : ℤ)) _).2
  norm_num

public theorem MultivariatePolynomialsTests.integerNonmember :
    (MvPolynomial.X (3 : ℕ) - MvPolynomial.C (4 : ℤ)) ∉
      Ideal.span (Set.range (fun i : ℕ =>
        (MvPolynomial.X i : MvPolynomial ℕ ℤ) - MvPolynomial.C (5 : ℤ))) := by
  rw [MvPolynomial.mem_ideal_span_X_sub_C_iff]
  norm_num

private theorem emptyVariablesNonmember :
    (MvPolynomial.C (1 : ℤ) : MvPolynomial (Fin 0) ℤ) ∉
      Ideal.span (Set.range (fun i : Fin 0 =>
        (MvPolynomial.X i : MvPolynomial (Fin 0) ℤ) - MvPolynomial.C (0 : ℤ))) := by
  rw [MvPolynomial.mem_ideal_span_X_sub_C_iff]
  norm_num

private theorem zeroDivisors :
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) -
      MvPolynomial.C (0 : ZMod 6)) ∈
      Ideal.span (Set.range (fun i : Fin 2 =>
        (MvPolynomial.X i : MvPolynomial (Fin 2) (ZMod 6)) -
          MvPolynomial.C (if i = 0 then (2 : ZMod 6) else 3))) := by
  apply (MvPolynomial.mem_ideal_span_X_sub_C_iff
    (fun i : Fin 2 => if i = 0 then (2 : ZMod 6) else 3) _).2
  norm_num
  exact ZMod.natCast_self 6

private theorem zeroRing (p : MvPolynomial (Fin 2) (ZMod 1)) :
    p ∈ Ideal.span (Set.range (fun i : Fin 2 =>
      (MvPolynomial.X i : MvPolynomial (Fin 2) (ZMod 1)) - MvPolynomial.C (0 : ZMod 1))) := by
  apply (MvPolynomial.mem_ideal_span_X_sub_C_iff (fun _ : Fin 2 => (0 : ZMod 1)) p).2
  exact Subsingleton.elim _ _

private theorem rationalVanishing :
    (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (7 : ℚ)) ∈
      MvPolynomial.vanishingIdeal ℚ {(fun _ : Fin 2 => (7 : ℚ))} := by
  rw [← MvPolynomial.ideal_span_X_sub_C_eq_vanishingIdeal_singleton]
  exact Ideal.subset_span (Set.mem_range_self (0 : Fin 2))

private theorem zeroPointVariableIdeal :
    Ideal.span (Set.range (fun i : ℕ =>
      (MvPolynomial.X i : MvPolynomial ℕ ℤ) - MvPolynomial.C (0 : ℤ))) =
      MvPolynomial.idealOfVars ℕ ℤ := by
  simp [MvPolynomial.idealOfVars]
