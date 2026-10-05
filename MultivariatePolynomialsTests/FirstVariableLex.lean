/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.FirstVariableLex

/-!
# First-variable lexicographic examples

The natural-number clients exercise arbitrary degree, a nonconstant lower
coefficient slice, zero degree, and the absence of remaining variables.
The last example shows why the top slice must be scalar.

## References

* `MultivariatePolynomials.FirstVariableLex`: scalar-top lexicographic degree
  and pointwise exponent comparison.
-/

set_option warningAsError true

example (n d : ℕ) :
    (MonomialOrder.lex : MonomialOrder (Fin (n + 1))).degree
        ((MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) ℕ) ^ d) =
      (0 : Fin n →₀ ℕ).cons d := by
  apply MonomialOrder.lex_degree_of_finSuccEquiv_scalar_top n d _ (1 : ℕ)
  · simp only [map_pow, MvPolynomial.finSuccEquiv_X_zero, Polynomial.natDegree_X_pow]
  · simp only [map_pow, MvPolynomial.finSuccEquiv_X_zero,
      Polynomial.coeff_X_pow_self, MvPolynomial.C_1]
  · exact one_ne_zero

example :
    (MonomialOrder.lex : MonomialOrder (Fin 2)).degree
        (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℕ) =
      (0 : Fin 1 →₀ ℕ).cons 1 := by
  have hX1 :
      (MvPolynomial.finSuccEquiv ℕ 1) (MvPolynomial.X (1 : Fin 2)) =
        Polynomial.C (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℕ) := by
    have hindex : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact MvPolynomial.finSuccEquiv_X_succ
  apply MonomialOrder.lex_degree_of_finSuccEquiv_scalar_top 1 1 _ (1 : ℕ)
  · simp [MvPolynomial.finSuccEquiv_X_zero, hX1]
  · simp [MvPolynomial.finSuccEquiv_X_zero, hX1]
  · exact one_ne_zero

example :
    (MonomialOrder.lex : MonomialOrder (Fin (0 + 1))).degree
        (1 : MvPolynomial (Fin (0 + 1)) ℕ) = (0 : Fin 0 →₀ ℕ).cons 0 := by
  apply MonomialOrder.lex_degree_of_finSuccEquiv_scalar_top 0 0 _ (1 : ℕ)
  · simp
  · simp
  · exact one_ne_zero

example (d i : ℕ) :
    ((0 : Fin 0 →₀ ℕ).cons d) ≤ (0 : Fin 0 →₀ ℕ).cons i ↔ d ≤ i :=
  Finsupp.cons_zero_le_cons_iff 0

example (d i : ℕ) :
    ((0 : Fin 1 →₀ ℕ).cons d) ≤
        (Finsupp.single (0 : Fin 1) 7).cons i ↔ d ≤ i :=
  Finsupp.cons_zero_le_cons_iff _

example :
    (MonomialOrder.lex : MonomialOrder (Fin 2)).degree
        (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℕ) ≠
      (0 : Fin 1 →₀ ℕ).cons 0 := by
  rw [MonomialOrder.degree_X]
  intro h
  have hcoord : (1 : ℕ) = 0 := by
    simpa using congrArg (fun exponent : Fin 2 →₀ ℕ => exponent 1) h
  exact one_ne_zero hcoord
