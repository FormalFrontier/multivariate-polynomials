/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.ResultantFactorization
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Crossed-resultant uniqueness over a ring with zero divisors

The fixed first factor `2 * X + 1` over `ℤ/4ℤ` has a nonzero, nonunit,
zero-divisor leading coefficient. Its crossed resultant with `X` is `-1`, so
pairwise top coefficients and equality of products still force uniqueness.
-/

open Polynomial

private theorem nonmonic_factorization_unique
    (G H' : (ZMod 4)[X]) (hG : G.natDegree ≤ 1) (hH' : H'.natDegree ≤ 1)
    (hGtop : G.coeff 1 = 2) (hH'top : H'.coeff 1 = 1)
    (hprod : G * X = (C 2 * X + 1) * H') :
    G = C 2 * X + 1 ∧ H' = X := by
  have hfixed : (C 2 * X + 1 : (ZMod 4)[X]).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp [natDegree_C_mul_X, show (2 : ZMod 4) ≠ 0 by decide]
    · simp
  have hresval : resultant (C 2 * X + 1 : (ZMod 4)[X]) X 1 1 = -1 := by
    change (sylvester (C 2 * X + 1) X 1 1 : Matrix (Fin 2) (Fin 2) (ZMod 4)).det = -1
    rw [Matrix.det_fin_two]
    norm_num [sylvester, Fin.addCases, coeff_one]
  have hres : IsRegular (resultant (C 2 * X + 1 : (ZMod 4)[X]) X 1 1) := by
    rw [hresval]
    exact (isUnit_neg_one : IsUnit (-1 : ZMod 4)).isRegular
  obtain ⟨h₁, h₂⟩ := eq_and_eq_of_mul_eq_mul_of_isRegular_resultant 1 1
    G X (C 2 * X + 1) H' hG hfixed natDegree_X_le hH'
    (by simpa [coeff_one] using hGtop) (by simpa using hH'top.symm) hprod hres
  exact ⟨h₁, h₂.symm⟩
