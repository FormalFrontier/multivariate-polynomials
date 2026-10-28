/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.ResultantCongruence

/-!
A cubic coefficient can disappear modulo `(2)` even when both nominal Sylvester
sizes are one. The congruence theorem does not require bounds on these polynomials.
-/

open Polynomial

example :
    resultant ((X : ℤ[X]) + C 2 * X ^ 3) (X + 1) 1 1 -
      resultant X (X + 1) 1 1 ∈ Ideal.span {(2 : ℤ)} := by
  apply resultant_sub_mem_ideal
  · intro k
    by_cases hk : k = 3
    · subst k
      simp
    · simp [hk]
  · intro k
    simp
