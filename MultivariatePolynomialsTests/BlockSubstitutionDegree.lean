/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.BlockSubstitutionDegree
import Mathlib.Algebra.Field.ZMod

/-!
# Ordinary-import degree regression checks

## References

* `MultivariatePolynomials.BlockSubstitutionDegree`: exact total degree;
  Mathlib's `Mathlib.Algebra.Field.ZMod` supplies finite coefficient rings.

-/

set_option warningAsError true

namespace MvPolynomial

universe u v w

variable {I : Type u} {J : Type v} {R : Type w} [CommSemiring R] [NoZeroDivisors R]

example (p : MvPolynomial I R) (q : MvPolynomial J R) :
    (blockSubst p q).totalDegree = p.totalDegree * q.totalDegree :=
  totalDegree_blockSubst p q

example (q : MvPolynomial J R) :
    (blockSubst (0 : MvPolynomial I R) q).totalDegree = 0 := by
  rw [totalDegree_blockSubst]
  simp

example (p : MvPolynomial I R) :
    (blockSubst p (0 : MvPolynomial J R)).totalDegree = 0 := by
  rw [totalDegree_blockSubst]
  simp

example (p : MvPolynomial I R) (r : R) :
    (blockSubst p (C r : MvPolynomial J R)).totalDegree = 0 := by
  rw [totalDegree_blockSubst]
  simp

example (c : ℕ) (q : MvPolynomial (Fin 3) ℕ) :
    (blockSubst (C c : MvPolynomial PEmpty ℕ) q).totalDegree = 0 := by
  rw [totalDegree_blockSubst, totalDegree_C, zero_mul]

example (c : ℕ) (p : MvPolynomial (Fin 2) ℕ) :
    (blockSubst p (C c : MvPolynomial PEmpty ℕ)).totalDegree = 0 := by
  rw [totalDegree_blockSubst, totalDegree_C, mul_zero]

example (p : MvPolynomial (Fin 2) (ZMod 1))
    (q : MvPolynomial PEmpty (ZMod 1)) :
    (blockSubst p q).totalDegree = p.totalDegree * q.totalDegree :=
  totalDegree_blockSubst p q

example :
    (blockSubst
      (X (0 : Fin 2) ^ 2 + X 1 : MvPolynomial (Fin 2) ℕ)
      (X (0 : Fin 3) ^ 2 + X 1 : MvPolynomial (Fin 3) ℕ)).totalDegree = 4 := by
  have hp : (X (0 : Fin 2) ^ 2 + X 1 : MvPolynomial (Fin 2) ℕ).totalDegree = 2 := by
    rw [totalDegree_add_eq_left_of_totalDegree_lt]
    · simp
    · simp
  have hq : (X (0 : Fin 3) ^ 2 + X 1 : MvPolynomial (Fin 3) ℕ).totalDegree = 2 := by
    rw [totalDegree_add_eq_left_of_totalDegree_lt]
    · simp
    · simp
  rw [totalDegree_blockSubst, hp, hq]

example :
    (blockSubst
      (X (0 : Fin 2) ^ 3 + X 1 : MvPolynomial (Fin 2) (ZMod 5))
      (X (0 : Fin 2) ^ 2 + X 1 : MvPolynomial (Fin 2) (ZMod 5))).totalDegree = 6 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp : (X (0 : Fin 2) ^ 3 + X 1 : MvPolynomial (Fin 2) (ZMod 5)).totalDegree = 3 := by
    rw [totalDegree_add_eq_left_of_totalDegree_lt]
    · simp
    · simp
  have hq : (X (0 : Fin 2) ^ 2 + X 1 : MvPolynomial (Fin 2) (ZMod 5)).totalDegree = 2 := by
    rw [totalDegree_add_eq_left_of_totalDegree_lt]
    · simp
    · simp
  rw [totalDegree_blockSubst, hp, hq]

end MvPolynomial
