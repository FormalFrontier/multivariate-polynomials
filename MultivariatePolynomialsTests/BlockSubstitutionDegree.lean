/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.BlockSubstitutionDegree
import MultivariatePolynomials.UniqueAlgEquiv
public import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Field.ZMod

/-!
# Ordinary-import degree regression checks

A private proposition records natural-degree compatibility for the canonical
unique-variable equivalence over a commutative semiring. The examples compute
the two degrees independently for a natural-number polynomial, and include the
zero polynomial and trivial coefficients. They do not assume or prove the
universally quantified proposition.
A further natural-number degree computation uses the canonical equivalence's
degree identity together with the independent total-degree computation.

## References

* `MultivariatePolynomials.BlockSubstitutionDegree`: exact total degree;
  Mathlib's `Mathlib.Algebra.Field.ZMod` supplies finite coefficient rings.
* Mathlib's `MvPolynomial.uniqueAlgEquiv`, its evaluation API, and the multivariate
  and univariate degree APIs.

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

noncomputable section

universe uniqueDegreeCoeff uniqueDegreeVar

namespace MvPolynomial

/-- Natural-degree compatibility, with independent coefficient and variable universes. -/
private def degreeCompatibility
    (R : Type uniqueDegreeCoeff) (σ : Type uniqueDegreeVar) [CommSemiring R] [Unique σ] : Prop :=
  ∀ p : MvPolynomial σ R,
    Polynomial.natDegree (MvPolynomial.uniqueAlgEquiv R σ p) = p.totalDegree

private theorem nat_unique_totalDegree :
    (MvPolynomial.C 3 + MvPolynomial.X (default : Unit) ^ 4 :
      MvPolynomial Unit ℕ).totalDegree = 4 := by
  have hdegree :
      (MvPolynomial.C 3 : MvPolynomial Unit ℕ).totalDegree <
        (MvPolynomial.X (default : Unit) ^ 4 : MvPolynomial Unit ℕ).totalDegree := by
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow]
    decide
  rw [MvPolynomial.totalDegree_add_eq_right_of_totalDegree_lt hdegree,
    MvPolynomial.totalDegree_X_pow]

public theorem nat_unique_image :
    MvPolynomial.uniqueAlgEquiv ℕ Unit
        (MvPolynomial.C 3 + MvPolynomial.X (default : Unit) ^ 4) =
      Polynomial.C 3 + Polynomial.X ^ 4 := by
  simp only [MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]

private theorem nat_unique_natDegree :
    Polynomial.natDegree
        (MvPolynomial.uniqueAlgEquiv ℕ Unit
          (MvPolynomial.C 3 + MvPolynomial.X (default : Unit) ^ 4)) = 4 := by
  rw [nat_unique_image]
  have hdegree :
      (Polynomial.C 3 : Polynomial ℕ).natDegree <
        (Polynomial.X ^ 4 : Polynomial ℕ).natDegree := by
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    decide
  rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt hdegree,
    Polynomial.natDegree_X_pow]

private theorem nat_unique_natDegree_of_totalDegree :
    Polynomial.natDegree
        (MvPolynomial.uniqueAlgEquiv ℕ Unit
          (MvPolynomial.C 3 + MvPolynomial.X (default : Unit) ^ 4)) = 4 := by
  rw [MvPolynomial.natDegree_uniqueAlgEquiv, nat_unique_totalDegree]

private theorem unique_zero_degrees
    {R : Type uniqueDegreeCoeff} {σ : Type uniqueDegreeVar} [CommSemiring R] [Unique σ] :
    Polynomial.natDegree
        (MvPolynomial.uniqueAlgEquiv R σ (0 : MvPolynomial σ R)) = 0 ∧
      (0 : MvPolynomial σ R).totalDegree = 0 := by
  constructor
  · simp only [map_zero, Polynomial.natDegree_zero]
  · exact MvPolynomial.totalDegree_zero

private theorem unique_trivial_degrees (p : MvPolynomial Unit (ZMod 1)) :
    Polynomial.natDegree (MvPolynomial.uniqueAlgEquiv (ZMod 1) Unit p) = 0 ∧
      p.totalDegree = 0 := by
  have hp : p = 0 := Subsingleton.elim _ _
  rw [hp]
  exact unique_zero_degrees (R := ZMod 1) (σ := Unit)

end MvPolynomial

end
