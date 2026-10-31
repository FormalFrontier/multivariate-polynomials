/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.Noetherian
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Noetherian polynomial rings and their boundaries

This module complements the worked applications beside the criteria in
`MultivariatePolynomials.Noetherian`. It retains model fidelity, independent
Noetherianity engines, coefficient-class and universe boundaries, and explicit
provider versus instance-inference compatibility.

The multivariate boundaries distinguish empty variables, finite variables over
the integers and a ring with zero divisors, infinite variables over nontrivial
Noetherian coefficient rings, and infinite variables over the trivial ring.
The negative examples use the variable-ideal obstruction directly. A further
consumer recovers finiteness of arbitrary variable subsets.

Univariate boundaries include the finite noncommutative ring of two-by-two
matrices over `ZMod 2`, the trivial ring `ZMod 1`, and the nontrivial ring
`ZMod 4` with a nonzero nilpotent. The matrix units verify noncommutativity;
the polynomial ring is infinite and is not Noetherian as a module over the
matrix coefficient ring. The corresponding self-Noetherian worked application
is beside the Hilbert basis theorem. Explicit-provider and inference checks
remain here, including iterated polynomials. Polynomials over `MvPolynomial ℕ ℤ`
remain non-Noetherian by descent to their coefficient ring.

Coefficient-module boundaries independently distinguish empty variables,
nonempty variables with trivial coefficients, and the stronger obstruction from
even finitely many nonempty variables with nontrivial coefficients. They use the
integers, the Boolean ring `ZMod 2` with addition modulo two, the componentwise
product ring `ℤ × ZMod 2` with zero divisors, and the non-ring commutative
semiring `ℕ`. Empty-variable positives use the coefficient-linear equivalence
directly; nonempty-variable negatives use polynomial or monomial-basis engines.
The direct empty, trivial, and nonempty-coefficient worked applications are
beside the combined criterion. A lifted variable with `ZMod 2` coefficients
exercises independent variable and coefficient universes here.

## References

* `MultivariatePolynomials.Noetherian`: Noetherian polynomial-ring criteria.
* `MultivariatePolynomials.IdealOfVars`: the infinite-variable ideal obstruction.
* Mathlib's Hilbert basis, empty-variable equivalence, principal ideal ring,
  finite-ring, and trivial-ring Noetherianity APIs.
* Mathlib, `Mathlib.Data.Matrix.Basis`: matrix units and their products.
* Mathlib, `Mathlib.Algebra.Polynomial.Monomial`: infinitude of polynomials over
  nontrivial semirings.
* Mathlib, `Mathlib.RingTheory.Polynomial.Basic`: polynomials are not finite
  modules over nontrivial coefficient semirings.
-/

@[expose] public section

universe u v

namespace MultivariatePolynomialsTests

private instance : Fact (1 < 6) := ⟨by decide⟩

-- Empty variables retain exactly the coefficient Noetherian condition.
example {R : Type v} [CommSemiring R] :
    IsNoetherianRing (MvPolynomial (Fin 0) R) ↔ IsNoetherianRing R := by
  constructor
  · intro h
    let : IsNoetherianRing (MvPolynomial (Fin 0) R) := h
    exact isNoetherianRing_of_ringEquiv (MvPolynomial (Fin 0) R)
      (MvPolynomial.isEmptyRingEquiv R (Fin 0))
  · intro h
    let : IsNoetherianRing R := h
    exact isNoetherianRing_of_ringEquiv R
      (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm

-- Even with no variables, a non-Noetherian coefficient ring remains non-Noetherian.
example :
    ¬ IsNoetherianRing (MvPolynomial (Fin 0) (MvPolynomial ℕ ℤ)) := by
  intro h
  let : IsNoetherianRing (MvPolynomial (Fin 0) (MvPolynomial ℕ ℤ)) := h
  have hbase : IsNoetherianRing (MvPolynomial ℕ ℤ) :=
    isNoetherianRing_of_ringEquiv (MvPolynomial (Fin 0) (MvPolynomial ℕ ℤ))
      (MvPolynomial.isEmptyRingEquiv (MvPolynomial ℕ ℤ) (Fin 0))
  let : IsNoetherianRing (MvPolynomial ℕ ℤ) := hbase
  exact MvPolynomial.idealOfVars_not_fg ℤ ℕ
    (Ideal.fg_of_isNoetherianRing (MvPolynomial.idealOfVars ℕ ℤ))

-- Finite-variable Noetherianity is supplied by the existing Hilbert basis instance.
example : IsNoetherianRing ℤ ∧
    IsNoetherianRing (MvPolynomial (Fin 2) ℤ) ∧
      Nontrivial (MvPolynomial (Fin 2) ℤ) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

example : IsNoetherianRing (ZMod 6) ∧
    IsNoetherianRing (MvPolynomial (Fin 2) (ZMod 6)) ∧
      Nontrivial (MvPolynomial (Fin 2) (ZMod 6)) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

example : (2 : ZMod 6) ≠ 0 ∧ (3 : ZMod 6) ≠ 0 ∧ (2 : ZMod 6) * 3 = 0 := by
  decide

-- Noetherian coefficients do not suffice for infinitely many variables.
example : IsNoetherianRing (ZMod 6) ∧
    ¬ IsNoetherianRing (MvPolynomial ℕ (ZMod 6)) := by
  refine ⟨inferInstance, ?_⟩
  intro h
  let : IsNoetherianRing (MvPolynomial ℕ (ZMod 6)) := h
  exact MvPolynomial.idealOfVars_not_fg (ZMod 6) ℕ
    (Ideal.fg_of_isNoetherianRing (MvPolynomial.idealOfVars ℕ (ZMod 6)))

-- Trivial coefficients make the polynomial ring Noetherian regardless of variables.
example : IsNoetherianRing (ZMod 1) ∧
    IsNoetherianRing (MvPolynomial ℕ (ZMod 1)) ∧ ¬ Finite ℕ := by
  exact ⟨inferInstance, inferInstance, Infinite.not_finite⟩

example : (MvPolynomial.X 0 : MvPolynomial ℕ (ZMod 1)) = 0 := by
  exact Subsingleton.elim _ _

-- The finite-variable conclusion provides an instance usable for arbitrary subsets.
-- The coefficient and variable universes remain independent.
example {σ : Type u} {R : Type v} [CommSemiring R] [Nontrivial R]
    [IsNoetherianRing (MvPolynomial σ R)] (S : Set σ) : S.Finite := by
  let : Finite σ := MvPolynomial.finite_of_isNoetherianRing (σ := σ) (R := R)
  exact S.toFinite

-- The matrix multiplication is the usual row-by-column multiplication.
private abbrev binaryMatrixRing := Matrix (Fin 2) (Fin 2) (ZMod 2)

private theorem binary_matrix_coefficient_conditions :
    Nonempty (Ring binaryMatrixRing) ∧ Finite binaryMatrixRing ∧
      Nontrivial binaryMatrixRing := by
  let : Nontrivial (ZMod 2) := ZMod.nontrivial_iff.mpr (by decide)
  exact ⟨⟨inferInstance⟩, inferInstance, inferInstance⟩

-- Both the scalar ring and the module are the matrix ring itself.
private theorem binary_matrix_isNoetherianRing : IsNoetherianRing binaryMatrixRing := by
  exact isNoetherian_of_finite binaryMatrixRing binaryMatrixRing

-- Two central coordinates are allowed over these genuinely noncommutative
-- coefficients; finite coordinates do not make the exponent monoid finite.
private theorem binary_matrix_two_coordinates_isNoetherianRing :
    IsNoetherianRing (AddMonoidAlgebra binaryMatrixRing (Fin 2 →₀ ℕ)) := by
  let : IsNoetherianRing binaryMatrixRing := binary_matrix_isNoetherianRing
  exact AddMonoidAlgebra.isNoetherianRing_finsupp binaryMatrixRing (Fin 2)

private theorem binary_matrix_noncommutative :
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod 2) *
        Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ZMod 2) ≠
      Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ZMod 2) *
        Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod 2) := by
  intro h
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h
  have h10 : (1 : ZMod 2) = 0 := by
    simpa [Matrix.single] using congrArg (fun M : binaryMatrixRing => M 0 0) h
  exact (show (1 : ZMod 2) ≠ 0 by decide) h10

private theorem binary_matrix_polynomial_infinite : Infinite (Polynomial binaryMatrixRing) := by
  let : Nontrivial binaryMatrixRing := binary_matrix_coefficient_conditions.2.2
  exact Polynomial.infinite

-- Coefficient-module Noetherianity is different from polynomial self-Noetherianity.
private theorem binary_matrix_polynomial_not_noetherian_over_coefficients :
    ¬ IsNoetherian binaryMatrixRing (Polynomial binaryMatrixRing) := by
  intro h
  let : Nontrivial binaryMatrixRing := binary_matrix_coefficient_conditions.2.2
  let : IsNoetherian binaryMatrixRing (Polynomial binaryMatrixRing) := h
  exact Polynomial.not_finite (R := binaryMatrixRing)
    (inferInstance : Module.Finite binaryMatrixRing (Polynomial binaryMatrixRing))

private theorem zmod_one_coefficient_conditions :
    Nonempty (CommRing (ZMod 1)) ∧ Subsingleton (ZMod 1) ∧
      IsNoetherianRing (ZMod 1) := by
  exact ⟨⟨inferInstance⟩, inferInstance, isNoetherian_of_subsingleton (ZMod 1) (ZMod 1)⟩

private theorem zmod_one_one_eq_zero : (1 : ZMod 1) = 0 := by
  exact Subsingleton.elim _ _

private theorem polynomial_zmod_one_subsingleton : Subsingleton (Polynomial (ZMod 1)) := by
  infer_instance

private theorem zmod_four_coefficient_conditions :
    Nonempty (CommRing (ZMod 4)) ∧ Nontrivial (ZMod 4) ∧
      IsNoetherianRing (ZMod 4) := by
  exact ⟨⟨inferInstance⟩, ZMod.nontrivial_iff.mpr (by decide),
    isNoetherian_of_finite (ZMod 4) (ZMod 4)⟩

private theorem zmod_four_nilpotent : (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by
  decide

private theorem polynomial_zmod_four_isNoetherianRing :
    IsNoetherianRing (Polynomial (ZMod 4)) := by
  let : IsNoetherianRing (ZMod 4) := zmod_four_coefficient_conditions.2.2
  exact Polynomial.isNoetherianRing

private theorem infinite_integer_polynomial_coefficient_conditions :
    Nonempty (CommRing (MvPolynomial ℕ ℤ)) ∧ Nontrivial (MvPolynomial ℕ ℤ) := by
  exact ⟨⟨inferInstance⟩, inferInstance⟩

private theorem infinite_integer_polynomial_not_isNoetherianRing :
    ¬ IsNoetherianRing (MvPolynomial ℕ ℤ) := by
  intro h
  let : IsNoetherianRing (MvPolynomial ℕ ℤ) := h
  exact MvPolynomial.idealOfVars_not_fg ℤ ℕ
    (Ideal.fg_of_isNoetherianRing (MvPolynomial.idealOfVars ℕ ℤ))

private theorem polynomial_infinite_integer_polynomial_not_isNoetherianRing :
    ¬ IsNoetherianRing (Polynomial (MvPolynomial ℕ ℤ)) := by
  intro h
  let : IsNoetherianRing (Polynomial (MvPolynomial ℕ ℤ)) := h
  exact infinite_integer_polynomial_not_isNoetherianRing
    (isNoetherianRing_of_surjective (Polynomial (MvPolynomial ℕ ℤ)) (MvPolynomial ℕ ℤ)
      Polynomial.constantCoeff Polynomial.constantCoeff_surjective)

private theorem polynomial_zmod_one_isNoetherianRing_of_isNoetherianRing :
    IsNoetherianRing (Polynomial (ZMod 1)) := by
  let : IsNoetherianRing (ZMod 1) := zmod_one_coefficient_conditions.2.2
  exact Polynomial.isNoetherianRing_of_isNoetherianRing (R := ZMod 1)

private theorem polynomial_zmod_four_isNoetherianRing_of_isNoetherianRing :
    IsNoetherianRing (Polynomial (ZMod 4)) := by
  let : IsNoetherianRing (ZMod 4) := zmod_four_coefficient_conditions.2.2
  exact Polynomial.isNoetherianRing_of_isNoetherianRing (R := ZMod 4)

-- Inference over noncommutative coefficients uses the general Hilbert basis instance.
private theorem binary_matrix_polynomial_noetherian_instance :
    IsNoetherianRing (Polynomial binaryMatrixRing) := by
  let : IsNoetherianRing binaryMatrixRing := binary_matrix_isNoetherianRing
  infer_instance

-- The commutative and trivial-ring instances remain available alongside the general one.
private theorem polynomial_zmod_one_noetherian_instance :
    IsNoetherianRing (Polynomial (ZMod 1)) := by
  let : IsNoetherianRing (ZMod 1) := zmod_one_coefficient_conditions.2.2
  infer_instance

private theorem polynomial_zmod_four_noetherian_instance :
    IsNoetherianRing (Polynomial (ZMod 4)) := by
  let : IsNoetherianRing (ZMod 4) := zmod_four_coefficient_conditions.2.2
  infer_instance

-- Both polynomial layers are inferred from the Noetherian matrix coefficient ring.
private theorem binary_matrix_iterated_polynomial_isNoetherianRing :
    Infinite (Polynomial (Polynomial binaryMatrixRing)) ∧
      IsNoetherianRing (Polynomial (Polynomial binaryMatrixRing)) := by
  let : Nontrivial binaryMatrixRing := binary_matrix_coefficient_conditions.2.2
  let : IsNoetherianRing binaryMatrixRing := binary_matrix_isNoetherianRing
  refine ⟨Polynomial.infinite, ?_⟩
  infer_instance

-- Coefficient-module models use only existing equivalence, basis, and
-- Noetherianity engines. The scalar in each IsNoetherian conclusion is the
-- literal coefficient semiring, never the polynomial semiring itself.
private theorem coefficient_integer_conditions :
    Nonempty (CommRing ℤ) ∧ Nontrivial ℤ ∧ IsNoetherianRing ℤ := by
  exact ⟨⟨inferInstance⟩, inferInstance, inferInstance⟩

private theorem coefficient_empty_integer :
    IsNoetherian ℤ (MvPolynomial Empty ℤ) := by
  exact isNoetherian_of_linearEquiv
    (MvPolynomial.isEmptyAlgEquiv ℤ Empty).toLinearEquiv.symm

private theorem coefficient_zero_infinite :
    Infinite ℕ ∧ Subsingleton (MvPolynomial ℕ (ZMod 1)) ∧
      IsNoetherian (ZMod 1) (MvPolynomial ℕ (ZMod 1)) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem coefficient_zero_nonempty :
    Nonempty Unit ∧ IsNoetherian (ZMod 1) (MvPolynomial Unit (ZMod 1)) := by
  exact ⟨inferInstance, inferInstance⟩

-- The earlier Fin 2 integer example is genuinely SELF-Noetherian. Its
-- coefficient module is nevertheless not Noetherian, even with finite variables.
private theorem coefficient_finite_integer_not_noetherian :
    ¬ IsNoetherian ℤ (MvPolynomial (Fin 2) ℤ) := by
  intro h
  let : IsNoetherian ℤ (MvPolynomial (Fin 2) ℤ) := h
  exact Module.not_finite_of_infinite_basis (MvPolynomial.basisMonomials (Fin 2) ℤ)
    (inferInstance : Module.Finite ℤ (MvPolynomial (Fin 2) ℤ))

private theorem coefficient_infinite_integer_not_noetherian :
    ¬ IsNoetherian ℤ (MvPolynomial ℕ ℤ) := by
  intro h
  let : IsNoetherian ℤ (MvPolynomial ℕ ℤ) := h
  exact Module.not_finite_of_infinite_basis (MvPolynomial.basisMonomials ℕ ℤ)
    (inferInstance : Module.Finite ℤ (MvPolynomial ℕ ℤ))

-- Empty variables do not remove the regular coefficient Noetherian condition.
private theorem coefficient_empty_non_noetherian :
    ¬ IsNoetherian (MvPolynomial ℕ ℤ)
      (MvPolynomial Empty (MvPolynomial ℕ ℤ)) := by
  intro h
  let : IsNoetherian (MvPolynomial ℕ ℤ)
    (MvPolynomial Empty (MvPolynomial ℕ ℤ)) := h
  exact infinite_integer_polynomial_not_isNoetherianRing
    (isNoetherian_of_linearEquiv
      (MvPolynomial.isEmptyAlgEquiv (MvPolynomial ℕ ℤ) Empty).toLinearEquiv)

-- The Boolean coefficient model is the actual ring ZMod 2: its addition is
-- modulo two (XOR), not the OR/AND semiring and not a new instance on Bool.
private theorem coefficient_boolean_ring_conditions :
    Nonempty (CommRing (ZMod 2)) ∧ IsNoetherianRing (ZMod 2) ∧
      (1 : ZMod 2) ≠ 0 ∧ (1 : ZMod 2) + 1 = 0 ∧
        (∀ b : ZMod 2, b * b = b) := by
  exact ⟨⟨inferInstance⟩, isNoetherian_of_finite (ZMod 2) (ZMod 2),
    by decide, by decide, by decide⟩

private theorem coefficient_empty_boolean :
    IsNoetherian (ZMod 2) (MvPolynomial Empty (ZMod 2)) := by
  let : IsNoetherianRing (ZMod 2) := isNoetherian_of_finite (ZMod 2) (ZMod 2)
  exact isNoetherian_of_linearEquiv
    (MvPolynomial.isEmptyAlgEquiv (ZMod 2) Empty).toLinearEquiv.symm

private theorem coefficient_unit_boolean_not_noetherian :
    ¬ IsNoetherian (ZMod 2) (MvPolynomial Unit (ZMod 2)) := by
  intro h
  let : Nontrivial (ZMod 2) := ZMod.nontrivial_iff.mpr (by decide)
  let : IsNoetherian (ZMod 2) (MvPolynomial Unit (ZMod 2)) := h
  let : IsNoetherian (ZMod 2) (Polynomial (ZMod 2)) :=
    isNoetherian_of_linearEquiv (MvPolynomial.uniqueAlgEquiv (ZMod 2) Unit).toLinearEquiv
  exact Polynomial.not_finite (R := ZMod 2)
    (inferInstance : Module.Finite (ZMod 2) (Polynomial (ZMod 2)))

-- Product coefficients retain their literal componentwise ring multiplication.
private theorem coefficient_product_conditions :
    Nonempty (CommRing (ℤ × ZMod 2)) ∧ Nontrivial (ℤ × ZMod 2) ∧
      IsNoetherianRing (ℤ × ZMod 2) := by
  let : IsNoetherianRing (ZMod 2) := isNoetherian_of_finite (ZMod 2) (ZMod 2)
  exact ⟨⟨inferInstance⟩, inferInstance, inferInstance⟩

private theorem coefficient_product_zero_divisors :
    ((1, 0) : ℤ × ZMod 2) ≠ 0 ∧ ((0, 1) : ℤ × ZMod 2) ≠ 0 ∧
      ((1, 0) : ℤ × ZMod 2) * (0, 1) = 0 := by
  decide

private theorem coefficient_product_not_domain : ¬ IsDomain (ℤ × ZMod 2) := by
  intro h
  let : IsDomain (ℤ × ZMod 2) := h
  rcases mul_eq_zero.mp coefficient_product_zero_divisors.2.2 with hzero | hzero
  · exact coefficient_product_zero_divisors.1 hzero
  · exact coefficient_product_zero_divisors.2.1 hzero

private theorem coefficient_product_not_field : ¬ IsField (ℤ × ZMod 2) := by
  intro h
  exact coefficient_product_not_domain h.isDomain

private theorem coefficient_empty_product :
    IsNoetherian (ℤ × ZMod 2) (MvPolynomial Empty (ℤ × ZMod 2)) := by
  let : IsNoetherianRing (ℤ × ZMod 2) := coefficient_product_conditions.2.2
  exact isNoetherian_of_linearEquiv
    (MvPolynomial.isEmptyAlgEquiv (ℤ × ZMod 2) Empty).toLinearEquiv.symm

private theorem coefficient_finite_product_self :
    IsNoetherianRing (MvPolynomial (Fin 2) (ℤ × ZMod 2)) := by
  let : IsNoetherianRing (ℤ × ZMod 2) := coefficient_product_conditions.2.2
  infer_instance

private theorem coefficient_finite_product_not_noetherian :
    ¬ IsNoetherian (ℤ × ZMod 2) (MvPolynomial (Fin 2) (ℤ × ZMod 2)) := by
  intro h
  let : IsNoetherian (ℤ × ZMod 2) (MvPolynomial (Fin 2) (ℤ × ZMod 2)) := h
  exact Module.not_finite_of_infinite_basis
    (MvPolynomial.basisMonomials (Fin 2) (ℤ × ZMod 2))
    (inferInstance : Module.Finite (ℤ × ZMod 2) (MvPolynomial (Fin 2) (ℤ × ZMod 2)))

private theorem coefficient_infinite_product_not_noetherian :
    ¬ IsNoetherian (ℤ × ZMod 2) (MvPolynomial ℕ (ℤ × ZMod 2)) := by
  intro h
  let : IsNoetherian (ℤ × ZMod 2) (MvPolynomial ℕ (ℤ × ZMod 2)) := h
  exact Module.not_finite_of_infinite_basis (MvPolynomial.basisMonomials ℕ (ℤ × ZMod 2))
    (inferInstance : Module.Finite (ℤ × ZMod 2) (MvPolynomial ℕ (ℤ × ZMod 2)))

-- Ordinary naturals are a genuine non-ring commutative semiring: 1 has no
-- additive inverse. Their regular Noetherianity is Mathlib's Frobenius provider.
private theorem coefficient_nat_conditions :
    Nonempty (CommSemiring ℕ) ∧ Nontrivial ℕ ∧ IsNoetherianRing ℕ ∧
      ¬ (∃ n : ℕ, 1 + n = 0) := by
  refine ⟨⟨inferInstance⟩, inferInstance, inferInstance, ?_⟩
  rintro ⟨n, hn⟩
  exact Nat.succ_ne_zero n (by simpa only [Nat.add_comm] using hn)

private theorem coefficient_empty_nat :
    IsNoetherian ℕ (MvPolynomial Empty ℕ) := by
  exact isNoetherian_of_linearEquiv
    (MvPolynomial.isEmptyAlgEquiv ℕ Empty).toLinearEquiv.symm

private theorem coefficient_unit_nat_not_noetherian :
    ¬ IsNoetherian ℕ (MvPolynomial Unit ℕ) := by
  intro h
  let : IsNoetherian ℕ (MvPolynomial Unit ℕ) := h
  let : IsNoetherian ℕ (Polynomial ℕ) :=
    isNoetherian_of_linearEquiv (MvPolynomial.uniqueAlgEquiv ℕ Unit).toLinearEquiv
  exact Polynomial.not_finite (R := ℕ)
    (inferInstance : Module.Finite ℕ (Polynomial ℕ))

-- The coefficient criterion also applies with independent variable and
-- coefficient universes, retaining the chosen lifted variable.
private theorem coefficient_zmod_two_not_noetherian_ulift :
    ¬ IsNoetherian (ZMod 2) (MvPolynomial (ULift.{u} Unit) (ZMod 2)) := by
  intro h
  rcases (MvPolynomial.isNoetherian_iff.mp h).2 with hσ | hR
  · exact hσ.false ⟨()⟩
  · exact (show (1 : ZMod 2) ≠ 0 by decide) (@Subsingleton.elim _ hR 1 0)

end MultivariatePolynomialsTests
