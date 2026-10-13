/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.Noetherian
import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Polynomial semirings with trivial additive units

Independent fixtures check natural coefficients, positive powers and the zero
exponent, the existing unique-variable equivalence, zero divisors and genuinely
noncommutative matrix multiplication. The zero ring and integers delimit the
nontriviality and additive-unit hypotheses. The named fixtures do not use the
negative polynomial theorem; anonymous clients only check its applicability.

## References

* Mathlib's Frobenius-number proof of Noetherianity of the natural numbers.
* Mathlib's additive-unit, polynomial coefficient, unique-variable equivalence,
  Noetherian ring-equivalence transport, product and matrix APIs.
-/

@[expose] public section

universe u v

namespace MultivariatePolynomialsTests

private theorem nat_coefficient_conditions :
    IsNoetherianRing ℕ ∧ Nontrivial ℕ ∧ Subsingleton (AddUnits ℕ) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem linear_coefficients :
    (1 + Polynomial.X ^ 1 : Polynomial ℕ) = 1 + Polynomial.X ∧
      (1 + Polynomial.X ^ 1 : Polynomial ℕ).coeff 0 = 1 ∧
      (1 + Polynomial.X ^ 1 : Polynomial ℕ).coeff 1 = 1 ∧ 0 < (1 : ℕ) := by
  simp [Polynomial.coeff_one]

private theorem cubic_coefficients :
    (1 + Polynomial.X ^ 3 : Polynomial ℕ).coeff 0 = 1 ∧
      (1 + Polynomial.X ^ 3 : Polynomial ℕ).coeff 3 = 1 ∧ 0 < (3 : ℕ) := by
  simp [Polynomial.coeff_one]

private theorem positive_polynomials_ne_zero :
    (1 + Polynomial.X ^ 1 : Polynomial ℕ) ≠ 0 ∧
      (1 + Polynomial.X ^ 3 : Polynomial ℕ) ≠ 0 := by
  constructor <;> intro h
  · exact Nat.one_ne_zero (by
      simpa using congrArg (fun p : Polynomial ℕ => p.coeff 0) h)
  · exact Nat.one_ne_zero (by
      simpa using congrArg (fun p : Polynomial ℕ => p.coeff 0) h)

private theorem zero_exponent_boundary :
    (1 + Polynomial.X ^ 0 : Polynomial ℕ) = 2 ∧
      (1 + Polynomial.X ^ 0 : Polynomial ℕ).coeff 0 = 2 ∧
      (1 + Polynomial.X ^ 0 : Polynomial ℕ).coeff 0 ≠ 1 := by
  simp [one_add_one_eq_two]

-- These are self-module transports, with independent coefficient/variable universes.
private theorem unique_noetherian_transport
    {σ : Type u} {R : Type v} [CommSemiring R] [Unique σ] :
    IsNoetherianRing (MvPolynomial σ R) ↔ IsNoetherianRing (Polynomial R) := by
  constructor
  · intro h
    let : IsNoetherianRing (MvPolynomial σ R) := h
    exact isNoetherianRing_of_ringEquiv (MvPolynomial σ R)
      (MvPolynomial.uniqueAlgEquiv R σ).toRingEquiv
  · intro h
    let : IsNoetherianRing (Polynomial R) := h
    exact isNoetherianRing_of_ringEquiv (Polynomial R)
      (MvPolynomial.uniqueAlgEquiv R σ).symm.toRingEquiv

private theorem pUnit_noetherian_transport
    {R : Type v} [CommSemiring R] :
    IsNoetherianRing (MvPolynomial PUnit.{u + 1} R) ↔
      IsNoetherianRing (Polynomial R) := by
  exact unique_noetherian_transport

private theorem nat_product_conditions :
    Nontrivial (ℕ × ℕ) ∧ Subsingleton (AddUnits (ℕ × ℕ)) := by
  exact ⟨inferInstance, inferInstance⟩

private theorem nat_product_zero_divisors :
    ((1, 0) : ℕ × ℕ) ≠ 0 ∧ ((0, 1) : ℕ × ℕ) ≠ 0 ∧
      ((1, 0) : ℕ × ℕ) * (0, 1) = 0 := by
  decide

-- Natural scalar action differs from product self-action; no Noetherian claim is made.
private theorem nat_product_scalar_control :
    (1 : ℕ) • ((0, 1) : ℕ × ℕ) = (0, 1) ∧
      ((1, 0) : ℕ × ℕ) * (0, 1) = 0 := by
  decide

private theorem matrix_coefficient_conditions :
    Nontrivial (Matrix (Fin 2) (Fin 2) ℕ) ∧
      Subsingleton (AddUnits (Matrix (Fin 2) (Fin 2) ℕ)) := by
  constructor
  · infer_instance
  · change Subsingleton (AddUnits (Fin 2 → Fin 2 → ℕ))
    infer_instance

private theorem matrix_noncommutative :
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℕ) *
        Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℕ) ≠
      Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℕ) *
        Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℕ) := by
  intro h
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h
  have h10 : (1 : ℕ) = 0 := by
    simpa [Matrix.single] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℕ => M 0 0) h
  exact Nat.one_ne_zero h10

private theorem zero_ring_boundary :
    Subsingleton (ZMod 1) ∧ IsNoetherianRing (Polynomial (ZMod 1)) ∧
      ¬ Nontrivial (ZMod 1) := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro h
  let : Nontrivial (ZMod 1) := h
  exact zero_ne_one (Subsingleton.elim (0 : ZMod 1) 1)

private theorem int_addUnits_not_subsingleton : ¬ Subsingleton (AddUnits ℤ) := by
  intro h
  have h10 : (1 : ℤ) = 0 := by
    simpa using congrArg AddUnits.val (h.elim (toAddUnits (1 : ℤ)) 0)
  exact one_ne_zero h10

-- These clients apply the negative theorem; the fixtures above do not use it.
example {R : Type u} [Semiring R] [Nontrivial R] [Subsingleton (AddUnits R)] :
    ¬ IsNoetherianRing (Polynomial R) :=
  Polynomial.not_isNoetherianRing_of_subsingleton_addUnits

example : ¬ IsNoetherianRing (Polynomial ℕ) :=
  Polynomial.not_isNoetherianRing_of_subsingleton_addUnits

example : ¬ IsNoetherianRing (Polynomial (ℕ × ℕ)) :=
  Polynomial.not_isNoetherianRing_of_subsingleton_addUnits

example : ¬ IsNoetherianRing (Polynomial (Matrix (Fin 2) (Fin 2) ℕ)) := by
  fail_if_success
    have : CommRing (Matrix (Fin 2) (Fin 2) ℕ) := inferInstance
  fail_if_success
    have : CommSemiring (Matrix (Fin 2) (Fin 2) ℕ) := inferInstance
  have := matrix_coefficient_conditions.2
  exact Polynomial.not_isNoetherianRing_of_subsingleton_addUnits

example {σ : Type u} {R : Type v} [CommSemiring R] [Unique σ]
    [Nontrivial R] [Subsingleton (AddUnits R)] :
    ¬ IsNoetherianRing (MvPolynomial σ R) := by
  exact fun h => Polynomial.not_isNoetherianRing_of_subsingleton_addUnits
    (unique_noetherian_transport.mp h)

example {R : Type v} [CommSemiring R] [Nontrivial R] [Subsingleton (AddUnits R)] :
    ¬ IsNoetherianRing (MvPolynomial PUnit.{u + 1} R) := by
  exact fun h => Polynomial.not_isNoetherianRing_of_subsingleton_addUnits
    (pUnit_noetherian_transport.mp h)

end MultivariatePolynomialsTests

#check @Polynomial.not_isNoetherianRing_of_subsingleton_addUnits
#check @MvPolynomial.uniqueAlgEquiv
