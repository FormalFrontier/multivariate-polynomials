/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Basic.NNReal.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Basic

/-!
# Trivial and nonnegative-real polynomial Artinian examples

These examples concern the canonical left self-action: the scalars and the module
in `IsArtinianRing (Polynomial R)` are both `Polynomial R`, rather than the
coefficient semiring `R` acting on polynomials.

Trivial coefficient semirings give Artinian polynomial semirings in every
coefficient universe. The concrete coefficient ring `ZMod 1` satisfies `0 = 1`.

The nonnegative reals have an infinite carrier but only finitely many ideals.
Their division semiring structure makes the coefficient self-module Artinian,
even though their usual addition has no inverse for `1`. Their univariate
polynomial semiring is not Artinian: its regular variable cannot be a unit.

## References

* Mathlib, `Mathlib.Algebra.Polynomial.Basic`: polynomial semirings with
  subsingleton coefficients.
* Mathlib, `Mathlib.Algebra.Polynomial.Coeff` and
  `Mathlib.Algebra.Polynomial.Degree.Operations`: regularity and noninvertibility
  of the polynomial variable.
* Mathlib, `Mathlib.RingTheory.Artinian.Module`: finite and trivial Artinian
  self-modules, division semirings, and units in Artinian semirings.
* Mathlib, `Mathlib.Basic.NNReal.Defs`, `Mathlib.Algebra.CharZero.Infinite`, and
  `Mathlib.RingTheory.Ideal.Basic`: the nonnegative real semifield, infinite
  characteristic-zero carriers, and finite ideal types of division semirings.
* Mathlib, `Mathlib.Data.ZMod.Defs`: the trivial modular coefficient ring.
-/

universe u

open scoped NNReal

namespace MultivariatePolynomialsTests

/-- Subsingleton coefficients make the polynomial self-module Artinian,
without requiring commutative multiplication or additive inverses. -/
private theorem subsingleton_coefficient_polynomial_artinian
    {R : Type u} [Semiring R] [Subsingleton R] :
    IsArtinianRing (Polynomial R) := by
  exact Ring.isArtinian_of_zero_eq_one (Subsingleton.elim _ _)

/-- The modular ring with modulus one is a zero coefficient ring, and its
polynomial semiring is Artinian by the finite-carrier lemma. -/
private theorem zmod_one_univariate_polynomial_artinian :
    (0 : ZMod 1) = 1 ∧ IsArtinianRing (Polynomial (ZMod 1)) := by
  exact ⟨Subsingleton.elim _ _,
    isArtinian_of_finite (R := Polynomial (ZMod 1)) (M := Polynomial (ZMod 1))⟩

/-- The nonnegative reals are infinite, but their ideal type is finite and
their left self-module is Artinian. -/
private theorem nnreal_infinite_artinian_coefficients :
    Infinite ℝ≥0 ∧ Finite (Ideal ℝ≥0) ∧ IsArtinianRing ℝ≥0 := by
  exact ⟨CharZero.infinite ℝ≥0, inferInstance, DivisionSemiring.instIsArtinianRing⟩

/-- The usual nonnegative-real addition has no additive inverse for one. -/
private theorem nnreal_no_additive_inverse_of_one :
    ¬ ∃ b : ℝ≥0, 1 + b = 0 := by
  rintro ⟨b, hb⟩
  have hle : (1 : ℝ≥0) ≤ 0 := by
    simpa only [hb] using (le_self_add : (1 : ℝ≥0) ≤ 1 + b)
  exact not_le_of_gt (show (0 : ℝ≥0) < 1 from zero_lt_one) hle

/-- The univariate polynomial semiring over the nonnegative reals is not
Artinian for its left self-action, despite Artinian coefficients. -/
private theorem nnreal_univariate_polynomial_not_artinian :
    ¬ IsArtinianRing (Polynomial ℝ≥0) := by
  intro h
  let : IsArtinianRing (Polynomial ℝ≥0) := h
  have hx : IsUnit (Polynomial.X : Polynomial ℝ≥0) :=
    IsArtinianRing.isUnit_iff_isRegular.mpr Polynomial.isRegular_X
  exact Polynomial.not_isUnit_X hx

end MultivariatePolynomialsTests
