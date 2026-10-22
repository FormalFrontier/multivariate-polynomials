/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Artinian.Module

/-!
# Matrix coefficients and Artinian polynomial rings

The ring of two-by-two matrices over `ZMod 2` has exactly sixteen elements.
It is Artinian for its regular left self-action, but is not commutative:
the products of the matrix units `E₀₁` and `E₁₀` are `E₀₀` and `E₁₁` in
the two orders, and these differ at entry `(0, 0)`.

The polynomial ring over this coefficient ring is not Artinian for its
regular left self-action. Right multiplication is linear for that action,
and the central variable is right-regular but not a unit. Thus finiteness
and Artinianity of the coefficient ring do not imply polynomial
self-Artinianity, even for noncommutative coefficients.

## References

* Mathlib, `Mathlib.Data.Matrix.Basis` and `Mathlib.Data.Matrix.Mul`:
  matrix units and matrix multiplication.
* Mathlib, `Mathlib.Data.Fintype.BigOperators` and `Mathlib.Data.ZMod.Defs`:
  cardinalities of function spaces and modular coefficient rings.
* Mathlib, `Mathlib.RingTheory.Artinian.Module`: finite Artinian modules
  and units from right-regular elements in left-Artinian semirings.
* Mathlib, `Mathlib.LinearAlgebra.Span.Basic`: the linear map of scalar
  multiples of an element.
* Mathlib, `Mathlib.Algebra.Polynomial.Coeff` and
  `Mathlib.Algebra.Polynomial.Degree.Operations`: regularity and nonunitness
  of the polynomial variable over semirings.
-/

namespace MultivariatePolynomialsTests

/-- Binary two-by-two matrices form a finite nontrivial ring with an Artinian left self-action. -/
private theorem matrix_zmod_two_coefficient_conditions :
    Nonempty (Ring (Matrix (Fin 2) (Fin 2) (ZMod 2))) ∧
      Nonempty (Fintype (Matrix (Fin 2) (Fin 2) (ZMod 2))) ∧
      Nontrivial (Matrix (Fin 2) (Fin 2) (ZMod 2)) ∧
      IsArtinianRing (Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
  let : Nontrivial (ZMod 2) := ZMod.nontrivial_iff.mpr (by decide)
  exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩, inferInstance,
    isArtinian_of_finite (R := Matrix (Fin 2) (Fin 2) (ZMod 2))
      (M := Matrix (Fin 2) (Fin 2) (ZMod 2))⟩

/-- There are exactly sixteen binary two-by-two matrices. -/
private theorem matrix_zmod_two_card :
    Fintype.card (Matrix (Fin 2) (Fin 2) (ZMod 2)) = 16 := by
  change Fintype.card (Fin 2 → Fin 2 → ZMod 2) = 16
  simpa only [Fintype.card_fun, ZMod.card, Fintype.card_fin] using
    (show (2 ^ 2 : ℕ) ^ 2 = 16 by decide)

/-- Multiplying the two off-diagonal matrix units in opposite orders gives the diagonal units. -/
private theorem matrix_zmod_two_unit_products :
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod 2) *
        Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ZMod 2) =
      Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ZMod 2) ∧
      Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ZMod 2) *
        Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod 2) =
      Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ZMod 2) := by
  constructor <;> simp only [Matrix.single_mul_single_same, one_mul]

/-- The two diagonal matrix units differ at entry `(0, 0)`. -/
private theorem matrix_zmod_two_diagonal_units_ne :
    Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ZMod 2) ≠
      Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ZMod 2) := by
  let : Nontrivial (ZMod 2) := ZMod.nontrivial_iff.mpr (by decide)
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod 2) => M 0 0) h
  have h10 : (1 : ZMod 2) = 0 := by
    simp at h00
  exact one_ne_zero h10

/-- The two off-diagonal matrix units do not commute. -/
private theorem matrix_zmod_two_units_do_not_commute :
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod 2) *
        Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ZMod 2) ≠
      Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ZMod 2) *
        Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod 2) := by
  rw [matrix_zmod_two_unit_products.1, matrix_zmod_two_unit_products.2]
  exact matrix_zmod_two_diagonal_units_ne

/-- Right multiplication respects the regular left action of the polynomial ring on itself. -/
private theorem matrix_polynomial_right_multiplication_left_linear
    (a p q : Polynomial (Matrix (Fin 2) (Fin 2) (ZMod 2))) :
    (a • p) * q = a • (p * q) := by
  simpa only [LinearMap.toSpanSingleton_apply, smul_eq_mul] using
    (LinearMap.toSpanSingleton (Polynomial (Matrix (Fin 2) (Fin 2) (ZMod 2)))
      (Polynomial (Matrix (Fin 2) (Fin 2) (ZMod 2))) q).map_smul a p

/-- Polynomials over binary two-by-two matrices are not Artinian for their left self-action. -/
private theorem matrix_polynomial_not_artinian :
    ¬ IsArtinianRing (Polynomial (Matrix (Fin 2) (Fin 2) (ZMod 2))) := by
  let : Nontrivial (Matrix (Fin 2) (Fin 2) (ZMod 2)) :=
    matrix_zmod_two_coefficient_conditions.2.2.1
  intro h
  let : IsArtinianRing (Polynomial (Matrix (Fin 2) (Fin 2) (ZMod 2))) := h
  have hx : IsRightRegular
      (Polynomial.X : Polynomial (Matrix (Fin 2) (Fin 2) (ZMod 2))) :=
    Polynomial.isRegular_X.right
  have hu : IsUnit
      (Polynomial.X : Polynomial (Matrix (Fin 2) (Fin 2) (ZMod 2))) :=
    IsArtinianRing.isUnit_iff_isRightRegular.mpr hx
  exact Polynomial.not_isUnit_X hu

end MultivariatePolynomialsTests
