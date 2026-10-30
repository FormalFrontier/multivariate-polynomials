/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.Laurent.Noetherian
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.FieldTheory.Finiteness

/-!
# Laurent Noetherianity with noncommutative and zero coefficients

The matrix example uses matrix multiplication, not the pointwise ring structure
on functions. Finite dimensionality over the rationals gives the coefficient
ring's left-Noetherianity by restriction of scalars.
-/

example : IsNoetherianRing (LaurentPolynomial (Matrix (Fin 2) (Fin 2) ℚ)) := by
  let : IsNoetherianRing (Matrix (Fin 2) (Fin 2) ℚ) :=
    isNoetherian_of_tower ℚ
      (inferInstance : IsNoetherian ℚ (Matrix (Fin 2) (Fin 2) ℚ))
  infer_instance

-- No nontriviality hypothesis is needed for the Laurent-ring instance.
example : IsNoetherianRing (LaurentPolynomial (ZMod 1)) := inferInstance
