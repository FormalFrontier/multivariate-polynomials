/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.LinearCoefficientEvaluation
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Prod

/-! Ordinary-import clients of base-valued linear coefficient evaluation. -/

set_option warningAsError true

namespace LinearCoefficientEvaluationClient

universe u v w

variable {R : Type u} {S : Type v} {V : Type w}
variable [CommSemiring R] [CommSemiring S] [Algebra R S]

private theorem basis_coordinate_client {J : Type*} (basis : Module.Basis J R S) (j : J)
    (F : MvPolynomial V S) (y : V → R) :
    basis.coord j (MvPolynomial.eval (algebraMap R S ∘ y) F) =
      MvPolynomial.eval y (AddMonoidAlgebra.map (basis.coord j).toAddMonoidHom F) :=
  MvPolynomial.eval_addMonoidAlgebraMap_of_linearMap (basis.coord j) F y

private def pairSum : (ℕ × ℕ) →ₗ[ℕ] ℕ :=
  LinearMap.fst ℕ ℕ ℕ + LinearMap.snd ℕ ℕ ℕ

private theorem pairSum_is_not_multiplicative :
    pairSum ((1 : ℕ × ℕ) * 1) ≠ pairSum (1 : ℕ × ℕ) * pairSum (1 : ℕ × ℕ) := by
  decide

private theorem pair_sum_client (F : MvPolynomial V (ℕ × ℕ)) (y : V → ℕ) :
    pairSum (MvPolynomial.eval (algebraMap ℕ (ℕ × ℕ) ∘ y) F) =
      MvPolynomial.eval y (AddMonoidAlgebra.map pairSum.toAddMonoidHom F) :=
  MvPolynomial.eval_addMonoidAlgebraMap_of_linearMap pairSum F y

private theorem zero_map_client (F : MvPolynomial V S) (y : V → R) :
    (0 : S →ₗ[R] R) (MvPolynomial.eval (algebraMap R S ∘ y) F) =
      MvPolynomial.eval y (AddMonoidAlgebra.map (0 : S →ₗ[R] R).toAddMonoidHom F) :=
  MvPolynomial.eval_addMonoidAlgebraMap_of_linearMap 0 F y

private theorem empty_variables_client (F : MvPolynomial Empty S) (y : Empty → R) :
    (0 : S →ₗ[R] R) (MvPolynomial.eval (algebraMap R S ∘ y) F) =
      MvPolynomial.eval y (AddMonoidAlgebra.map (0 : S →ₗ[R] R).toAddMonoidHom F) :=
  MvPolynomial.eval_addMonoidAlgebraMap_of_linearMap 0 F y

end LinearCoefficientEvaluationClient
