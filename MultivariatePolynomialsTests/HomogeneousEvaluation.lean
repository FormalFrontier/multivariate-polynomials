/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.HomogeneousEvaluation
public import MultivariatePolynomials.GradeZero

/-!
# Homogeneous-evaluation clients

These examples instantiate the weighted and ordinary scaling laws and evaluate
arithmetic in the degree-zero homogeneous component.

## References

* `MultivariatePolynomials.HomogeneousEvaluation`: the scaling theorems and
  their Mathlib homogeneous-polynomial dependencies.
* `MultivariatePolynomials.GradeZero`: the coefficient algebra equivalence.
-/

set_option warningAsError true

@[expose] public section

namespace HomogeneousEvaluationClient

variable {ι B R : Type*} [CommSemiring B] [CommSemiring R]

example (w : ι → ℕ) (d : ℕ) (p : MvPolynomial ι B)
    (hp : p.IsWeightedHomogeneous w d) (σ : B →+* R) (v : ι → R) (a : R) :
    MvPolynomial.eval₂Hom σ (fun i => a ^ w i * v i) p =
      a ^ d * MvPolynomial.eval₂Hom σ v p :=
  hp.eval₂Hom_scaleVariables w d p σ v a

example (d : ℕ) (p : MvPolynomial ι B) (hp : p.IsHomogeneous d)
    (σ : B →+* R) (v : ι → R) (a : R) :
    MvPolynomial.eval₂Hom σ (fun i => a * v i) p =
      a ^ d * MvPolynomial.eval₂Hom σ v p :=
  hp.eval₂Hom_mul_left d p σ v a

example (w : ι → ℕ) (d : ℕ) (σ : B →+* R) (v : ι → R) (a : R) :
    MvPolynomial.eval₂Hom σ (fun i => a ^ w i * v i) (0 : MvPolynomial ι B) =
      a ^ d * MvPolynomial.eval₂Hom σ v 0 :=
  (MvPolynomial.isWeightedHomogeneous_zero B w d).eval₂Hom_scaleVariables
    w d 0 σ v a

end HomogeneousEvaluationClient

namespace GradeZeroClient

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

example (p : MvPolynomial.homogeneousSubmodule (Fin 2) K 0)
    (a : K) (v : Fin 2 → K) :
    MvPolynomial.eval v
      ((p * MvPolynomial.gradeZeroAlgEquiv (Fin 2) K a + 1 :
        MvPolynomial.homogeneousSubmodule (Fin 2) K 0) : MvPolynomial (Fin 2) K) =
      (MvPolynomial.gradeZeroAlgEquiv (Fin 2) K).symm p * a + 1 := by
  -- Component arithmetic, coefficient recovery, and evaluation.
  have hp : (p : MvPolynomial (Fin 2) K) =
      MvPolynomial.C ((MvPolynomial.gradeZeroAlgEquiv (Fin 2) K).symm p) := by
    simpa only [MvPolynomial.coe_gradeZeroAlgEquiv] using
      (congrArg (fun q : MvPolynomial.homogeneousSubmodule (Fin 2) K 0 =>
        (q : MvPolynomial (Fin 2) K))
        ((MvPolynomial.gradeZeroAlgEquiv (Fin 2) K).apply_symm_apply p)).symm
  simp only [Submodule.coe_add, SetLike.GradeZero.coe_mul,
    SetLike.GradeZero.coe_one, MvPolynomial.coe_gradeZeroAlgEquiv,
    hp, map_add, map_mul, map_one, MvPolynomial.eval_C]

example {R : Type*} [CommSemiring R] (r : R) :
    MvPolynomial.constantCoeff
      (algebraMap (MvPolynomial.homogeneousSubmodule Empty R 0)
        (MvPolynomial Empty R) (MvPolynomial.gradeZeroAlgEquiv Empty R r)) = r := by
  -- Empty-variable boundary with the original component-to-polynomial algebra map.
  simp only [SetLike.GradeZero.algebraMap_apply,
    MvPolynomial.coe_gradeZeroAlgEquiv, MvPolynomial.constantCoeff_C]

end GradeZeroClient
