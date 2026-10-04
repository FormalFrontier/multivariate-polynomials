/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.PolynomialCoefficientHomogeneity
import Mathlib.Data.ZMod.Basic

set_option warningAsError true

namespace PolynomialCoefficientHomogeneityClient

open MvPolynomial Polynomial

variable {R σ : Type*} [CommSemiring R]

private noncomputable def parameter (bound : ℕ) (indexVar : σ) :
    MvPolynomial (σ × Fin (bound + 1)) R[X] :=
  ∑ index : Fin (bound + 1),
    MvPolynomial.C (Polynomial.X ^ index.val) * MvPolynomial.X (indexVar, index)

private lemma parameter_isHomogeneous (bound : ℕ) (indexVar : σ) :
    (parameter (R := R) bound indexVar).IsHomogeneous 1 := by
  unfold parameter
  apply MvPolynomial.IsHomogeneous.sum Finset.univ _ _
  intro index _
  simpa only [zero_add] using
    (MvPolynomial.isHomogeneous_C (σ × Fin (bound + 1))
      (Polynomial.X ^ index.val : R[X])).mul
      (MvPolynomial.isHomogeneous_X (R := R[X]) (indexVar, index))

private lemma finite_parameter_substitution (bound degree : ℕ)
    (p : MvPolynomial σ R[X]) (hp : p.IsHomogeneous degree) (index : ℕ) :
    ((((MvPolynomial.optionEquivRight R (σ × Fin (bound + 1))).symm.trans
      (MvPolynomial.optionEquivLeft R (σ × Fin (bound + 1))))
      (MvPolynomial.eval₂ MvPolynomial.C (parameter bound) p)).coeff index).IsHomogeneous
      degree := by
  apply MvPolynomial.IsHomogeneous.coeff_polynomial_interchange _ degree
  simpa only [one_mul] using
    hp.eval₂ (MvPolynomial.C : R[X] →+* MvPolynomial (σ × Fin (bound + 1)) R[X])
      (parameter bound) (fun b => MvPolynomial.isHomogeneous_C (σ × Fin (bound + 1)) b)
      (parameter_isHomogeneous bound)

example (bound degree index : ℕ) (p : MvPolynomial σ R[X])
    (hp : p.IsHomogeneous degree) :
    ((((MvPolynomial.optionEquivRight R (σ × Fin (bound + 1))).symm.trans
      (MvPolynomial.optionEquivLeft R (σ × Fin (bound + 1))))
      (MvPolynomial.eval₂ MvPolynomial.C (parameter bound) p)).coeff index).IsHomogeneous
      degree :=
  finite_parameter_substitution bound degree p hp index

example (degree index : ℕ) :
    ((((MvPolynomial.optionEquivRight R σ).symm.trans
      (MvPolynomial.optionEquivLeft R σ)) (0 : MvPolynomial σ R[X])).coeff index).IsHomogeneous
      degree :=
  MvPolynomial.IsHomogeneous.coeff_polynomial_interchange _ degree index
    (MvPolynomial.isHomogeneous_zero (σ := σ) (R := R[X]) degree)

public theorem homogeneousZeroCoefficient (p : MvPolynomial σ R[X])
    (hp : p.IsHomogeneous 0) (index : ℕ) :
    ((((MvPolynomial.optionEquivRight R σ).symm.trans
      (MvPolynomial.optionEquivLeft R σ)) p).coeff index).IsHomogeneous 0 :=
  MvPolynomial.IsHomogeneous.coeff_polynomial_interchange p 0 index hp

example (degree index : ℕ) (p : MvPolynomial σ R[X])
    (hp : p.IsHomogeneous degree) :
    ((((MvPolynomial.optionEquivRight R (σ × Fin 1)).symm.trans
      (MvPolynomial.optionEquivLeft R (σ × Fin 1)))
      (MvPolynomial.eval₂ MvPolynomial.C (parameter 0) p)).coeff index).IsHomogeneous
      degree :=
  finite_parameter_substitution 0 degree p hp index

example (p : MvPolynomial σ (Polynomial (ZMod 1)))
    (degree index : ℕ) (hp : p.IsHomogeneous degree) :
    ((((MvPolynomial.optionEquivRight (ZMod 1) σ).symm.trans
      (MvPolynomial.optionEquivLeft (ZMod 1) σ)) p).coeff index).IsHomogeneous degree :=
  MvPolynomial.IsHomogeneous.coeff_polynomial_interchange p degree index hp

example (p : MvPolynomial σ (Polynomial (ZMod 6)))
    (degree index : ℕ) (hp : p.IsHomogeneous degree) :
    ((((MvPolynomial.optionEquivRight (ZMod 6) σ).symm.trans
      (MvPolynomial.optionEquivLeft (ZMod 6) σ)) p).coeff index).IsHomogeneous degree :=
  MvPolynomial.IsHomogeneous.coeff_polynomial_interchange p degree index hp

end PolynomialCoefficientHomogeneityClient
