/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.HomogeneousEvaluation

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
