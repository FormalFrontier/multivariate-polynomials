module

import MultivariatePolynomials.CoefficientProductResultant

/-!
# A unit criterion for an empty-block coefficient-product Jacobian

A unit mapped inactive constant gives a unit Jacobian determinant at every target
point, for every natural size of the active block.
-/

set_option autoImplicit false

universe u v

example {C : Type u} [CommSemiring C] {R : Type v} [CommRing R]
    (n : ℕ) (g h : Polynomial C) (φ : C →+* R) (a : Fin (0 + n) → R)
    (hg : IsUnit (φ (g.coeff 0))) :
    IsUnit (Matrix.det (fun r s : Fin (0 + n) =>
      MvPolynomial.eval₂Hom φ a
        (MvPolynomial.pderiv s (MvPolynomial.coefficientProduct 0 n g h r)))) := by
  rw [MvPolynomial.det_eval₂Hom_pderiv_coefficientProduct_zero_left_bound]
  exact hg.pow n
