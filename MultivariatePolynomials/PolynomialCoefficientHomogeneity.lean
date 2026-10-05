/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Homogeneity of polynomial coefficients after interchanging variables

The variables indexed by `σ` keep their homogeneous degree when a polynomial
coefficient ring `R[X]` is interchanged with the multivariate polynomial ring.
The polynomial variable has weight zero, and a zero coefficient may carry any
homogeneous label.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Equiv`: `optionEquivRight` and
  `optionEquivLeft` interchange the polynomial parameter with multivariate
  variables; `Mathlib.RingTheory.MvPolynomial.Homogeneous` supplies the labels.
-/

set_option warningAsError true

@[expose] public section

namespace MvPolynomial.IsHomogeneous

open MvPolynomial Polynomial

variable {R σ : Type*} [CommSemiring R]

private noncomputable def interchange (p : MvPolynomial σ R[X]) : (MvPolynomial σ R)[X] :=
  ((optionEquivRight R σ).symm.trans (optionEquivLeft R σ)) p

private lemma interchange_C_C (r : R) :
    interchange (MvPolynomial.C (Polynomial.C r) : MvPolynomial σ R[X]) =
      Polynomial.C (MvPolynomial.C r) := by
  change (optionEquivLeft R σ) ((optionEquivRight R σ).symm (C (Polynomial.C r))) = _
  rw [← optionEquivRight_C R σ r, AlgEquiv.symm_apply_apply, optionEquivLeft_C]

private lemma interchange_C_X :
    interchange (MvPolynomial.C Polynomial.X : MvPolynomial σ R[X]) = Polynomial.X := by
  change (optionEquivLeft R σ) ((optionEquivRight R σ).symm (C Polynomial.X)) = _
  rw [← optionEquivRight_X_none R σ, AlgEquiv.symm_apply_apply, optionEquivLeft_X_none]

private lemma interchange_C (b : R[X]) :
    interchange (MvPolynomial.C b : MvPolynomial σ R[X]) =
      Polynomial.map MvPolynomial.C b := by
  let coefficientHom : R[X] →+* (MvPolynomial σ R)[X] :=
    (((optionEquivRight R σ).symm.trans (optionEquivLeft R σ)).toRingHom).comp
      (MvPolynomial.C : R[X] →+* MvPolynomial σ R[X])
  let mappedHom : R[X] →+* (MvPolynomial σ R)[X] :=
    Polynomial.mapRingHom (MvPolynomial.C : R →+* MvPolynomial σ R)
  have hom_eq : coefficientHom = mappedHom := Polynomial.ringHom_ext
    (fun a => by
      change interchange (MvPolynomial.C (Polynomial.C a)) =
        Polynomial.map MvPolynomial.C (Polynomial.C a)
      simpa only [Polynomial.map_C] using interchange_C_C (σ := σ) a)
    (by
      change interchange (MvPolynomial.C Polynomial.X) =
        Polynomial.map MvPolynomial.C Polynomial.X
      simpa only [Polynomial.map_X] using interchange_C_X (R := R) (σ := σ))
  exact congrArg (fun hom : R[X] →+* (MvPolynomial σ R)[X] => hom b) hom_eq

private lemma interchange_X (i : σ) :
    interchange (MvPolynomial.X i : MvPolynomial σ R[X]) =
      Polynomial.C (MvPolynomial.X i) := by
  change (optionEquivLeft R σ) ((optionEquivRight R σ).symm (X i)) = _
  rw [← optionEquivRight_X_some R σ i, AlgEquiv.symm_apply_apply,
    optionEquivLeft_X_some]

private lemma interchange_monomial (m : σ →₀ ℕ) (b : R[X]) :
    interchange (MvPolynomial.monomial m b) =
      Polynomial.map MvPolynomial.C b * Polynomial.C (MvPolynomial.monomial m (1 : R)) := by
  calc
    interchange (MvPolynomial.monomial m b) =
        interchange (MvPolynomial.C b) *
          ∏ i ∈ m.support, interchange (MvPolynomial.X i) ^ m i := by
      simp only [MvPolynomial.monomial_eq, Finsupp.prod, interchange, map_mul, map_prod,
        map_pow]
    _ = _ := by
      rw [interchange_C]
      simp only [interchange_X, ← map_pow, ← map_prod, MvPolynomial.prod_X_pow_eq_monomial]

private lemma interchange_coeff_monomial (m : σ →₀ ℕ) (b : R[X]) (n : ℕ) :
    (interchange (MvPolynomial.monomial m b)).coeff n =
      MvPolynomial.monomial m (b.coeff n) := by
  simp only [interchange_monomial, Polynomial.coeff_mul_C, Polynomial.coeff_map,
    MvPolynomial.C_mul_monomial, mul_one]

private lemma interchange_coeff_coeff (p : MvPolynomial σ R[X]) (n : ℕ)
    (m : σ →₀ ℕ) :
    ((interchange p).coeff n).coeff m = (p.coeff m).coeff n := by
  induction p using MvPolynomial.induction_on' with
  | monomial exponent b =>
    classical
    simp [interchange_coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs <;> simp
  | add p q hp hq =>
    simpa only [interchange, map_add, Polynomial.coeff_add, AddMonoidAlgebra.coeff_add,
      Finsupp.coe_add, Pi.add_apply] using congrArg₂ (· + ·) hp hq

/-- Taking a coefficient in the polynomial parameter preserves the homogeneous
label in the multivariate variables after the native interchange equivalence. -/
theorem coeff_polynomial_interchange (p : MvPolynomial σ R[X]) (degree index : ℕ)
    (hp : p.IsHomogeneous degree) :
    ((((MvPolynomial.optionEquivRight R σ).symm.trans
      (MvPolynomial.optionEquivLeft R σ)) p).coeff index).IsHomogeneous degree := by
  change ((interchange p).coeff index).IsHomogeneous degree
  intro exponent hcoeff
  apply hp
  intro hzero
  apply hcoeff
  simp only [interchange_coeff_coeff, hzero, Polynomial.coeff_zero]

end MvPolynomial.IsHomogeneous
