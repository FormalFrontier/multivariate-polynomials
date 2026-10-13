/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials.Noetherian
import MultivariatePolynomials.Artinian
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Algebra.GroupWithZero.Regular
import Mathlib.Basic.NNReal.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Polynomial coefficient modules

The canonical coefficient action differs from polynomial multiplication as a
self-module. Trivial coefficients give both finiteness conditions. Rational,
natural, nonnegative real and matrix coefficients give independent Noetherian
and Artinian obstructions for the coefficient module.

The Noetherian obstructions use the polynomial finite-generation obstruction.
The Artinian obstructions use injectivity of right multiplication by the variable
and its failure to reach the constant polynomial one. Nonnegative reals have an
infinite carrier but only two ideals. Matrix coefficients have row-by-column
multiplication and need not commute.

## References

* Mathlib's polynomial coefficient, regular-variable and finite-generation APIs;
  its Noetherian finite-module and Artinian endomorphism theorems.
* Mathlib's Frobenius-number proof for natural coefficients, division-semiring
  ideal classification, matrix-unit and cardinality APIs.
* `MultivariatePolynomials.Noetherian`: the noncommutative Hilbert basis theorem
  and the polynomial obstruction for trivial additive units.
-/

@[expose] public section

open scoped NNReal

universe u

namespace MultivariatePolynomialsTests.PolynomialCoefficientModules

private theorem coefficient_left_action {R : Type u} [Semiring R]
    (r : R) (p : Polynomial R) : r • p = Polynomial.C r * p :=
  (Polynomial.C_mul' r p).symm

private theorem zero_coefficient_collapse :
    Subsingleton (ZMod 1) ∧ Nonempty (ZMod 1) ∧ (1 : ZMod 1) = 0 := by
  exact ⟨ZMod.subsingleton_iff.mpr rfl, ⟨0⟩, Subsingleton.elim _ _⟩

private theorem zero_polynomial_collapse :
    (∀ p : Polynomial (ZMod 1), p = 0) ∧
      (Polynomial.X : Polynomial (ZMod 1)) = 0 ∧
      (1 : Polynomial (ZMod 1)) = 0 := by
  exact ⟨fun p => Subsingleton.elim p 0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

private theorem zero_coefficient_module_conditions :
    IsNoetherian (ZMod 1) (Polynomial (ZMod 1)) ∧
      IsArtinian (ZMod 1) (Polynomial (ZMod 1)) := by
  exact ⟨isNoetherian_of_subsingleton (ZMod 1) (Polynomial (ZMod 1)),
    isArtinian_of_finite⟩

private theorem rational_self_conditions :
    IsNoetherianRing ℚ ∧ IsArtinianRing ℚ ∧
      IsNoetherianRing (Polynomial ℚ) ∧ Infinite (Polynomial ℚ) := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

private theorem rational_coefficient_not_noetherian :
    ¬ IsNoetherian ℚ (Polynomial ℚ) := by
  intro h
  let : IsNoetherian ℚ (Polynomial ℚ) := h
  exact Polynomial.not_finite (inferInstance : Module.Finite ℚ (Polynomial ℚ))

private theorem rational_coefficient_not_artinian :
    ¬ IsArtinian ℚ (Polynomial ℚ) := by
  intro h
  let : IsArtinian ℚ (Polynomial ℚ) := h
  have hinj : Function.Injective (LinearMap.mulRight ℚ (Polynomial.X : Polynomial ℚ)) :=
    Polynomial.isRegular_X.right
  obtain ⟨p, hp⟩ := IsArtinian.surjective_of_injective_endomorphism
    (LinearMap.mulRight ℚ (Polynomial.X : Polynomial ℚ)) hinj (1 : Polynomial ℚ)
  have h01 : (0 : ℚ) = 1 := by
    simpa only [LinearMap.mulRight_apply, Polynomial.coeff_mul_X_zero,
      Polynomial.coeff_one_zero] using congrArg (fun q : Polynomial ℚ => q.coeff 0) hp
  exact zero_ne_one h01

private theorem natural_self_noetherian : IsNoetherianRing ℕ := by
  infer_instance

private theorem natural_one_has_no_additive_inverse : ¬ ∃ n : ℕ, 1 + n = 0 := by
  rintro ⟨n, hn⟩
  exact Nat.succ_ne_zero n (by simpa only [Nat.add_comm] using hn)

private theorem natural_self_not_artinian : ¬ IsArtinianRing ℕ := by
  intro h
  let : IsArtinianRing ℕ := h
  have htwo : IsUnit (2 : ℕ) := IsArtinianRing.isUnit_iff_isRightRegular.mpr
    (IsRegular.of_ne_zero (by decide : (2 : ℕ) ≠ 0)).right
  have h21 : (2 : ℕ) = 1 := Nat.isUnit_iff.mp htwo
  exact (by decide : (2 : ℕ) ≠ 1) h21

private theorem natural_polynomial_self_not_noetherian :
    ¬ IsNoetherianRing (Polynomial ℕ) := by
  exact Polynomial.not_isNoetherianRing_of_subsingleton_addUnits

private theorem natural_coefficient_not_noetherian :
    ¬ IsNoetherian ℕ (Polynomial ℕ) := by
  intro h
  let : IsNoetherian ℕ (Polynomial ℕ) := h
  exact Polynomial.not_finite (inferInstance : Module.Finite ℕ (Polynomial ℕ))

private theorem natural_coefficient_not_artinian :
    ¬ IsArtinian ℕ (Polynomial ℕ) := by
  intro h
  let : IsArtinian ℕ (Polynomial ℕ) := h
  have hinj : Function.Injective (LinearMap.mulRight ℕ (Polynomial.X : Polynomial ℕ)) :=
    Polynomial.isRegular_X.right
  obtain ⟨p, hp⟩ := IsArtinian.surjective_of_injective_endomorphism
    (LinearMap.mulRight ℕ (Polynomial.X : Polynomial ℕ)) hinj (1 : Polynomial ℕ)
  have h01 : (0 : ℕ) = 1 := by
    simpa only [LinearMap.mulRight_apply, Polynomial.coeff_mul_X_zero,
      Polynomial.coeff_one_zero] using congrArg (fun q : Polynomial ℕ => q.coeff 0) hp
  exact zero_ne_one h01

private theorem nnreal_infinite : Infinite ℝ≥0 := by
  exact CharZero.infinite ℝ≥0

private theorem nnreal_one_has_no_additive_inverse : ¬ ∃ r : ℝ≥0, 1 + r = 0 := by
  rintro ⟨r, hr⟩
  have hpos : (0 : ℝ≥0) < 1 + r :=
    lt_of_lt_of_le zero_lt_one (le_self_add : (1 : ℝ≥0) ≤ 1 + r)
  exact (ne_of_gt hpos) hr

private theorem nnreal_ideal_and_self_conditions :
    Finite (Ideal ℝ≥0) ∧ IsNoetherianRing ℝ≥0 ∧ IsArtinianRing ℝ≥0 := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem nnreal_coefficient_not_noetherian :
    ¬ IsNoetherian ℝ≥0 (Polynomial ℝ≥0) := by
  intro h
  let : IsNoetherian ℝ≥0 (Polynomial ℝ≥0) := h
  exact Polynomial.not_finite (inferInstance : Module.Finite ℝ≥0 (Polynomial ℝ≥0))

private theorem nnreal_coefficient_not_artinian :
    ¬ IsArtinian ℝ≥0 (Polynomial ℝ≥0) := by
  intro h
  let : IsArtinian ℝ≥0 (Polynomial ℝ≥0) := h
  have hinj : Function.Injective (LinearMap.mulRight ℝ≥0 (Polynomial.X : Polynomial ℝ≥0)) :=
    Polynomial.isRegular_X.right
  obtain ⟨p, hp⟩ := IsArtinian.surjective_of_injective_endomorphism
    (LinearMap.mulRight ℝ≥0 (Polynomial.X : Polynomial ℝ≥0)) hinj (1 : Polynomial ℝ≥0)
  have h01 : (0 : ℝ≥0) = 1 := by
    simpa only [LinearMap.mulRight_apply, Polynomial.coeff_mul_X_zero,
      Polynomial.coeff_one_zero] using congrArg (fun q : Polynomial ℝ≥0 => q.coeff 0) hp
  exact zero_ne_one h01

private abbrev M2 := Matrix (Fin 2) (Fin 2) (ZMod 2)

private theorem matrix_card : Fintype.card M2 = 16 := by
  calc
    Fintype.card M2 = Fintype.card (Fin 2 → Fin 2 → ZMod 2) :=
      Fintype.card_congr (Matrix.of (m := Fin 2) (n := Fin 2) (α := ZMod 2)).symm
    _ = (2 ^ 2) ^ 2 := by rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    _ = 16 := by decide

private theorem matrix_self_conditions :
    Finite M2 ∧ IsNoetherianRing M2 ∧ IsArtinianRing M2 := by
  exact ⟨inferInstance, isNoetherian_of_finite M2 M2,
    isArtinian_of_finite (R := M2) (M := M2)⟩

private theorem matrix_polynomial_self_noetherian : IsNoetherianRing (Polynomial M2) := by
  let : IsNoetherianRing M2 := isNoetherian_of_finite M2 M2
  exact Polynomial.isNoetherianRing_of_isNoetherianRing

private theorem matrix_row_multiplication (A B : M2) (i j : Fin 2) :
    (A * B) i j = ∑ k : Fin 2, A i k * B k j := by
  exact Matrix.mul_apply

private theorem matrix_elementary_products :
    (Matrix.single 0 1 1 : M2) * Matrix.single 1 0 1 = Matrix.single 0 0 1 ∧
      (Matrix.single 1 0 1 : M2) * Matrix.single 0 1 1 = Matrix.single 1 1 1 := by
  constructor <;> simp only [Matrix.single_mul_single_same, one_mul]

private theorem matrix_elementary_noncommuting :
    (Matrix.single 0 1 1 : M2) * Matrix.single 1 0 1 ≠
      (Matrix.single 1 0 1 : M2) * Matrix.single 0 1 1 := by
  intro h
  rw [matrix_elementary_products.1, matrix_elementary_products.2] at h
  have h10 : (1 : ZMod 2) = 0 := by
    simpa [Matrix.single] using congrArg (fun A : M2 => A 0 0) h
  exact one_ne_zero h10

private theorem matrix_coefficient_left_action (r : M2) (p : Polynomial M2) :
    r • p = Polynomial.C r * p := by
  exact (Polynomial.C_mul' r p).symm

private theorem matrix_coefficient_not_noetherian :
    ¬ IsNoetherian M2 (Polynomial M2) := by
  intro h
  let : IsNoetherian M2 (Polynomial M2) := h
  exact Polynomial.not_finite (inferInstance : Module.Finite M2 (Polynomial M2))

private theorem matrix_coefficient_not_artinian :
    ¬ IsArtinian M2 (Polynomial M2) := by
  intro h
  let : IsArtinian M2 (Polynomial M2) := h
  have hinj : Function.Injective (LinearMap.mulRight M2 (Polynomial.X : Polynomial M2)) :=
    Polynomial.isRegular_X.right
  obtain ⟨p, hp⟩ := IsArtinian.surjective_of_injective_endomorphism
    (LinearMap.mulRight M2 (Polynomial.X : Polynomial M2)) hinj (1 : Polynomial M2)
  have h01 : (0 : M2) = 1 := by
    simpa only [LinearMap.mulRight_apply, Polynomial.coeff_mul_X_zero,
      Polynomial.coeff_one_zero] using congrArg (fun q : Polynomial M2 => q.coeff 0) hp
  exact zero_ne_one h01

end MultivariatePolynomialsTests.PolynomialCoefficientModules

namespace MultivariatePolynomialsTests.PolynomialCoefficientModules

private theorem zero_coefficient_noetherian :
    IsNoetherian (ZMod 1) (Polynomial (ZMod 1)) := by
  exact (Polynomial.isNoetherian_iff (ZMod 1)).mpr inferInstance

private theorem zero_coefficient_artinian :
    IsArtinian (ZMod 1) (Polynomial (ZMod 1)) := by
  exact (Polynomial.isArtinian_iff (ZMod 1)).mpr inferInstance

private theorem nnreal_coefficient_noetherian_obstruction :
    ¬ IsNoetherian ℝ≥0 (Polynomial ℝ≥0) := by
  intro h
  exact not_subsingleton ℝ≥0 ((Polynomial.isNoetherian_iff ℝ≥0).mp h)

private theorem matrix_coefficient_artinian_obstruction :
    ¬ IsArtinian M2 (Polynomial M2) := by
  intro h
  exact not_subsingleton M2 ((Polynomial.isArtinian_iff M2).mp h)

end MultivariatePolynomialsTests.PolynomialCoefficientModules
