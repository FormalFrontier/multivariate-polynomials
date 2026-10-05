/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.LocalizedCoordinateQuotient
import Mathlib.Data.ZMod.Basic

/-!
# Localized coordinate quotient clients

The fraction calculations use the evaluation equivalence and its characteristic laws.
The nonzero variable in the unlocalized quotient is proved independently.
The remaining examples exercise zero, unit, zero-ring, zero-divisor, and
nilpotent boundaries without requiring a domain or a field in the general API.

## References

* `MultivariatePolynomials.LocalizedCoordinateQuotient`: the project
  equivalence and its Mathlib polynomial-quotient/localization dependencies.
-/

namespace MultivariatePolynomialsTests.LocalizedCoordinateQuotient

open Polynomial

local notation "Base" => ℚ[X]
local notation "axisIdeal" =>
  (Ideal.span ({C (X : ℚ[X]) * (X : (ℚ[X])[X])} : Set (ℚ[X])[X]))
local notation "axisQuotient" => (Base[X] ⧸ axisIdeal)
local notation "axisCoefficient" =>
  (Ideal.Quotient.mk axisIdeal (C (X : Base)))
local notation "axisVariable" => (Ideal.Quotient.mk axisIdeal (X : Base[X]))
local notation "axisLocalization" => (Localization.Away axisCoefficient)
local notation "coefficientLocalization" => (Localization.Away (X : Base))

private noncomputable def rationalAxesAlgEquiv :
    axisLocalization ≃ₐ[ℚ] coefficientLocalization :=
  (quotientSpanCMulXAwayAlgEquiv (X : Base)).restrictScalars ℚ

private theorem rationalScalar :
    rationalAxesAlgEquiv (algebraMap ℚ axisLocalization 3) =
      algebraMap ℚ coefficientLocalization 3 :=
  rationalAxesAlgEquiv.commutes 3

private theorem mixedRepresentative_nonconstant (coefficient : Base) :
    (C ((X : Base) + 1) + X : Base[X]) ≠ C coefficient := by
  intro heq
  have hcoeff := congrArg (fun polynomial : Base[X] => polynomial.coeff 1) heq
  simp [coeff_add, coeff_one] at hcoeff

private theorem mixedFraction_evaluates :
    quotientSpanCMulXAwayAlgEquiv (X : Base)
        (IsLocalization.mk' axisLocalization
          (Ideal.Quotient.mk axisIdeal (C ((X : Base) + 1) + X))
          (Submonoid.pow axisCoefficient 2)) =
      IsLocalization.mk' coefficientLocalization ((X : Base) + 1)
        (Submonoid.pow (X : Base) 2) := by
  convert quotientSpanCMulXAwayAlgEquiv_mk' (X : Base)
    (C ((X : Base) + 1) + X) 2 using 1
  simp

private theorem mixedFraction_reconstructs :
    (quotientSpanCMulXAwayAlgEquiv (X : Base)).symm
        (IsLocalization.mk' coefficientLocalization ((X : Base) + 1)
          (Submonoid.pow (X : Base) 2)) =
      IsLocalization.mk' axisLocalization
        (Ideal.Quotient.mk axisIdeal (C ((X : Base) + 1)))
        (Submonoid.pow axisCoefficient 2) := by
  convert quotientSpanCMulXAwayAlgEquiv_symm_mk'
    (X : Base) ((X : Base) + 1) 2 using 1

/-- The outer variable remains nonzero in the quotient before localization. -/
public theorem axisVariable_ne_zero : axisVariable ≠ 0 := by
  intro heq
  let testHom : Base[X] →+* Base :=
    eval₂RingHom ((C : ℚ →+* Base).comp (evalRingHom (0 : ℚ))) X
  have hspan : axisIdeal ≤ RingHom.ker testHom := by
    apply Ideal.span_le.mpr
    intro polynomial hmem
    have hgenerator : polynomial = (C (X : Base) * X : Base[X]) := by
      simpa only [Set.mem_singleton_iff] using hmem
    rw [hgenerator]
    simp [testHom, RingHom.mem_ker]
  have hmap : testHom (X : Base[X]) = 0 := by
    exact RingHom.mem_ker.mp (hspan (Ideal.Quotient.eq_zero_iff_mem.mp heq))
  simp [testHom] at hmap

private theorem mixedFraction_roundTrip :
    (quotientSpanCMulXAwayAlgEquiv (X : Base)).symm
        (IsLocalization.mk' coefficientLocalization ((X : Base) + 1)
          (Submonoid.pow (X : Base) 2)) =
      IsLocalization.mk' axisLocalization
        (Ideal.Quotient.mk axisIdeal (C ((X : Base) + 1) + X))
        (Submonoid.pow axisCoefficient 2) := by
  rw [← mixedFraction_evaluates]
  exact (quotientSpanCMulXAwayAlgEquiv (X : Base)).left_inv _

private theorem axisVariable_vanishes :
    quotientSpanCMulXAwayAlgEquiv (X : Base)
        (IsLocalization.mk' axisLocalization axisVariable
          (Submonoid.pow axisCoefficient 1)) = 0 := by
  convert quotientSpanCMulXAwayAlgEquiv_mk' (X : Base) (X : Base[X]) 1 using 1
  simp

private theorem axisCoefficient_inverse :
    quotientSpanCMulXAwayAlgEquiv (X : Base)
        (IsLocalization.Away.invSelf axisCoefficient) =
      IsLocalization.Away.invSelf (X : Base) := by
  exact quotientSpanCMulXAwayAlgEquiv_invSelf (X : Base)

private theorem zeroLocalization : (1 : Localization.Away (0 : ℤ)) = 0 := by
  simpa using
    (IsLocalization.Away.mul_invSelf (S := Localization.Away (0 : ℤ)) (0 : ℤ)).symm

private theorem unitVariableZero :
    Ideal.Quotient.mk (Ideal.span ({C (1 : ℤ) * X} : Set ℤ[X])) (X : ℤ[X]) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have h : (C (1 : ℤ) * X : ℤ[X]) ∈
      Ideal.span ({C (1 : ℤ) * X} : Set ℤ[X]) :=
    Ideal.subset_span (Set.mem_singleton _)
  simpa only [map_one, one_mul] using h

private theorem zeroRingLocalization : (1 : Localization.Away (0 : ZMod 1)) = 0 := by
  simpa using
    (IsLocalization.Away.mul_invSelf (S := Localization.Away (0 : ZMod 1))
      (0 : ZMod 1)).symm

private theorem modSixZeroDivisor :
    (2 : ZMod 6) ≠ 0 ∧ (3 : ZMod 6) ≠ 0 ∧ (2 : ZMod 6) * 3 = 0 := by
  decide

private theorem modSixCoefficient :
    quotientSpanCMulXAwayAlgEquiv (2 : ZMod 6)
        (algebraMap _ _
          (Ideal.Quotient.mk
            (Ideal.span ({C (2 : ZMod 6) * X} : Set (ZMod 6)[X])) (C 3))) =
      algebraMap (ZMod 6) (Localization.Away (2 : ZMod 6)) 3 := by
  simp [quotientSpanCMulXAwayAlgEquiv_mk]

private theorem modFourNilpotent : (2 : ZMod 4) ^ 2 = 0 := by
  decide

private theorem modFourLocalization : (1 : Localization.Away (2 : ZMod 4)) = 0 := by
  have hmap : (algebraMap (ZMod 4) (Localization.Away (2 : ZMod 4)) 2) ^ 2 = 0 := by
    rw [← map_pow, modFourNilpotent, map_zero]
  have hunit :=
    IsLocalization.Away.mul_invSelf (S := Localization.Away (2 : ZMod 4)) (2 : ZMod 4)
  have hunit2 := congrArg (fun z : Localization.Away (2 : ZMod 4) => z ^ 2) hunit
  simp only [mul_pow, hmap, zero_mul, one_pow] at hunit2
  exact hunit2.symm

end MultivariatePolynomialsTests.LocalizedCoordinateQuotient
