/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Regular
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Ring.ULift
import Mathlib.Basic.NNReal.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.RingTheory.Artinian.Module

/-!
# Artinian polynomial rings and their boundaries

These examples use the regular left action: in `IsArtinianRing S`, the
scalars and the module are both `S`, and scalar multiplication is ring
multiplication. In particular, polynomial self-Artinianity is not Artinianity
as a module over the coefficient semiring.

Zero coefficients give Artinian polynomial rings for arbitrary variable
types. Empty variables reflect the coefficient Artinian condition through
the empty-variable equivalence. Over the field `ZMod 2`, even one variable
prevents self-Artinianity, as do infinitely many variables. The same
obstruction applies to the finite Artinian ring `ZMod 4`, with a nonzero
nilpotent, and to `ZMod 2 × ZMod 2`, with nonzero zero divisors.

The nonnegative real numbers form an Artinian division semiring without
additive inverses. Their polynomial semiring is Artinian with empty variables
but not with a single variable. The natural numbers give another commutative
semiring without additive inverses: they are Noetherian but not Artinian,
and their polynomial semirings fail to be Artinian both with empty variables
and with a single variable. Lifted examples allow the variable and coefficient
universes to vary independently.

## References

* Mathlib, `Mathlib.RingTheory.Artinian.Module`: finite Artinian modules,
  transport along ring equivalences, and regular elements of Artinian semirings.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Basic` and
  `Mathlib.Algebra.MvPolynomial.Equiv`: regular variables, constant coefficients,
  and the empty-variable equivalence.
* Mathlib, `Mathlib.Algebra.Field.ZMod` and `Mathlib.Data.ZMod.Basic`:
  modular coefficient rings and their field structure.
* Mathlib, `Mathlib.Basic.NNReal.Defs`: the nonnegative real semifield.
* Mathlib, `Mathlib.NumberTheory.FrobeniusNumber`: Noetherianity of `ℕ`.
-/

universe u v

open scoped NNReal

namespace MultivariatePolynomialsTests

private theorem zmod_one_coefficient_conditions :
    Nonempty (CommRing (ZMod 1)) ∧ Subsingleton (ZMod 1) ∧
      IsArtinianRing (ZMod 1) := by
  exact ⟨⟨inferInstance⟩, inferInstance,
    isArtinian_of_finite (R := ZMod 1) (M := ZMod 1)⟩

private theorem zmod_one_polynomial_artinian {σ : Type u} :
    Subsingleton (MvPolynomial σ (ZMod 1)) ∧
      IsArtinianRing (MvPolynomial σ (ZMod 1)) := by
  exact ⟨inferInstance,
    isArtinian_of_finite (R := MvPolynomial σ (ZMod 1))
      (M := MvPolynomial σ (ZMod 1))⟩

private theorem zmod_one_variable_eq_zero {σ : Type u} (i : σ) :
    (MvPolynomial.X i : MvPolynomial σ (ZMod 1)) = 0 := by
  exact Subsingleton.elim _ _

-- The ring equivalence transports both the scalar semiring and its self-module.
private theorem empty_variable_artinian_reflection {σ : Type u} {R : Type v}
    [CommSemiring R] [IsEmpty σ] :
    IsArtinianRing (MvPolynomial σ R) ↔ IsArtinianRing R := by
  constructor
  · intro h
    let : IsArtinianRing (MvPolynomial σ R) := h
    exact (MvPolynomial.isEmptyAlgEquiv R σ).toRingEquiv.isArtinianRing
  · intro h
    let : IsArtinianRing R := h
    exact (MvPolynomial.isEmptyAlgEquiv R σ).toRingEquiv.symm.isArtinianRing

private theorem zmod_two_field_conditions :
    Nonempty (Field (ZMod 2)) ∧ Nontrivial (ZMod 2) ∧
      IsArtinianRing (ZMod 2) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact ⟨⟨inferInstance⟩, inferInstance, inferInstance⟩

private theorem empty_zmod_two_polynomial_artinian :
    IsArtinianRing (MvPolynomial Empty (ZMod 2)) := by
  let : IsArtinianRing (ZMod 2) := zmod_two_field_conditions.2.2
  exact (MvPolynomial.isEmptyRingEquiv (ZMod 2) Empty).symm.isArtinianRing

-- A unit variable would have a unit constant coefficient, although that coefficient is zero.
private theorem singleton_zmod_two_polynomial_not_artinian :
    ¬ IsArtinianRing (MvPolynomial PUnit (ZMod 2)) := by
  intro h
  let : Nontrivial (ZMod 2) := zmod_two_field_conditions.2.1
  let : IsArtinianRing (MvPolynomial PUnit (ZMod 2)) := h
  have hx : IsUnit (MvPolynomial.X PUnit.unit : MvPolynomial PUnit (ZMod 2)) :=
    IsArtinianRing.isUnit_iff_isRegular.mpr MvPolynomial.isRegular_X
  have hz : IsUnit (0 : ZMod 2) := by
    simpa only [MvPolynomial.constantCoeff_X] using
      hx.map (MvPolynomial.constantCoeff : MvPolynomial PUnit (ZMod 2) →+* ZMod 2)
  exact not_isUnit_zero hz

private theorem infinite_zmod_two_polynomial_not_artinian :
    ¬ IsArtinianRing (MvPolynomial ℕ (ZMod 2)) := by
  intro h
  let : Nontrivial (ZMod 2) := zmod_two_field_conditions.2.1
  let : IsArtinianRing (MvPolynomial ℕ (ZMod 2)) := h
  have hx : IsUnit (MvPolynomial.X 0 : MvPolynomial ℕ (ZMod 2)) :=
    IsArtinianRing.isUnit_iff_isRegular.mpr MvPolynomial.isRegular_X
  have hz : IsUnit (0 : ZMod 2) := by
    simpa only [MvPolynomial.constantCoeff_X] using
      hx.map (MvPolynomial.constantCoeff : MvPolynomial ℕ (ZMod 2) →+* ZMod 2)
  exact not_isUnit_zero hz

-- Finite-carrier Artinianity is a lemma, not a global finite-ring instance.
private theorem zmod_four_coefficient_conditions :
    Nonempty (CommRing (ZMod 4)) ∧ Finite (ZMod 4) ∧
      Nontrivial (ZMod 4) ∧ IsArtinianRing (ZMod 4) := by
  exact ⟨⟨inferInstance⟩, inferInstance, ZMod.nontrivial_iff.mpr (by decide),
    isArtinian_of_finite (R := ZMod 4) (M := ZMod 4)⟩

private theorem zmod_four_nonzero_nilpotent :
    (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by
  decide

private theorem empty_zmod_four_polynomial_artinian :
    IsArtinianRing (MvPolynomial Empty (ZMod 4)) := by
  let : IsArtinianRing (ZMod 4) := zmod_four_coefficient_conditions.2.2.2
  exact (MvPolynomial.isEmptyRingEquiv (ZMod 4) Empty).symm.isArtinianRing

private theorem singleton_zmod_four_polynomial_not_artinian :
    ¬ IsArtinianRing (MvPolynomial PUnit (ZMod 4)) := by
  intro h
  let : Nontrivial (ZMod 4) := zmod_four_coefficient_conditions.2.2.1
  let : IsArtinianRing (MvPolynomial PUnit (ZMod 4)) := h
  have hx : IsUnit (MvPolynomial.X PUnit.unit : MvPolynomial PUnit (ZMod 4)) :=
    IsArtinianRing.isUnit_iff_isRegular.mpr MvPolynomial.isRegular_X
  have hz : IsUnit (0 : ZMod 4) := by
    simpa only [MvPolynomial.constantCoeff_X] using
      hx.map (MvPolynomial.constantCoeff : MvPolynomial PUnit (ZMod 4) →+* ZMod 4)
  exact not_isUnit_zero hz

private theorem product_coefficient_conditions :
    Nonempty (CommRing (ZMod 2 × ZMod 2)) ∧ Finite (ZMod 2 × ZMod 2) ∧
      Nontrivial (ZMod 2 × ZMod 2) ∧ IsArtinianRing (ZMod 2 × ZMod 2) := by
  let : Nontrivial (ZMod 2) := zmod_two_field_conditions.2.1
  exact ⟨⟨inferInstance⟩, inferInstance, inferInstance,
    isArtinian_of_finite (R := ZMod 2 × ZMod 2) (M := ZMod 2 × ZMod 2)⟩

private theorem product_nonzero_zero_divisors :
    ((1, 0) : ZMod 2 × ZMod 2) ≠ 0 ∧ ((0, 1) : ZMod 2 × ZMod 2) ≠ 0 ∧
      ((1, 0) : ZMod 2 × ZMod 2) * (0, 1) = 0 := by
  decide

private theorem empty_product_polynomial_artinian :
    IsArtinianRing (MvPolynomial Empty (ZMod 2 × ZMod 2)) := by
  let : IsArtinianRing (ZMod 2 × ZMod 2) := product_coefficient_conditions.2.2.2
  exact (MvPolynomial.isEmptyRingEquiv (ZMod 2 × ZMod 2) Empty).symm.isArtinianRing

private theorem singleton_product_polynomial_not_artinian :
    ¬ IsArtinianRing (MvPolynomial PUnit (ZMod 2 × ZMod 2)) := by
  intro h
  let : Nontrivial (ZMod 2 × ZMod 2) := product_coefficient_conditions.2.2.1
  let : IsArtinianRing (MvPolynomial PUnit (ZMod 2 × ZMod 2)) := h
  have hx : IsUnit
      (MvPolynomial.X PUnit.unit : MvPolynomial PUnit (ZMod 2 × ZMod 2)) :=
    IsArtinianRing.isUnit_iff_isRegular.mpr MvPolynomial.isRegular_X
  have hz : IsUnit (0 : ZMod 2 × ZMod 2) := by
    simpa only [MvPolynomial.constantCoeff_X] using
      hx.map (MvPolynomial.constantCoeff :
        MvPolynomial PUnit (ZMod 2 × ZMod 2) →+* ZMod 2 × ZMod 2)
  exact not_isUnit_zero hz

-- A division semiring has only two ideals, even when its carrier is infinite.
private theorem nnreal_coefficient_conditions :
    Nonempty (CommSemiring ℝ≥0) ∧ Nontrivial ℝ≥0 ∧ IsArtinianRing ℝ≥0 := by
  exact ⟨⟨inferInstance⟩, inferInstance, inferInstance⟩

private theorem nnreal_one_has_no_additive_inverse :
    ¬ (∃ r : ℝ≥0, 1 + r = 0) := by
  rintro ⟨r, hr⟩
  have hle : (1 : ℝ≥0) ≤ 0 := by
    simpa only [hr] using (le_self_add : (1 : ℝ≥0) ≤ 1 + r)
  exact one_ne_zero (le_antisymm hle zero_le)

private theorem empty_nnreal_polynomial_artinian :
    IsArtinianRing (MvPolynomial Empty ℝ≥0) := by
  let : IsArtinianRing ℝ≥0 := nnreal_coefficient_conditions.2.2
  exact (MvPolynomial.isEmptyRingEquiv ℝ≥0 Empty).symm.isArtinianRing

private theorem singleton_nnreal_polynomial_not_artinian :
    ¬ IsArtinianRing (MvPolynomial PUnit ℝ≥0) := by
  intro h
  let : IsArtinianRing (MvPolynomial PUnit ℝ≥0) := h
  have hx : IsUnit (MvPolynomial.X PUnit.unit : MvPolynomial PUnit ℝ≥0) :=
    IsArtinianRing.isUnit_iff_isRegular.mpr MvPolynomial.isRegular_X
  have hz : IsUnit (0 : ℝ≥0) := by
    simpa only [MvPolynomial.constantCoeff_X] using
      hx.map (MvPolynomial.constantCoeff : MvPolynomial PUnit ℝ≥0 →+* ℝ≥0)
  exact not_isUnit_zero hz

-- The usual addition on ℕ has no inverse for 1; no ring structure is substituted.
private theorem nat_semiring_conditions :
    Nonempty (CommSemiring ℕ) ∧ Nontrivial ℕ ∧ IsNoetherianRing ℕ ∧
      ¬ (∃ n : ℕ, 1 + n = 0) := by
  refine ⟨⟨inferInstance⟩, inferInstance, inferInstance, ?_⟩
  rintro ⟨n, hn⟩
  exact Nat.succ_ne_zero n (by simpa only [Nat.add_comm] using hn)

private theorem nat_not_artinian : ¬ IsArtinianRing ℕ := by
  intro h
  let : IsArtinianRing ℕ := h
  have htwo : IsUnit (2 : ℕ) :=
    IsArtinianRing.isUnit_iff_isRegular.mpr (IsRegular.of_ne_zero (by decide))
  exact (show (2 : ℕ) ≠ 1 by decide) (Nat.isUnit_iff.mp htwo)

private theorem empty_nat_polynomial_not_artinian :
    ¬ IsArtinianRing (MvPolynomial Empty ℕ) := by
  intro h
  let : IsArtinianRing (MvPolynomial Empty ℕ) := h
  exact nat_not_artinian
    (MvPolynomial.isEmptyAlgEquiv ℕ Empty).toRingEquiv.isArtinianRing

private theorem singleton_nat_polynomial_not_artinian :
    ¬ IsArtinianRing (MvPolynomial PUnit ℕ) := by
  intro h
  let : IsArtinianRing (MvPolynomial PUnit ℕ) := h
  have hx : IsUnit (MvPolynomial.X PUnit.unit : MvPolynomial PUnit ℕ) :=
    IsArtinianRing.isUnit_iff_isRegular.mpr MvPolynomial.isRegular_X
  have hz : IsUnit (0 : ℕ) := by
    simpa only [MvPolynomial.constantCoeff_X] using
      hx.map (MvPolynomial.constantCoeff : MvPolynomial PUnit ℕ →+* ℕ)
  exact not_isUnit_zero hz

private theorem lifted_zero_coefficient_polynomial_artinian {σ : Type u} :
    IsArtinianRing (MvPolynomial σ (ULift.{v} (ZMod 1))) := by
  exact isArtinian_of_finite (R := MvPolynomial σ (ULift.{v} (ZMod 1)))
    (M := MvPolynomial σ (ULift.{v} (ZMod 1)))

private theorem empty_lifted_zmod_four_polynomial_artinian :
    IsArtinianRing (MvPolynomial (ULift.{u} Empty) (ULift.{v} (ZMod 4))) := by
  let : IsArtinianRing (ZMod 4) := zmod_four_coefficient_conditions.2.2.2
  let : IsArtinianRing (ULift.{v} (ZMod 4)) :=
    (ULift.ringEquiv : ULift.{v} (ZMod 4) ≃+* ZMod 4).symm.isArtinianRing
  exact (MvPolynomial.isEmptyRingEquiv (ULift.{v} (ZMod 4))
    (ULift.{u} Empty)).symm.isArtinianRing

private theorem lifted_singleton_zmod_two_polynomial_not_artinian :
    ¬ IsArtinianRing (MvPolynomial (ULift.{u} PUnit) (ZMod 2)) := by
  intro h
  let : Nontrivial (ZMod 2) := zmod_two_field_conditions.2.1
  let : IsArtinianRing (MvPolynomial (ULift.{u} PUnit) (ZMod 2)) := h
  have hx : IsUnit (MvPolynomial.X (ULift.up PUnit.unit) :
      MvPolynomial (ULift.{u} PUnit) (ZMod 2)) :=
    IsArtinianRing.isUnit_iff_isRegular.mpr MvPolynomial.isRegular_X
  have hz : IsUnit (0 : ZMod 2) := by
    simpa only [MvPolynomial.constantCoeff_X] using
      hx.map (MvPolynomial.constantCoeff :
        MvPolynomial (ULift.{u} PUnit) (ZMod 2) →+* ZMod 2)
  exact not_isUnit_zero hz

end MultivariatePolynomialsTests
