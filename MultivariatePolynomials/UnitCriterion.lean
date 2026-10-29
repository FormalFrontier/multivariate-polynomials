/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.UnitCoefficients
public import MultivariatePolynomials.UnitSufficiency
public import Mathlib.Algebra.MvPolynomial.Nilpotent
import GroupTheory.MonoidLocalization.GrothendieckGroup.Nilpotent

/-!
# The coefficient criterion for units

A multivariate polynomial over a commutative semiring is a unit if and only if
its constant coefficient is a unit and all its nonconstant coefficients are
nilpotent additive units.

For necessity, map to the Grothendieck ring and apply Mathlib's
`MvPolynomial.isUnit_iff`. Additive invertibility of the original coefficients
allows `Algebra.GrothendieckAddGroup.isNilpotent_ofRingHom_iff` to reflect their
nilpotence. Sufficiency is `MvPolynomial.isUnit_of_coeff_isNilpotent_isAddUnit`.

Over a commutative ring the additive-invertibility conditions are redundant;
`MvPolynomial.isUnit_coeff_zero_and_isNilpotent_isAddUnit_iff` identifies the
coefficient conditions with those in Mathlib's criterion.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace MvPolynomial

/-- A polynomial over a commutative semiring is a unit exactly when its constant
coefficient is a unit and every nonconstant coefficient is a nilpotent additive
unit. This generalizes Mathlib's `MvPolynomial.isUnit_iff`. -/
theorem isUnit_iff_coeff_isNilpotent_isAddUnit
    {R : Type u} {σ : Type v} [CommSemiring R] {p : MvPolynomial σ R} :
    IsUnit p ↔ IsUnit (p.coeff 0) ∧ ∀ d ≠ 0,
      IsNilpotent (p.coeff d) ∧ IsAddUnit (p.coeff d) := by
  constructor
  · intro hp
    have hc : IsUnit (p.coeff 0) := by
      simpa only [constantCoeff_eq] using
        hp.map (constantCoeff : MvPolynomial σ R →+* R)
    refine ⟨hc, fun d hd => ?_⟩
    have ha := isAddUnit_coeff_of_isUnit hp hd
    refine ⟨?_, ha⟩
    have hu : IsUnit (map (Algebra.GrothendieckAddGroup.ofRingHom R) p) :=
      hp.map (map (Algebra.GrothendieckAddGroup.ofRingHom R))
    have hn := (MvPolynomial.isUnit_iff.mp hu).2 d hd
    exact (Algebra.GrothendieckAddGroup.isNilpotent_ofRingHom_iff ha).mp
      (by simpa only [coeff_map] using hn)
  · rintro ⟨hc, hn⟩
    exact isUnit_of_coeff_isNilpotent_isAddUnit p hc hn

/-- Over a commutative ring, the coefficient conditions with additive invertibility
are equivalent to the conditions in `MvPolynomial.isUnit_iff`. -/
theorem isUnit_coeff_zero_and_isNilpotent_isAddUnit_iff
    {R : Type u} {σ : Type v} [CommRing R] (p : MvPolynomial σ R) :
    (IsUnit (p.coeff 0) ∧ ∀ d ≠ 0,
      IsNilpotent (p.coeff d) ∧ IsAddUnit (p.coeff d)) ↔
      (IsUnit (p.coeff 0) ∧ ∀ d ≠ 0, IsNilpotent (p.coeff d)) := by
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨hc, fun d hd => (h d hd).1⟩
  · rintro ⟨hc, h⟩
    have hp : IsUnit p := isUnit_iff.mpr ⟨hc, h⟩
    exact ⟨hc, fun d hd => ⟨h d hd, isAddUnit_coeff_of_isUnit hp hd⟩⟩

end MvPolynomial
