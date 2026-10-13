/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Artinian.Module

@[expose] public section

/-!
# Artinian multivariate polynomial semirings

A multivariate polynomial semiring is Artinian as a module over itself if and only if
its coefficient semiring is Artinian and either there are no variables or the
coefficient semiring is subsingleton.

The scalars in `IsArtinianRing (MvPolynomial σ R)` are the polynomials themselves,
not the coefficients in `R`.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Basic` and
  `Mathlib.Algebra.MvPolynomial.Equiv`: regular variables, constant coefficients,
  and the empty-variable equivalence.
* Mathlib, `Mathlib.RingTheory.Artinian.Module`: surjective descent,
  transport along ring equivalences, finite Artinian modules, and the equivalence
  between regular elements and units in Artinian semirings.
* Mathlib, `Mathlib.Algebra.Group.Units.Hom` and
  `Mathlib.Algebra.GroupWithZero.Units.Basic`: images of units and the criterion
  for zero to be a unit.
-/

universe u v

namespace MvPolynomial

/-- A multivariate polynomial semiring is Artinian over itself exactly when its coefficient
semiring is Artinian and either its variable type is empty or its coefficient semiring
is subsingleton. -/
theorem isArtinianRing_iff {σ : Type u} {R : Type v} [CommSemiring R] :
    IsArtinianRing (MvPolynomial σ R) ↔ IsArtinianRing R ∧ (IsEmpty σ ∨ Subsingleton R) := by
  constructor
  · intro h
    let : IsArtinianRing (MvPolynomial σ R) := h
    have hsurj : Function.Surjective (constantCoeff : MvPolynomial σ R →+* R) :=
      fun r ↦ ⟨C r, constantCoeff_C σ r⟩
    refine ⟨hsurj.isArtinianRing, ?_⟩
    rcases isEmpty_or_nonempty σ with hσ | hσ
    · exact Or.inl hσ
    · right
      let i : σ := Classical.choice hσ
      -- A regular variable is a unit; its constant coefficient then makes zero a unit.
      have hx : IsUnit (X i : MvPolynomial σ R) :=
        IsArtinianRing.isUnit_iff_isRegular.mpr isRegular_X
      have hz : IsUnit (0 : R) := by
        simpa only [constantCoeff_X] using
          hx.map (constantCoeff : MvPolynomial σ R →+* R)
      exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hz)
  · rintro ⟨hR, hσ | hRsub⟩
    · let : IsArtinianRing R := hR
      let : IsEmpty σ := hσ
      exact (isEmptyAlgEquiv R σ).toRingEquiv.symm.isArtinianRing
    · let : Subsingleton R := hRsub
      exact isArtinian_of_finite (R := MvPolynomial σ R) (M := MvPolynomial σ R)

end MvPolynomial
