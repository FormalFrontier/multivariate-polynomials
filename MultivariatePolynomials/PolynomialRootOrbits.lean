/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Minpoly.IsConjRoot

/-!
# Polynomial roots and automorphism orbits

In a normal field extension, the automorphism orbit of an element is the set of
roots of its minimal polynomial. Its cardinality is the polynomial's separable
degree, and equals the full degree exactly when the element is separable.
Normality includes algebraicity; neither separability nor finite-dimensionality
of the extension is assumed. Inseparable roots are counted only once.

## References

The orbit identification uses Mathlib's `Normal.minpoly_eq_iff_mem_orbit` and
`isConjRoot_iff_mem_minpoly_rootSet`. The cardinality comparison uses Mathlib's
`Polynomial.natSepDegree_eq_of_splits` and
`Polynomial.natSepDegree_eq_natDegree_iff`.
-/

@[expose] public section

universe u v

namespace Normal

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The conjugates under automorphisms of a normal extension are precisely the
roots of the element's minimal polynomial. -/
theorem orbit_eq_rootSet_minpoly [Normal K L] (x : L) :
    MulAction.orbit (L ≃ₐ[K] L) x = (minpoly K x).rootSet L := by
  ext y
  rw [← minpoly_eq_iff_mem_orbit,
    ← isConjRoot_iff_mem_minpoly_rootSet ((inferInstance : Normal K L).isIntegral x),
    isConjRoot_def]
  exact eq_comm

/-- The number of automorphism conjugates is the separable degree of the minimal
polynomial, without assuming that the element is separable. -/
theorem ncard_orbit_eq_natSepDegree [Normal K L] (x : L) :
    (MulAction.orbit (L ≃ₐ[K] L) x).ncard = (minpoly K x).natSepDegree := by
  classical
  rw [orbit_eq_rootSet_minpoly, Polynomial.rootSet_def, Set.ncard_coe_finset]
  exact (Polynomial.natSepDegree_eq_of_splits (minpoly K x)
    ((inferInstance : Normal K L).splits x)).symm

/-- An automorphism orbit in a normal extension has the full minimal-polynomial
degree exactly when the element is separable over the base field. -/
theorem ncard_orbit_eq_natDegree_iff_isSeparable [Normal K L] (x : L) :
    (MulAction.orbit (L ≃ₐ[K] L) x).ncard = (minpoly K x).natDegree ↔ IsSeparable K x := by
  rw [ncard_orbit_eq_natSepDegree]
  exact Polynomial.natSepDegree_eq_natDegree_iff (minpoly K x)
    (minpoly.ne_zero ((inferInstance : Normal K L).isIntegral x))

end Normal
