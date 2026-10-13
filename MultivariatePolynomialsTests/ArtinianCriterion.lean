/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials
import Mathlib.Basic.NNReal.Defs
import Mathlib.RingTheory.Artinian.Module

/-!
# Applications of the Artinian polynomial criterion

The Artinian criterion rules out polynomial self-Artinianity whenever the
variable type is nonempty and the coefficient commutative semiring is nontrivial.
The scalars here are the polynomials themselves, acting by multiplication,
not just the coefficient semiring.

With their usual addition and multiplication, the nonnegative real numbers
form a semifield, but not a ring: the element `1` has no additive inverse.
Although their carrier is infinite, they are Artinian because their ideal
lattice has only two elements. The criterion gives Artinian polynomial
semirings over these coefficients with empty variables, but not with a single
variable. The relevant finiteness is finiteness of ideals, not finiteness of
the coefficient carrier.

## References

* `MultivariatePolynomials.Artinian`: the polynomial self-Artinian criterion.
* Mathlib, `Mathlib.Basic.NNReal.Defs`: the nonnegative real semifield with
  its usual operations.
* Mathlib, `Mathlib.RingTheory.Artinian.Module`: Artinianity of division
  semirings from their finite ideal lattice.
-/

universe u v

open scoped NNReal

namespace MultivariatePolynomialsTests

private theorem nonempty_polynomial_not_artinian {σ : Type u} {R : Type v}
    [CommSemiring R] [Nonempty σ] [Nontrivial R] :
    ¬ IsArtinianRing (MvPolynomial σ R) := by
  intro h
  rcases (MvPolynomial.isArtinianRing_iff.mp h).2 with hσ | hR
  · exact hσ.false (Classical.choice (inferInstance : Nonempty σ))
  · exact (not_subsingleton R) hR

private theorem empty_nnreal_polynomial_artinian :
    IsArtinianRing (MvPolynomial Empty ℝ≥0) := by
  exact MvPolynomial.isArtinianRing_iff.mpr ⟨inferInstance, Or.inl inferInstance⟩

private theorem singleton_nnreal_polynomial_not_artinian :
    ¬ IsArtinianRing (MvPolynomial PUnit ℝ≥0) := by
  exact nonempty_polynomial_not_artinian

end MultivariatePolynomialsTests
