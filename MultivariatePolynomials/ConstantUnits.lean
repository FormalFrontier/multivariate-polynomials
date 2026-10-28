/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Units among constant multivariate polynomials

The constant embedding of a commutative semiring into its multivariate polynomial
semiring is a local homomorphism: it preserves and reflects units. Reflection
follows from the retraction given by `MvPolynomial.constantCoeff`.

The instances below make the generic characteristic theorem `isUnit_map_iff`
(and its simp rule) available for both `MvPolynomial.C` and `algebraMap`.
-/

@[expose] public section

namespace MvPolynomial

universe u v

variable {R : Type u} {σ : Type v} [CommSemiring R]

/-- The constant embedding of a commutative semiring reflects units. -/
instance isLocalHom_C : IsLocalHom (C : R →+* MvPolynomial σ R) :=
  isLocalHom_of_leftInverse constantCoeff (constantCoeff_C σ)

/-- The scalar map into a multivariate polynomial semiring reflects units. -/
instance isLocalHom_algebraMap : IsLocalHom (algebraMap R (MvPolynomial σ R)) :=
  inferInstanceAs (IsLocalHom (C : R →+* MvPolynomial σ R))

end MvPolynomial
