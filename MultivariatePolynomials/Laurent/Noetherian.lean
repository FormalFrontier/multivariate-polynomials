/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.Laurent.Basic
public import MultivariatePolynomials.Noetherian

import CoherentModules.RingTheory.Noetherian

/-!
# Left-Noetherian Laurent polynomial rings

The central Laurent polynomial ring over a left-Noetherian ring is left-Noetherian.
The coefficient ring need not be commutative, and the zero ring is included.
Noetherianity here concerns the regular left self-module, not the module over
the coefficient ring.

## References

The proof combines the arbitrary-ring polynomial Hilbert basis theorem in
`MultivariatePolynomials.Noetherian` with the left-unit clearing criterion in
`CoherentModules.RingTheory.Noetherian`. The latter API was developed with
Plinth's assistance.
-/

@[expose] public section

universe u

namespace LaurentPolynomial

/-- The central Laurent polynomial ring over a left-Noetherian ring is left-Noetherian.
No commutativity or nontriviality assumption on the coefficient ring is needed. -/
theorem isNoetherianRing_of_isNoetherianRing
    {R : Type u} [Ring R] [IsNoetherianRing R] :
    IsNoetherianRing (LaurentPolynomial R) :=
  _root_.isNoetherianRing_of_unit_mul_mem_range
    (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R)
    exists_unit_mul_mem_range_toLaurent

attribute [instance 100] isNoetherianRing_of_isNoetherianRing

end LaurentPolynomial
