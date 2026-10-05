/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import MultivariatePolynomials

/-!
# Selected public axiom check

This private-by-module test prints the transitive axioms of the public theorem.
It is not a census of every stored private theorem or generated declaration.

## References

* `MultivariatePolynomials.IdealOfVars`: the theorem whose axioms are printed;
  see that module for its mathematical and Mathlib sources.
-/

#print axioms MvPolynomial.idealOfVars_not_fg
