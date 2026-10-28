/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import MultivariatePolynomials.IntegrallyClosed

/-!
# Integral closure with infinitely many polynomial variables

The polynomial ring `MvPolynomial ℕ ℚ` is an integrally closed domain, and its
variable type is not finite. Mathlib's arbitrary-variable unique factorization
instance and its integral-closure theorem for GCD domains supply the ring-theoretic
inputs independently of the normal-domain polynomial instance. This coefficient
ring in turn gives the iterated ring `MvPolynomial ℕ (MvPolynomial ℕ ℚ)` treated in
`MultivariatePolynomials.IntegrallyClosed`.

## References

* `Mathlib.RingTheory.Polynomial.UniqueFactorization`: unique factorization for
  multivariate polynomial rings, without a finiteness assumption on the variables.
* `Mathlib.Algebra.GCDMonoid.IntegrallyClosed`: GCD domains are integrally closed.
-/
