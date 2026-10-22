/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Integral closure with infinitely many polynomial variables

The polynomial ring `MvPolynomial ℕ ℚ` is an integrally closed domain, and its
variable type is not finite. Mathlib's arbitrary-variable unique factorization
instance and its integral-closure theorem for GCD domains supply the ring-theoretic
inputs independently of the normal-domain polynomial instance.

## References

* `Mathlib.RingTheory.Polynomial.UniqueFactorization`: unique factorization for
  multivariate polynomial rings, without a finiteness assumption on the variables.
* `Mathlib.Algebra.GCDMonoid.IntegrallyClosed`: GCD domains are integrally closed.
-/

namespace MultivariatePolynomialsTests.InfiniteIntegrallyClosed

private theorem variables_not_finite : ¬ Finite ℕ :=
  Infinite.not_finite

private theorem isIntegrallyClosed : IsIntegrallyClosed (MvPolynomial ℕ ℚ) := by
  let : UniqueFactorizationMonoid (MvPolynomial ℕ ℚ) :=
    MvPolynomial.uniqueFactorizationMonoid ℕ
  exact GCDMonoid.toIsIntegrallyClosed

end MultivariatePolynomialsTests.InfiniteIntegrallyClosed
