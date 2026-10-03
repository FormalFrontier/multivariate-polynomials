# Monic multivariate polynomial lifts

SPDX-License-Identifier: Apache-2.0

Import `MultivariatePolynomials.MonicLift` directly, or import the public aggregate
`MultivariatePolynomials`. For any variable type `σ`, commutative rings `R` and
`S`, monomial order `m : MonomialOrder σ`, surjective coefficient homomorphism
`φ : R →+* S`, and `p : MvPolynomial σ S` with `hp : m.Monic p`, the theorem
`m.exists_monic_lift φ hφ p hp` states:

```lean
∃ q : MvPolynomial σ R,
  MvPolynomial.map φ q = p ∧ m.Monic q ∧ m.degree q = m.degree p
```

The last equality is **literal equality of exponents** in `σ →₀ ℕ`, not merely
equality up to the monomial-order relation. There is no finite-variable,
injectivity, domain, field, local-ring or unconditional `Nontrivial` hypothesis.
The lift is existential, not a canonical choice or uniqueness assertion.

When `S` is nontrivial, choose coefficient preimages for the finite support of
`p`, set the leading coefficient to `1`, and set coefficients outside the
support to `0`. The nonzero chosen coefficients and leading coefficient give
actual support equality, hence equal degrees and a monic lift. When `S` is the
zero ring, `p = 1` and taking `q = 1` proves the stated map, monicity and degree
equalities; **support equality is not asserted** in this branch.

The [ordinary-import client](../MultivariatePolynomialsTests/MonicLift.lean) covers the generic
interface, a noninjective integer quotient, empty variables, a zero target
and a zero source. With this repository's pinned Lean toolchain and mathlib
revision, fetch the matching precompiled cache successfully in the project
root **before** the focused producer/client commands:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake --wfail build MultivariatePolynomials.MonicLift
LEAN_NUM_THREADS=2 lake --wfail build MultivariatePolynomialsTests.MonicLift
```

Riccardo Brasca’s mathlib `Polynomial.lifts_and_natDegree_eq_and_monic` is a univariate analogue; Antoine Chambert-Loir’s `MonomialOrder` infrastructure also informs this distinct project proof. See [CREDITS.md](../CREDITS.md).
