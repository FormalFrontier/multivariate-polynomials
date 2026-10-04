# Fixed linear multivariate-polynomial division

SPDX-License-Identifier: Apache-2.0

Import `MultivariatePolynomials.LinearDivision`. Given any variable
type `σ`, commutative ring `R`, monomial order `m : MonomialOrder σ`, and
arbitrary family `b : ι → MvPolynomial σ R` with
`hb : ∀ i, IsUnit (m.leadingCoeff (b i))`, this module constructs **fixed
`R`-linear maps**

```lean
m.linearDivisionQuotient b hb  : MvPolynomial σ R →ₗ[R] (ι →₀ MvPolynomial σ R)
m.linearDivisionRemainder b hb : MvPolynomial σ R →ₗ[R] MvPolynomial σ R
```

For every `p`, `linearDivision_decomposition` states
`p = Finsupp.linearCombination (MvPolynomial σ R) b (Q p) + B p`.
The coefficient ring of this `Finsupp.linearCombination` is the **polynomial
ring**, since its weights are quotient polynomials; the *operators* `Q` and
`B` are linear over `R`. The theorem `linearDivision_remainder_support` states
that each actual exponent `α ∈ (B p).support` satisfies
`∀ i, ¬ m.degree (b i) ≤ α`. Here `≤` is **componentwise exponent order**,
not a comparison in the monomial order `m`. For every `J : Ideal R`,
`linearDivision_remainder_coeffsIn` and
`linearDivision_quotient_coeffsIn` preserve the native `MvPolynomial.coeffsIn`
condition for `B p` and each quotient coordinate `(Q p) i`. This applies in
particular to `J ^ n` without adding a filtration type. The
`linearDivision_remainder_of_reduced` and
`linearDivision_quotient_of_reduced` laws say that input already avoiding all
cones has `B p = p` and `Q p = 0`.

Unlike a second existence theorem for polynomial division, these operators
select a division witness **once for each basis monomial** and extend the
selection `R`-linearly across finite support. For a monomial already outside
all cones, the selected witness is exactly `(0, monomial α 1)`. Other division
witnesses need not be unique; no uniqueness or canonical independence of the
chosen maps, Gröbner-basis hypothesis, finite-variable hypothesis, or
restricted-series division is claimed.

Ordinary-import clients are in
`MultivariatePolynomialsTests/LinearDivision.lean`. They exercise
decomposition and literal cone avoidance, linearity, arbitrary coefficient
ideals (including the nonzero proper ideal `(2)` in `ZMod 4`), a finite family,
an empty divisor family, zero input, the zero ring, and an already reduced
constant relative to the nonempty family `{X₀}`. These are proof clients, not
computations of choice-dependent quotient values. For a cache-first focused
check in the pinned Lake project:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake build MultivariatePolynomials.LinearDivision
LEAN_NUM_THREADS=2 lake build MultivariatePolynomialsTests
```

Mathlib’s `MonomialOrder.div` infrastructure is credited to Antoine Chambert-Loir.
The fixed linear maps and their Lean clients are separate original project work;
see [CREDITS.md](../CREDITS.md).
