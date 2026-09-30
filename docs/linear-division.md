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
`Test/LinearDivision.lean`. They exercise
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

The producer is transferred unchanged from the reviewed incubator revision
`dd83b2ff0e22e8296fec1bfc90aa21ae2c30f681` (original isolated donor
`c5f1df76f937c4998dd32fc6ae0927d228228841`) at pinned Lean
`v4.34.0-rc2` and mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`.
Its earlier acceptance does not establish acceptance or publication of this
destination module. Source-specific correspondence is tracked separately:
this library claims neither complete coverage of any source nor
restricted-series division.

Provenance: the reused mathlib `MonomialOrder.div` algorithm is by Antoine
Chambert-Loir; native `Finsupp.linearCombination`, `coeffsIn` and associated
mathlib infrastructure are credited to their mathlib contributors. The
basis-witness selection, its `R`-linear extension, proofs and clients were
authored by formalization-worker-a, Hive Task
`hive-request-8f572d0acbd2a67fa6928136f1d95e308310f068` (UID
`c2ca9eef-6f30-47f8-aa69-03b5696b517b`). Registration into the accepted
incubator parent was by worker-a Task
`hive-request-c1398e69c939502c9cd691c5b69a7aded3986119` (UID
`2ee8b752-3803-4e73-a0eb-3d627aa580a9`) and independently reviewed by
worker-b Task `hive-request-825f4191bc7b3fcd6dcf31cb48420d298e4cf453`
(UID `aeb09a2a-10e3-4d4e-8a32-5937cddc10bb`). The present transfer is
mechanical, not new mathematical authorship or independent destination review.
