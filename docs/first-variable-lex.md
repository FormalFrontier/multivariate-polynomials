# Scalar-top first-variable lex degree

Let `p : MvPolynomial (Fin (n + 1)) K` over a commutative semiring. Separating
variable zero gives a polynomial `F = MvPolynomial.finSuccEquiv K n p` whose
coefficients are multivariate polynomials in the remaining `n` variables. If
`F.natDegree = d` and `F.coeff d = MvPolynomial.C c` with `c ≠ 0`, then the
maximum degree in `MonomialOrder.lex` is the pure first-variable exponent
`(0 : Fin n →₀ ℕ).cons d`. Import
[`MultivariatePolynomials.FirstVariableLex`](../MultivariatePolynomials/FirstVariableLex.lean)
for `MonomialOrder.lex_degree_of_finSuccEquiv_scalar_top`.

Every supported exponent `β.cons i` has `i ≤ d`. If `i < d`, it lies strictly
below the pure degree-`d` exponent in the first-priority lex order, irrespective
of `β`. If `i = d`, the scalar-top hypothesis forces `β = 0`. Finally `c ≠ 0`
puts the pure exponent in the support. This proof does not use subtraction, a
domain assumption or a valuation. It includes `n = 0` and `d = 0`.

For **pointwise** comparison of exponents, the separate theorem
`Finsupp.cons_zero_le_cons_iff` says
`(0 : Fin n →₀ ℕ).cons d ≤ β.cons i ↔ d ≤ i`. The remaining coordinates
contribute no constraint because their baseline exponent is zero. This is a
componentwise cone, not a lexicographic upper interval.

The [direct-import examples](../Test/FirstVariableLex.lean) instantiate the
result over `ℕ`, including a nonconstant lower slice (`X 0 + X 1`), zero
degree, and no remaining variables. `X 1` over `Fin 2` illustrates the need
for the scalar-top condition: its maximum lex exponent has a nonzero tail.
