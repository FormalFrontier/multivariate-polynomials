# Polynomial-coefficient homogeneity

Import `MultivariatePolynomials.PolynomialCoefficientHomogeneity` to use
`MvPolynomial.IsHomogeneous.coeff_polynomial_interchange`. For any type of
variables `σ`, commutative semiring `R`, polynomial
`p : MvPolynomial σ (Polynomial R)` and naturals `d k`, its signature is:

```lean
p.IsHomogeneous d →
  ((((MvPolynomial.optionEquivRight R σ).symm.trans
    (MvPolynomial.optionEquivLeft R σ)) p).coeff k).IsHomogeneous d
```

This is the native composition of mathlib algebra equivalences, not a new
interchange operator. The variable of `Polynomial R` has weight **zero**: the
degree label `d` measures only the `σ`-variables, not the parameter's degree.
This is about homogeneous *labels*, not necessarily the actual total degree;
zero coefficients satisfy every label. No finite-variable, integral-domain,
field or nontriviality hypothesis is needed. The private proof establishes
the coefficient identity after interchange; coefficient extraction is additive,
not a ring homomorphism.

The ordinary-import client in
`Test/PolynomialCoefficientHomogeneity.lean` tests a finite
parameter substitution: for each `i : σ`, replace `X i` by
`∑ j : Fin (s + 1), C (Polynomial.X ^ j.val) * X (i, j)`.
The native `IsHomogeneous.eval₂` gives degree `d` for the substituted
polynomial, and the bridge gives the same label to *each* polynomial
coefficient. The client also checks zero, degree zero, `s = 0`, `ZMod 1` and
`ZMod 6` without strengthening the general assumptions. This theorem does
not assert actual-degree equality, recover a nonzero input from a coefficient,
or descend to finite bases.

The theorem and client are original project work using mathlib’s native interchange, not a new operator or a full coordinate-descent result. See [CREDITS.md](../CREDITS.md).

To reproduce checks from this project root with the pinned Lean toolchain and mathlib:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build MultivariatePolynomials.PolynomialCoefficientHomogeneity
lake --wfail build MultivariatePolynomialsTests
```
