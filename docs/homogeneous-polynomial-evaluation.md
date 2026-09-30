# Homogeneous polynomial evaluation under variable scaling

Import `MultivariatePolynomials.HomogeneousEvaluation` directly, or import
`MultivariatePolynomials` for the aggregate public interface. The ordinary-import
client is [`Test/HomogeneousEvaluation.lean`](../Test/HomogeneousEvaluation.lean);
neither import requires an incubator or source-repository dependency.

For any index type `ι`, commutative semirings `B`, `R`, unital ring homomorphism
`σ : B →+* R`, variable values `v : ι → R`, weights `w : ι → ℕ`, degree `d : ℕ`,
polynomial `p : MvPolynomial ι B` and scalar `a : R`, the theorem
`MvPolynomial.IsWeightedHomogeneous.eval₂Hom_scaleVariables` says that if
`p.IsWeightedHomogeneous w d`, then

```lean
MvPolynomial.eval₂Hom σ (fun i => a ^ w i * v i) p =
  a ^ d * MvPolynomial.eval₂Hom σ v p
```

The ordinary homogeneous specialization
`MvPolynomial.IsHomogeneous.eval₂Hom_mul_left`, assuming
`p.IsHomogeneous d`, replaces the variable function with `fun i => a * v i`.
The coefficient homomorphism is **unchanged** in both equalities. No nonzero,
unit, integral-domain, finite-index, positive-degree or nonempty-index hypothesis
is needed. In particular the results apply to the zero polynomial and zero
semiring, empty index types, zero weights, degree zero and zero scalar; `a ^ 0`
keeps its ordinary semiring meaning.

The proof expands `p` into its finite monomial support via native
`MvPolynomial.support_sum_monomial_coeff`, uses native
`MvPolynomial.eval₂Hom_monomial`, converts the product of scalar powers to the
power of `Finsupp.weight w`, and applies the weighted-homogeneity hypothesis
to each occurring monomial. The ordinary case uses mathlib's definition
`IsHomogeneous = IsWeightedHomogeneous 1`. This asserts an equality of evaluations
of a homogeneous polynomial, **not** a ring homomorphism sending all polynomials
to `a ^ degree` times their evaluations.

The [producer](../MultivariatePolynomials/HomogeneousEvaluation.lean) depends only on mathlib. Formal Frontier Agents developed these scaling laws independently of the motivating ideal example; see [CREDITS.md](../CREDITS.md).
